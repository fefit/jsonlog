use clap::Parser;
use evalexpr::{context_map, ContextWithMutableVariables, Function, Value as EvalValue};
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use regex::Regex;
use serde_json::Value as JsonValue;
use std::collections::HashMap;
use std::error::Error;
use std::fs::File;
use std::io::{BufRead, BufReader, Read};

type JsonData = HashMap<String, JsonValue>;
type BoxDynOutputFn = Box<dyn Fn(&JsonData) -> String + Send + Sync>;
type BoxDynCondFn = Box<dyn Fn(&JsonData) -> bool + Send + Sync>;
/// Simple program to greet a person
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
  /// Start index of the row number
  #[arg(short = 'i', long, allow_negative_numbers(true))]
  index: Option<i32>,

  /// The splitter of the row, use
  #[arg(short = 's', long, default_value_t = String::from("\n"))]
  split: String,

  /// Format the display
  #[arg(short = 'd', long)]
  disp: String,

  /// Condition to filter the rows
  #[arg(short = 'c', long)]
  cond: Option<String>,

  /// The parallel count for output data.
  #[arg(short = 'p', long, default_value_t = 4)]
  par: usize,

  /// The count of rows should be shown
  #[arg(short = 'n', long)]
  num: Option<usize>,

  /// The log file.
  file: String,
}

/**
 * Proxy value
 */
pub enum ProxyValue {
  Bool(bool),
  Float(f64),
  Int(i64),
  Null,
  String(String),
  Unexpected(String),
}

impl From<&JsonValue> for ProxyValue {
  fn from(json: &JsonValue) -> Self {
    match json {
      JsonValue::Bool(b) => ProxyValue::Bool(*b),
      JsonValue::Number(n) => {
        if n.is_f64() {
          return ProxyValue::Float(n.as_f64().unwrap());
        }
        ProxyValue::Int(n.as_i64().unwrap())
      }
      JsonValue::Null => ProxyValue::Null,
      JsonValue::String(s) => ProxyValue::String(s.clone()),
      v => ProxyValue::Unexpected(format!("{:?}", v)),
    }
  }
}

impl From<ProxyValue> for EvalValue {
  fn from(value: ProxyValue) -> EvalValue {
    match value {
      ProxyValue::Bool(b) => EvalValue::Boolean(b),
      ProxyValue::String(s) => EvalValue::String(s),
      ProxyValue::Float(f) => EvalValue::Float(f),
      ProxyValue::Int(i) => EvalValue::Int(i),
      ProxyValue::Null => EvalValue::Empty,
      ProxyValue::Unexpected(s) => EvalValue::String(s),
    }
  }
}

/**
 *
 *
 */
struct BufferedOutput {
  output_fn: BoxDynOutputFn,
  cond_fn: BoxDynCondFn,
  cap: usize,
  data: Vec<String>,
  rows: usize,
}

impl BufferedOutput {
  /**
   * new instance
   */
  fn new(cap: usize, output_fn: BoxDynOutputFn, cond_fn: BoxDynCondFn) -> Self {
    let cap = cap.min(1);
    BufferedOutput {
      cap: cap.min(1),
      cond_fn,
      output_fn,
      data: Vec::with_capacity(cap),
      rows: 0,
    }
  }
  /**
   * end
   */
  fn end(&mut self) {
    let cond_fn = self.cond_fn.as_mut();
    let output_fn = &self.output_fn;
    self.data.par_iter().for_each(|r| {
      if let Ok(json) = serde_json::from_str::<JsonData>(r) {
        if cond_fn(&json) {
          print!("{}", output_fn(&json));
        }
      }
    });
  }
  /**
   * push data
   */
  fn push(&mut self, row: String) {
    if self.rows == 0 {
      let cond_fn = &mut self.cond_fn;
      let output_fn = &self.output_fn;
      if let Ok(json) = serde_json::from_str::<JsonData>(&row) {
        if cond_fn(&json) {
          println!();
          print!("{}", output_fn(&json));
        }
      }
    } else {
      let index = self.rows % self.cap;
      self.data[index] = row;
      self.rows += 1;
      if self.rows == self.cap {
        self.end();
      }
    };
  }
}

fn main() -> Result<(), Box<dyn Error>> {
  let args = Args::parse();
  let start_index = if let Some(start) = args.index {
    0.min(start)
  } else {
    0
  } as usize;
  // build the display data
  let mut output_fns: Vec<BoxDynOutputFn> = vec![];
  {
    let mut quote_char = '\0';
    let mut maybe_escape = false;
    let mut is_expr = false;
    let mut cur_str = String::new();
    let mut iter = args.disp.chars();
    // iterator over the display string
    while let Some(ch) = iter.next() {
      if is_expr {
        // in expr
        if quote_char != '\0' {
          if quote_char == ch {
            quote_char = '\0';
          }
        } else {
          // not in quote
          if ch == '}' {
            let expr = evalexpr::build_operator_tree(&cur_str)?;
            output_fns.push(Box::new(move |data: &JsonData| {
              let mut ctx_disp = context_map! {
                "__len__" => 1
              }
              .unwrap();
              for (key, value) in data.iter() {
                ctx_disp
                  .set_value(key.into(), ProxyValue::from(value).into())
                  .unwrap();
              }
              format!("{}", expr.eval_with_context(&ctx_disp).unwrap())
            }));
            cur_str = String::new();
            is_expr = false;
            continue;
          } else if ch == '"' || ch == '\'' {
            quote_char = ch;
          }
        }
        cur_str.push(ch);
      } else {
        // not in expr
        if ch == '{' {
          if let Some(next_ch) = iter.next() {
            if next_ch == '{' {
              cur_str.push(ch);
            } else {
              if !cur_str.is_empty() {
                let seg = std::mem::take(&mut cur_str);
                output_fns.push(Box::new(move |_| seg.clone()));
              }
              cur_str.push(next_ch);
              is_expr = true;
            }
          }
        } else if ch == '}' {
          if maybe_escape {
            maybe_escape = false;
          } else {
            maybe_escape = true;
            cur_str.push(ch);
          }
        } else {
          cur_str.push(ch);
        }
      }
    }
    // at the end, the cur_str is not empty, should take as a string
    if !cur_str.is_empty() {
      output_fns.push(Box::new(move |_| cur_str.clone()));
    }
  }
  // generate output function
  let output_fn = Box::new(move |data: &JsonData| {
    let mut result = String::new();
    for cb in output_fns.iter() {
      let seg = cb(data);
      result.push_str(&seg);
    }
    result
  });
  // condition function
  let cond_fn: BoxDynCondFn = if let Some(cond) = args.cond {
    let expr = evalexpr::build_operator_tree(&cond)
      .map_err(|e| format!("The --cond argument uses an unsupported expression:{}", e))?;
    Box::new(move |data: &JsonData| {
      let mut ctx_cond = context_map! {
        "__len__" => 1
      }
      .unwrap();
      for (key, value) in data.iter() {
        ctx_cond
          .set_value(key.into(), ProxyValue::from(value).into())
          .unwrap_or(());
      }
      let bool_cond = expr.eval_boolean_with_context(&ctx_cond);
      bool_cond.unwrap_or(false)
    })
  } else {
    Box::new(|_: &JsonData| true)
  };
  //
  let mut buf_output = BufferedOutput::new(args.par, output_fn, cond_fn);
  // get the split string array
  if args.split == "\n" {
    let file = File::open(args.file)?;
    let reader = BufReader::new(file);
    if start_index == 0 {
      for line in reader.lines() {
        buf_output.push(line?);
      }
    } else {
      for line in reader.lines().skip(start_index) {
        buf_output.push(line?);
      }
    }
  } else {
    let rule = Regex::new(&args.split)
      .map_err(|e| format!("The --split argument is not a valid regex: {}", e))
      .unwrap();
    let mut file = File::open(args.file)?;
    let mut content = String::with_capacity(200);
    file.read_to_string(&mut content)?;
    let mut segs = content.split(&rule).collect::<Vec<&str>>();
    // jump index
    if start_index > 0 {
      segs
        .split_off(start_index)
        .iter()
        .for_each(|s| buf_output.push(s.to_string()));
    } else {
      segs.iter().for_each(|s| buf_output.push(s.to_string()));
    }
  }
  Ok(())
}
