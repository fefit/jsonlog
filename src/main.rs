use clap::Parser;
use evalexpr::{context_map, ContextWithMutableVariables, Function, Value as EvalValue};
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use regex::Regex;
use serde_json::Value as JsonValue;
use std::collections::HashMap;
use std::error::Error;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Read};
use std::process;

type JsonData = HashMap<String, JsonValue>;
type BoxDynOutputFn = Box<dyn Fn(&JsonData) -> String + Send + Sync>;
type BoxDynCondFn = Box<dyn Fn(&JsonData) -> bool + Send + Sync>;

/// Simple program to greet a person
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
  /// Start index of the row number
  #[arg(short = 'i', long)]
  index: Option<usize>,

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
  #[arg(short = 'p', long)]
  par: Option<usize>,

  /// The count of rows should be shown
  #[arg(short = 'n', long, default_value_t = 0)]
  num: usize,

  /// The log file.
  file: Option<String>,
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
 * Buffered Output
 *
 */
struct BufferedOutput {
  output_fn: BoxDynOutputFn,
  cond_fn: BoxDynCondFn,
  cap: usize,
  data: Vec<String>,
  rows: usize,
  last_index: usize,
  non_first: bool,
  max_rows: usize,
}

impl BufferedOutput {
  /**
   * new instance
   */
  fn new(cap: usize, max_rows: usize, output_fn: BoxDynOutputFn, cond_fn: BoxDynCondFn) -> Self {
    let cap = if cap == 0 { 1 } else { cap };
    BufferedOutput {
      cap,
      last_index: cap - 1,
      cond_fn,
      output_fn,
      data: vec![String::new(); cap],
      rows: 0,
      max_rows,
      non_first: false,
    }
  }
  /**
   * end
   */
  fn end(&mut self, is_end: bool) {
    let rows = if is_end {
      self.rows % self.cap
    } else {
      self.cap
    };
    if rows > 0 {
      let cond_fn = self.cond_fn.as_mut();
      let output_fn = &self.output_fn;
      let result = self.data[0..rows]
        .par_iter()
        .map(|r| {
          if let Ok(json) = serde_json::from_str::<JsonData>(r) {
            if cond_fn(&json) {
              return (true, output_fn(&json));
            }
          }
          (false, String::new())
        })
        .collect::<Vec<(bool, String)>>();
      result.iter().for_each(|(is_ok, s)| {
        if *is_ok {
          println!();
          print!("{}", s);
        }
      });
    }
  }
  /**
   * push data
   */
  fn push(&mut self, row: String) {
    if self.non_first {
      let index = self.rows % self.cap;
      self.data[index] = row;
      self.rows += 1;
      if self.rows + 1 == self.max_rows {
        self.end(true);
        process::exit(0);
      } else if index == self.last_index {
        self.end(false);
      }
    } else {
      let cond_fn = &mut self.cond_fn;
      let output_fn = &self.output_fn;
      if let Ok(json) = serde_json::from_str::<JsonData>(&row) {
        if cond_fn(&json) {
          print!("{}", output_fn(&json));
          self.non_first = true;
        }
      }
      if self.max_rows == 1 {
        process::exit(0);
      }
    };
  }
}

fn main() -> Result<(), Box<dyn Error>> {
  let args = Args::parse();
  let start_index = args.index.unwrap_or(0);
  let max_rows = if args.num == 0 { usize::MAX } else { args.num };
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
                "_len_" => Function::new(|argument| {
                  if let Ok(s) = argument.as_string() {
                    return Ok(EvalValue::Int(s.len() as i64));
                  }
                  Ok(argument.clone())
                })
              }
              .unwrap();
              for (key, value) in data.iter() {
                ctx_disp
                  .set_value(key.into(), ProxyValue::from(value).into())
                  .unwrap();
              }
              if let Ok(value) = expr.eval_with_context(&ctx_disp) {
                match value {
                  EvalValue::String(s) => s,
                  v => format!("{}", v),
                }
              } else {
                String::new()
              }
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
        "_len_" => Function::new(|argument| {
          if let Ok(s) = argument.as_string() {
            return Ok(EvalValue::Int(s.len() as i64));
          }
          Ok(EvalValue::Int(0))
        })
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
  // buffered output
  let mut buf_output = BufferedOutput::new(
    args.par.unwrap_or_else(num_cpus::get),
    max_rows,
    output_fn,
    cond_fn,
  );
  // read the logs from file
  if args.split == "\n" {
    if let Some(args_file) = args.file {
      let file = File::open(args_file)?;
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
      let lines = io::stdin().lock().lines();
      if start_index > 0 {
        for line in lines.skip(start_index) {
          let input = line?;
          if input.is_empty() {
            break;
          }
          buf_output.push(input);
        }
      } else {
        for line in lines {
          let input = line?;
          if input.is_empty() {
            break;
          }
          buf_output.push(input);
        }
      }
    }
  } else {
    let rule = Regex::new(&args.split)
      .map_err(|e| format!("The --split argument is not a valid regex: {}", e))
      .unwrap();
    let mut content = String::with_capacity(200);
    if let Some(args_file) = args.file {
      let mut file = File::open(args_file)?;
      file.read_to_string(&mut content)?;
    } else {
      let lines = io::stdin().lock().lines();
      for line in lines {
        let input = line?;
        if input.is_empty() {
          break;
        }
        content.push_str(&input);
      }
    }
    // jump index
    if start_index > 0 {
      rule
        .split(&content)
        .into_iter()
        .skip(start_index)
        .for_each(|s| {
          buf_output.push(s.to_string());
        });
    } else {
      rule
        .split(&content)
        .into_iter()
        .for_each(|s| buf_output.push(s.to_string()));
    }
  }
  buf_output.end(true);
  Ok(())
}
