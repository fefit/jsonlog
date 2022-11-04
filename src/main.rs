use clap::Parser;
use evalexpr::{
  context_map, ContextWithMutableFunctions, ContextWithMutableVariables, Function,
  Value as EvalValue,
};
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use regex::Regex;
use serde_json::Value as JsonValue;
use std::collections::HashMap;
use std::error::Error as StdError;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Read};
use std::process;
use thiserror::Error;

type JsonData = HashMap<String, JsonValue>;
type BoxDynOutputFn = Box<dyn Fn(&JsonData) -> String + Send + Sync>;
type BoxDynCondFn = Box<dyn Fn(&JsonData) -> bool + Send + Sync>;
type BoxDynError = Box<dyn StdError>;
#[derive(Error, Debug)]
enum ArgumentError {
  #[error("{0}")]
  Parse(String),
}

const ESCAPE_CHARS: [(char, char); 9] = [
  ('n', 0x0a as char),
  ('t', 0x09 as char),
  ('\\', '\\'),
  ('r', 0x0d as char),
  ('v', 0x0b as char),
  ('f', 0x0c as char),
  ('?', 0x3f as char),
  ('a', 0x07 as char),
  ('b', 0x08 as char),
];

#[inline]
fn is_hex_char(ch: char) -> bool {
  matches!(ch, '0'..='9' | 'a'..='f' | 'A'..='F')
}

#[inline]
fn hex_to_char(hex_str: &str) -> Result<char, BoxDynError> {
  radix_str_to_char(hex_str, 16)
}

#[inline]
fn radix_str_to_char(radix_str: &str, radix: u32) -> Result<char, BoxDynError> {
  let code = u32::from_str_radix(radix_str, radix).unwrap();
  if let Some(ch) = std::char::from_u32(code) {
    return Ok(ch);
  }
  Err(Box::new(ArgumentError::Parse(format!(
    "invalid universal character \\u{}",
    radix_str
  ))))
}

fn escape_normal(ch: char) -> Option<char> {
  for (orig, esc) in ESCAPE_CHARS {
    if ch == orig {
      return Some(esc);
    }
  }
  None
}

#[derive(PartialEq, Eq)]
enum EscapeRandWidth {
  Hex,
  Octal,
}

/// A commond line tool for parsing json data logs.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
  /// The data starting number index
  #[arg(short = 'i', long, default_value_t = 0)]
  index: usize,

  /// The data seperator
  #[arg(short = 's', long, default_value_t = String::from("\n"))]
  sep: String,

  /// Each data output display template
  #[arg(short = 'd', long)]
  disp: String,

  /// Filter condition expression for each data
  #[arg(short = 'c', long)]
  cond: Option<String>,

  /// Number of parallel buffered outputs
  #[arg(short = 'p', long)]
  par: Option<usize>,

  /// The total number of data
  #[arg(short = 'n', long, default_value_t = usize::MAX)]
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

fn main() -> Result<(), BoxDynError> {
  let args = Args::parse();
  let start_index = args.index;
  let max_rows = if args.num == 0 { usize::MAX } else { args.num };
  // build the display data
  let mut output_fns: Vec<BoxDynOutputFn> = vec![];
  {
    let mut quote_char = '\0';
    let mut maybe_escape = false;
    let mut is_expr = false;
    let mut cur_str = String::new();
    let mut iter = args.disp.chars();
    let mut escaped: Option<EscapeRandWidth> = None;
    let mut rand_escaped = String::new();
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
            // get the variable identifiers
            let var_idents = expr
              .iter_variable_identifiers()
              .into_iter()
              .map(|s| s.to_string())
              .collect::<Vec<_>>();
            // get the function identifiers
            let fn_idents = expr
              .iter_function_identifiers()
              .into_iter()
              .map(|s| s.to_string())
              .collect::<Vec<_>>();
            output_fns.push(Box::new(move |data: &JsonData| {
              let mut ctx_disp = evalexpr::HashMapContext::new();
              // register variables, if not exist, registy an empty value
              for key in &var_idents {
                let value = if let Some(val) = data.get(key) {
                  ProxyValue::from(val).into()
                } else {
                  EvalValue::Empty
                };
                ctx_disp.set_value(key.into(), value).unwrap();
              }
              let keys = data.keys().cloned().collect::<Vec<_>>();
              if fn_idents.contains(&String::from("has_key")) {
                ctx_disp
                  .set_function(
                    "has_key".into(),
                    Function::new(move |argument| {
                      if let Ok(k) = argument.as_string() {
                        return Ok(EvalValue::Boolean(keys.contains(&k)));
                      }
                      Ok(EvalValue::Boolean(false))
                    }),
                  )
                  .unwrap();
              }
              if let Ok(value) = expr.eval_with_context(&ctx_disp) {
                match value {
                  EvalValue::String(s) => s,
                  EvalValue::Empty => String::new(),
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
        // special escape
        if let Some(esc) = &escaped {
          let mut has_parsed = false;
          let mut esc_end = false;
          let mut radix: u32 = 16;
          match esc {
            EscapeRandWidth::Hex => {
              if is_hex_char(ch) {
                rand_escaped.push(ch);
                has_parsed = true;
              }
              esc_end = true;
            }
            EscapeRandWidth::Octal => {
              if matches!(ch, '0'..='7') {
                rand_escaped.push(ch);
                esc_end = rand_escaped.len() == 3;
                has_parsed = true;
              } else {
                esc_end = true;
              }
              radix = 8;
            }
          }
          if esc_end {
            cur_str.push(radix_str_to_char(&rand_escaped, radix)?);
            escaped = None;
            rand_escaped = String::new();
          }
          if has_parsed {
            continue;
          }
        }
        // not in expr
        match ch {
          '{' => {
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
          }
          '}' => {
            if maybe_escape {
              maybe_escape = false;
            } else {
              maybe_escape = true;
              cur_str.push(ch);
            }
          }
          '\\' => {
            if let Some(next_ch) = iter.next() {
              if let Some(esc) = escape_normal(next_ch) {
                cur_str.push(esc);
              } else {
                match next_ch {
                  'u' => {
                    let first = iter
                      .next()
                      .expect("the --disp uses an incomplete unicode character \\u");
                    let mut uni = String::new();
                    if first == '{' {
                      for hex in iter.by_ref() {
                        if hex == '}' {
                          break;
                        }
                        if is_hex_char(hex) && uni.len() < 6 {
                          uni.push(hex);
                        } else {
                          return Err(Box::new(ArgumentError::Parse(format!(
                            "the --disp use a wrong unicode character \\u{{{}{}",
                            uni, hex
                          ))));
                        }
                      }
                    } else if is_hex_char(first) {
                      uni.push(first);
                      for _ in 0..3 {
                        if let Some(hex) = iter.next() {
                          if is_hex_char(hex) {
                            uni.push(hex);
                          } else {
                            return Err(Box::new(ArgumentError::Parse(format!(
                              "the --disp use a wrong unicode character \\u{}{}",
                              uni, hex
                            ))));
                          }
                        } else {
                          return Err(Box::new(ArgumentError::Parse(format!(
                            "the --disp use a wrong unicode character \\u{}",
                            uni
                          ))));
                        }
                      }
                    } else {
                      return Err(Box::new(ArgumentError::Parse(format!(
                        "the --disp use a wrong unicode character \\u{}",
                        first
                      ))));
                    }
                    cur_str.push(hex_to_char(&uni)?);
                  }
                  'U' => {
                    // c style unicode
                    let mut uni = String::new();
                    for _ in 0..8 {
                      if let Some(hex) = iter.next() {
                        if is_hex_char(hex) {
                          uni.push(ch);
                        } else {
                          return Err(Box::new(ArgumentError::Parse(format!(
                            "the --disp use a wrong unicode character \\U{}{}",
                            uni, hex
                          ))));
                        }
                      } else {
                        return Err(Box::new(ArgumentError::Parse(format!(
                          "the --disp use a wrong unicode character \\U{}",
                          uni
                        ))));
                      }
                    }
                    cur_str.push(hex_to_char(&uni)?);
                  }
                  'x' => {
                    // hex
                    let hex = iter
                      .next()
                      .expect("the --disp uses an incomplete hex character \\x");
                    if is_hex_char(hex) {
                      escaped = Some(EscapeRandWidth::Hex);
                      rand_escaped = String::from(hex);
                    } else {
                      return Err(Box::new(ArgumentError::Parse(format!(
                        "the --disp uses a wrong hex \\x{}",
                        hex
                      ))));
                    }
                  }
                  'c' => {
                    // controll characters
                    let controll = iter
                      .next()
                      .expect("the --disp uses an incomplete controll character \\c");
                    let actual_ch = (match controll {
                      '@' => 0x00,
                      le @ ('A'..='Z') => (le as u8) - 64,
                      '[' => 0x1B,
                      '\\' => 0x1C,
                      ']' => 0x1D,
                      '^' => 0x1E,
                      '_' => 0x1F,
                      '?' => 0x7F,
                      w_ch => {
                        return Err(Box::new(ArgumentError::Parse(format!(
                          "the --disp uses a wrong controll character \\c{}",
                          w_ch
                        ))));
                      }
                    }) as char;
                    cur_str.push(actual_ch);
                  }
                  '0'..='7' => {
                    // octal characters
                    escaped = Some(EscapeRandWidth::Octal);
                    rand_escaped = String::from(next_ch);
                  }
                  w_ch => {
                    return Err(Box::new(ArgumentError::Parse(format!(
                      "the --disp uses an unkown escape character \\{}",
                      w_ch
                    ))))
                  }
                }
              }
            }
          }
          _ => {
            cur_str.push(ch);
          }
        }
      }
    }
    // at the end, the cur_str is not empty, should take as a string
    if let Some(esc) = escaped {
      let radix = if matches!(esc, EscapeRandWidth::Hex) {
        16
      } else {
        8
      };
      cur_str.push(radix_str_to_char(&rand_escaped, radix)?);
    }
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
      let mut ctx_cond = evalexpr::HashMapContext::new();
      let mut keys: Vec<String> = vec![];
      for (key, value) in data.iter() {
        ctx_cond
          .set_value(key.into(), ProxyValue::from(value).into())
          .unwrap_or(());
        keys.push(key.clone());
      }
      ctx_cond
        .set_function(
          "has_key".into(),
          Function::new(move |argument| {
            if let Ok(k) = argument.as_string() {
              return Ok(EvalValue::Boolean(keys.contains(&k)));
            }
            Ok(EvalValue::Boolean(false))
          }),
        )
        .unwrap();
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
  if args.sep == "\n" {
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
    let rule = Regex::new(&args.sep)
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
