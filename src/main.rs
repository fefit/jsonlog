use clap::Parser;
use evalexpr::{
  ContextWithMutableFunctions, ContextWithMutableVariables, Function, Value as EvalValue,
};
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};
use regex::Regex;
use serde_json::Value as JsonValue;
use std::collections::HashMap;
use std::error::Error as StdError;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Read};
use std::process;
use std::str::Chars;
use thiserror::Error;

type JsonData = HashMap<String, JsonValue>;
type BoxDynOutputFn = Box<dyn Fn(&JsonData, usize) -> String + Send + Sync>;
type BoxDynCondFn = Box<dyn Fn(&JsonData, usize) -> bool + Send + Sync>;
type BoxDynPrintFn = Box<dyn Fn(&BufferedOutput, usize) + Send + Sync>;
type BoxDynError = Box<dyn StdError>;
type GenResult<T = ()> = Result<T, BoxDynError>;

const EXP_DATA_HAS_KEY: &str = "data::has_key";
const EXP_DATA_ROW: &str = "data::row";

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

/**
 * escape normal characters
 */
fn escape_normal(ch: char) -> Option<char> {
  for (orig, esc) in ESCAPE_CHARS {
    if ch == orig {
      return Some(esc);
    }
  }
  None
}

#[inline]
fn is_hex_char(ch: char) -> bool {
  matches!(ch, '0'..='9' | 'a'..='f' | 'A'..='F')
}

#[inline]
fn hex_to_char(hex_str: &str) -> GenResult<char> {
  radix_str_to_char(hex_str, 16)
}

#[inline]
fn radix_str_to_char(radix_str: &str, radix: u32) -> GenResult<char> {
  let code = u32::from_str_radix(radix_str, radix).unwrap();
  if let Some(ch) = std::char::from_u32(code) {
    return Ok(ch);
  }
  Err(Box::new(ArgumentError::Parse(format!(
    "invalid universal character \\u{}",
    radix_str
  ))))
}

/**
 * parse \xhhh and octal \nnn
 */
fn parse_maybe_still_in_escape(
  cur_str: &mut String,
  ch: char,
  escape_data: &mut EscapeData,
) -> GenResult<bool> {
  if let Some(esc) = &escape_data.escaped {
    let mut has_parsed = false;
    let (esc_end, radix) = match esc {
      EscapeRandWidth::Hex => {
        if is_hex_char(ch) {
          escape_data.rand_escaped.push(ch);
          has_parsed = true;
        }
        (true, 16)
      }
      EscapeRandWidth::Octal => {
        let esc_end = if matches!(ch, '0'..='7') {
          escape_data.rand_escaped.push(ch);
          has_parsed = true;
          escape_data.rand_escaped.len() == 3
        } else {
          true
        };
        (esc_end, 8)
      }
    };
    if esc_end {
      cur_str.push(radix_str_to_char(&escape_data.rand_escaped, radix)?);
      escape_data.escaped = None;
      escape_data.rand_escaped = String::new();
    }
    return Ok(has_parsed);
  }
  Ok(false)
}

/**
 * parse in escape characters
 */
fn parse_in_escape(
  cur_str: &mut String,
  ch: char,
  escape_data: &mut EscapeData,
  iter: &mut Chars,
  arg_name: &str,
) -> GenResult {
  if let Some(next_ch) = iter.next() {
    if let Some(esc) = escape_normal(next_ch) {
      cur_str.push(esc);
    } else {
      match next_ch {
        'u' => {
          let first = iter
            .next()
            .unwrap_or_else(|| panic!("the {} uses an incomplete unicode character \\u", arg_name));
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
                  "the {} use a wrong unicode character \\u{{{}{}",
                  arg_name, uni, hex
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
                    "the {} use a wrong unicode character \\u{}{}",
                    arg_name, uni, hex
                  ))));
                }
              } else {
                return Err(Box::new(ArgumentError::Parse(format!(
                  "the {} use a wrong unicode character \\u{}",
                  arg_name, uni
                ))));
              }
            }
          } else {
            return Err(Box::new(ArgumentError::Parse(format!(
              "the {} use a wrong unicode character \\u{}",
              arg_name, first
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
                  "the {} use a wrong unicode character \\U{}{}",
                  arg_name, uni, hex
                ))));
              }
            } else {
              return Err(Box::new(ArgumentError::Parse(format!(
                "the {} use a wrong unicode character \\U{}",
                arg_name, uni
              ))));
            }
          }
          cur_str.push(hex_to_char(&uni)?);
        }
        'x' => {
          // hex
          let hex = iter
            .next()
            .unwrap_or_else(|| panic!("the {} uses an incomplete hex character \\x", arg_name));
          if is_hex_char(hex) {
            escape_data.escaped = Some(EscapeRandWidth::Hex);
            escape_data.rand_escaped = String::from(hex);
          } else {
            return Err(Box::new(ArgumentError::Parse(format!(
              "the {} uses a wrong hex \\x{}",
              arg_name, hex
            ))));
          }
        }
        'c' => {
          // controll characters
          let controll = iter.next().unwrap_or_else(|| {
            panic!("the {} uses an incomplete controll character \\c", arg_name)
          });
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
                "the {} uses a wrong controll character \\c{}",
                arg_name, w_ch
              ))));
            }
          }) as char;
          cur_str.push(actual_ch);
        }
        '0'..='7' => {
          // octal characters
          escape_data.escaped = Some(EscapeRandWidth::Octal);
          escape_data.rand_escaped = String::from(next_ch);
        }
        w_ch => {
          return Err(Box::new(ArgumentError::Parse(format!(
            "the {} uses an unkown escape character \\{}",
            arg_name, w_ch
          ))))
        }
      }
    }
  }
  Ok(())
}

/**
 * parse the end
 */
fn parse_in_escape_end(cur_str: &mut String, escape_data: &mut EscapeData) -> GenResult {
  if let Some(esc) = &escape_data.escaped {
    let radix = if matches!(esc, EscapeRandWidth::Hex) {
      16
    } else {
      8
    };
    cur_str.push(radix_str_to_char(&escape_data.rand_escaped, radix)?);
  }
  Ok(())
}

/**
 * parse string with escaped
 */
fn parse_escape_output(content: &str, arg_name: &str) -> GenResult<String> {
  let mut cur_str = String::with_capacity(10);
  let mut escape_data = EscapeData::default();
  let mut iter = content.chars();
  while let Some(ch) = iter.next() {
    if parse_maybe_still_in_escape(&mut cur_str, ch, &mut escape_data)? {
      continue;
    }
    if ch == '\\' {
      parse_in_escape(&mut cur_str, ch, &mut escape_data, &mut iter, arg_name)?;
    } else {
      cur_str.push(ch);
    }
  }
  parse_in_escape_end(&mut cur_str, &mut escape_data)?;
  Ok(cur_str)
}

/**
 * generate output fn
 */
fn gen_output_fn(tmpl: &str, arg_name: &str) -> GenResult<(bool, BoxDynOutputFn)> {
  let mut output_fns: Vec<BoxDynOutputFn> = vec![];
  let mut quote_char = '\0';
  let mut maybe_escape = false;
  let mut is_expr = false;
  let mut cur_str = String::new();
  let mut iter = tmpl.chars();
  let mut escape_data = EscapeData::default();
  let mut use_row = false;
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
          // check if has data row variable
          let has_row = var_idents.contains(&String::from(EXP_DATA_ROW));
          // set whether use row
          use_row = use_row || has_row;
          // put output segments
          output_fns.push(Box::new(move |data: &JsonData, line| {
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
            if has_row {
              ctx_disp
                .set_value(EXP_DATA_ROW.into(), EvalValue::Int(line as i64))
                .unwrap();
            }
            if fn_idents.contains(&String::from(EXP_DATA_HAS_KEY)) {
              let keys = data.keys().cloned().collect::<Vec<_>>();
              ctx_disp
                .set_function(
                  EXP_DATA_HAS_KEY.into(),
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
      if parse_maybe_still_in_escape(&mut cur_str, ch, &mut escape_data)? {
        continue;
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
                output_fns.push(Box::new(move |_, _| seg.clone()));
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
          parse_in_escape(&mut cur_str, ch, &mut escape_data, &mut iter, arg_name)?;
        }
        _ => {
          cur_str.push(ch);
        }
      }
    }
  }
  // at the end, the cur_str is not empty, should take as a string
  parse_in_escape_end(&mut cur_str, &mut escape_data)?;
  if !cur_str.is_empty() {
    output_fns.push(Box::new(move |_, _| cur_str.clone()));
  }
  // generate output function
  Ok((
    use_row,
    Box::new(move |data: &JsonData, line| {
      let mut result = String::new();
      for cb in output_fns.iter() {
        let seg = cb(data, line);
        result.push_str(&seg);
      }
      result
    }),
  ))
}

#[derive(Default)]
struct EscapeData {
  escaped: Option<EscapeRandWidth>,
  rand_escaped: String,
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

  /// The output data seperator
  #[arg(short = 'j', long)]
  out_sep: Option<String>,

  /// Each data output display template
  #[arg(short = 'd', long)]
  disp: Option<String>,

  ///
  #[arg(short = 'e', long)]
  err_disp: Option<String>,

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
enum ProxyValue {
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
struct BufferedOutputConfig {
  max_rows: usize,
  cap: usize,
  out_sep: String,
  show_disp: bool,
  show_err_disp: bool,
  no_use_row: bool,
}

struct BufferedOutput {
  non_first: bool,
  rows: usize,
  last_index: usize,
  data: Vec<String>,
  config: BufferedOutputConfig,
  cond_fn: BoxDynCondFn,
  output_fn: BoxDynOutputFn,
  err_output_fn: BoxDynOutputFn,
  print_fn: BoxDynPrintFn,
}

impl BufferedOutput {
  /**
   * new instance
   */
  fn new(
    mut config: BufferedOutputConfig,
    cond_fn: BoxDynCondFn,
    output_fn: BoxDynOutputFn,
    err_output_fn: BoxDynOutputFn,
  ) -> Self {
    let cap = if config.cap == 0 { 1 } else { config.cap };
    let print_fn = if config.no_use_row {
      Box::new(|this: &BufferedOutput, rows: usize| {
        let row_no = this.rows + 2;
        let cond_fn = &this.cond_fn;
        let output_fn = &this.output_fn;
        let err_output_fn = &this.err_output_fn;
        let result = this.data[0..rows]
          .par_iter()
          .map(|r| {
            let maybe_json = serde_json::from_str::<JsonData>(r);
            if let Ok(json) = maybe_json {
              if this.config.show_disp && cond_fn(&json, row_no) {
                return (
                  true,
                  format!("{}{}", this.config.out_sep, output_fn(&json, row_no)),
                );
              }
            } else if this.config.show_err_disp {
              let mut json = HashMap::new();
              json.insert(
                String::from("data::error"),
                JsonValue::String(maybe_json.err().unwrap().to_string()),
              );
              return (
                true,
                format!("{}{}", this.config.out_sep, err_output_fn(&json, row_no)),
              );
            }
            (false, String::new())
          })
          .collect::<Vec<(bool, String)>>();
        result.iter().for_each(|(is_print, content)| {
          if *is_print {
            print!("{}", content);
          }
        });
      })
    } else {
      Box::new(|this: &BufferedOutput, rows| {
        let row_no = this.rows + 2;
        let cond_fn = &this.cond_fn;
        let output_fn = &this.output_fn;
        let err_output_fn = &this.err_output_fn;
        // just parallel the json parsing
        let result = this.data[0..rows]
          .par_iter()
          .map(|r| serde_json::from_str::<JsonData>(r))
          .collect::<Vec<_>>();
        result.iter().enumerate().for_each(|(index, maybe_json)| {
          let cur_row_no = row_no + index;
          if let Ok(json) = maybe_json {
            if this.config.show_disp && cond_fn(json, cur_row_no) {
              print!("{}{}", this.config.out_sep, output_fn(json, cur_row_no));
            }
          } else if this.config.show_err_disp {
            let mut json = HashMap::new();
            json.insert(
              String::from("data::error"),
              JsonValue::String(maybe_json.as_ref().err().unwrap().to_string()),
            );
            print!(
              "{}{}",
              this.config.out_sep,
              err_output_fn(&json, cur_row_no)
            );
          }
        });
      }) as BoxDynPrintFn
    };
    config.cap = cap;
    BufferedOutput {
      rows: 0,
      non_first: false,
      last_index: cap - 1,
      data: vec![String::new(); cap],
      config,
      cond_fn,
      output_fn,
      err_output_fn,
      print_fn,
    }
  }
  /**
   * end
   */
  fn end(&self, is_end: bool) {
    let cap = self.config.cap;
    let rows = if is_end { self.rows % cap } else { cap };
    let print_fn = &self.print_fn;
    if rows > 0 {
      print_fn(self, rows);
    }
  }
  /**
   * push data
   */
  fn push(&mut self, row: String) {
    if self.non_first {
      let index = self.rows % self.config.cap;
      self.data[index] = row;
      self.rows += 1;
      if self.rows + 1 == self.config.max_rows {
        self.end(true);
        process::exit(0);
      } else if index == self.last_index {
        self.end(false);
      }
    } else {
      let cond_fn = &self.cond_fn;
      let output_fn = &self.output_fn;
      let err_output_fn = &self.err_output_fn;
      let maybe_json = serde_json::from_str::<JsonData>(&row);
      const LINE: usize = 1;
      if let Ok(json) = maybe_json {
        if self.config.show_disp && cond_fn(&json, LINE) {
          print!("{}", output_fn(&json, LINE));
          self.non_first = true;
        }
      } else if self.config.show_err_disp {
        let mut json = HashMap::new();
        json.insert(
          String::from("data::error"),
          JsonValue::String(maybe_json.err().unwrap().to_string()),
        );
        print!("{}", err_output_fn(&json, LINE));
        self.non_first = true;
      }
      if self.config.max_rows == 1 {
        process::exit(0);
      }
    };
  }
}

fn main() -> GenResult {
  // args
  let args = Args::parse();
  // condition function
  let mut cond_use_row = false;
  let cond_fn: BoxDynCondFn = if let Some(cond) = args.cond {
    let expr = evalexpr::build_operator_tree(&cond)
      .map_err(|e| format!("The --cond argument uses an unsupported expression:{}", e))?;
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
    let has_row = var_idents.contains(&String::from(EXP_DATA_ROW));
    cond_use_row = has_row;
    Box::new(move |data: &JsonData, line| {
      let mut ctx_cond = evalexpr::HashMapContext::new();
      for key in &var_idents {
        let value = if let Some(val) = data.get(key) {
          ProxyValue::from(val).into()
        } else {
          EvalValue::Empty
        };
        ctx_cond.set_value(key.into(), value).unwrap();
      }
      if has_row {
        ctx_cond
          .set_value(EXP_DATA_ROW.into(), EvalValue::Int(line as i64))
          .unwrap();
      }
      if fn_idents.contains(&String::from(EXP_DATA_HAS_KEY)) {
        let keys = data.keys().cloned().collect::<Vec<_>>();
        ctx_cond
          .set_function(
            EXP_DATA_HAS_KEY.into(),
            Function::new(move |argument| {
              if let Ok(k) = argument.as_string() {
                return Ok(EvalValue::Boolean(keys.contains(&k)));
              }
              Ok(EvalValue::Boolean(false))
            }),
          )
          .unwrap();
      }
      let bool_cond = expr.eval_boolean_with_context(&ctx_cond);
      bool_cond.unwrap_or(false)
    })
  } else {
    Box::new(|_, _| true)
  };
  // buffered output
  let start_index = args.index;
  let max_rows = if args.num == 0 { usize::MAX } else { args.num };
  let out_sep = if let Some(out_sep) = args.out_sep {
    parse_escape_output(&out_sep, "--out-sep")?
  } else {
    String::from("\n")
  };
  let (show_disp, (disp_use_row, output_fn)) = if let Some(tmpl) = args.disp {
    (true, gen_output_fn(&tmpl, "--disp")?)
  } else {
    (
      false,
      (
        false,
        Box::new(|_: &JsonData, _| String::new()) as BoxDynOutputFn,
      ),
    )
  };
  let (show_err_disp, (err_disp_use_row, err_output_fn)) = if let Some(tmpl) = args.err_disp {
    (true, gen_output_fn(&tmpl, "--err-disp")?)
  } else {
    (
      false,
      (
        false,
        Box::new(|_: &JsonData, _| String::new()) as BoxDynOutputFn,
      ),
    )
  };
  let mut buf_output = BufferedOutput::new(
    BufferedOutputConfig {
      max_rows,
      cap: args.par.unwrap_or_else(num_cpus::get),
      out_sep,
      show_disp,
      show_err_disp,
      no_use_row: !(cond_use_row || disp_use_row || err_disp_use_row),
    },
    cond_fn,
    output_fn,
    err_output_fn,
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
