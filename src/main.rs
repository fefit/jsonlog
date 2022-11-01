use clap::Parser;
use regex::Regex;
use std::error::Error;
use std::fs::File;
use std::io::{BufRead, BufReader, Read};

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
  disp: Option<String>,

  /// Condition to filter the rows
  #[arg(short = 'c', long)]
  cond: Option<String>,

  /// The count of rows should be shown
  #[arg(short = 'n', long)]
  num: Option<usize>,

  #[arg(short = 'f', long, action = clap::ArgAction::Append)]
  field: Vec<String>,

  /// The log file.
  file: String,
}

fn main() -> Result<(), Box<dyn Error>> {
  let args = Args::parse();
  let start_index = if let Some(start) = args.index {
    0.min(start)
  } else {
    0
  } as usize;
  // get the split string array
  let mut result: Vec<String> = Vec::with_capacity(50);
  if args.split == "\n" {
    let file = File::open(args.file)?;
    let reader = BufReader::new(file);
    if start_index == 0 {
      for line in reader.lines() {
        result.push(line?);
      }
    } else {
      for line in reader.lines().skip(start_index) {
        result.push(line?);
      }
    }
  } else {
    let rule = Regex::new(&args.split)
      .map_err(|e| format!("The splitter  is not a valid regex: {}", e))
      .unwrap();
    let mut file = File::open(args.file)?;
    let mut content = String::with_capacity(200);
    file.read_to_string(&mut content)?;
    result = content.split(rule).collect::<Vec<String>>();
    // jump index
    if start_index > 0 {
      result = result.split_off(start_index);
    }
  }
  //
  Ok(())
}
