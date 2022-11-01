use clap::Parser;

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

    /// Display fields list
    #[arg(short = 'd', long, action = clap::ArgAction::Append)]
    disp: Vec<String>,

    /// Condition to filter the rows
    #[arg(short = 'c', long)]
    cond: Option<String>,

    /// The count of rows should be shown
    #[arg(short = 'n', long)]
    num: Option<usize>,

    #[arg(short = 'f', long, action = clap::ArgAction::Append)]
    field: Vec<String>,
}

fn main() {
    let args = Args::parse();
    let start_index = if let Some(start) = args.index {
        0.min(start)
    } else {
        0
    } as usize;
}
