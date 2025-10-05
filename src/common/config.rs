use clap::Parser;
use std::path::PathBuf;

#[derive(Parser, Debug, Clone)]
#[command(name = "unilang")]
#[command(author = "Paul Passeron <paul.passeron.pro@gmail.com>")]
#[command(version = "0.1.0")]
#[command(about = "Compiles unilang source files", long_about = None)]
pub struct Config {
    /// Source files to compile
    #[arg(required = true, value_name = "FILE")]
    pub files: Vec<PathBuf>,

    /// Output file path
    #[arg(short, long, value_name = "FILE", default_value = "a.out")]
    pub output: PathBuf,

    /// Path to the standard library
    /// Path to the standard library
    #[arg(short, long, value_name = "DIR", default_value_os_t = get_default_std())]
    pub std: PathBuf,
}

fn get_default_std() -> PathBuf {
    std::env::var("UL_STD_PATH")
        .ok()
        .map_or_else(|| std::env::current_dir().unwrap(), |x| PathBuf::from(x))
}
