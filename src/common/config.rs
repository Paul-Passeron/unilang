use std::path::PathBuf;

#[derive(Debug)]
pub struct Config {
    pub files: PathBuf,
    pub output: Option<PathBuf>,
    pub std: Option<PathBuf>,
}
