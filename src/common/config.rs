use std::path::PathBuf;

#[derive(Debug, Clone)]
pub struct Config {
    pub files: PathBuf,
    pub output: Option<PathBuf>,
    pub std: Option<PathBuf>,
}
