use std::path::{Path, PathBuf};

#[derive(Debug, Clone)]
pub struct IncludeResolver {
    std: PathBuf,
}

impl IncludeResolver {
    pub fn new(std: PathBuf) -> Self {
        Self { std }
    }

    fn get_path_for_dir(path: &[&String], dir: &Path) -> Option<PathBuf> {
        let mut p = PathBuf::from(dir);
        for s in path {
            p.push(s);
        }
        p.set_extension("ul");
        p.exists().then_some(p)
    }

    pub fn get_path(&self, path: Vec<&String>) -> Option<PathBuf> {
        if path.is_empty() {
            return None;
        }

        if path[0] == "std" {
            return Self::get_path_for_dir(&path[1..], &self.std);
        }

        let current = std::env::current_dir().unwrap();

        if let Some(x) = Self::get_path_for_dir(&path[..], &current) {
            return Some(x);
        }

        if let Some(x) = Self::get_path_for_dir(&path[..], current.parent().unwrap()) {
            return Some(x);
        }

        None
    }
}
