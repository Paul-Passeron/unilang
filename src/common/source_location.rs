use std::{
    collections::HashMap,
    path::{Path, PathBuf},
};

use crate::nir::interner::{ConstructibleId, HashInterner, Interner};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FileId(u32);

#[derive(Debug, Clone, Copy)]
pub struct Location {
    pub file: FileId,
    pub location: u32,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Span {
    pub file: FileId,
    start: u32,
    end: u32,
}

impl Span {
    pub fn from(start: &Location, end: &Location) -> Option<Self> {
        if start.file != end.file {
            None
        } else {
            let (s, e) = if start.location > end.location {
                (end.location, start.location)
            } else {
                (start.location, end.location)
            };
            Some(Self {
                file: start.file,
                start: s,
                end: e,
            })
        }
    }

    pub fn start(&self) -> Location {
        Location::new(self.file, self.start)
    }

    pub fn end(&self) -> Location {
        Location::new(self.file, self.end)
    }
}

impl Location {
    pub fn new(id: FileId, location: u32) -> Self {
        Self { file: id, location }
    }

    pub fn span_to(&self, end: &Location) -> Span {
        Span::from(self, end).unwrap()
    }

    pub fn to_string(&self, file_manager: &FileManager) -> String {
        let file = file_manager.files.get(&self.file).unwrap();
        let name = file_manager.paths.get(self.file);
        let name = name.strip_prefix(std::env::current_dir().unwrap()).unwrap();
        let mut lines = 1;
        let mut col = 1;
        for (i, c) in file.content.chars().enumerate() {
            if i == self.location as usize {
                break;
            }
            col += 1;
            if c == '\n' {
                lines += 1;
                col = 1;
            }
        }
        format!("{}:{}:{}", name.display(), lines, col)
    }
}

impl ConstructibleId for FileId {
    fn new(id: u32) -> Self {
        Self(id)
    }
}

pub type FileInterner = HashInterner<FileId, PathBuf>;

#[derive(Debug, Clone)]
pub struct SourceFile {
    pub id: FileId,
    pub content: String,
}

#[derive(Debug, Clone)]
pub struct FileManager {
    pub paths: FileInterner,
    pub files: HashMap<FileId, SourceFile>,
}

impl SourceFile {
    pub fn from(path: &Path) -> Option<Self> {
        if !path.exists() {
            return None;
        }

        None
    }
}

impl<'a> FileManager {
    pub fn new() -> Self {
        Self {
            paths: FileInterner::new(),
            files: HashMap::new(),
        }
    }

    pub fn add_file(&mut self, path: &'a Path) -> Option<FileId> {
        if !path.exists() {
            return None;
        }

        let path = std::fs::canonicalize(path);

        if path.is_err() {
            return None;
        }

        let path = path.unwrap();

        let new_id = self.paths.insert(path.clone());

        if self.files.contains_key(&new_id) {
            return Some(new_id);
        }
        let content = std::fs::read_to_string(path);

        if content.is_err() {
            return None;
        }

        let content = content.unwrap();

        let file = SourceFile {
            id: new_id,
            content: content.chars().collect(),
        };

        self.files.insert(new_id, file);

        Some(new_id)
    }
}
