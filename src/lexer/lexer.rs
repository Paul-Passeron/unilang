#![allow(dead_code)]
#![allow(unused_variables)]

use core::fmt;

use regex::Regex;

use crate::{
    common::source_location::{Location, SourceFile, Span},
    lexer::{
        Token,
        rules::{get_skip_rules, get_token_rules},
    },
};

#[derive(Debug)]
pub struct Error {
    pub message: String,
    pub location: Location,
}

pub struct Lexer<'a, T> {
    file: &'a SourceFile,
    indices: Vec<usize>,
    location: Location,
    token_patterns: Vec<(Regex, fn(&str, Span) -> Result<T, Error>)>,
    skip_patterns: Vec<Regex>,
}

impl<'a, T: fmt::Debug> Iterator for Lexer<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_token().ok()
    }
}

impl<'a, T> Lexer<'a, T> {
    fn advance(&mut self) -> Option<char> {
        if !self.is_done() {
            let c: char = self
                .file
                .content
                .chars()
                .nth(self.location.location as usize)
                .unwrap();
            self.location.location += 1;
            Some(c)
        } else {
            None
        }
    }

    fn advance_n(&mut self, n: usize) {
        for _ in 0..n {
            self.advance();
        }
    }

    pub fn is_done(&mut self) -> bool {
        self.location.location as usize >= self.file.content.len()
    }

    fn skip(&mut self) {
        loop {
            if self.is_done() {
                break;
            }
            let mut skip_count = 0;
            let mut could_skip = false;
            for regex in &self.skip_patterns {
                let to_match: &str =
                    &self.file.content[self.indices[self.location.location as usize]..];
                if let Some(mat) = regex.find(to_match) {
                    if mat.start() == 0 {
                        could_skip = true;
                        skip_count += mat.len();
                        break;
                    }
                }
            }
            if !could_skip {
                break;
            }
            self.advance_n(skip_count);
        }
    }

    pub fn new_blank(
        source: &'a SourceFile,
        token_patterns: Vec<(Regex, fn(&str, Span) -> Result<T, Error>)>,
        skip_patterns: Vec<Regex>,
    ) -> Self {
        Self {
            location: Location::new(source.id, 0),
            indices: source.content.char_indices().map(|(x, _)| x).collect(),
            file: source,
            token_patterns,
            skip_patterns,
        }
    }

    pub fn next_token(&mut self) -> Result<T, Error> {
        self.skip();
        if self.is_done() {
            Err(Error {
                location: self.location.clone(),
                message: String::from("EOF"),
            })
        } else {
            let mut token_length = 0;
            let mut res: Result<T, Error> = Err(Error {
                message: format!(
                    "Unexpected character `{}`",
                    self.file
                        .content
                        .chars()
                        .nth(self.location.location as usize)
                        .unwrap_or('\0')
                ),
                location: self.location.clone(),
            });
            for (regex, func) in &self.token_patterns {
                let start = self.location;
                let to_match = &self.file.content[self.location.location as usize..];
                if let Some(mat) = regex.find(to_match) {
                    if mat.start() == 0 {
                        token_length = mat.end();
                        let token_string: &str = &to_match[..token_length];
                        let mut end = self.location;
                        for _ in 0..token_length {
                            let c = self
                                .file
                                .content
                                .chars()
                                .nth(end.location as usize)
                                .unwrap();
                            end.location += 1;
                        }
                        res = func(token_string, start.span_to(&end));
                        break;
                    }
                }
            }
            self.advance_n(token_length);
            res
        }
    }
}

impl<'a> Lexer<'a, Token> {
    pub fn new(source: &'a SourceFile) -> Self {
        Self::new_blank(source, get_token_rules(), get_skip_rules())
    }
}
