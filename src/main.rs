#![feature(formatting_options)]
#![allow(dead_code)]
#![feature(let_chains)]
#![feature(get_mut_unchecked)]
use std::path::PathBuf;

use crate::{common::config::Config, nir::context::GlobalContext};

mod common;
mod lexer;
mod nir;
mod parser;
mod ty;

fn main() {
    let config = Config {
        files: PathBuf::from("./examples/main.ul"),
        output: None,
        std: None,
    };

    let ctx = GlobalContext::new(config);

    ctx.compile();
}
