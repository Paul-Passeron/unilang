#![feature(formatting_options)]
#![allow(dead_code)]
#![feature(let_chains)]
#![feature(iterator_try_collect)]

use clap::Parser;

use crate::{common::config::Config, nir::context::GlobalContext};

mod common;
mod lexer;
mod nir;
mod parser;
mod ty;

fn main() {
    let config = Config::parse();
    let ctx = GlobalContext::new(config);
    ctx.compile();
}
