#![feature(formatting_options)]
#![allow(dead_code)]
#![feature(let_chains)]
#![feature(iterator_try_collect)]

use clap::Parser;

use crate::common::{config::Config, context::GlobalContext};

mod common;
mod lexer;
mod mono_ir;
mod nir;
mod parser;
mod ty;

fn main() {
    match GlobalContext::new(Config::parse()).compile() {
        Err(error) => panic!("{:?}", error),
        _ => (),
    }
    // clir::test();
}
