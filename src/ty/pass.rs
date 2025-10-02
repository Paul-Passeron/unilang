use crate::ty::{TcError, TyCtx};

pub trait Pass<'ctx, I> {
    type Output;
    fn run(&mut self, ctx: &mut TyCtx<'ctx>, input: I) -> Result<Self::Output, TcError>;
}
