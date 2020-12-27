use std::str::FromStr;

use crate::mips_lang::types::arch::*;
use crate::mips_lang::{IResult, Span};

#[derive(Debug)]
pub enum TokenValue {
    Register(Reg),
    FloatReg(FpReg),
}

#[derive(Debug)]
pub struct Token<'a> {
    pub position: Span<'a>,
    pub value: TokenValue,
}

