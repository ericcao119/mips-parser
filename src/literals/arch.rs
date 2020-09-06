/* This file exists to contain literals specific to the MIPS32 architecture */

use crate::parser::{MIPSParser, Rule};
use crate::utils::{ToSigned, ToUnsigned};
use pest::{error::Error, Parser};
use std::fmt::Display;
use std::result::Result;
use std::str::FromStr;

const NUM_REGISTERS: u32 = 32;


// reg = @{ }
// fp_reg = @{ "$f31"|"$f30"|"$f29"|"$f28"|"$f27"|"$f26"|"$f25"|"$f24"|"$f23"|"$f22"|"$f21"|"$f20"|"$f19"|"$f18"|"$f17"|"$f16"|"$f15"|"$f14"|"$f13"|"$f12"|"$f11"|"$f10"|"$f9"|"$f8"|"$f7"|"$f6"|"$f5"|"$f4"|"$f3"|"$f2"|"$f1"|"$f0"}


/// A general purpose register
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct Reg {
    pub reg_no: u32,
}

impl Display for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        write!(f, "${}", self.reg_no)
    }
    
}

impl FromStr for Reg {
    type Err = &'static str;
    fn from_str(reg_str: &str) -> std::result::Result<Self, <Self as FromStr>::Err> {
        match reg_str {
            "$ra"|"$31" => Ok(Reg::new(31)),
            "$fp"|"$30" => Ok(Reg::new(30)),
            "$sp"|"$29" => Ok(Reg::new(29)),
            "$gp"|"$28" => Ok(Reg::new(28)),
            "$k1"|"$27" => Ok(Reg::new(27)),
            "$k0"|"$26" => Ok(Reg::new(26)),
            "$t9"|"$25" => Ok(Reg::new(25)),
            "$t8"|"$24" => Ok(Reg::new(24)),
            "$s7"|"$23" => Ok(Reg::new(23)),
            "$s6"|"$22" => Ok(Reg::new(22)),
            "$s5"|"$21" => Ok(Reg::new(21)),
            "$s4"|"$20" => Ok(Reg::new (20)),
            "$s3"|"$19" => Ok(Reg::new (19)),
            "$s2"|"$18" => Ok(Reg::new (18)),
            "$s1"|"$17" => Ok(Reg::new (17)),
            "$s0"|"$16" => Ok(Reg::new (16)),
            "$t7"|"$15" => Ok(Reg::new (15)),
            "$t6"|"$14" => Ok(Reg::new (14)),
            "$t5"|"$13" => Ok(Reg::new (13)),
            "$t4"|"$12" => Ok(Reg::new (12)),
            "$t3"|"$11" => Ok(Reg::new (11)),
            "$t2"|"$10" => Ok(Reg::new (10)),
            "$t1"|"$9" => Ok(Reg::new (9)),
            "$t0"|"$8" => Ok(Reg::new (8)),
            "$a3"|"$7" => Ok(Reg::new (7)),
            "$a2"|"$6" => Ok(Reg::new(6)),
            "$a1"|"$5" => Ok(Reg::new(5)),
            "$a0"|"$4" => Ok(Reg::new(4)),
            "$v1"|"$3" => Ok(Reg::new(3)),
            "$v0"|"$2" => Ok(Reg::new(2)),
            "$at"|"$1" => Ok(Reg::new(1)),
            "$zero"|"$0" => Ok(Reg::new(0)),
            _ => Err("Invalid Register String")
        }
    }
}

impl Reg {
    fn new(idx: u32) -> Reg {
        if idx >= NUM_REGISTERS {
            panic!("Register number {} is too large!", idx);
        }

        Reg { reg_no: idx }
    }
}
