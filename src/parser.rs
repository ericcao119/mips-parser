use crate::expression::{BinOp, MonOp, Operand};
use pest::error::Error;
use pest::Parser;
use std::iter::Iterator;
use std::str;

use itertools::Itertools;

#[derive(Parser)]
#[grammar = "mips.pest"]
struct MIPSParser;

pub fn parse(source: &str) -> Result<(), Error<Rule>> {
    let pairs = MIPSParser::parse(Rule::expr, source)?;
    for pair in pairs {
        match pair.as_rule() {
            Rule::expr => {
                parse_expr(pair);
            }
            _ => panic!("Failed"),
        }
    }

    Ok(())
}

fn parse_expr_helper(source: &str) -> Operand {
    let mut pairs = MIPSParser::parse(Rule::expr, source).unwrap();
    let pair = pairs.next().unwrap();
    match pair.as_rule() {
        Rule::expr => {
            parse_expr(pair).unwrap()
        }
        _ => panic!("Failed"),
    }
}

fn parse_expr(pair: pest::iterators::Pair<Rule>) -> Result<Operand, ()> {
    match pair.as_rule() {
        Rule::expr => {
            let expr = pair.into_inner().next().unwrap();
            println!("{}", expr.as_str());
            parse_expr(expr)
        }

        Rule::bit_or_expr => {
            let mut pairs = pair.into_inner();
            let value = parse_expr(pairs.next().unwrap())?;

            pairs
                .chunks(2)
                .into_iter()
                .try_fold(value, |acc, mut chunk| {
                    let op_rule = chunk.next().unwrap();
                    let operand_rule = chunk.next().unwrap();

                    let op: BinOp = op_rule.as_str().parse()?;
                    let operand = parse_expr(operand_rule)?;

                    assert_eq!(BinOp::BitOrOp, op);
                    Ok(acc | operand)
                })
        }
        Rule::bit_and_expr => {
            let mut pairs = pair.into_inner();
            let value = parse_expr(pairs.next().unwrap())?;

            pairs
                .chunks(2)
                .into_iter()
                .try_fold(value, |acc, mut chunk| {
                    let op_rule = chunk.next().unwrap();
                    let operand_rule = chunk.next().unwrap();

                    let op: BinOp = op_rule.as_str().parse()?;
                    let operand = parse_expr(operand_rule)?;
                    assert_eq!(BinOp::BitAndOp, op);
                    Ok(acc & operand)
                })
        }
        Rule::add_expr => {
            let mut pairs = pair.into_inner();
            let value = parse_expr(pairs.next().unwrap())?;

            pairs
                .chunks(2)
                .into_iter()
                .try_fold(value, |acc, mut chunk| {
                    let op_rule = chunk.next().unwrap();
                    let operand_rule = chunk.next().unwrap();

                    let op: BinOp = op_rule.as_str().parse()?;
                    let operand = parse_expr(operand_rule)?;
                    match op {
                        BinOp::PlusOp => Ok(acc + operand),
                        BinOp::MinusOp => Ok(acc - operand),
                        _ => Err(()),
                    }
                })
        }
        Rule::mul_expr => {
            let mut pairs = pair.into_inner();
            let value = parse_expr(pairs.next().unwrap())?;

            pairs
                .chunks(2)
                .into_iter()
                .try_fold(value, |acc, mut chunk| {
                    let op_rule = chunk.next().unwrap();
                    let operand_rule = chunk.next().unwrap();

                    let op: BinOp = op_rule.as_str().parse()?;
                    let operand = parse_expr(operand_rule)?;
                    match op {
                        BinOp::TimesOp => Ok(acc * operand),
                        BinOp::DivideOp => Ok(acc / operand),
                        _ => Err(()),
                    }
                })
        }
        Rule::unary_expr => {
            let mut pairs = pair.into_inner();
            let first = pairs.next().unwrap();

            match first.as_rule() {
                Rule::op_unary => {
                    let op: MonOp = first.as_str().parse()?;
                    let operand = parse_expr(pairs.next().unwrap())?;
                    Ok(match op {
                        MonOp::BitNotOp => !operand,
                        MonOp::NegOp => -operand,
                        MonOp::PosOp => operand,
                    })
                }
                Rule::atomic_expr => parse_expr(first),
                _ => panic!("Invalid rule within unsigned!"),
            }
        }
        Rule::atomic_expr => {
            let mut pairs = pair.into_inner();
            let inner = pairs.next().unwrap();

            match inner.as_rule() {
                Rule::unsigned => parse_expr(inner),
                Rule::ident => Ok(Operand::var(inner.as_str())),
                Rule::expr => parse_expr(inner),
                _ => panic!("Invalid rule within unsigned!"),
            }
        }
        Rule::unsigned => {
            let mut pairs = pair.into_inner();
            let inner = pairs.next().unwrap();

            Ok(match inner.as_rule() {
                Rule::bin => Operand::unsigned(u32::from_str_radix(&inner.as_str().replace("_", ""), 2).unwrap()),
                Rule::hex => Operand::unsigned(u32::from_str_radix(&inner.as_str().replace("_", ""), 16).unwrap()),
                Rule::dec => Operand::unsigned(u32::from_str_radix(&inner.as_str().replace("_", ""), 10).unwrap()),
                Rule::char => {
                    let character_str = inner.as_str().trim_matches('\'');
                    let character = strip_ansi_escapes::strip(character_str).unwrap();
                    Operand::unsigned(character[0] as u32)
                }
                _ => panic!("Invalid rule within unsigned!"),
            })
        }
        _ => panic!("Unmatched case in expression!"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ident() {
        let case = "abc";
        let expected = "abc";
        let mut pairs = MIPSParser::parse(Rule::ident, case).unwrap().into_iter();
        assert_eq!(pairs.next().unwrap().as_str(), expected);
    }

    #[test]
    fn test_special() {
        let case = "_$$";
        let expected = "_$$";
        let mut pairs = MIPSParser::parse(Rule::ident, case).unwrap().into_iter();
        assert_eq!(pairs.next().unwrap().as_str(), expected);
    }

    #[test]
    #[should_panic]
    fn fail_ident() {
        let case = "0ab";
        let mut pairs = MIPSParser::parse(Rule::ident, case).unwrap().into_iter();
        pairs.next().unwrap().as_str();
    }

    #[test]
    #[should_panic]
    fn fail_ident_reserved_keyword() {
        let case = "$s0";
        let mut pairs = MIPSParser::parse(Rule::ident, case).unwrap().into_iter();
        pairs.next().unwrap().as_str();
    }

    #[test]
    fn test_reg() {
        let general_registers = [
            "$0", "$1", "$2", "$3", "$4", "$5", "$6", "$7", "$8", "$9", "$10", "$11", "$12", "$13",
            "$14", "$15", "$16", "$17", "$18", "$19", "$20", "$21", "$22", "$23", "$24", "$25",
            "$26", "$27", "$28", "$29", "$30", "$31", "$zero", "$at", "$v0", "$v1", "$a0", "$a1",
            "$a2", "$a3", "$t0", "$t1", "$t2", "$t3", "$t4", "$t5", "$t6", "$t7", "$s0", "$s1",
            "$s2", "$s3", "$s4", "$s5", "$s6", "$s7", "$t8", "$t9", "$k0", "$k1", "$gp", "$sp",
            "$fp", "$ra",
        ];

        for case in general_registers.iter() {
            let mut pairs = MIPSParser::parse(Rule::reg, case).unwrap().into_iter();
            assert_eq!(pairs.next().unwrap().as_str(), *case);
        }
    }

    #[test]
    fn test_reg_shorthand() {
        let case = "$ra";
        let expected = "$ra";
        let mut pairs = MIPSParser::parse(Rule::reg, case).unwrap().into_iter();
        assert_eq!(pairs.next().unwrap().as_str(), expected);
    }

    #[test]
    fn test_float_reg() {
        let float_registers = [
            "$f0", "$f1", "$f2", "$f3", "$f4", "$f5", "$f6", "$f7", "$f8", "$f9", "$f10", "$f11",
            "$f12", "$f13", "$f14", "$f15", "$f16", "$f17", "$f18", "$f19", "$f20", "$f21", "$f22",
            "$f23", "$f24", "$f25", "$f26", "$f27", "$f28", "$f29", "$f30", "$f31",
        ];
        for case in float_registers.iter() {
            let mut pairs = MIPSParser::parse(Rule::fp_reg, case).unwrap().into_iter();
            assert_eq!(pairs.next().unwrap().as_str(), *case);
        }
    }

    #[test]
    fn test_run() {
        let expr = parse_expr_helper("'a' * 0_00_1 & b * 'c'");
        println!("{:?}", expr)
    }

    #[test]
    fn test_constants() {
        // let expression = "";
        // let mut pairs = MIPSParser::parse(Rule::fp_reg, expression).unwrap().into_iter();
        // assert_eq!(pairs.next().unwrap)

        //     SECTION("Constants") {
        //     REQUIRE(eval_expr("1", expression) == 1);
        //     REQUIRE(eval_expr("20", expression) == 20);
        //     REQUIRE(eval_expr("a", expression) == 1);
        //     REQUIRE(eval_expr("a0", expression) == 3);
        //     REQUIRE(eval_expr("deadbeef", expression) == 0xdeadbeef);
        //     REQUIRE(test_parser("asda", expression));
        // }

        // SECTION("Unary Operators") {
        //     REQUIRE(eval_expr("- 0b111110000", expression) == (uint32_t)-496);
        //     REQUIRE(eval_expr("-0xff0000", expression) == (uint32_t)-16711680);

        //     // TOO MANY DIGITS!
        //     REQUIRE_THROWS(eval_expr("-0xfffffffff", expression) == (uint32_t)-16711680);
        // }

        // SECTION("Mul/Div Operators") {
        //     REQUIRE(eval_expr("1*2", expression) == (uint32_t)2);
        //     REQUIRE(eval_expr("1 / 2", expression) == (uint32_t)0);
        //     REQUIRE(eval_expr("1 / 2 * 2", expression) == (uint32_t)0);
        //     REQUIRE(eval_expr("1 * 2 / 2", expression) == (uint32_t)1);
        //     REQUIRE(eval_expr("1 * 2 / -2", expression) == (uint32_t)-1);
        //     REQUIRE(eval_expr("-1 * 2 / -2", expression) == (uint32_t)1);
        //     REQUIRE(eval_expr("-1 * -2 / -2", expression) == (uint32_t)-1);
        //     REQUIRE(eval_expr("two/one", expression) == (uint32_t)2);

        //     REQUIRE_THROWS(eval_expr("2 ** -1", expression));
        // }

        // SECTION("Add/Sub Operators") {
        //     REQUIRE(eval_expr("1+2", expression) == (uint32_t)3);
        //     REQUIRE(eval_expr("1 - 2", expression) == (uint32_t)-1);
        // }

        // SECTION("Add/Sub Operators") {
        //     REQUIRE(eval_expr("1+2", expression) == (uint32_t)3);
        //     REQUIRE(eval_expr("1 - 2", expression) == (uint32_t)-1);
        // }

        // SECTION("Add/Sub Operators") {
        //     REQUIRE(eval_expr("1+2", expression) == (uint32_t)3);
        //     REQUIRE(eval_expr("1 - 2", expression) == (uint32_t)-1);
        // }

        // SECTION("Or Operators") {
        //     REQUIRE(eval_expr("1 | 2", expression) == (uint32_t)3);
        //     REQUIRE(eval_expr("1 | deadbeef", expression) == (uint32_t)(1 | 0xdeadbeef));
        //     REQUIRE(eval_expr("-1 | 2", expression) == (uint32_t)-1);
        //     REQUIRE(eval_expr("2 | -1", expression) == (uint32_t)-1);

        //     REQUIRE_THROWS(eval_expr("2 || -1", expression));
        // }

        // SECTION("ANd Operators") {
        //     REQUIRE(eval_expr("1 & 2", expression) == (uint32_t)0);
        //     REQUIRE(eval_expr("1 & deadbeef", expression) == (uint32_t)(1 & 0xdeadbeef));
        //     REQUIRE(eval_expr("-1 & 2", expression) == (uint32_t)2);
        //     REQUIRE(eval_expr("2 & -1", expression) == (uint32_t)2);

        //     REQUIRE_THROWS(eval_expr("2 && -1", expression));
        // }

        // SECTION("Parentheses") {
        //     REQUIRE(eval_expr("(1 & 2) | 3", expression) == (uint32_t)3);
        //     REQUIRE(eval_expr("(0b10101 | 0b1010) + (5 * 5)", expression) == (uint32_t)56);
        //     REQUIRE(eval_expr("(0b10101 | 0b1010) & (5 * 5)", expression) == (uint32_t)25);
        //     REQUIRE(eval_expr("-(-1)", expression) == (uint32_t)1);

        //     REQUIRE_THROWS(eval_expr("(0b10101 | 0b1010", expression));
        // }

        // SECTION("Order of Operations") {
        //     REQUIRE(eval_expr("1 & 2 * 3 | +4 + ~5 - 1", expression) == (uint32_t)-3);
        //     REQUIRE(eval_expr("(1 & (2 * 3 | +4) + ~5) - 1", expression) == (uint32_t)-1);
        // }

        // SECTION("Literal List") {
        //     client::ast::LiteralLst<client::ast::expression> expr_lst;
        //     parse_expression("0 1 2 3", mips_parser::EXPR_LST, expr_lst);

        //     REQUIRE(expr_lst.size() == 4);
        //     REQUIRE(eval(expr_lst[0]) == 0);
        //     REQUIRE(eval(expr_lst[1]) == 1);
        //     REQUIRE(eval(expr_lst[2]) == 2);
        //     REQUIRE(eval(expr_lst[3]) == 3);
        // }

        // SECTION("Repeat List") {
        //     client::ast::RepeatLst<client::ast::expression> expr_lst;
        //     parse_expression("1 : 10", mips_parser::REPEAT_EXPR_LST, expr_lst);

        //     REQUIRE(eval(expr_lst.repeat_num) == 10);
        //     REQUIRE(eval(expr_lst.repeat_value) == 1);
        // }
    }
}
