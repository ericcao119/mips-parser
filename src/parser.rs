use crate::expression::{BinOp, Eval, MonOp, Operand};
use nom::{
    bytes::complete::escaped_transform,
    character::complete::{none_of, one_of},
    IResult,
};
use pest::{error::Error, Parser};
use std::collections::HashMap;
use std::iter::Iterator;
use std::num::Wrapping;
use std::str;

use itertools::Itertools;

#[derive(Parser)]
#[grammar = "mips.pest"]
struct MIPSParser;

/// Function for parsing entire program into a list of commands
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

    unimplemented!()
}

/// Sub parser for unsigned integers. It supports reading from
/// - Hex strings prefixed with 0X or 0x. Underscores are removed, so 0x_f_f is valid
/// - Binary strings prefixed with 0B or 0b. Underscores are removed, so 0x_f_f is valid
/// - Decimal strings.
/// - Characters
fn parse_unsigned(pair: pest::iterators::Pair<Rule>) -> u32 {
    match pair.as_rule() {
        Rule::unsigned => {
            let mut pairs = pair.into_inner();
            let inner = pairs.next().unwrap();

            match inner.as_rule() {
                Rule::bin => u32::from_str_radix(&inner.as_str()[2..].replace("_", ""), 2).unwrap(),

                Rule::hex => {
                    u32::from_str_radix(&inner.as_str()[2..].replace("_", ""), 16).unwrap()
                }

                Rule::dec => u32::from_str_radix(&inner.as_str().replace("_", ""), 10).unwrap(),
                Rule::char => {
                    let character_str = inner.as_str().trim_matches('\'');
                    let character = match &character_str[..] {
                        r"\n" => '\n' as u8,
                        r"\t" => '\t' as u8,
                        r"\\" => '\\' as u8,
                        r"\0" => '\0' as u8,
                        r#"\0""# => '"' as u8,
                        r"\'" => '\'' as u8,
                        &_ => {
                            if &character_str[..1] != r"\" {
                                // Plain character
                                *(&character_str[..1].chars().next().unwrap()) as u8
                            } else if &character_str[..2] == r"\x" {
                                // Hex encoding
                                u8::from_str_radix(&character_str[2..], 16).unwrap()
                            } else {
                                panic!("Unrecognized escape")
                            }
                        }
                    };
                    character as u32
                }
                _ => unreachable!(),
            }
        }
        _ => unreachable!(),
    }
}

/// Sub parser for integer expressions. It follows the following operators and precedence
/// - Unary Operators: ~, +, /
/// - Multiplicative Operators: * -
/// - Addititve Operators: = -
/// - Bitwise And: &
/// - Bitwise And: |
///
/// Operands can either be expressed as integers, unsigned, variables, or expressions built from those atomics
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
                _ => unreachable!(),
            }
        }
        Rule::atomic_expr => {
            let mut pairs = pair.into_inner();
            let inner = pairs.next().unwrap();

            match inner.as_rule() {
                Rule::unsigned => Ok(Operand::unsigned(parse_unsigned(inner))),
                Rule::ident => Ok(Operand::var(inner.as_str())),
                Rule::expr => parse_expr(inner),
                _ => unreachable!(),
            }
        }
        _ => panic!("Unmatched case in expression!"),
    }
}

/// Replaces escaped characters with their corresponding value in an arbitrary string.
///
/// So "ab\tcd" => "ab  cd"
fn unescape(escaped_str: &str) -> String {
    const HEX_DIGIT: &str = "0123456789abcdefABCDEF";
    let escape_string: IResult<&str, String, ()> =
        escaped_transform(none_of("\\"), r"\".chars().next().unwrap(), |i: &str| {
            alt!(i,
              tag!("\\")      => { |_| { '\\' }}
            | tag!("\"")      => { |_| { '\"' }}
            | tag!("n")       => { |_| { '\n' }}
            | tag!("r")       => { |_| { '\r' }}
            | tag!("t")       => { |_| { '\t' }}
            | tag!("0")       => { |_| { '\0' }}
            | tag!("\'")      => { |_| { '\'' }}
            | preceded!(char!('x'), tuple!(one_of!(HEX_DIGIT), one_of!(HEX_DIGIT))) => {
                |(c1, c2): (char, char)| {
                    println!("Hex String");
                    match (c1.to_digit(16), c2.to_digit(16)) {
                    (Some(d1), Some(d2)) => {
                        (((d1 as u8) << 4) + d2 as u8) as char
                    },
                    _ => unreachable!(),
                }
                }
            }
            )
        })(escaped_str);
    let (remaining, output) = escape_string.unwrap();
    assert_eq!("", remaining);
    output
}

// Parses a quote_string
fn parse_quote_string(quote_str: &str) -> String {
    if quote_str == r#""""# {
        return String::from("");
    }
    if quote_str.len() <= 2 {
        panic!("Invalid quote string")
    }

    unescape(&quote_str[1..quote_str.len() - 1])
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! parser_helper {
        (fn $name: ident -> $ret:ty, $pair: ident: $type: expr, $pat: pat => $body: expr) => {
            fn $name(source: &str) -> $ret {
                let mut pairs = MIPSParser::parse($type, source).unwrap();
                let $pair = pairs.next().unwrap();

                if $pair.as_span().start() != 0 || $pair.as_span().end() != source.len() {
                    panic!("Did not capture the entire string!")
                }

                match $pair.as_rule() {
                    $pat => $body,
                    _ => panic!("Failed"),
                }
            }
        };
    }

    parser_helper!(fn parse_expr_helper -> Operand, pair: Rule::expr, Rule::expr => parse_expr(pair).unwrap());
    parser_helper!(fn parse_unsigned_helper -> u32, pair: Rule::unsigned, Rule::unsigned => parse_unsigned(pair));

    lazy_static! {
        static ref ENV: HashMap<&'static str, Wrapping<u32>> = hashmap! {
            "a" => Wrapping(1),
            "ab" => Wrapping(2),
            "a0" => Wrapping(3),

            // hex strings
            "deadbeef" => Wrapping( 0xdeadbeef),
            "deadc0de" => Wrapping( 0xdeadc0de),
            "ffffffff" => Wrapping( 0xffffffff),

            // Small ints
            "one" => Wrapping( 1),
            "two" => Wrapping( 2),
            "three" => Wrapping( 3),
        };
    }

    fn mapping(name: &str) -> Wrapping<u32> {
        *ENV.get(name).unwrap()
    }

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

    // #[test]
    // fn test_run() {
    //     let expr = parse_helper("'a' * 0B_10_1 & b * 'c'");
    //     // let expr = parse_expr_helper("'a' * 0_00_1 & b * 'c'");
    //     println!("{:?}", expr)
    // }

    #[test]
    fn test_unsigned() {
        assert_eq!(5, parse_unsigned_helper("0B_10_1"));
        assert_eq!(3, parse_unsigned_helper("0b_01_1"));
        assert_eq!(510, parse_unsigned_helper("0x_1f_e"));
        assert_eq!(239, parse_unsigned_helper("0X_E_f"));
        assert_eq!(239, parse_unsigned_helper("239"));
        assert_eq!(99, parse_unsigned_helper("'c'"));
        assert_eq!(10, parse_unsigned_helper(r"'\n'"));
        assert_eq!(0, parse_unsigned_helper(r#"'\0'"#));
        assert_eq!(255, parse_unsigned_helper(r#"'\xff'"#));
    }

    #[test]
    #[should_panic]
    fn test_invalid_unsigned() {
        assert_eq!(5, parse_unsigned_helper("'as'"));
    }

    #[test]
    fn test_quote_string() {
        let actual = parse_quote_string(r#""""#);
        assert_eq!("", actual);

        let actual = parse_quote_string(r#""\x41""#);
        assert_eq!("A", actual);

        let actual = parse_quote_string(r#""\r""#);
        assert_eq!("\r", actual);

        let actual = parse_quote_string(r#""\n""#);
        assert_eq!("\n", actual);

        let actual = parse_quote_string(r#""\n\r\t\\\0\"\'\x41assad""#);
        assert_eq!("\n\r\t\\\0\"\'\x41assad", actual);

        let actual = parse_quote_string(r#""assad""#);
        assert_eq!("assad", actual);
    }

    #[test]
    fn test_constants() {
        assert_eq!(parse_expr_helper("1").eval_u32(mapping), 1);
        assert_eq!(parse_expr_helper("20").eval_u32(mapping), 20);
        assert_eq!(parse_expr_helper("a").eval_u32(mapping), 1);
        assert_eq!(parse_expr_helper("a0").eval_u32(mapping), 3);
        assert_eq!(parse_expr_helper("deadbeef").eval_u32(mapping), 0xdeadbeef);
    }

    #[test]
    fn test_unary() {
        assert_eq!(parse_expr_helper("- 0b111110000").eval_i32(mapping), -496);
        assert_eq!(parse_expr_helper("-0xff0000").eval_i32(mapping), -16711680);
    }

    #[test]
    #[should_panic]
    fn test_unary_fail() {
        // TOO MANY DIGITS!
        parse_expr_helper("-0xfffffffff").eval_i32(mapping);
    }

    #[test]
    fn test_mul_operators() {
        assert_eq!(parse_expr_helper("1*2").eval_i32(mapping), 2);
        assert_eq!(parse_expr_helper("1 / 2").eval_i32(mapping), 0);
        assert_eq!(parse_expr_helper("1 / 2 * 2").eval_i32(mapping), 0);
        assert_eq!(parse_expr_helper("1 * 2 / 2").eval_i32(mapping), 1);
        assert_eq!(parse_expr_helper("1 * 2 / -2").eval_i32(mapping), -1);
        assert_eq!(parse_expr_helper("-1 * 2 / -2").eval_i32(mapping), 1);
        assert_eq!(parse_expr_helper("-1 * -2 / -2").eval_i32(mapping), -1);
        assert_eq!(parse_expr_helper("two/one").eval_i32(mapping), 2);
    }

    #[test]
    #[should_panic]
    fn test_mul_operators_fail() {
        parse_expr_helper("2 ** -1");
    }

    #[test]
    fn test_add_operators() {
        assert_eq!(parse_expr_helper("1+2").eval_i32(mapping), 3);
        assert_eq!(parse_expr_helper("1 - 2").eval_i32(mapping), -1);
    }

    #[test]
    #[should_panic]
    fn test_add_operators_fail() {
        parse_expr_helper("2 ++ -1");
    }

    #[test]
    fn test_or_operators() {
        assert_eq!(parse_expr_helper("1 | 2").eval_i32(mapping), 3);
        assert_eq!(parse_expr_helper("-1 | 2").eval_i32(mapping), -1);
        assert_eq!(parse_expr_helper("2 | -1").eval_i32(mapping), -1);
        assert_eq!(parse_expr_helper("1 | deadbeef").eval_u32(mapping), (1 | 0xdeadbeef));
    }

    #[test]
    #[should_panic]
    fn test_or_operators_fail() {
        parse_expr_helper("2 || -1");
    }

    #[test]
    fn test_and_operators() {
        assert_eq!(parse_expr_helper("1 & 2").eval_u32(mapping), 0);
        assert_eq!(parse_expr_helper("1 & deadbeef").eval_u32(mapping), (1 & 0xdeadbeef));
        assert_eq!(parse_expr_helper("-1 & 2").eval_u32(mapping), 2);
        assert_eq!(parse_expr_helper("2 & -1").eval_u32(mapping), 2);

    }

    #[test]
    #[should_panic]
    fn test_and_operators_fail() {
        parse_expr_helper("2 && -1");
    }

    #[test]
    fn test_paren() {
        assert_eq!(parse_expr_helper("(1 & 2) | 3").eval_u32(mapping), 3);
        assert_eq!(parse_expr_helper("(0b10101 | 0b1010) + (5 * 5)").eval_u32(mapping), 56);
        assert_eq!(parse_expr_helper("(0b10101 | 0b1010) & (5 * 5)").eval_u32(mapping), 25);
        assert_eq!(parse_expr_helper("-(-1)").eval_u32(mapping), 1);
    }

    #[test]
    #[should_panic]
    fn test_paren_fail() {
        parse_expr_helper("(0b10101 | 0b1010");
    }

    fn test_order_of_operations() {
        assert_eq!(parse_expr_helper("1 & 2 * 3 | +4 + ~5 - 1").eval_i32(mapping), -3);
        assert_eq!(parse_expr_helper("(1 & (2 * 3 | +4) + ~5) - 1").eval_i32(mapping), -1);
    }

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
