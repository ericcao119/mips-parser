use pest::Parser;

#[derive(Parser)]
#[grammar = "mips.pest"]
struct MIPSParser;

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
