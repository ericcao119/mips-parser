use std::{
    boxed::Box, collections::HashMap, fmt, mem::transmute_copy, num::Wrapping, str::FromStr,
    vec::Vec,
};

fn to_i32(value: Wrapping<u32>) -> Wrapping<i32> {
    let reinterpreted: Wrapping<i32> = Wrapping(unsafe { transmute_copy(&value.0) });
    reinterpreted
}

fn to_u32(value: Wrapping<i32>) -> Wrapping<u32> {
    let reinterpreted: Wrapping<u32> = Wrapping(unsafe { transmute_copy(&value.0) });
    reinterpreted
}

pub trait Eval {
    fn eval(&self, mapping: fn(&str) -> Wrapping<u32>) -> Wrapping<u32>;
}

enum MonOp {
    PosOp,
    NegOp,
    BitNotOp,
}

impl FromStr for MonOp {
    type Err = ();

    fn from_str(s: &str) -> Result<MonOp, ()> {
        match s {
            "+" => Ok(MonOp::PosOp),
            "-" => Ok(MonOp::NegOp),
            "~" => Ok(MonOp::BitNotOp),
            _ => Err(()),
        }
    }
}

impl fmt::Display for MonOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            MonOp::PosOp => write!(f, "+"),
            MonOp::NegOp => write!(f, "-"),
            MonOp::BitNotOp => write!(f, "~"),
        }
    }
}

enum BinOp {
    PlusOp,
    MinusOp,
    TimesOp,
    DivideOp,
    BitAndOp,
    BitOrOp,
}

impl FromStr for BinOp {
    type Err = ();

    fn from_str(s: &str) -> Result<BinOp, ()> {
        match s {
            "+" => Ok(BinOp::PlusOp),
            "-" => Ok(BinOp::MinusOp),
            "*" => Ok(BinOp::TimesOp),
            "/" => Ok(BinOp::DivideOp),
            "&" => Ok(BinOp::BitAndOp),
            "|" => Ok(BinOp::BitOrOp),
            _ => Err(()),
        }
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            BinOp::PlusOp => write!(f, "+"),
            BinOp::MinusOp => write!(f, "-"),
            BinOp::TimesOp => write!(f, "*"),
            BinOp::DivideOp => write!(f, "/"),
            BinOp::BitAndOp => write!(f, "&"),
            BinOp::BitOrOp => write!(f, "|"),
        }
    }
}

struct Unary {
    operator: MonOp,
    operand: Operand,
}

impl fmt::Display for Unary {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}", self.operator, self.operand)
    }
}

impl Eval for Unary {
    fn eval(&self, mapping: fn(&str) -> Wrapping<u32>) -> Wrapping<u32> {
        let mut value: Wrapping<u32> = self.operand.eval(mapping);

        match self.operator {
            MonOp::PosOp => value,
            MonOp::NegOp => -value,
            MonOp::BitNotOp => !value,
        }
    }
}

struct BinaryOperation {
    operator: BinOp,
    operand: Operand,
}

impl fmt::Display for BinaryOperation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}{}", self.operator, self.operand)
    }
}

struct Expr {
    first: Operand,
    rest: Vec<BinaryOperation>,
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.first)?;
        for operation in self.rest.iter() {
            write!(f, "{}", operation)?;
        }
        Ok(())
    }
}

impl Eval for Expr {
    fn eval(&self, mapping: fn(&str) -> Wrapping<u32>) -> Wrapping<u32> {
        let mut value = self.first.eval(mapping);
        for oper in self.rest.iter() {
            match oper.operator {
                BinOp::PlusOp => value += oper.operand.eval(mapping),
                BinOp::MinusOp => value -= oper.operand.eval(mapping),
                BinOp::TimesOp => {
                    let mut int = to_i32(value);
                    int *= to_i32(oper.operand.eval(mapping));
                    value = to_u32(int);
                }
                BinOp::DivideOp => {
                    let mut int = to_i32(value);
                    int /= to_i32(oper.operand.eval(mapping));
                    value = to_u32(int);
                }
                BinOp::BitAndOp => value &= oper.operand.eval(mapping),
                BinOp::BitOrOp => value |= oper.operand.eval(mapping),
            };
        }
        value
    }
}

enum Operand {
    Var(String),
    Num(Wrapping<u32>),
    Unary(Box<Unary>),
    Expr(Box<Expr>),
}

impl Operand {
    fn constant(num: u32) -> Operand {
        Operand::Num(Wrapping(num))
    }

    fn var(name: &str) -> Operand {
        Operand::Var(String::from(name))
    }

    fn integer(num: i32) -> Operand {
        Operand::Num(Wrapping(unsafe { transmute_copy(&num) }))
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            Operand::Var(name) => write!(f, "{}", name)?,
            Operand::Num(value) => write!(f, "{}", value)?,
            Operand::Unary(unary) => write!(f, "{}", unary)?,
            Operand::Expr(expr) => write!(f, "({})", expr)?,
        }

        Ok(())
    }
}

impl Eval for Operand {
    fn eval(&self, mapping: fn(&str) -> Wrapping<u32>) -> Wrapping<u32> {
        match &self {
            Operand::Var(name) => mapping(name),
            Operand::Num(value) => *value,
            Operand::Unary(unary) => (*unary).eval(mapping),
            Operand::Expr(expr) => (*expr).eval(mapping),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    lazy_static! {
        static ref ENV: HashMap<&'static str, Wrapping<u32>> = hashmap! {
            "abc" => Wrapping(123),
            "deadc0de" => Wrapping(0xdeadc0de),
            "deadbeef" => Wrapping(0xdeadbeef),
            "one" => Wrapping(1),
        };
    }

    fn mapping(name: &str) -> Wrapping<u32> {
        *ENV.get(name).unwrap()
    }

    #[test]
    fn test_constant() {
        let expr = Operand::Num(Wrapping(32));
        assert_eq!(32, expr.eval(|_| { Wrapping(0) }).0);
    }

    #[test]
    fn test_label() {
        let expr = Operand::Var(String::from("one"));
        assert_eq!(Wrapping(1), expr.eval(mapping))
    }

    #[test]
    fn test_unary_constant() {
        let num = Wrapping(0xffffffff);

        let expr = Operand::Unary(Box::new(Unary {
            operator: MonOp::PosOp,
            operand: Operand::Num(num),
        }));
        assert_eq!(Wrapping(0xffffffff), expr.eval(mapping));

        let expr = Operand::Unary(Box::new(Unary {
            operator: MonOp::NegOp,
            operand: Operand::Num(num),
        }));
        assert_eq!(Wrapping(1), expr.eval(mapping));

        let expr = Operand::Unary(Box::new(Unary {
            operator: MonOp::BitNotOp,
            operand: Operand::Num(num),
        }));
        assert_eq!(Wrapping(0), expr.eval(mapping));
    }

    #[test]
    fn test_unary_label() {
        let var = String::from("abc");
        let expr = Operand::Unary(Box::new(Unary {
            operator: MonOp::PosOp,
            operand: Operand::Var(var.clone()),
        }));
        assert_eq!(Wrapping(123), expr.eval(mapping));

        let expr = Operand::Unary(Box::new(Unary {
            operator: MonOp::NegOp,
            operand: Operand::Var(var.clone()),
        }));
        assert_eq!(Wrapping(0xffffff85), expr.eval(mapping));

        let expr = Operand::Unary(Box::new(Unary {
            operator: MonOp::BitNotOp,
            operand: Operand::Var(var.clone()),
        }));
        assert_eq!(Wrapping(0xffffff84), expr.eval(mapping));
    }

    #[test]
    fn test_expr_single() {
        let expr = Operand::Expr(Box::new(Expr {
            first: Operand::constant(12),
            rest: vec![],
        }));

        assert_eq!(Wrapping(12), expr.eval(mapping));

        let expr = Operand::Expr(Box::new(Expr {
            first: Operand::var("abc"),
            rest: vec![],
        }));

        assert_eq!(Wrapping(123), expr.eval(mapping));
    }

    #[test]
    fn test_expr_valid_ops() {
        // 12 + -13
        let expr = Operand::Expr(Box::new(Expr {
            first: Operand::constant(12),
            rest: vec![BinaryOperation {
                operator: BinOp::PlusOp,
                operand: Operand::integer(-13),
            }],
        }));
        assert_eq!(to_u32(Wrapping(-1)), expr.eval(mapping));

        // 12 - 13
        let expr = Operand::Expr(Box::new(Expr {
            first: Operand::constant(12),
            rest: vec![BinaryOperation {
                operator: BinOp::MinusOp,
                operand: Operand::integer(13),
            }],
        }));
        assert_eq!(to_u32(Wrapping(-1)), expr.eval(mapping));

        // 12 * -1
        let expr = Operand::Expr(Box::new(Expr {
            first: Operand::constant(12),
            rest: vec![BinaryOperation {
                operator: BinOp::TimesOp,
                operand: Operand::integer(-1),
            }],
        }));
        assert_eq!(to_u32(Wrapping(-12)), expr.eval(mapping));

        // -4 / -2
        let expr = Operand::Expr(Box::new(Expr {
            first: Operand::integer(-4),
            rest: vec![BinaryOperation {
                operator: BinOp::DivideOp,
                operand: Operand::integer(-2),
            }],
        }));
        assert_eq!(to_u32(Wrapping(2)), expr.eval(mapping));

        // 4 / -2
        let expr = Operand::Expr(Box::new(Expr {
            first: Operand::integer(4),
            rest: vec![BinaryOperation {
                operator: BinOp::DivideOp,
                operand: Operand::integer(-2),
            }],
        }));
        assert_eq!(to_u32(Wrapping(-2)), expr.eval(mapping));

        // -4 / 2
        let expr = Operand::Expr(Box::new(Expr {
            first: Operand::integer(-4),
            rest: vec![BinaryOperation {
                operator: BinOp::DivideOp,
                operand: Operand::integer(2),
            }],
        }));
        assert_eq!(to_u32(Wrapping(-2)), expr.eval(mapping));

        // 2 / 4
        let expr = Operand::Expr(Box::new(Expr {
            first: Operand::integer(2),
            rest: vec![BinaryOperation {
                operator: BinOp::DivideOp,
                operand: Operand::integer(4),
            }],
        }));
        assert_eq!(to_u32(Wrapping(0)), expr.eval(mapping));

        // 0xffff0000 & -1
        let expr = Operand::Expr(Box::new(Expr {
            first: Operand::constant(0xffff0000),
            rest: vec![BinaryOperation {
                operator: BinOp::BitAndOp,
                operand: Operand::integer(-1),
            }],
        }));
        assert_eq!(Wrapping(0xffff0000), expr.eval(mapping));

        // 0xffff0000 | -1
        let expr = Operand::Expr(Box::new(Expr {
            first: Operand::constant(0xffff0000),
            rest: vec![BinaryOperation {
                operator: BinOp::BitOrOp,
                operand: Operand::integer(-1),
            }],
        }));
        assert_eq!(Wrapping(0xffffffff), expr.eval(mapping));
    }

    #[test]
    fn test_expr_nested() {
        // 12 - 13 = -1
        let expr_neg1 = Operand::Expr(Box::new(Expr {
            first: Operand::constant(12),
            rest: vec![BinaryOperation {
                operator: BinOp::PlusOp,
                operand: Operand::integer(-13),
            }],
        }));
        assert_eq!(Operand::integer(-1).eval(mapping), expr_neg1.eval(mapping));

        // Compound instruction
        // abc + abc + abc = 123 * 3 = 369
        let expr_369 = Operand::Expr(Box::new(Expr {
            first: Operand::var("abc"),
            rest: vec![
                BinaryOperation {
                    operator: BinOp::PlusOp,
                    operand: Operand::var("abc"),
                },
                BinaryOperation {
                    operator: BinOp::PlusOp,
                    operand: Operand::var("abc"),
                },
            ],
        }));
        assert_eq!(Wrapping(369), expr_369.eval(mapping));

        // Compound instruction
        // one * deadbeef / abc = 30373402
        let expr_30373402 = Operand::Expr(Box::new(Expr {
            first: Operand::var("one"),
            rest: vec![
                BinaryOperation {
                    operator: BinOp::TimesOp,
                    operand: Operand::var("deadbeef"),
                },
                BinaryOperation {
                    operator: BinOp::DivideOp,
                    operand: Operand::var("abc"),
                },
            ],
        }));
        assert_eq!(-Wrapping::<u32>(4545030), expr_30373402.eval(mapping));

        let complex = Operand::Expr(Box::new(Expr {
            first: expr_neg1,
            rest: vec![
                BinaryOperation {
                    operator: BinOp::TimesOp,
                    operand: expr_30373402,
                },
                BinaryOperation {
                    operator: BinOp::DivideOp,
                    operand: expr_369,
                },
            ],
        }));

        assert_eq!(Wrapping(12317), complex.eval(mapping))
    }
}
