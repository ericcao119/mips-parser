extern crate pest;

#[macro_use]
extern crate pest_derive;

#[macro_use]
extern crate maplit;

#[macro_use]
extern crate lazy_static;

mod arith;
mod expression;
mod ident;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
