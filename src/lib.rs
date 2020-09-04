#[macro_use]
extern crate pest_derive;
extern crate pest;
#[macro_use]
extern crate maplit;
#[macro_use]
extern crate lazy_static;
extern crate itertools;

pub mod expression;
pub mod parser;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
