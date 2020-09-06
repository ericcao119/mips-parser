#[macro_use]
extern crate pest_derive;
extern crate pest;
#[macro_use]
extern crate maplit;
#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate nom;
extern crate itertools;


#[macro_use]
pub mod parser;

pub mod utils;
pub mod literals;
pub mod expression;


#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
