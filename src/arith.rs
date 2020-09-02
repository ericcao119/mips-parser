use std::num::Wrapping;
use std::mem::transmute;


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unsigned_negation() {
        let mut unsigned :Wrapping<u32> = Wrapping::<u32>(1);
        assert_eq!(0xffffffff, (-unsigned).0);
    }

    #[test]
    fn test_unsigned_conversion() {
        let mut unsigned :Wrapping<u32> = Wrapping::<u32>(1);
        let mut int :Wrapping<i32> = Wrapping(unsafe { transmute(unsigned.0) });
        assert_eq!(1, int.0);


        let mut unsigned :Wrapping<u32> = Wrapping::<u32>(0xffffffff);
        let mut int :Wrapping<i32> = Wrapping(unsafe { transmute(unsigned.0) });
        assert_eq!(-1, int.0);
    }
}