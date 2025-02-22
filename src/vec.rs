use std::ops::{Deref, DerefMut, RangeBounds};

use crate::{
    gcd::gcd,
    params::{Num, C_STYLE_MOD, GOAL},
};

#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Vector(Box<[Num]>);

impl Vector {
    pub fn constant(n: Num) -> Vector {
        Vector(vec![n; GOAL.len()].into_boxed_slice())
    }

    pub fn from_slice(ns: &[Num]) -> Vector {
        Vector(ns.to_owned().into_boxed_slice())
    }

    pub fn map(mut self, function: fn(Num) -> Num) -> Vector {
        for x in &mut self.0.iter_mut() {
            *x = function(*x)
        }
        self
    }
}

impl Deref for Vector {
    type Target = Box<[Num]>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Vector {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

macro_rules! impl_op {
    ($trait:ident, $func:ident, $op:tt) => {
        impl std::ops::$trait<&Self> for Vector {
            type Output = Vector;

            fn $func(mut self, rhs: &Self) -> Self::Output {
                for (x, y) in self.iter_mut().zip(rhs.iter()) {
                    *x $op y;
                }
                self
            }
        }
    }
}

macro_rules! impl_unary {
    ($trait:ident, $func:ident, $op:tt) => {
        impl std::ops::$trait for Vector {
            type Output = Vector;

            fn $func(mut self) -> Self::Output {
                for x in self.iter_mut() {
                    *x = $op(*x);
                }
                self
            }
        }
    };
}

impl_op!(Add, add, +=);
impl_op!(Sub, sub, -=);
impl_op!(Mul, mul, *=);
impl_op!(Div, div, /=);
impl_op!(Rem, rem, %=);
impl_op!(BitAnd, bitand, &=);
impl_op!(BitOr, bitor, |=);
impl_op!(BitXor, bitxor, ^=);
impl_op!(Shl, shl, <<=);
impl_op!(Shr, shr, >>=);
impl_unary!(Not, not, !);
impl_unary!(Neg, neg, -);

pub fn divmod(left: &Vector, right: &Vector) -> Option<(Vector, Vector)> {
    if left
        .iter()
        .zip(right.iter())
        .any(|(&x, &y)| y == 0 || (x, y) == (Num::MIN, -1))
    {
        None
    } else if C_STYLE_MOD {
        Some((left.clone() / right, left.clone() % right))
    } else {
        let modulo = (left.clone() % right + right) % right;
        let div = (left.clone() - &modulo) / right;
        Some((div, modulo))
    }
}

pub fn vec_or(left: &Vector, right: &Vector) -> Vector {
    let mut left = left.clone();
    for (x, y) in left.iter_mut().zip(right.iter()) {
        if *x == 0 {
            *x = *y;
        }
    }
    left
}

pub fn vec_eq(left: &Vector, right: &Vector) -> Vector {
    let mut left = left.clone();
    for (x, y) in left.iter_mut().zip(right.iter()) {
        *x = (*x == *y) as Num;
    }
    left
}

pub fn vec_lt(left: &Vector, right: &Vector) -> Vector {
    let mut left = left.clone();
    for (x, y) in left.iter_mut().zip(right.iter()) {
        *x = (*x < *y) as Num;
    }
    left
}

pub fn vec_le(left: &Vector, right: &Vector) -> Vector {
    let mut left = left.clone();
    for (x, y) in left.iter_mut().zip(right.iter()) {
        *x = (*x <= *y) as Num;
    }
    left
}

pub fn vec_gcd(left: &Vector, right: &Vector) -> Vector {
    let mut left = left.clone();
    for (x, y) in left.iter_mut().zip(right.iter()) {
        *x = gcd(*x, *y);
    }
    left
}

pub fn vec_pow(left: &Vector, right: &Vector) -> Vector {
    let mut left = left.clone();
    for (x, y) in left.iter_mut().zip(right.iter()) {
        *x = (*x).pow(*y as u32);
    }
    left
}

pub fn vec_in<R: RangeBounds<Num>>(vec: &Vector, bounds: R) -> bool {
    (0..GOAL.len()).all(|i| bounds.contains(&vec[i]))
}
