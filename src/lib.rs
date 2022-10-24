use std::cmp::Ordering;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::str::FromStr;

use iso_4217::CurrencyCode;
use rust_decimal::Decimal;
use rust_decimal::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct Money {
    pub amount: Decimal,
    pub currency: CurrencyCode,
}

#[derive(Debug, PartialEq)]
pub enum MoneyError {
    NotSameCurrencyError,
}

impl Display for MoneyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MoneyError::NotSameCurrencyError => write!(f, "NotSameCurrencyError"),
        }
    }
}

impl Hash for Money {
    fn hash<H>(&self, state: &mut H)
        where
            H: Hasher,
    {
        self.amount.hash(state);
        state.write_u32(self.currency.num());
    }
}

impl PartialOrd for Money {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.currency != other.currency {
            None
        } else if self.amount > other.amount {
            Some(Ordering::Greater)
        } else if self.amount < other.amount {
            Some(Ordering::Less)
        } else {
            Some(Ordering::Equal)
        }
    }
}

impl Money {

}

#[cfg(test)]
mod tests {
    use iso_4217::CurrencyCode;
    use rust_decimal::Decimal;
    use rust_decimal::prelude::{FromPrimitive, Zero};

    use super::*;

    #[test]
    fn test_value() {
        let m1 = Money::new(Decimal::from(1), CurrencyCode::USD);
        assert_eq!(m1.breach_encapsulation_of_amount().to_u32().unwrap(), 1);
        assert_eq!(*m1.breach_encapsulation_of_currency(), CurrencyCode::USD);
    }

    #[test]
    fn test_eq() {
        let m1 = Money::new(Decimal::from(1), CurrencyCode::USD);
        let m2 = Money::new(Decimal::from(1), CurrencyCode::USD);
        assert_eq!(m1, m2);
    }

    #[test]
    fn test_ne() {
        let m1 = Money::new(Decimal::from(1), CurrencyCode::USD);
        let m2 = Money::new(Decimal::from(2), CurrencyCode::USD);
        assert_ne!(m1, m2);
    }

    #[test]
    fn test_zero() {
        let m1 = Money::zero(CurrencyCode::USD);
        let m2 = Money::new(Decimal::zero(), CurrencyCode::USD);
        assert_eq!(m1.abs(), m2);
    }

    #[test]
    fn test_abs() {
        let m1 = Money::new(Decimal::from_i32(-1).unwrap(), CurrencyCode::USD);
        let m2 = Money::new(Decimal::from_i32(1).unwrap(), CurrencyCode::USD);
        assert_eq!(m1.abs(), m2);
    }

    #[test]
    fn test_negated() {
        let m1 = Money::new(Decimal::from(1), CurrencyCode::USD);
        let m2 = m1.clone().negated();
        assert_eq!(m2, Money::new(Decimal::from(-1), CurrencyCode::USD));
    }

    #[test]
    fn test_add() {
        let m1 = Money::new(Decimal::from(1), CurrencyCode::USD);
        let m2 = Money::new(Decimal::from(2), CurrencyCode::USD);
        let m3 = m1.clone().add(m2.clone()).unwrap();
        assert_eq!(
            m3,
            Money::new(Decimal::from_i32(3).unwrap(), CurrencyCode::USD)
        );

        let mut m4 = m1.clone();
        m4.add_mut(m2.clone()).unwrap();
        assert_eq!(m4, m3);
    }

    #[test]
    fn test_subtract() {
        let m1 = Money::new(Decimal::from(1), CurrencyCode::USD);
        let m2 = Money::new(Decimal::from(1), CurrencyCode::USD);
        let m3 = m1.clone().subtract(m2.clone()).unwrap();
        assert_eq!(m3, Money::zero(CurrencyCode::USD));

        let mut m4 = m1.clone();
        m4.subtract_mut(m2.clone()).unwrap();
        assert_eq!(m4, m3);
    }

    #[test]
    fn test_times() {
        let m1 = Money::new(Decimal::from(1), CurrencyCode::USD);
        let m2 = m1.clone().times(Decimal::from_i32(2).unwrap());
        assert_eq!(
            m2,
            Money::new(Decimal::from_i32(2).unwrap(), CurrencyCode::USD)
        );

        let mut m3 = m1.clone();
        m3.times_mut(Decimal::from_i32(2).unwrap());
        assert_eq!(
            m3,
            Money::new(Decimal::from_i32(2).unwrap(), CurrencyCode::USD)
        );
    }

    #[test]
    fn test_divided_by() {
        let m1 = Money::new(Decimal::from(10), CurrencyCode::USD);
        let m2 = m1.clone().divided_by(Decimal::from_i32(2).unwrap());
        assert_eq!(
            m2,
            Money::new(Decimal::from_i32(5).unwrap(), CurrencyCode::USD)
        );

        let mut m3 = m1.clone();
        m3.divided_by_mut(Decimal::from_i32(2).unwrap());
        assert_eq!(
            m3,
            Money::new(Decimal::from_i32(5).unwrap(), CurrencyCode::USD)
        );
    }
}
