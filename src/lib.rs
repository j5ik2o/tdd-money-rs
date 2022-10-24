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
        assert_eq!(m1.negated(), Money::new(Decimal::from(-1), CurrencyCode::USD));
    }

    #[test]
    fn test_add() {
        let mut m = Money::new(Decimal::from(1), CurrencyCode::USD);
        m.add(Money::new(Decimal::from(2), CurrencyCode::USD)).unwrap();
        assert_eq!(m, Money::new(Decimal::from(3), CurrencyCode::USD));
    }

    #[test]
    fn test_subtract() {
        let mut m = Money::new(Decimal::from(1), CurrencyCode::USD);
        m.subtract(Money::new(Decimal::from(1), CurrencyCode::USD)).unwrap();
        assert_eq!(m, Money::new(Decimal::from(0), CurrencyCode::USD));
    }

    #[test]
    fn test_times() {
        let mut m = Money::new(Decimal::from(1), CurrencyCode::USD);
        m.times(Decimal::from_i32(2).unwrap());
        assert_eq!(
            m,
            Money::new(Decimal::from_i32(2).unwrap(), CurrencyCode::USD)
        );
    }

    #[test]
    fn test_divided_by() {
        let mut m = Money::new(Decimal::from(10), CurrencyCode::USD);
        m.divided_by(Decimal::from_i32(2).unwrap());
        assert_eq!(
            m,
            Money::new(Decimal::from_i32(5).unwrap(), CurrencyCode::USD)
        );
    }
}
