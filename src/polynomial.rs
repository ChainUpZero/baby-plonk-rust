use bls12_381::Scalar;
use std::ops::{Add, Mul, Sub};
#[derive(Debug, Clone, PartialEq)]
pub enum Basis {
    Lagrange,
    Monomial,
}
#[derive(PartialEq, Debug)]
pub struct Polynomial {
    pub values: Vec<Scalar>,
    pub basis: Basis,
}
impl Polynomial {
    pub fn new(values: Vec<Scalar>, basis: Basis) -> Polynomial {
        Polynomial { values, basis }
    }
}

impl Add for Polynomial {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        assert_eq!(self.basis, other.basis, "Basis must be the same");

        match self.basis {
            //点值表示
            Basis::Lagrange => {
                assert_eq!(
                    self.values.len(),
                    other.values.len(),
                    "Polynomials must have the same length"
                );
                Polynomial {
                    values: self
                        .values
                        .iter()
                        .zip(other.values.iter())
                        .map(|(a, b)| a + b)
                        .collect(),
                    basis: self.basis,
                }
            }
            Basis::Monomial => {
                // 系数表示
                let max_len = std::cmp::max(self.values.len(), other.values.len());
                let mut result = vec![Scalar::from(0); max_len];
                for (i, value) in self.values.iter().enumerate() {
                    result[i] += value;
                }
                for (i, value) in other.values.iter().enumerate() {
                    result[i] += value;
                }
                Polynomial {
                    values: result,
                    basis: self.basis,
                }
            }
        }
    }
}
impl Sub for Polynomial {
    type Output = Self;
    fn sub(self, other: Self) -> Self::Output {
        assert_eq!(self.basis, other.basis, "Basis must be the same");

        match self.basis {
            //点值表示
            Basis::Lagrange => {
                assert_eq!(
                    self.values.len(),
                    other.values.len(),
                    "Polynomials must have the same length"
                );
                Polynomial {
                    values: self
                        .values
                        .iter()
                        .zip(other.values.iter())
                        .map(|(a, b)| a - b)
                        .collect(),
                    basis: self.basis,
                }
            }
            Basis::Monomial => {
                // 系数表示
                let max_len = std::cmp::max(self.values.len(), other.values.len());
                let mut result = vec![Scalar::from(0); max_len];
                for (i, value) in self.values.iter().enumerate() {
                    result[i] += value;
                }
                for (i, value) in other.values.iter().enumerate() {
                    result[i] -= value;
                }
                Polynomial {
                    values: result,
                    basis: self.basis,
                }
            }
        }
    }
}
// impl Mul for Polynomial {
//     type Output = Self;
//     fn mul(self, other: Self) -> Self::Output {
//         assert_eq!(self.basis, other.basis, "Basis must be the same");
//         match self.basis {
//             Basis::Lagrange => {
//                 //点值表示
//                 assert_eq!(
//                     self.values.len(),
//                     other.values.len(),
//                     "Polynomials must have the same length"
//                 );
//                 Polynomial {
//                     values: self
//                         .values
//                         .iter()
//                         .zip(other.values.iter())
//                         .map(|(a, b)| a * b)
//                         .collect(),
//                     basis: self.basis,
//                 }
//             }
//             Basis::Monomial => {
//                 //系数表示

//             }
//         }
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_monomial_add() {
        //monomial意思是系数表示
        let p1 = Polynomial::new(vec![Scalar::from(1), Scalar::from(2)], Basis::Monomial);
        let p2 = Polynomial::new(vec![Scalar::from(3), Scalar::from(4)], Basis::Monomial);
        let p3 = Polynomial::new(vec![Scalar::from(4), Scalar::from(6)], Basis::Monomial);
        assert_eq!(p1 + p2, p3);

        let p1 = Polynomial::new(
            vec![Scalar::from(1), Scalar::from(2), Scalar::from(2)],
            Basis::Monomial,
        );
        let p2 = Polynomial::new(vec![Scalar::from(3), Scalar::from(4)], Basis::Monomial);
        let p3 = Polynomial::new(
            vec![Scalar::from(4), Scalar::from(6), Scalar::from(2)],
            Basis::Monomial,
        );
        assert_eq!(p1 + p2, p3);
    }

    #[test]
    fn test_lagrange_add() {
        //lagrange意思是点值表示
        let p1 = Polynomial::new(vec![Scalar::from(1), Scalar::from(2)], Basis::Lagrange);
        let p2 = Polynomial::new(vec![Scalar::from(3), Scalar::from(4)], Basis::Lagrange);
        let p3 = Polynomial::new(vec![Scalar::from(4), Scalar::from(6)], Basis::Lagrange);
        assert_eq!(p1 + p2, p3);
    }

    #[test]
    fn test_monomial_sub() {
        //monomial意思是系数表示
        let p1 = Polynomial::new(vec![Scalar::from(3), Scalar::from(4)], Basis::Monomial);
        let p2 = Polynomial::new(vec![Scalar::from(1), Scalar::from(2)], Basis::Monomial);
        let p3 = Polynomial::new(vec![Scalar::from(2), Scalar::from(2)], Basis::Monomial);
        assert_eq!(p1 - p2, p3);
    }
}
