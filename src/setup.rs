use crate::polynomial::{Basis, Polynomial};
use bls12_381::{G1Projective, G2Projective, Scalar};
#[derive(Debug)]
struct Setup {
    powers_of_x: Vec<G1Projective>,
    X2: G2Projective,
}
impl Setup {
    pub fn generate_srs(powers: usize, tau: Scalar) -> Setup {
        //生成g1,tau*g1,tau^2 * g1...,tau^(powers-1) * g1
        //tau*g2

        println!("Start to generate SRS...");
        let mut setup = Setup {
            powers_of_x: Vec::new(),
            X2: G2Projective::generator(),
        };
        let cur_powers = G1Projective::generator();

        setup.powers_of_x.push(cur_powers);
        for _ in 1..powers {
            let cur_powers = cur_powers * tau;
            setup.powers_of_x.push(cur_powers);
        }

        setup.X2 = G2Projective::generator() * tau;
        println!("Finish generating SRS.");
        setup
    }
    pub fn commit(&self, polynomial: Polynomial) -> G1Projective {
        //默认是系数(monomial)形式
        if polynomial.basis == Basis::Lagrange {
            todo!();
        } else {
            //系数表示
            let mut commitment = G1Projective::identity();
            //commitment = a1 * g1 + a2 * tau * g1  + ...
            for (i, scalar) in polynomial.values.iter().enumerate() {
                let point = self.powers_of_x[i];
                commitment += scalar * point;
            }

            commitment
        }
    }
}
#[cfg(test)]
mod tests {
    use crate::polynomial;

    use super::*;

    #[test]
    fn test_generate_srs() {
        //passed
        let setup = Setup::generate_srs(2, Scalar::from(1));
        assert_eq!(setup.powers_of_x[0], setup.powers_of_x[1]);
    }

    #[test]
    fn test_commit() {
        //passed
        let setup = Setup::generate_srs(2, Scalar::from(2)); //g1和2*g1
        let poly = Polynomial::new(vec![Scalar::from(2), Scalar::from(3)], Basis::Monomial);
        let commitment = setup.commit(poly);
        let g1 = G1Projective::generator();
        //2 * g1 + 3 *  2*g1
        assert_eq!(
            commitment,
            Scalar::from(2) * g1 + Scalar::from(3) * Scalar::from(2) * g1
        );
    }
}
