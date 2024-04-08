use crate::{
    polynomial::{Basis, Polynomial},
    utils::ntt_381,
};
use bls12_381::{G1Projective, G2Projective, Scalar};
#[derive(Debug, Clone)]
pub struct Setup {
    pub powers_of_x: Vec<G1Projective>,
    pub x_2: G2Projective,
}
impl Setup {
    pub fn generate_srs(powers: usize, tau: Scalar) -> Setup {
        //生成g1,tau*g1,tau^2 * g1...,tau^(powers-1) * g1
        //tau*g2

        // println!("Start to generate SRS...");
        let mut setup = Setup {
            powers_of_x: Vec::new(),
            x_2: G2Projective::generator(),
        };
        let cur_powers = G1Projective::generator();

        setup.powers_of_x.push(cur_powers);
        for _ in 1..powers {
            let cur_powers = cur_powers * tau;
            setup.powers_of_x.push(cur_powers);
        }

        setup.x_2 = G2Projective::generator() * tau;
        // println!("Finish generating SRS.");
        setup
    }
    pub fn commit(&self, polynomial: &Polynomial) -> G1Projective {
        //默认是系数(monomial)形式

        let values;
        if polynomial.basis == Basis::Lagrange {
            values = ntt_381(&polynomial.values);
        } else {
            //系数表示
            values = polynomial.values.clone();
        }
        // assert_eq!(values.len(), self.powers_of_x.len());
        let mut commitment = G1Projective::identity();
        //commitment = a1 * g1 + a2 * tau * g1  + ...

        for (i, scalar) in values.iter().enumerate() {
            let point = self.powers_of_x[i];
            commitment += scalar * point;
        }

        commitment
    }
}
#[cfg(test)]
mod tests {
    use crate::{polynomial, utils::i_ntt_381};

    use super::*;

    #[test]
    fn test_generate_srs() {
        //passed
        let setup = Setup::generate_srs(2, Scalar::from(1));
        assert_eq!(setup.powers_of_x[0], setup.powers_of_x[1]);
    }

    #[test]
    fn test_monomial_commit() {
        //passed
        let setup = Setup::generate_srs(2, Scalar::from(2)); //g1和2*g1
        let poly = Polynomial::new(vec![Scalar::from(2), Scalar::from(3)], Basis::Monomial);
        let commitment = setup.commit(&poly);
        let g1 = G1Projective::generator();
        //2 * g1 + 3 *  2*g1
        assert_eq!(
            commitment,
            Scalar::from(2) * g1 + Scalar::from(3) * Scalar::from(2) * g1
        );
    }
    #[test]
    fn test_lagrange_commit() {
        //passed
        let setup = Setup::generate_srs(2, Scalar::from(2)); //g1和2*g1
        let poly = Polynomial::new(vec![Scalar::from(3), Scalar::from(3)], Basis::Lagrange);
        let commitment = setup.commit(&poly);
        let g1 = G1Projective::generator();
        //6 * g1 + 0 *  2*g1
        assert_eq!(commitment, Scalar::from(6) * g1);
    }
    #[test]
    fn test_ntt() {
        //passed
        let test_vec = vec![Scalar::from(3), Scalar::from(3)];
        let mid = ntt_381(&test_vec);
        println!("res:{:?}", mid);
        println!("res mid :{:?}", i_ntt_381(&mid));
    }
}
