use crate::polynomial::{Basis, Polynomial};
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
        let mut cur_powers = G1Projective::generator();
        let mut setup = Setup {
            powers_of_x: Vec::with_capacity(powers), // 提前分配空间
            x_2: G2Projective::generator() * tau,    // 直接计算
        };

        setup.powers_of_x.push(cur_powers); // 添加 G1 的生成元
        for _ in 1..powers {
            cur_powers *= tau; // 累乘 tau
            setup.powers_of_x.push(cur_powers);
        }

        // println!("Finish generating SRS.");
        setup
    }
    pub fn commit(&self, polynomial: &Polynomial) -> G1Projective {
        //默认是系数(monomial)形式
        assert_eq!(polynomial.basis, Basis::Monomial);
        let values = polynomial.values.clone();

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
    use super::*;
    use crate::utils::i_ntt_381;
    use bls12_381::{pairing, G2Affine};

    #[test]
    fn test_generate_srs() {
        //passed
        let tau = Scalar::from(2);
        let setup = Setup::generate_srs(8, tau);
        for i in 0..8 {
            assert_eq!(
                setup.powers_of_x[i],
                G1Projective::generator() * tau.pow(&[i as u64, 0, 0, 0])
            );
        }
        // assert_eq!(setup.powers_of_x[0] * tau, setup.powers_of_x[1]);
    }

    #[test]
    fn test_monomial_commit() {
        //passed
        let setup = Setup::generate_srs(2, Scalar::from(10)); //g1和2*g1
        let poly = Polynomial::new(vec![Scalar::from(2), Scalar::from(3)], Basis::Monomial);
        let commitment = setup.commit(&poly);
        let g1 = G1Projective::generator();
        //2 * g1 + 3 *  2*g1
        //tau^0 * 2 * g1 + tau^1 * 3 * g1
        assert_eq!(
            commitment,
            Scalar::from(2) * g1 + Scalar::from(10) * Scalar::from(3) * g1
        );
        //second test

        let tau = Scalar::from(2);
        let setup = Setup::generate_srs(8, tau);

        let poly1 = Polynomial::new(vec![Scalar::zero(), Scalar::one()], Basis::Monomial);
        let poly2 = Polynomial::new(vec![Scalar::zero(), Scalar::one()], Basis::Monomial);

        let poly3 = Polynomial::new(
            vec![Scalar::zero(), Scalar::zero(), Scalar::one()],
            Basis::Monomial,
        );
        let poly1_1 = setup.commit(&poly1);

        let poly3_1 = setup.commit(&poly3);

        // x * G2 = x*G2 = tau*g2
        //x * x = x^2

        assert_eq!(poly1_1, G1Projective::generator() * tau);

        //(3x^2 + 2x + 1)(x-1) = 3x^3 - x^2 - x - 1
        let poly1 = Polynomial::new(
            vec![Scalar::one(), Scalar::from(2), Scalar::from(3)],
            Basis::Monomial,
        );
        let poly2 = Polynomial::new(vec![Scalar::one().neg(), Scalar::one()], Basis::Monomial);
        let poly3 = Polynomial::new(
            vec![
                Scalar::one().neg(),
                Scalar::one().neg(),
                Scalar::one().neg(),
                Scalar::from(3),
            ],
            Basis::Monomial,
        );
        //(x-1)G2 = (tau-1)G2 = tauG2 - G2
        assert_eq!(
            pairing(
                &setup.commit(&poly1).into(),
                &(setup.x_2 - G2Projective::generator()).into()
            ),
            pairing(&setup.commit(&poly3).into(), &G2Affine::generator())
        );
    }
    // #[test]
    // fn test_lagrange_commit() {
    //     //passed
    //     let setup = Setup::generate_srs(2, Scalar::from(2)); //g1和2*g1
    //     let poly = Polynomial::new(vec![Scalar::from(3), Scalar::from(3)], Basis::Lagrange);
    //     let commitment = setup.commit(&poly);
    //     let g1 = G1Projective::generator();
    //     //6 * g1 + 0 *  2*g1
    //     assert_eq!(commitment, Scalar::from(6) * g1);
    // }
    #[test]
    fn test_ntt() {
        //passed
        use crate::utils::ntt_381;
        let test_vec = vec![Scalar::from(3), Scalar::from(3)];
        let mid = ntt_381(&test_vec);
        println!("res:{:?}", mid);
        println!("res mid :{:?}", i_ntt_381(&mid));
    }
}
