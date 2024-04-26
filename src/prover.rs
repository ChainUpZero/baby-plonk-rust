use crate::polynomial::{Basis, Polynomial};
use crate::program::{CommonPreprocessedInput, Program};
use crate::setup::{self, Setup};

use crate::transcript::PlonkTranscript;
use crate::utils::{i_ntt_381, ntt_381, root_of_unity, roots_of_unity, Rlc};
use crate::verifier::Proof;
use bls12_381::{pairing, G1Affine, G2Affine, G2Projective};
use bls12_381::{G1Projective, Scalar};
use ff::Field;
use merlin::Transcript;
use std::collections::HashMap;

pub struct RandomNums {
    pub alpha: Option<Scalar>,
    pub beta: Option<Scalar>,
    pub gamma: Option<Scalar>,
    pub zeta: Option<Scalar>,
    pub nu: Option<Scalar>,
    pub mu: Option<Scalar>,
}
struct WitnessPolys {
    a: Option<Polynomial>,
    b: Option<Polynomial>,
    c: Option<Polynomial>,
    z: Option<Polynomial>,
    zw: Option<Polynomial>,

    w_zeta: Option<Polynomial>,
    w_zeta_omega: Option<Polynomial>,

    a_coeff: Option<Polynomial>,
    b_coeff: Option<Polynomial>,
    c_coeff: Option<Polynomial>,
    z_coeff: Option<Polynomial>,
    z_omega_coeff: Option<Polynomial>,
    t_lo_coeff: Option<Polynomial>,
    t_mid_coeff: Option<Polynomial>,
    t_hi_coeff: Option<Polynomial>,
    z_h_coeff: Option<Polynomial>,
}
struct Evaluations {
    a_bar: Scalar,
    b_bar: Scalar,
    c_bar: Scalar,
    s1_bar: Scalar,
    s2_bar: Scalar,
    z_omega_bar: Scalar,
}

pub struct Prover {
    group_order: u64,
    program: Program,
    setup: Setup,
    pk: CommonPreprocessedInput,
    random_nums: RandomNums,
    witness_polys: WitnessPolys,
    evals: Option<Evaluations>,
    k1: Scalar,
    k2: Scalar,
    blinding_coeffs: Option<[Scalar; 11]>,
    public_input_poly: Option<Polynomial>,
}
impl Prover {
    pub fn new(setup: Setup, program: Program) -> Prover {
        Prover {
            group_order: program.group_order,
            setup,
            pk: program.common_preprocessed_input(),
            program,
            random_nums: RandomNums {
                alpha: None,
                beta: None,
                gamma: None,
                zeta: None,
                nu: None,
                mu: None,
            },

            witness_polys: WitnessPolys {
                a: None,
                b: None,
                c: None,
                z: None,
                zw: None,
                t_lo_coeff: None,
                t_mid_coeff: None,
                t_hi_coeff: None,
                w_zeta: None,
                w_zeta_omega: None,

                a_coeff: None,
                b_coeff: None,
                c_coeff: None,
                z_coeff: None,
                z_omega_coeff: None,
                z_h_coeff: None,
            },
            evals: None,
            k1: Scalar::from(2),
            k2: Scalar::from(3),
            blinding_coeffs: None,
            public_input_poly: None,
        }
    }

    pub fn prove(&mut self, witness: HashMap<String, Scalar>) -> Proof {
        println!("Prove started...");
        let mut rng = rand::thread_rng();

        self.blinding_coeffs = Some([Scalar::from(0); 11].map(|_| Scalar::random(&mut rng)));

        let mut transcript = Transcript::new(b"plonk");

        let public_vars: Vec<_> = self
            .program
            .get_public_assignment()
            .iter()
            .map(|x| x.clone().unwrap())
            .collect();
        let mut values: Vec<_> = public_vars
            .iter()
            .map(|x| witness.get(x).unwrap().neg())
            .collect();
        for _ in 0..self.group_order as usize - public_vars.len() {
            values.push(Scalar::zero());
        }
        self.public_input_poly = Some(Polynomial::new(values, Basis::Lagrange));

        //round1
        let (a_1, b_1, c_1) = self.round_1(witness);
        let (beta, gamma) = transcript.round_1(a_1, b_1, c_1);

        self.random_nums.beta = Some(beta);
        self.random_nums.gamma = Some(gamma);

        //round2
        let z_1 = self.round_2();
        let alpha = transcript.round_2(z_1);
        self.random_nums.alpha = Some(alpha);

        //round3
        let (t_lo_1, t_mid_1, t_hi_1) = self.round_3();
        let zeta = transcript.round_3(t_lo_1, t_mid_1, t_hi_1);
        self.random_nums.zeta = Some(zeta);

        //round4
        let (a_bar, b_bar, c_bar, s1_bar, s2_bar, z_omega_bar) = self.round_4();
        let nu = transcript.round_4(a_bar, b_bar, c_bar, s1_bar, s2_bar, z_omega_bar);
        self.random_nums.nu = Some(nu);

        //round5
        // let (w_zeta_1, w_zeta_omega_1) = self.round_5();
        let round5_test_return = self.round_5();
        let w_zeta_1 = round5_test_return.w_zeta_1;
        let w_zeta_omega_1 = round5_test_return.w_zeta_omega_1;

        let mu = transcript.round_5(w_zeta_1, w_zeta_omega_1);
        self.random_nums.mu = Some(mu);

        println!("Prove finished");
        //以下测试
        let mu = Scalar::from(3);

        let ql_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.ql.values),
            Basis::Monomial,
        ));
        let qr_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.qr.values),
            Basis::Monomial,
        ));
        let qo_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.qo.values),
            Basis::Monomial,
        ));
        let qc_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.qc.values),
            Basis::Monomial,
        ));
        let qm_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.qm.values),
            Basis::Monomial,
        ));
        let s1_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.s1.values),
            Basis::Monomial,
        ));
        let s2_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.s2.values),
            Basis::Monomial,
        ));
        let s3_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.s3.values),
            Basis::Monomial,
        ));
        let omega = root_of_unity(self.group_order);
        let mut l1_values = vec![Scalar::one()];
        for _ in 0..self.group_order - 1 {
            l1_values.push(Scalar::zero());
        }
        let l1_coeff = Polynomial::new(l1_values, Basis::Lagrange).i_ntt();
        let l_1_zeta = l1_coeff.coeffs_evaluate(zeta);
        let z_h_zeta = zeta.pow(&[self.group_order, 0, 0, 0]) - Scalar::one();

        let d_1_1 = a_bar * b_bar * qm_1 + a_bar * ql_1 + b_bar * qr_1 + c_bar * qo_1 + qc_1;
        let d_1_2 = (a_bar.rlc(&zeta, beta, gamma)
            * b_bar.rlc(&(self.k1 * zeta), beta, gamma)
            * c_bar.rlc(&(self.k2 * zeta), beta, gamma)
            * alpha
            + l_1_zeta * alpha * alpha
            + mu)
            * z_1;
        let d_1_3 = a_bar.rlc(&s1_bar, beta, gamma)
            * b_bar.rlc(&s2_bar, beta, gamma)
            * alpha
            * beta
            * z_omega_bar
            * s3_1;
        let d_1_4 = z_h_zeta
            * (t_lo_1
                + zeta.pow(&[self.group_order, 0, 0, 0]) * t_mid_1
                + zeta.pow(&[2 * self.group_order, 0, 0, 0]) * t_hi_1);

        let d_1 = d_1_1 + d_1_2 - d_1_3 - d_1_4;

        let f_1 = d_1
            + nu * a_1
            + nu.pow(&[2, 0, 0, 0]) * b_1
            + nu.pow(&[3, 0, 0, 0]) * c_1
            + nu.pow(&[4, 0, 0, 0]) * s1_1
            + nu.pow(&[5, 0, 0, 0]) * s2_1;

        let public_input_poly = self.public_input_poly.clone().unwrap();
        let public_input_eval = public_input_poly.i_ntt().coeffs_evaluate(zeta);

        let r_0 = public_input_eval
            - l_1_zeta * alpha * alpha
            - alpha
                * (a_bar.rlc(&s1_bar, beta, gamma))
                * (b_bar.rlc(&s2_bar, beta, gamma))
                * (c_bar + gamma)
                * z_omega_bar;

        let e_1 = (nu * a_bar
            + nu.pow(&[2, 0, 0, 0]) * b_bar
            + nu.pow(&[3, 0, 0, 0]) * c_bar
            + nu.pow(&[4, 0, 0, 0]) * s1_bar
            + nu.pow(&[5, 0, 0, 0]) * s2_bar
            + mu * z_omega_bar
            - r_0)
            * G1Projective::generator();

        println!("unsure e_1:{:?}:", G1Affine::from(e_1));
        println!("unsure r_0:{:?}", r_0);

        println!("unsure mu:{:?}", mu);
        println!("round5_test_return.mu:{:?}", round5_test_return.mu);

        assert_eq!(self.k1, round5_test_return.k1);
        assert_eq!(self.k2, round5_test_return.k2);

        assert_eq!(l_1_zeta, round5_test_return.l_1_zeta);
        assert_eq!(z_1, round5_test_return.z_1);

        assert_eq!(round5_test_return.d_1_1, d_1_1);

        assert_eq!(round5_test_return.d_1_3, d_1_3);
        assert_eq!(round5_test_return.d_1_4, d_1_4);
        assert_eq!(round5_test_return.d_1_2, d_1_2);

        assert!(
            pairing(
                &(w_zeta_1 + mu * w_zeta_omega_1).into(),
                &self.setup.x_2.into()
            ) == pairing(
                &(zeta * w_zeta_1 + mu * zeta * omega * w_zeta_omega_1 + round5_test_return.f_1
                    - e_1)
                    .into(),
                &G2Affine::generator(),
            )
        );

        // assert_eq!(e_1, round5_test_return.e_1);
        // assert_eq!(f_1, round5_test_return.f_1);

        // let f_1 = round5_test_return.f_1;
        // let e_1 = round5_test_return.e_1;

        assert!(
            pairing(
                &(w_zeta_1 + mu * w_zeta_omega_1).into(),
                &self.setup.x_2.into()
            ) == pairing(
                &(zeta * w_zeta_1 + mu * zeta * omega * w_zeta_omega_1 + f_1 - e_1).into(),
                &G2Affine::generator(),
            )
        );
        //以上

        Proof {
            a_1,
            b_1,
            c_1,
            z_1,
            t_lo_1,
            t_mid_1,
            t_hi_1,
            w_zeta_1,
            w_zeta_omega_1,
            a_bar,
            b_bar,
            c_bar,
            s1_bar,
            s2_bar,
            z_omega_bar,
        }
    }
    pub fn round_1(
        &mut self,
        witness: HashMap<String, Scalar>,
    ) -> (G1Projective, G1Projective, G1Projective) {
        //计算a(x),b(x),c(x)
        //example
        //witness = {"a": 1,"b":3}

        let mut a_values = vec![Scalar::from(0); self.group_order as usize];
        let mut b_values = vec![Scalar::from(0); self.group_order as usize];
        let mut c_values = vec![Scalar::from(0); self.group_order as usize];
        //a_values对应L
        //b_values对应R
        //c_values对应O
        println!("self.program.constraints:{:?}", self.program.constraints);
        for (i, constraint) in self.program.constraints.iter().enumerate() {
            //constraint.wires = {L:Some('a'),R,Some('b'),O:Some('c')}
            //处理A的第i个约束

            //constraint.wires.L是该门的L的变量名。R和O同理
            let l = constraint.wires.L.clone();
            a_values[i] = match l {
                Some(v) => *witness.get(&v).unwrap(),
                None => Scalar::zero(),
            };

            let r = constraint.wires.R.clone();
            b_values[i] = match r {
                Some(v) => *witness.get(&v).unwrap(),
                None => Scalar::zero(),
            };

            let o = constraint.wires.O.clone();
            c_values[i] = match o {
                Some(v) => *witness.get(&v).unwrap(),
                None => Scalar::zero(),
            };

            // a_values[i] = *witness.get(constraint.wires.L.as_ref().unwrap()).unwrap();
            // b_values[i] = *witness.get(constraint.wires.R.as_ref().unwrap()).unwrap();
            // c_values[i] = *witness.get(constraint.wires.O.as_ref().unwrap()).unwrap();
        }

        let mut z_h_values = vec![Scalar::one().neg()];
        for _ in 0..self.group_order - 1 {
            z_h_values.push(Scalar::zero());
        }
        z_h_values.push(Scalar::one());

        let z_h_coeff = Polynomial::new(z_h_values, Basis::Monomial);

        let [b1, b2, b3, b4, b5, b6] = [
            self.blinding_coeffs.unwrap()[0],
            self.blinding_coeffs.unwrap()[1],
            self.blinding_coeffs.unwrap()[2],
            self.blinding_coeffs.unwrap()[3],
            self.blinding_coeffs.unwrap()[4],
            self.blinding_coeffs.unwrap()[5],
        ];

        let a = Polynomial::new(a_values, Basis::Lagrange);
        let b = Polynomial::new(b_values, Basis::Lagrange);
        let c = Polynomial::new(c_values, Basis::Lagrange);

        let a_blinding = Polynomial::new(vec![b2, b1], Basis::Monomial);
        let b_blinding = Polynomial::new(vec![b4, b3], Basis::Monomial);
        let c_blinding = Polynomial::new(vec![b6, b5], Basis::Monomial);

        let a_coeff = a_blinding.clone() * z_h_coeff.clone() + a.clone().i_ntt();
        let b_coeff = b_blinding.clone() * z_h_coeff.clone() + b.clone().i_ntt();
        let c_coeff = c_blinding.clone() * z_h_coeff.clone() + c.clone().i_ntt();

        let a_1 = self.setup.commit(&a_coeff);
        let b_1 = self.setup.commit(&b_coeff);
        let c_1 = self.setup.commit(&c_coeff);

        let omega = root_of_unity(self.group_order);

        for i in 0..self.group_order - 1 {
            assert_eq!(
                (a.i_ntt() * self.pk.ql.i_ntt()
                    + b.i_ntt() * self.pk.qr.i_ntt()
                    + a.i_ntt() * b.i_ntt() * self.pk.qm.i_ntt()
                    + c.i_ntt() * self.pk.qo.i_ntt()
                    + self.public_input_poly.clone().unwrap().i_ntt()
                    + self.pk.qc.i_ntt())
                .coeffs_evaluate(omega.pow(&[i, 0, 0, 0])),
                Scalar::zero()
            );
        }

        self.witness_polys.a = Some(a);
        self.witness_polys.b = Some(b);
        self.witness_polys.c = Some(c);
        self.witness_polys.a_coeff = Some(a_coeff);
        self.witness_polys.b_coeff = Some(b_coeff);
        self.witness_polys.c_coeff = Some(c_coeff);
        self.witness_polys.z_h_coeff = Some(z_h_coeff);

        (a_1, b_1, c_1)
    }

    pub fn round_2(&mut self) -> G1Projective {
        //计算z(x)
        let mut z_values = vec![Scalar::one()];
        let roots_of_unity = roots_of_unity(self.program.group_order);
        let beta = self.random_nums.beta.unwrap();
        let gamma = self.random_nums.gamma.unwrap();

        for i in 0..self.program.group_order as usize {
            z_values.push(
                z_values[z_values.len() - 1]
                    * self.witness_polys.a.as_ref().unwrap().values[i].rlc(
                        &roots_of_unity[i],
                        beta,
                        gamma,
                    )
                    * self.witness_polys.b.as_ref().unwrap().values[i].rlc(
                        &(roots_of_unity[i] * &self.k1),
                        beta,
                        gamma,
                    )
                    * self.witness_polys.c.as_ref().unwrap().values[i].rlc(
                        &(roots_of_unity[i] * &self.k2),
                        beta,
                        gamma,
                    )
                    * self.witness_polys.a.as_ref().unwrap().values[i]
                        .rlc(&self.pk.s1.values[i], beta, gamma)
                        .invert()
                        .unwrap()
                    * self.witness_polys.b.as_ref().unwrap().values[i]
                        .rlc(&self.pk.s2.values[i], beta, gamma)
                        .invert()
                        .unwrap()
                    * self.witness_polys.c.as_ref().unwrap().values[i]
                        .rlc(&self.pk.s3.values[i], beta, gamma)
                        .invert()
                        .unwrap(),
            );
        }

        assert_eq!(z_values.pop().unwrap(), Scalar::from(1));
        for i in 0..self.group_order as usize {
            assert_eq!(
                self.witness_polys.a.as_ref().unwrap().values[i].rlc(
                    &roots_of_unity[i],
                    beta,
                    gamma
                ) * self.witness_polys.b.as_ref().unwrap().values[i].rlc(
                    &(self.k1 * roots_of_unity[i]),
                    beta,
                    gamma
                ) * self.witness_polys.c.as_ref().unwrap().values[i].rlc(
                    &(self.k2 * roots_of_unity[i]),
                    beta,
                    gamma
                ) * z_values[i],
                self.witness_polys.a.as_ref().unwrap().values[i].rlc(
                    &self.pk.s1.values[i],
                    beta,
                    gamma
                ) * self.witness_polys.b.as_ref().unwrap().values[i].rlc(
                    &self.pk.s2.values[i],
                    beta,
                    gamma
                ) * self.witness_polys.c.as_ref().unwrap().values[i].rlc(
                    &self.pk.s3.values[i],
                    beta,
                    gamma
                ) * z_values[(i + 1) % self.group_order as usize]
            )
        }

        let z = Polynomial::new(z_values, Basis::Lagrange);

        let [b7, b8, b9] = [
            self.blinding_coeffs.unwrap()[6],
            self.blinding_coeffs.unwrap()[7],
            self.blinding_coeffs.unwrap()[8],
        ];

        let z_blinding = Polynomial::new(vec![b9, b8, b7], Basis::Monomial);
        let z_h_coeff = self.witness_polys.z_h_coeff.clone().unwrap();

        let z_coeff = z_blinding * z_h_coeff + z.i_ntt();

        let z_1 = self.setup.commit(&z_coeff.clone());
        self.witness_polys.z = Some(z);
        self.witness_polys.z_coeff = Some(z_coeff);
        z_1
    }

    pub fn round_3(&mut self) -> (G1Projective, G1Projective, G1Projective) {
        //compute t(x)  i.e t_lo(x),t_mid(x),t_hi(x)
        let roots_of_unity = roots_of_unity(self.group_order);

        let polys = vec![
            self.pk.s1.clone().values,
            self.pk.s2.clone().values,
            self.pk.s3.clone().values,
            self.pk.ql.clone().values,
            self.pk.qr.clone().values,
            self.pk.qm.clone().values,
            self.pk.qo.clone().values,
            self.pk.qc.clone().values,
        ];
        let coeff_polys: Vec<_> = polys
            .iter()
            .map(|values| Polynomial::new(i_ntt_381(values), Basis::Monomial))
            .collect();
        let (s1_coeff, s2_coeff, s3_coeff, ql_coeff, qr_coeff, qm_coeff, qo_coeff, qc_coeff) = (
            coeff_polys[0].clone(),
            coeff_polys[1].clone(),
            coeff_polys[2].clone(),
            coeff_polys[3].clone(),
            coeff_polys[4].clone(),
            coeff_polys[5].clone(),
            coeff_polys[6].clone(),
            coeff_polys[7].clone(),
        );
        let a_coeff = self.witness_polys.a_coeff.clone().unwrap();
        let b_coeff = self.witness_polys.b_coeff.clone().unwrap();
        let c_coeff = self.witness_polys.c_coeff.clone().unwrap();
        let z_coeff = self.witness_polys.z_coeff.clone().unwrap();

        let mut l1_values = vec![Scalar::one()];
        for _ in 0..self.group_order - 1 {
            l1_values.push(Scalar::zero());
        }
        let l1 = Polynomial::new(l1_values, Basis::Lagrange);

        let mut z_h_values = vec![Scalar::one().neg()];
        for _ in 0..self.group_order - 1 {
            z_h_values.push(Scalar::zero());
        }
        z_h_values.push(Scalar::one());

        let z_h_coeff = Polynomial::new(z_h_values, Basis::Monomial);

        let gate_constraints_coeff = a_coeff.clone() * ql_coeff.clone()
            + b_coeff.clone() * qr_coeff.clone()
            + a_coeff.clone() * b_coeff.clone() * qm_coeff.clone()
            + c_coeff.clone() * qo_coeff.clone()
            + self.public_input_poly.clone().unwrap().i_ntt()
            + qc_coeff.clone();

        let roots_poly_coeff = Polynomial::new(i_ntt_381(&roots_of_unity.clone()), Basis::Monomial);

        let omega = root_of_unity(self.group_order);
        let z_omega_coeff = self.monomial_z_to_z_omega(z_coeff.clone(), omega);

        //以下是测试

        // for i in 0..self.group_order as usize {
        //     assert_eq!(
        //         self.witness_polys.a.as_ref().unwrap().values[i].rlc(
        //             &roots_of_unity[i],
        //             beta,
        //             gamma
        //         ) * self.witness_polys.b.as_ref().unwrap().values[i].rlc(
        //             &(self.k1 * roots_of_unity[i]),
        //             beta,
        //             gamma
        //         ) * self.witness_polys.c.as_ref().unwrap().values[i].rlc(
        //             &(self.k2 * roots_of_unity[i]),
        //             beta,
        //             gamma
        //         ) * self.witness_polys.z.clone().unwrap().values[i],
        //         self.witness_polys.a.as_ref().unwrap().values[i].rlc(
        //             &self.pk.s1.values[i],
        //             beta,
        //             gamma
        //         ) * self.witness_polys.b.as_ref().unwrap().values[i].rlc(
        //             &self.pk.s2.values[i],
        //             beta,
        //             gamma
        //         ) * self.witness_polys.c.as_ref().unwrap().values[i].rlc(
        //             &self.pk.s3.values[i],
        //             beta,
        //             gamma
        //         ) * z_omega.values[i % self.group_order as usize]
        //     )
        // }

        let omega = root_of_unity(self.group_order);
        let beta = self.random_nums.beta.unwrap();
        let gamma = self.random_nums.gamma.unwrap();

        assert!(beta != Scalar::zero());
        assert!(gamma != Scalar::zero());

        let r2_x = (a_coeff.clone().coeffs_evaluate(omega) + beta * omega + gamma)
            * (b_coeff.clone().coeffs_evaluate(omega) + beta * self.k1 * omega + gamma)
            * (c_coeff.clone().coeffs_evaluate(omega) + beta * self.k2 * omega + gamma)
            * z_coeff.clone().coeffs_evaluate(omega)
            - (a_coeff.clone().coeffs_evaluate(omega)
                + s1_coeff.clone().coeffs_evaluate(omega) * beta
                + gamma)
                * (b_coeff.clone().coeffs_evaluate(omega)
                    + s2_coeff.clone().coeffs_evaluate(omega) * beta
                    + gamma)
                * (c_coeff.clone().coeffs_evaluate(omega)
                    + self.pk.s3.i_ntt().coeffs_evaluate(omega) * beta
                    + gamma)
                * z_omega_coeff.clone().coeffs_evaluate(omega);
        assert!(r2_x == Scalar::zero());

        //以上

        let permutation_grand_product_coeff = (a_coeff.rlc(&roots_poly_coeff, beta, gamma)
            * b_coeff.rlc(&(roots_poly_coeff.clone() * self.k1), beta, gamma)
            * c_coeff.rlc(&(roots_poly_coeff.clone() * self.k2), beta, gamma))
            * z_coeff.clone()
            - (a_coeff.rlc(&s1_coeff, beta, gamma)
                * b_coeff.rlc(&s2_coeff, beta, gamma)
                * c_coeff.rlc(&s3_coeff, beta, gamma))
                * z_omega_coeff.clone();
        let l1_coeff = Polynomial::new(i_ntt_381(&l1.values.clone()), Basis::Monomial);

        let permutation_first_row_coeff = (z_coeff.clone() - Scalar::one()) * l1_coeff;

        let alpha = self.random_nums.alpha.unwrap();

        let all_constraints = gate_constraints_coeff
            + permutation_grand_product_coeff * alpha
            + permutation_first_row_coeff * alpha.pow(&[2u64, 0, 0, 0]);

        let t_coeff = all_constraints / z_h_coeff;

        let (t_lo_coeff, t_mid_coeff, t_hi_coeff) = self.split_t_to_3pieces(t_coeff.clone());

        println!("Generated the quotient polynomial!");

        //x^n
        let mut x_pow_n_values = vec![Scalar::zero(); self.group_order as usize + 1];
        x_pow_n_values[self.group_order as usize] = Scalar::from(1);

        //x^2n
        let mut x_pow_2n_values = vec![Scalar::zero(); self.group_order as usize * 2 + 1];
        x_pow_2n_values[self.group_order as usize * 2] = Scalar::from(1);
        assert_eq!(
            t_coeff.clone(),
            t_lo_coeff.clone()
                + Polynomial::new(x_pow_n_values.clone(), Basis::Monomial) * t_mid_coeff.clone()
                + Polynomial::new(x_pow_2n_values, Basis::Monomial) * t_hi_coeff.clone()
        );
        let [b10, b11] = [
            self.blinding_coeffs.unwrap()[9],
            self.blinding_coeffs.unwrap()[10],
        ];

        let t_lo_blinding = Polynomial::new(x_pow_n_values.clone(), Basis::Monomial) * b10;
        let t_mid_blinding = Polynomial::new(x_pow_n_values, Basis::Monomial) * b11 - b10;
        let t_hi_blinding = b11.neg();

        let t_lo_coeff = t_lo_coeff + t_lo_blinding;
        let t_mid_coeff = t_mid_coeff + t_mid_blinding;
        let t_hi_coeff = t_hi_coeff + t_hi_blinding;

        println!("t_lo_coeff.values.len():{:?}", t_lo_coeff.values.len());
        println!("t_mid_coeff.values.len():{:?}", t_mid_coeff.values.len());
        println!("t_hi_coeff.values.len():{:?}", t_hi_coeff.values.len());

        let t_lo_1 = self.setup.commit(&t_lo_coeff);
        let t_mid_1 = self.setup.commit(&t_mid_coeff);
        let t_hi_1 = self.setup.commit(&t_hi_coeff);

        self.pk.s1_coeff = Some(s1_coeff);
        self.pk.s2_coeff = Some(s2_coeff);

        self.witness_polys.a_coeff = Some(a_coeff);
        self.witness_polys.b_coeff = Some(b_coeff);
        self.witness_polys.c_coeff = Some(c_coeff);
        self.witness_polys.z_coeff = Some(z_coeff);
        self.witness_polys.z_omega_coeff = Some(z_omega_coeff);
        self.witness_polys.t_lo_coeff = Some(t_lo_coeff);
        self.witness_polys.t_mid_coeff = Some(t_mid_coeff);
        self.witness_polys.t_hi_coeff = Some(t_hi_coeff);

        (t_lo_1, t_mid_1, t_hi_1)
    }

    pub fn round_4(&mut self) -> (Scalar, Scalar, Scalar, Scalar, Scalar, Scalar) {
        let zeta = self.random_nums.zeta.unwrap();
        let a_bar = self
            .witness_polys
            .a_coeff
            .as_ref()
            .unwrap()
            .coeffs_evaluate(zeta);
        let b_bar = self
            .witness_polys
            .b_coeff
            .as_ref()
            .unwrap()
            .coeffs_evaluate(zeta);
        let c_bar = self
            .witness_polys
            .c_coeff
            .as_ref()
            .unwrap()
            .coeffs_evaluate(zeta);
        let s1_bar = self.pk.s1_coeff.as_ref().unwrap().coeffs_evaluate(zeta);
        let s2_bar = self.pk.s2_coeff.as_ref().unwrap().coeffs_evaluate(zeta);
        let z_omega_bar = self
            .witness_polys
            .z_omega_coeff
            .as_ref()
            .unwrap()
            .coeffs_evaluate(zeta);

        self.evals = Some(Evaluations {
            a_bar,
            b_bar,
            c_bar,
            s1_bar,
            s2_bar,
            z_omega_bar,
        });

        (a_bar, b_bar, c_bar, s1_bar, s2_bar, z_omega_bar)
    }

    pub fn round_5(&mut self) -> Round5TestReturn {
        let nu = self.random_nums.nu.unwrap();

        let a_bar = self.evals.as_ref().unwrap().a_bar;
        let b_bar = self.evals.as_ref().unwrap().b_bar;
        let c_bar = self.evals.as_ref().unwrap().c_bar;
        let s1_bar = self.evals.as_ref().unwrap().s1_bar;
        let s2_bar = self.evals.as_ref().unwrap().s2_bar;
        let z_omega_bar = self.evals.as_ref().unwrap().z_omega_bar;

        let alpha = self.random_nums.alpha.unwrap();
        let beta = self.random_nums.beta.unwrap();
        let gamma = self.random_nums.gamma.unwrap();
        let zeta = self.random_nums.zeta.unwrap();

        let a_coeff = self.witness_polys.a_coeff.clone().unwrap();
        let b_coeff = self.witness_polys.b_coeff.clone().unwrap();
        let c_coeff = self.witness_polys.c_coeff.clone().unwrap();
        let s1_coeff = self.pk.s1_coeff.clone().unwrap();
        let s2_coeff = self.pk.s2_coeff.clone().unwrap();
        let z_coeff = self.witness_polys.z_coeff.clone().unwrap();

        let r1_coeff = self.pk.qm.i_ntt() * a_bar * b_bar
            + self.pk.ql.i_ntt() * a_bar
            + self.pk.qr.i_ntt() * b_bar
            + self.pk.qo.i_ntt() * c_bar
            + self
                .public_input_poly
                .clone()
                .unwrap()
                .i_ntt()
                .coeffs_evaluate(zeta)
            + self.pk.qc.i_ntt();

        let r2_coeff = z_coeff.clone()
            * (a_bar + zeta * beta + gamma)
            * (b_bar + zeta * beta * self.k1 + gamma)
            * (c_bar + zeta * beta * self.k2 + gamma)
            - (self.pk.s3.i_ntt() * beta + c_bar + gamma)
                * (a_bar + s1_bar * beta + gamma)
                * (b_bar + s2_bar * beta + gamma)
                * z_omega_bar;

        let mut l1_values = vec![Scalar::zero(); self.group_order as usize];
        l1_values[0] = Scalar::one();
        let l1_coeff = Polynomial::new(i_ntt_381(&l1_values), Basis::Monomial);

        let r3_coeff = (z_coeff.clone() - Scalar::one()) * l1_coeff.coeffs_evaluate(zeta);

        //x^n-1
        let mut z_h_values = vec![Scalar::one().neg()];
        for _ in 0..self.group_order - 1 {
            z_h_values.push(Scalar::zero());
        }
        z_h_values.push(Scalar::one());
        let z_h_coeff = Polynomial::new(z_h_values, Basis::Monomial);

        let omega = root_of_unity(self.group_order);

        assert_eq!(z_h_coeff.coeffs_evaluate(omega), Scalar::zero());

        let r4_coeff = (self.witness_polys.t_lo_coeff.clone().unwrap()
            + self.witness_polys.t_mid_coeff.clone().unwrap()
                * zeta.pow(&[self.group_order, 0, 0, 0])
            + self.witness_polys.t_hi_coeff.clone().unwrap()
                * zeta.pow(&[2 * self.group_order, 0, 0, 0]))
            * z_h_coeff.coeffs_evaluate(zeta);

        let r_coeff =
            r1_coeff.clone() + r2_coeff.clone() * alpha + r3_coeff.clone() * alpha * alpha
                - r4_coeff.clone();

        assert_eq!(r_coeff.coeffs_evaluate(zeta), Scalar::zero());

        //x - zeta = -zeta + x
        //系数形式
        let mut x_minus_zeta_poly_values = vec![Scalar::zero(); 2];
        x_minus_zeta_poly_values[0] = zeta.neg();
        x_minus_zeta_poly_values[1] = Scalar::one();

        let w_zeta_coeff = (r_coeff
            + (a_coeff.clone() - a_bar) * nu
            + (b_coeff.clone() - b_bar) * nu * nu
            + (c_coeff.clone() - c_bar) * nu.pow(&[3u64, 0, 0, 0])
            + (s1_coeff.clone() - s1_bar) * nu.pow(&[4u64, 0, 0, 0])
            + (s2_coeff.clone() - s2_bar) * nu.pow(&[5u64, 0, 0, 0]))
            / Polynomial::new(x_minus_zeta_poly_values, Basis::Monomial);

        //x - zeta*omega = -zeta*omega + x
        let omega = root_of_unity(self.group_order);
        let mut x_minus_zeta_omega_poly_values = vec![Scalar::zero(); 2];
        x_minus_zeta_omega_poly_values[0] = (zeta * omega).neg();
        x_minus_zeta_omega_poly_values[1] = Scalar::one();

        let w_zeta_omega_coeff = (z_coeff - z_omega_bar)
            / Polynomial::new(x_minus_zeta_omega_poly_values, Basis::Monomial);

        let w_zeta_1 = self.setup.commit(&w_zeta_coeff);
        let w_zeta_omega_1 = self.setup.commit(&w_zeta_omega_coeff);

        self.witness_polys.w_zeta = Some(w_zeta_coeff.clone());
        self.witness_polys.w_zeta_omega = Some(w_zeta_omega_coeff.clone());

        //以下测试

        let mu = Scalar::from(3);
        let x_poly = Polynomial::new(vec![Scalar::zero(), Scalar::one()], Basis::Monomial);
        // let ql_coeff = self.pk.ql.clone().i_ntt();
        // let qr_coeff = self.pk.qr.clone().i_ntt();
        // let qm_coeff = self.pk.qm.clone().i_ntt();
        // let qo_coeff = self.pk.qo.clone().i_ntt();
        // let qc_coeff = self.pk.qc.clone().i_ntt();

        let ql_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.ql.values),
            Basis::Monomial,
        ));
        let qr_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.qr.values),
            Basis::Monomial,
        ));
        let qo_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.qo.values),
            Basis::Monomial,
        ));
        let qc_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.qc.values),
            Basis::Monomial,
        ));
        let qm_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.qm.values),
            Basis::Monomial,
        ));
        let s1_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.s1.values),
            Basis::Monomial,
        ));
        let s2_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.s2.values),
            Basis::Monomial,
        ));
        let s3_1 = self.setup.commit(&Polynomial::new(
            i_ntt_381(&self.pk.s3.values),
            Basis::Monomial,
        ));

        let omega = root_of_unity(self.group_order);

        let z_h_zeta = zeta.pow(&[self.group_order, 0, 0, 0]) - Scalar::one();

        let mut l1_values = vec![Scalar::one()];
        for _ in 0..self.group_order - 1 {
            l1_values.push(Scalar::zero());
        }
        let l1_coeff = Polynomial::new(l1_values, Basis::Lagrange).i_ntt();
        let l_1_zeta = l1_coeff.coeffs_evaluate(zeta);

        // let l_1_zeta = omega * (z_h_zeta) * (n * (zeta - omega)).invert().unwrap(); //

        let z_coeff = self.witness_polys.z_coeff.clone().unwrap();

        let t_lo_coeff = self.witness_polys.t_lo_coeff.clone().unwrap();
        let t_mid_coeff = self.witness_polys.t_mid_coeff.clone().unwrap();
        let t_hi_coeff = self.witness_polys.t_hi_coeff.clone().unwrap();

        let public_input_poly = self.public_input_poly.clone().unwrap();
        let public_input_eval = public_input_poly.i_ntt().coeffs_evaluate(zeta);

        // let d_1 = qm_coeff * a_bar * b_bar
        //     + ql_coeff * a_bar
        //     + qr_coeff * b_bar
        //     + qo_coeff * c_bar
        //     + qc_coeff;

        // let d_2 = z_coeff
        //     * (a_bar.rlc(&zeta, beta, gamma)
        //         * b_bar.rlc(&(Scalar::from(2) * zeta), beta, gamma)
        //         * c_bar.rlc(&(Scalar::from(3) * zeta), beta, gamma)
        //         * alpha
        //         + l_1_zeta * alpha * alpha
        //         + mu);

        // let d_3 = self.pk.s3.i_ntt()
        //     * a_bar.rlc(&s1_bar, beta, gamma)
        //     * b_bar.rlc(&s2_bar, beta, gamma)
        //     * alpha
        //     * beta
        //     * z_omega_bar;

        // let d_4 = (t_lo_coeff
        //     + t_mid_coeff * zeta.pow(&[self.group_order, 0, 0, 0])
        //     + t_hi_coeff * zeta.pow(&[2 * self.group_order, 0, 0, 0]))
        //     * z_h_zeta;

        // let d_coeff = d_1 + d_2 - d_3 - d_4;

        let z_1 = self
            .setup
            .commit(&self.witness_polys.z_coeff.clone().unwrap());
        let t_lo_1 = self.setup.commit(&t_lo_coeff);
        let t_mid_1 = self.setup.commit(&t_mid_coeff);
        let t_hi_1 = self.setup.commit(&t_hi_coeff);

        let d_1_1 = a_bar * b_bar * qm_1 + a_bar * ql_1 + b_bar * qr_1 + c_bar * qo_1 + qc_1;

        let d_1_2 = (a_bar.rlc(&zeta, beta, gamma)
            * b_bar.rlc(&(self.k1 * zeta), beta, gamma)
            * c_bar.rlc(&(self.k2 * zeta), beta, gamma)
            * alpha
            + l_1_zeta * alpha * alpha
            + mu)
            * z_1;
        let d_1_3 = a_bar.rlc(&s1_bar, beta, gamma)
            * b_bar.rlc(&s2_bar, beta, gamma)
            * alpha
            * beta
            * z_omega_bar
            * s3_1;
        let d_1_4 = z_h_zeta
            * (t_lo_1
                + zeta.pow(&[self.group_order, 0, 0, 0]) * t_mid_1
                + zeta.pow(&[2 * self.group_order, 0, 0, 0]) * t_hi_1);

        let d_1 = d_1_1 + d_1_2 - d_1_3 - d_1_4;

        // let f_coeff = d_coeff
        //     + a_coeff * nu
        //     + b_coeff * nu.pow(&[2, 0, 0, 0])
        //     + c_coeff * nu.pow(&[3, 0, 0, 0])
        //     + s1_coeff * nu.pow(&[4, 0, 0, 0])
        //     + s2_coeff * nu.pow(&[5, 0, 0, 0]);

        let a_1 = self
            .setup
            .commit(&self.witness_polys.a_coeff.clone().unwrap());
        let b_1 = self
            .setup
            .commit(&self.witness_polys.b_coeff.clone().unwrap());
        let c_1 = self
            .setup
            .commit(&self.witness_polys.c_coeff.clone().unwrap());

        let f_1 = d_1
            + nu * a_1
            + nu.pow(&[2, 0, 0, 0]) * b_1
            + nu.pow(&[3, 0, 0, 0]) * c_1
            + nu.pow(&[4, 0, 0, 0]) * s1_1
            + nu.pow(&[5, 0, 0, 0]) * s2_1;

        let r_0 = public_input_eval
            - l_1_zeta * alpha * alpha
            - alpha
                * (a_bar.rlc(&s1_bar, beta, gamma))
                * (b_bar.rlc(&s2_bar, beta, gamma))
                * (c_bar + gamma)
                * z_omega_bar;

        // let e = nu * a_bar
        //     + nu.pow(&[2, 0, 0, 0]) * b_bar
        //     + nu.pow(&[3, 0, 0, 0]) * c_bar
        //     + nu.pow(&[4, 0, 0, 0]) * s1_bar
        //     + nu.pow(&[5, 0, 0, 0]) * s2_bar
        //     + mu * z_omega_bar
        //     - r_0;

        // assert_eq!(
        //     (w_zeta_coeff.clone() + w_zeta_omega_coeff.clone() * mu) * x_poly.clone(),
        //     w_zeta_coeff.clone() * zeta
        //         + w_zeta_omega_coeff.clone() * mu * zeta * omega
        //         + f_coeff.clone()
        //         - e
        // );
        // assert_eq!(
        //     pairing(
        //         &((w_zeta_coeff.coeffs_evaluate(zeta)
        //             + w_zeta_omega_coeff.coeffs_evaluate(zeta) * mu)
        //             * G1Projective::generator())
        //         .into(),
        //         &(x_poly.coeffs_evaluate(zeta) * G2Projective::generator()).into()
        //     ),
        //     pairing(
        //         &((w_zeta_coeff.coeffs_evaluate(zeta) * zeta
        //             + w_zeta_omega_coeff.coeffs_evaluate(zeta) * mu * zeta * omega
        //             + f_coeff.coeffs_evaluate(zeta)
        //             - e)
        //             * G1Projective::generator())
        //         .into(),
        //         &G2Affine::generator()
        //     )
        // );

        //x * G2 => tau*G2

        // assert_eq!(
        //     pairing(
        //         &self
        //             .setup
        //             .commit(&(w_zeta_coeff.clone() + w_zeta_omega_coeff.clone() * mu))
        //             .into(),
        //         &(tau * G2Projective::generator()).into()
        //     ),
        //     pairing(
        //         &self
        //             .setup
        //             .commit(
        //                 &(w_zeta_coeff.clone() * zeta
        //                     + w_zeta_omega_coeff.clone() * mu * zeta * omega
        //                     + f_coeff.clone()
        //                     - e)
        //             )
        //             .into(),
        //         &G2Affine::generator()
        //     )
        // );

        let e_1 = (nu * a_bar
            + nu.pow(&[2, 0, 0, 0]) * b_bar
            + nu.pow(&[3, 0, 0, 0]) * c_bar
            + nu.pow(&[4, 0, 0, 0]) * s1_bar
            + nu.pow(&[5, 0, 0, 0]) * s2_bar
            + mu * z_omega_bar
            - r_0)
            * G1Projective::generator();

        println!("correct e_1:{:?}", G1Affine::from(e_1));
        println!("correct r_0:{:?}", r_0);

        assert_eq!(
            pairing(
                &(w_zeta_1 + w_zeta_omega_1 * mu) //没错
                    .into(),
                &(self.setup.x_2).into()
            ),
            pairing(
                &(w_zeta_1 * zeta + mu * zeta * omega * w_zeta_omega_1 + f_1 - e_1).into(),
                &G2Affine::generator()
            )
        );

        //以上

        // (w_zeta_1, w_zeta_omega_1)

        Round5TestReturn {
            x_2: self.setup.x_2,
            mu,
            zeta,
            omega,
            w_zeta_1,
            w_zeta_omega_1,
            f_1,
            e_1,
            d_1_1,
            d_1_2,
            d_1_3,
            d_1_4,
            k1: self.k1,
            k2: self.k2,
            z_1,
            l_1_zeta,
        }
    }

    fn split_t_to_3pieces(&self, t: Polynomial) -> (Polynomial, Polynomial, Polynomial) {
        let n = self.group_order as usize;
        let t_low_values = (&t.values[0..n]).to_vec();
        let t_mid_values = (&t.values[n..2 * n]).to_vec();
        let t_hi_values = (&t.values[2 * n..]).to_vec();
        (
            Polynomial::new(t_low_values, Basis::Monomial),
            Polynomial::new(t_mid_values, Basis::Monomial),
            Polynomial::new(t_hi_values, Basis::Monomial),
        )
    }

    fn monomial_z_to_z_omega(&self, z: Polynomial, omega: Scalar) -> Polynomial {
        let mut new_values = Vec::with_capacity(z.values.len());
        let mut omega_power = Scalar::one(); // omega^0

        for (_, &coeff) in z.values.iter().enumerate() {
            new_values.push(coeff * omega_power);
            omega_power *= omega; // 更新 omega_power 为 omega^(i+1)
        }

        Polynomial {
            values: new_values,
            basis: Basis::Monomial,
        }
    }
}
struct Round5TestReturn {
    w_zeta_1: G1Projective,
    w_zeta_omega_1: G1Projective,
    f_1: G1Projective,
    e_1: G1Projective,
    mu: Scalar,
    omega: Scalar,
    zeta: Scalar,
    x_2: G2Projective,
    d_1_1: G1Projective,
    d_1_2: G1Projective,
    d_1_3: G1Projective,
    d_1_4: G1Projective,
    k1: Scalar,
    k2: Scalar,
    z_1: G1Projective,
    l_1_zeta: Scalar,
}

#[cfg(test)]
mod tests {

    use crate::assembly::AssemblyEqn;

    use super::*;
    fn initilization() -> (Prover, HashMap<String, Scalar>) {
        let setup = Setup::generate_srs(8 + 6, Scalar::from(1));
        let constraints: Vec<_> = vec!["e public"]
            .into_iter()
            .map(AssemblyEqn::eq_to_assembly)
            .collect();
        let program = Program::new(constraints, 8);
        let mut prover = Prover::new(setup, program);

        let mut witness: HashMap<String, Scalar> = HashMap::new();
        witness.insert("e".to_owned(), Scalar::from(3));
        let public_vars: Vec<_> = prover
            .program
            .get_public_assignment()
            .iter()
            .map(|x| x.clone().unwrap())
            .collect();
        let mut values: Vec<_> = public_vars
            .iter()
            .map(|x| witness.get(x).unwrap().neg())
            .collect();
        for _ in 0..prover.group_order as usize - public_vars.len() {
            values.push(Scalar::zero());
        }
        prover.public_input_poly = Some(Polynomial::new(values, Basis::Lagrange));

        let mut rng = rand::thread_rng();

        prover.blinding_coeffs = Some([Scalar::from(0); 11].map(|_| Scalar::random(&mut rng)));

        (prover, witness)
    }

    #[test]
    fn test_prove() {
        let setup = Setup::generate_srs(8 + 6, Scalar::from(2));

        //程序为：
        //c <== a * b
        //b <== a + d
        let constraints: Vec<_> = vec!["e public", "c <== a * b + b", "e <== c * d"]
            .into_iter()
            .map(AssemblyEqn::eq_to_assembly)
            .collect();

        //ql * a(x) + qr*b(x) + qm*a(x)*b(x) + qo*c(x) + qc=0
        // assert_eq!(constraints[0].wires.L, Some("a".to_string()));
        // assert_eq!(constraints[0].wires.R, Some("b".to_string()));
        // assert_eq!(constraints[0].wires.O, Some("c".to_string()));
        // assert_eq!(constraints[0].coeffs.L, Scalar::zero());
        // assert_eq!(constraints[0].coeffs.R, Scalar::zero());
        // assert_eq!(constraints[0].coeffs.M, Scalar::one());
        // assert_eq!(constraints[0].coeffs.O, Scalar::one().neg());
        // assert_eq!(constraints[0].coeffs.C, Scalar::zero());

        let program = Program::new(constraints, 8);

        let mut prover = Prover::new(setup.clone(), program.clone());

        let mut witness: HashMap<String, Scalar> = HashMap::new();
        witness.insert("a".to_owned(), Scalar::from(3));
        witness.insert("b".to_owned(), Scalar::from(4));
        witness.insert("c".to_owned(), Scalar::from(16));
        witness.insert("d".to_owned(), Scalar::from(5));
        witness.insert("e".to_owned(), Scalar::from(80));

        // let (a_1, b_1, c_1) = prover.round_1(witness);
        // let z_1 = prover.round_2();
        // let (t_lo_1, t_mid_1, t_hi_1) = prover.round_3();
        // let (a_bar, b_bar, c_bar, s1_bar, s2_bar, z_omega_bar) = prover.round_4();
        // let (w_zeta_1, w_zeta_omega_1) = prover.round_5();

        let proof = prover.prove(witness);
    }
    #[test]
    fn test_public_input() {
        let setup = Setup::generate_srs(8 + 3, Scalar::from(1));
        let constraints: Vec<_> = vec!["a <== b * c"]
            .into_iter()
            .map(AssemblyEqn::eq_to_assembly)
            .collect();
        let program = Program::new(constraints, 8);
        let mut prover = Prover::new(setup, program);

        let mut witness: HashMap<String, Scalar> = HashMap::new();
        witness.insert("b".to_owned(), Scalar::from(2));
        witness.insert("c".to_owned(), Scalar::from(3));
        witness.insert("a".to_owned(), Scalar::from(6));

        let public_vars: Vec<_> = prover
            .program
            .get_public_assignment()
            .iter()
            .map(|x| x.clone().unwrap())
            .collect();
        let mut values: Vec<_> = public_vars
            .iter()
            .map(|x| witness.get(x).unwrap().neg())
            .collect();
        for _ in 0..prover.group_order as usize - public_vars.len() {
            values.push(Scalar::zero());
        }
        prover.public_input_poly = Some(Polynomial::new(values, Basis::Lagrange));
        println!("public_input_poly:{:?}", prover.public_input_poly);
        let mut rng = rand::thread_rng();

        prover.blinding_coeffs = Some([Scalar::from(0); 11].map(|_| Scalar::random(&mut rng)));

        prover.round_1(witness);
    }

    #[test]
    fn test_round_1() {
        //passed
        //round1用于生成a(x),b(x),c(x)和他们的承诺
        let (mut prover, witness) = initilization();

        prover.round_1(witness);
        //如果constraints是vec!["c <== a*b"]
        //且witness: a==3,b==5,c==15
        // 则矩阵：
        //A  B  C
        //3  5  15
        //0  0  0
        //...(总共8行，因为group_order为8,剩余全为0)

        let a_values = prover.witness_polys.a.unwrap().values;
        let b_values = prover.witness_polys.b.unwrap().values;
        let c_values = prover.witness_polys.c.unwrap().values;
        let ql_values = prover.pk.ql.values;
        let qr_values = prover.pk.qr.values;
        let qo_values = prover.pk.qo.values;
        let qc_values = prover.pk.qc.values;
        let qm_values = prover.pk.qm.values;
        println!("a_values:{:?}", a_values);
        println!("b_values:{:?}", b_values);
        println!("c_values:{:?}", c_values);
        println!("ql_values:{:?}", ql_values);
        println!("qr_values:{:?}", qr_values);
        println!("qo_values:{:?}", qo_values);
        println!("qm_values:{:?}", qm_values);
        println!("qc_values:{:?}", qc_values);

        // assert_eq!(qo_values[0], Scalar::one().neg());
        //qo_values[0] = -1

        // assert_eq!(
        //     qo_values[0] * Scalar::from(15) + Scalar::from(3) * Scalar::from(5),
        //     Scalar::zero()
        // );

        let a_coeff = Polynomial::new(i_ntt_381(&a_values), Basis::Monomial);
        let b_coeff = Polynomial::new(i_ntt_381(&b_values), Basis::Monomial);
        let c_coeff = Polynomial::new(i_ntt_381(&c_values), Basis::Monomial);
        let ql_coeff = Polynomial::new(i_ntt_381(&ql_values), Basis::Monomial);
        let qr_coeff = Polynomial::new(i_ntt_381(&qr_values), Basis::Monomial);
        let qo_coeff = Polynomial::new(i_ntt_381(&qo_values), Basis::Monomial);
        let qc_coeff = Polynomial::new(i_ntt_381(&qc_values), Basis::Monomial);
        let qm_coeff = Polynomial::new(i_ntt_381(&qm_values), Basis::Monomial);

        use crate::utils::ntt_381;
        println!("ql_coeff:{:?}", ql_coeff.clone());
        println!("ql_coeff convert:{:?}", ntt_381(&ql_coeff.values));

        let res_coeff = a_coeff.clone() * ql_coeff
            + b_coeff.clone() * qr_coeff
            + a_coeff * b_coeff * qm_coeff
            + c_coeff * qo_coeff
            + qc_coeff;

        let roots_of_unity = roots_of_unity(prover.group_order);
        for (_, root_of_unity) in roots_of_unity.iter().enumerate() {
            assert_eq!(
                res_coeff.coeffs_evaluate(root_of_unity.clone()),
                Scalar::zero()
            );
        }
    }

    #[test]

    fn test_round_2() {
        //passed
        let (mut prover, witness) = initilization();

        prover.round_1(witness);
        prover.round_2();
    }
    #[test]
    fn test_round_3() {
        let (mut prover, witness) = initilization();

        prover.round_1(witness);
        prover.round_2();
        prover.round_3();
    }

    #[test]
    fn test_round_4() {
        let (mut prover, witness) = initilization();

        prover.round_1(witness);
        prover.round_2();
        prover.round_3();
        prover.round_4();
    }

    #[test]
    fn test_round_5() {
        let (mut prover, witness) = initilization();

        prover.round_1(witness);
        prover.round_2();
        prover.round_3();
        prover.round_4();
        prover.round_5();
    }

    #[test]
    fn test_coset() {
        // let omega = root_of_unity(8);
        let v1 = roots_of_unity(8);
        let v2: Vec<Scalar> = v1.iter().map(|x| x * Scalar::from(2)).collect();
        let v3: Vec<Scalar> = v1.iter().map(|x| x * Scalar::from(3)).collect();
        assert!(!has_intersection(&v1, &v2));
        assert!(!has_intersection(&v1, &v3));
        assert!(!has_intersection(&v3, &v2));
    }
    fn has_intersection<T: PartialEq>(vec1: &Vec<T>, vec2: &Vec<T>) -> bool {
        for item1 in vec1 {
            if vec2.contains(item1) {
                return true;
            }
        }
        false
    }
}
