use crate::polynomial::{Basis, Polynomial};
use crate::program::{CommonPreprocessedInput, Program};
use crate::setup::Setup;
use crate::utils::{i_ntt_381, ntt_381, root_of_unity, roots_of_unity, Rlc};
use bls12_381::{G1Projective, Scalar};
use std::collections::btree_map::Values;
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
}
impl Prover {
    pub fn new(setup: Setup, program: Program) -> Prover {
        Prover {
            group_order: program.group_order,
            setup,
            pk: program.common_preprocessed_input(),
            program,
            random_nums: RandomNums {
                alpha: None, //2
                beta: None,  //3
                gamma: None, //4
                zeta: None,  //5
                nu: None,    //6
                mu: None,    //7
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
            },
            evals: None,
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
        for (i, constraint) in self.program.constraints.iter().enumerate() {
            //constraint.wires = {L:Some('a'),R,Some('b'),O:Some('c')}
            //处理A的第i个约束

            //constraint.wires.L是该门的L的变量名。R和O同理
            a_values[i] = *witness.get(constraint.wires.L.as_ref().unwrap()).unwrap();
            b_values[i] = *witness.get(constraint.wires.R.as_ref().unwrap()).unwrap();
            c_values[i] = *witness.get(constraint.wires.O.as_ref().unwrap()).unwrap();
        }

        let a = Polynomial::new(a_values, Basis::Lagrange);
        let b = Polynomial::new(b_values, Basis::Lagrange);
        let c = Polynomial::new(c_values, Basis::Lagrange);

        let a_1 = self
            .setup
            .commit(&Polynomial::new(i_ntt_381(&a.values), Basis::Monomial));
        let b_1 = self
            .setup
            .commit(&Polynomial::new(i_ntt_381(&b.values), Basis::Monomial));
        let c_1 = self
            .setup
            .commit(&Polynomial::new(i_ntt_381(&c.values), Basis::Monomial));

        self.witness_polys.a = Some(a);
        self.witness_polys.b = Some(b);
        self.witness_polys.c = Some(c);

        (a_1, b_1, c_1)
    }

    pub fn round_2(&mut self) -> G1Projective {
        //计算z(x)
        let mut z_values = vec![Scalar::one()];
        let roots_of_unity = roots_of_unity(self.program.group_order);

        self.random_nums.beta = Some(Scalar::from(3));
        self.random_nums.gamma = Some(Scalar::from(4));

        for i in 0..self.program.group_order as usize {
            z_values.push(
                z_values[z_values.len() - 1]
                    * self.witness_polys.a.as_ref().unwrap().values[i].rlc(&roots_of_unity[i])
                    * self.witness_polys.b.as_ref().unwrap().values[i]
                        .rlc(&(roots_of_unity[i] * Scalar::from(2)))
                    * self.witness_polys.c.as_ref().unwrap().values[i]
                        .rlc(&(roots_of_unity[i] * Scalar::from(3)))
                    * self.witness_polys.a.as_ref().unwrap().values[i]
                        .rlc(&self.pk.s1.values[i])
                        .invert()
                        .unwrap()
                    * self.witness_polys.b.as_ref().unwrap().values[i]
                        .rlc(&self.pk.s2.values[i])
                        .invert()
                        .unwrap()
                    * self.witness_polys.c.as_ref().unwrap().values[i]
                        .rlc(&self.pk.s3.values[i])
                        .invert()
                        .unwrap(),
            );
        }

        assert_eq!(z_values.pop().unwrap(), Scalar::from(1));
        for i in 0..self.group_order as usize {
            assert_eq!(
                self.witness_polys.a.as_ref().unwrap().values[i].rlc(&roots_of_unity[i])
                    * self.witness_polys.b.as_ref().unwrap().values[i]
                        .rlc(&(Scalar::from(2) * roots_of_unity[i]))
                    * self.witness_polys.c.as_ref().unwrap().values[i]
                        .rlc(&(Scalar::from(3) * roots_of_unity[i]))
                    * z_values[i],
                self.witness_polys.a.as_ref().unwrap().values[i].rlc(&self.pk.s1.values[i])
                    * self.witness_polys.b.as_ref().unwrap().values[i].rlc(&self.pk.s2.values[i])
                    * self.witness_polys.c.as_ref().unwrap().values[i].rlc(&self.pk.s3.values[i])
                    * z_values[(i + 1) % self.group_order as usize]
            )
        }

        let z = Polynomial::new(z_values, Basis::Lagrange);
        let z_1 = self
            .setup
            .commit(&Polynomial::new(i_ntt_381(&z.values), Basis::Monomial));
        self.witness_polys.z = Some(z);
        z_1
    }

    pub fn round_3(&mut self) -> (G1Projective, G1Projective, G1Projective) {
        //compute t(x)  i.e t_lo(x),t_mid(x),t_hi(x)
        let roots_of_unity = roots_of_unity(self.group_order);

        let polys = vec![
            self.witness_polys.a.clone().unwrap().values,
            self.witness_polys.b.clone().unwrap().values,
            self.witness_polys.c.clone().unwrap().values,
            self.pk.s1.clone().values,
            self.pk.s2.clone().values,
            self.pk.s3.clone().values,
            self.witness_polys.z.clone().unwrap().values,
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
        let (
            a_coeff,
            b_coeff,
            c_coeff,
            s1_coeff,
            s2_coeff,
            s3_coeff,
            z_coeff,
            ql_coeff,
            qr_coeff,
            qm_coeff,
            qo_coeff,
            qc_coeff,
        ) = (
            coeff_polys[0].clone(),
            coeff_polys[1].clone(),
            coeff_polys[2].clone(),
            coeff_polys[3].clone(),
            coeff_polys[4].clone(),
            coeff_polys[5].clone(),
            coeff_polys[6].clone(),
            coeff_polys[7].clone(),
            coeff_polys[8].clone(),
            coeff_polys[9].clone(),
            coeff_polys[10].clone(),
            coeff_polys[11].clone(),
        );

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
            + qc_coeff.clone();

        let roots_poly_coeff = Polynomial::new(i_ntt_381(&roots_of_unity.clone()), Basis::Monomial);

        let z_omega = Polynomial::new(
            self.witness_polys.z.clone().unwrap().shift_left(1),
            Basis::Lagrange,
        );

        let z_omega_coeff = Polynomial::new(
            i_ntt_381(&self.witness_polys.z.clone().unwrap().shift_left(1)),
            Basis::Monomial,
        );

        for i in 0..self.group_order as usize {
            assert_eq!(
                self.witness_polys.a.as_ref().unwrap().values[i].rlc(&roots_of_unity[i])
                    * self.witness_polys.b.as_ref().unwrap().values[i]
                        .rlc(&(Scalar::from(2) * roots_of_unity[i]))
                    * self.witness_polys.c.as_ref().unwrap().values[i]
                        .rlc(&(Scalar::from(3) * roots_of_unity[i]))
                    * self.witness_polys.z.clone().unwrap().values[i],
                self.witness_polys.a.as_ref().unwrap().values[i].rlc(&self.pk.s1.values[i])
                    * self.witness_polys.b.as_ref().unwrap().values[i].rlc(&self.pk.s2.values[i])
                    * self.witness_polys.c.as_ref().unwrap().values[i].rlc(&self.pk.s3.values[i])
                    * z_omega.values[i % self.group_order as usize]
            )
        }

        let permutation_grand_product_coeff = (a_coeff.rlc(&roots_poly_coeff)
            * b_coeff.rlc(&(roots_poly_coeff.clone() * Scalar::from(2)))
            * c_coeff.rlc(&(roots_poly_coeff.clone() * Scalar::from(3))))
            * z_coeff.clone()
            - (a_coeff.rlc(&s1_coeff) * b_coeff.rlc(&s2_coeff) * c_coeff.rlc(&s3_coeff))
                * z_omega_coeff.clone();
        let l1_coeff = Polynomial::new(i_ntt_381(&l1.values.clone()), Basis::Monomial);

        let permutation_first_row_coeff = (z_coeff.clone() - Scalar::one()) * l1_coeff;

        let alpha = Scalar::from(2);
        self.random_nums.alpha = Some(alpha);

        let all_constraints = gate_constraints_coeff
            + permutation_grand_product_coeff * alpha
            + permutation_first_row_coeff * alpha.pow(&[2u64, 0, 0, 0]);

        let t_coeff = all_constraints / z_h_coeff;

        let (t_lo_coeff, t_mid_coeff, t_hi_coeff) = self.split_t_to_3pieces(t_coeff.clone());

        println!("Generated the quotient polynomial!");

        let t_lo_1 = self.setup.commit(&t_lo_coeff);
        let t_mid_1 = self.setup.commit(&t_mid_coeff);
        let t_hi_1 = self.setup.commit(&t_hi_coeff);

        //x^n
        let mut x_pow_n_values = vec![Scalar::zero(); self.group_order as usize + 1];
        x_pow_n_values[self.group_order as usize] = Scalar::from(1);

        //x^2n
        let mut x_pow_2n_values = vec![Scalar::zero(); self.group_order as usize * 2 + 1];
        x_pow_2n_values[self.group_order as usize * 2] = Scalar::from(1);
        assert_eq!(
            t_coeff.clone(),
            t_lo_coeff.clone()
                + Polynomial::new(x_pow_n_values, Basis::Monomial) * t_mid_coeff.clone()
                + Polynomial::new(x_pow_2n_values, Basis::Monomial) * t_hi_coeff.clone()
        );

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
        let zeta = Scalar::from(5);
        self.random_nums.zeta = Some(zeta);
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
            .z_coeff
            .as_ref()
            .unwrap()
            .coeffs_evaluate(zeta * root_of_unity(self.group_order));

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

    pub fn round_5(&mut self) -> (G1Projective, G1Projective) {
        let nu = Scalar::from(6);
        self.random_nums.nu = Some(nu);
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

        let r1 = self.pk.qm.clone() * a_bar * b_bar
            + self.pk.ql.clone() * a_bar
            + self.pk.qr.clone() * b_bar
            + self.pk.qo.clone() * c_bar
            + self.pk.qc.clone();

        let r1_coeff = Polynomial::new(r1.values, Basis::Monomial);

        let r2 = (self.witness_polys.z.clone().unwrap()
            * (a_bar + beta * zeta + gamma)
            * (b_bar + beta * Scalar::from(2) * zeta + gamma)
            * (c_bar + beta * Scalar::from(3) * zeta + gamma)
            - (self.pk.s3.clone() * beta + gamma + c_bar)
                * (a_bar + beta * s1_bar + gamma)
                * (b_bar + beta * s2_bar + gamma)
                * z_omega_bar)
            * alpha;

        let r2_coeff = Polynomial::new(r2.values, Basis::Monomial);

        let mut l1_values = vec![Scalar::zero(); self.group_order as usize];
        l1_values[0] = Scalar::one();
        let l1_coeff = Polynomial::new(i_ntt_381(&l1_values), Basis::Monomial);

        let r3 = ((self.witness_polys.z.clone().unwrap() - Scalar::from(1))
            * l1_coeff.coeffs_evaluate(zeta))
            * alpha.pow(&[2u64, 0, 0, 0]);

        let r3_coeff = Polynomial::new(r3.values, Basis::Monomial);

        //x^n-1
        let mut z_h_values = vec![Scalar::one().neg()];
        for _ in 0..self.group_order - 1 {
            z_h_values.push(Scalar::zero());
        }
        z_h_values.push(Scalar::one());
        let z_h_coeff = Polynomial::new(z_h_values, Basis::Monomial);

        let r4_coeff = (self.witness_polys.t_lo_coeff.clone().unwrap()
            + self.witness_polys.t_mid_coeff.clone().unwrap()
                * zeta.pow(&[self.group_order, 0, 0, 0])
            + self.witness_polys.t_hi_coeff.clone().unwrap()
                * zeta.pow(&[2 * self.group_order, 0, 0, 0]))
            * z_h_coeff.coeffs_evaluate(zeta);

        let r = r1_coeff + r2_coeff + r3_coeff - r4_coeff;

        //x - zeta = -zeta + x
        //系数形式
        let mut x_minus_zeta_poly_values = vec![Scalar::zero(); 2];
        x_minus_zeta_poly_values[0] = zeta.neg();
        x_minus_zeta_poly_values[1] = Scalar::one();

        let w_zeta = (r
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

        let w_zeta_omega = (z_coeff - z_omega_bar)
            / Polynomial::new(x_minus_zeta_omega_poly_values, Basis::Monomial);

        let w_zeta_1 = self.setup.commit(&w_zeta);
        let w_zeta_omega_1 = self.setup.commit(&w_zeta_omega);

        self.witness_polys.w_zeta = Some(w_zeta);
        self.witness_polys.w_zeta_omega = Some(w_zeta_omega);

        (w_zeta_1, w_zeta_omega_1)
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
}

#[cfg(test)]
mod tests {

    use crate::assembly::AssemblyEqn;

    use super::*;
    fn initilization() -> (Prover, HashMap<String, Scalar>) {
        let setup = Setup::generate_srs(8, Scalar::from(1));
        let constraints: Vec<_> = vec!["c <== a*b"]
            .into_iter()
            .map(AssemblyEqn::eq_to_assembly)
            .collect();

        let program = Program::new(constraints, 8);
        let prover = Prover::new(setup, program);

        let mut witness: HashMap<String, Scalar> = HashMap::new();
        witness.insert("a".to_owned(), Scalar::from(3));
        witness.insert("b".to_owned(), Scalar::from(5));
        witness.insert("c".to_owned(), Scalar::from(15));

        (prover, witness)
    }

    #[test]
    fn test_round_1() {
        //passed
        //round1用于生成a(x),b(x),c(x)和他们的承诺
        let (mut prover, mut witness) = initilization();

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

        assert_eq!(qo_values[0], Scalar::one().neg());
        //qo_values[0] = -1

        assert_eq!(
            qo_values[0] * Scalar::from(15) + Scalar::from(3) * Scalar::from(5),
            Scalar::zero()
        );

        let a_coeff = Polynomial::new(i_ntt_381(&a_values), Basis::Monomial);
        let b_coeff = Polynomial::new(i_ntt_381(&b_values), Basis::Monomial);
        let c_coeff = Polynomial::new(i_ntt_381(&c_values), Basis::Monomial);
        let ql_coeff = Polynomial::new(i_ntt_381(&ql_values), Basis::Monomial);
        let qr_coeff = Polynomial::new(i_ntt_381(&qr_values), Basis::Monomial);
        let qo_coeff = Polynomial::new(i_ntt_381(&qo_values), Basis::Monomial);
        let qc_coeff = Polynomial::new(i_ntt_381(&qc_values), Basis::Monomial);
        let qm_coeff = Polynomial::new(i_ntt_381(&qm_values), Basis::Monomial);

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
        let (mut prover, mut witness) = initilization();

        prover.round_1(witness);
        prover.round_2();
    }
    #[test]
    fn test_round_3() {
        let (mut prover, mut witness) = initilization();

        prover.round_1(witness);
        prover.round_2();
        prover.round_3();
    }

    #[test]
    fn test_round_4() {
        let (mut prover, mut witness) = initilization();

        prover.round_1(witness);
        prover.round_2();
        prover.round_3();
        prover.round_4();
    }

    #[test]
    fn test_round_5() {
        let (mut prover, mut witness) = initilization();

        prover.round_1(witness);
        prover.round_2();
        prover.round_3();
        prover.round_4();
        prover.round_5();
    }
}
