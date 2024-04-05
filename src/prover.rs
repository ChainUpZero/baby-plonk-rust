use crate::polynomial::{Basis, Polynomial};
use crate::program::{CommonPreprocessedInput, Program};
use crate::setup::Setup;
use crate::utils::{i_ntt_381, ntt_381, root_of_unity, roots_of_unity, Rlc};
use bls12_381::{G1Projective, Scalar};
use std::collections::btree_map::Values;
use std::collections::HashMap;
struct RandomNums {
    alpha: Option<Scalar>,
    beta: Option<Scalar>,
    gamma: Option<Scalar>,
    zeta: Option<Scalar>,
    nu: Option<Scalar>,
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
    zw_coeff: Option<Polynomial>,
    t_low_coeff: Option<Polynomial>,
    t_mid_coeff: Option<Polynomial>,
    t_hi_coeff: Option<Polynomial>,
}
struct Evaluations {
    a_bar: Scalar,
    b_bar: Scalar,
    c_bar: Scalar,
    s1_bar: Scalar,
    s2_bar: Scalar,
    zw_bar: Scalar,
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
            },

            witness_polys: WitnessPolys {
                a: None,
                b: None,
                c: None,
                z: None,
                zw: None,
                t_low_coeff: None,
                t_mid_coeff: None,
                t_hi_coeff: None,
                w_zeta: None,
                w_zeta_omega: None,

                a_coeff: None,
                b_coeff: None,
                c_coeff: None,
                z_coeff: None,
                zw_coeff: None,
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

        let c_a = self.setup.commit(&a);
        let c_b = self.setup.commit(&b);
        let c_c = self.setup.commit(&c);

        self.witness_polys.a = Some(a);
        self.witness_polys.b = Some(b);
        self.witness_polys.c = Some(c);

        (c_a, c_b, c_c)
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
        let z_1 = self.setup.commit(&z);
        self.witness_polys.z = Some(z);
        z_1
    }

    fn round_3(&mut self) -> (G1Projective, G1Projective, G1Projective) {
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

        let mut l0_values = vec![Scalar::one()];
        for _ in 0..self.group_order - 1 {
            l0_values.push(Scalar::zero());
        }
        let l0 = Polynomial::new(l0_values, Basis::Lagrange);

        let mut z_h_values = vec![Scalar::one().neg()];
        for _ in 0..self.group_order - 2 {
            z_h_values.push(Scalar::zero());
        }
        z_h_values.push(Scalar::one());
        // z_H(x) = (x-w^0)(x-w)(x-w^2)...(x-w^n-1)
        //又因为这是一个roots of unity群
        //所以Z_H(x) = x^n - 1,n 为group_order
        //算出z_h(x)的系数表示的原因是
        // 最后要计算h(x)/z_h(x)
        // 而z_h(x)作为除数，如果用点值表示的话在roots of unity上全为0，所以无法进行除法
        //所以只能将z_h(x)变为系数形式来除。因此，h(x)也要变为系数形式
        let zh_coeff = Polynomial::new(z_h_values, Basis::Monomial);

        let gate_constraints_coeff = a_coeff.clone() * ql_coeff.clone()
            + b_coeff.clone() * qr_coeff.clone()
            + a_coeff.clone() * b_coeff.clone() * qm_coeff.clone()
            + c_coeff.clone() * qo_coeff.clone()
            + qc_coeff.clone();

        let roots_poly_coeff = Polynomial::new(i_ntt_381(&roots_of_unity.clone()), Basis::Monomial);

        let zw = Polynomial::new(
            self.witness_polys.z.clone().unwrap().shift_left(1),
            Basis::Lagrange,
        );

        let zw_coeff = Polynomial::new(
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
                    * zw.values[i % self.group_order as usize]
            )
        }

        let permutation_grand_product_coeff = (a_coeff.rlc(&roots_poly_coeff)
            * b_coeff.rlc(&(roots_poly_coeff.clone() * Scalar::from(2)))
            * c_coeff.rlc(&(roots_poly_coeff.clone() * Scalar::from(3))))
            * z_coeff.clone()
            - (a_coeff.rlc(&s1_coeff) * b_coeff.rlc(&s2_coeff) * c_coeff.rlc(&s3_coeff))
                * zw_coeff.clone();
        let l0_coeff = Polynomial::new(l0.values.clone(), Basis::Monomial);

        let permutation_first_row_coeff = (z_coeff.clone() - Scalar::one()) * l0_coeff;

        let alpha = Scalar::from(2);
        self.random_nums.alpha = Some(alpha);

        let all_constraints = gate_constraints_coeff
            + permutation_grand_product_coeff * alpha
            + permutation_first_row_coeff * alpha.pow(&[2u64, 0, 0, 0]);

        let t_coeff = all_constraints / zh_coeff;

        let (t_low_coeff, t_mid_coeff, t_hi_coeff) = self.split_t_to_3pieces(t_coeff);

        println!("Generated the quotient polynomial!");

        let c_t_low_coeff = self.setup.commit(&t_low_coeff);
        let c_t_mid_coeff = self.setup.commit(&t_mid_coeff);
        let c_t_hi_coeff = self.setup.commit(&t_hi_coeff);

        self.pk.s1_coeff = Some(s1_coeff);
        self.pk.s2_coeff = Some(s2_coeff);

        self.witness_polys.a_coeff = Some(a_coeff);
        self.witness_polys.b_coeff = Some(b_coeff);
        self.witness_polys.c_coeff = Some(c_coeff);
        self.witness_polys.z_coeff = Some(z_coeff);
        self.witness_polys.zw_coeff = Some(zw_coeff);
        self.witness_polys.t_low_coeff = Some(t_low_coeff);
        self.witness_polys.t_mid_coeff = Some(t_mid_coeff);
        self.witness_polys.t_hi_coeff = Some(t_hi_coeff);

        (c_t_low_coeff, c_t_mid_coeff, c_t_hi_coeff)
    }

    fn round_4(&mut self) -> (Scalar, Scalar, Scalar, Scalar, Scalar, Scalar) {
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
        let zw_bar = self
            .witness_polys
            .zw_coeff
            .as_ref()
            .unwrap()
            .coeffs_evaluate(zeta);

        self.evals = Some(Evaluations {
            a_bar,
            b_bar,
            c_bar,
            s1_bar,
            s2_bar,
            zw_bar,
        });

        (a_bar, b_bar, c_bar, s1_bar, s2_bar, zw_bar)
    }

    fn round_5(&mut self) -> (G1Projective, G1Projective) {
        let nu = Scalar::from(6);
        self.random_nums.nu = Some(nu);
        let a_bar = self.evals.as_ref().unwrap().a_bar;
        let b_bar = self.evals.as_ref().unwrap().b_bar;
        let c_bar = self.evals.as_ref().unwrap().c_bar;
        let s1_bar = self.evals.as_ref().unwrap().s1_bar;
        let s2_bar = self.evals.as_ref().unwrap().s2_bar;
        let zw_bar = self.evals.as_ref().unwrap().zw_bar;

        let alpha = self.random_nums.alpha.unwrap();
        let beta = self.random_nums.beta.unwrap();
        let gamma = self.random_nums.gamma.unwrap();
        let zeta = self.random_nums.zeta.unwrap();

        let a = self.witness_polys.a.clone().unwrap();
        let b = self.witness_polys.b.clone().unwrap();
        let c = self.witness_polys.c.clone().unwrap();
        let s1 = self.pk.s1.clone();
        let s2 = self.pk.s2.clone();
        let z = self.witness_polys.z.clone().unwrap();

        let r1 = self.pk.qm.clone() * a_bar * b_bar
            + self.pk.ql.clone() * a_bar
            + self.pk.qr.clone() * b_bar
            + self.pk.qo.clone() * c_bar
            + self.pk.qc.clone();

        let r2 = (self.witness_polys.z.clone().unwrap()
            * (a_bar + beta * zeta + gamma)
            * (b_bar + beta * Scalar::from(2) * zeta + gamma)
            * (c_bar + beta * Scalar::from(3) * zeta + gamma)
            - (self.pk.s3.clone() * beta + gamma + c_bar)
                * (a_bar + beta * s1_bar + gamma)
                * (b_bar + beta * s2_bar + gamma)
                * zw_bar)
            * alpha;

        let mut l0_values = vec![Scalar::zero(); self.group_order as usize];
        l0_values[0] = Scalar::one();
        let coeffs_l0 = Polynomial::new(i_ntt_381(&l0_values), Basis::Monomial);
        let r3 = ((self.witness_polys.z.clone().unwrap() - Scalar::from(1))
            * coeffs_l0.coeffs_evaluate(zeta))
            * alpha.pow(&[2u64, 0, 0, 0]);

        let r4_coeff = (self.witness_polys.t_low_coeff.clone().unwrap()
            + self.witness_polys.t_mid_coeff.clone().unwrap()
                * zeta.pow(&[self.group_order, 0, 0, 0])
            + self.witness_polys.t_hi_coeff.clone().unwrap()
                * zeta.pow(&[2 * self.group_order, 0, 0, 0]))
            * self
                .witness_polys
                .z_coeff
                .as_ref()
                .unwrap()
                .coeffs_evaluate(zeta);

        println!("r4_coeff.values.len():{}", r4_coeff.values.len());
        let r4 = Polynomial::new(ntt_381(&r4_coeff.values), Basis::Lagrange);

        let r = r1 + r2 + r3 + r4;

        //x - zeta = -zeta + x
        let mut x_minus_zeta_poly_values = vec![Scalar::zero(); self.group_order as usize];
        x_minus_zeta_poly_values[0] = zeta.neg();
        x_minus_zeta_poly_values[1] = Scalar::one();

        let w_zeta = (r
            + (a - a_bar) * nu
            + (b - b_bar) * nu * nu
            + (c - c_bar) * nu.pow(&[3u64, 0, 0, 0])
            + (s1 - s1_bar) * nu.pow(&[4u64, 0, 0, 0])
            + (s2 - s2_bar) * nu.pow(&[5u64, 0, 0, 0]))
            / Polynomial::new(x_minus_zeta_poly_values, Basis::Lagrange);

        //x - zeta*omega = -zeta*omega + x
        let omega = root_of_unity(self.group_order);
        let mut x_minus_zeta_omega_poly_values = vec![Scalar::zero(); self.group_order as usize];
        x_minus_zeta_omega_poly_values[0] = (zeta * omega).neg();
        x_minus_zeta_omega_poly_values[1] = Scalar::one();

        let w_zeta_omega =
            (z - zw_bar) / Polynomial::new(x_minus_zeta_omega_poly_values, Basis::Lagrange);

        let c_w_zeta = self.setup.commit(&w_zeta);
        let c_w_zeta_omega = self.setup.commit(&w_zeta_omega);

        self.witness_polys.w_zeta = Some(w_zeta);
        self.witness_polys.w_zeta_omega = Some(w_zeta_omega);

        (c_w_zeta, c_w_zeta_omega)
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
        let constraints: Vec<_> = vec!["c <== a*b", "b <== a + d"]
            .into_iter()
            .map(AssemblyEqn::eq_to_assembly)
            .collect();

        let program = Program::new(constraints, 8);
        let prover = Prover::new(setup, program);

        let mut witness: HashMap<String, Scalar> = HashMap::new();
        witness.insert("a".to_owned(), Scalar::from(3));
        witness.insert("b".to_owned(), Scalar::from(5));
        witness.insert("c".to_owned(), Scalar::from(15));
        witness.insert("d".to_owned(), Scalar::from(2));

        (prover, witness)
    }

    #[test]
    fn test_round_1() {
        //passed
        //round1用于生成a(x),b(x),c(x)和他们的承诺
        let (mut prover, mut witness) = initilization();

        let (a_1, b_1, c_1) = prover.round_1(witness);
        //如果constraints是vec!["c <== a*b", "b <== a+d"]
        //且witness: a==3,b==5,c==15,d==2
        // 则矩阵：
        //A  B  C
        //3  5  15
        //3  2  5
        //0  0  0
        //...(总共8行，因为group_order为8,剩余全为0)
        let mut expect_ax_values = vec![Scalar::zero(); prover.group_order as usize];
        expect_ax_values[0] = Scalar::from(3);
        expect_ax_values[1] = Scalar::from(3);

        let mut expect_bx_values = vec![Scalar::zero(); prover.group_order as usize];
        expect_bx_values[0] = Scalar::from(5);
        expect_bx_values[1] = Scalar::from(2);

        let mut expect_cx_values = vec![Scalar::zero(); prover.group_order as usize];
        expect_cx_values[0] = Scalar::from(15);
        expect_cx_values[1] = Scalar::from(5);

        let expect_ax = Polynomial::new(expect_ax_values, Basis::Lagrange);
        let expect_bx = Polynomial::new(expect_bx_values, Basis::Lagrange);
        let expect_cx = Polynomial::new(expect_cx_values, Basis::Lagrange);

        // assert_eq!(expect_ax, prover.witness_polys.a.unwrap());
        // assert_eq!(expect_bx, prover.witness_polys.b.unwrap());
        // assert_eq!(expect_cx, prover.witness_polys.c.unwrap());

        let a = prover.witness_polys.a.as_ref().unwrap();
        let b = prover.witness_polys.b.as_ref().unwrap();
        let c = prover.witness_polys.c.as_ref().unwrap();

        assert_eq!(
            a.clone() * prover.pk.ql.clone()
                + b.clone() * prover.pk.qr.clone()
                + a.clone() * b.clone() * prover.pk.qm.clone()
                + c.clone() * prover.pk.qo.clone()
                + prover.pk.qc.clone(),
            Polynomial::new(
                vec![Scalar::zero(); prover.group_order as usize],
                Basis::Lagrange
            )
        );
    }

    #[test]

    fn test_round_2() {
        //passed
        let (mut prover, mut witness) = initilization();

        let (a_1, b_1, c_1) = prover.round_1(witness);
        prover.round_2();
    }
    #[test]
    fn test_round_3() {
        let (mut prover, mut witness) = initilization();

        let (a_1, b_1, c_1) = prover.round_1(witness);
        prover.round_2();
        prover.round_3();
    }

    #[test]
    fn test_round_4() {
        let (mut prover, mut witness) = initilization();

        let (a_1, b_1, c_1) = prover.round_1(witness);
        prover.round_2();
        prover.round_3();
        prover.round_4();
    }

    #[test]
    fn test_round_5() {
        let (mut prover, mut witness) = initilization();

        let (a_1, b_1, c_1) = prover.round_1(witness);
        prover.round_2();
        prover.round_3();
        prover.round_4();
        prover.round_5();
    }
}
