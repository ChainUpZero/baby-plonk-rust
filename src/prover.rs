use crate::polynomial::{Basis, Polynomial};
use crate::program::{CommonPreprocessedInput, Program};
use crate::setup::Setup;
use crate::utils::roots_of_unity;
use bls12_381::{G1Projective, Scalar};
use std::collections::HashMap;
struct RandomNums {
    alpha: Option<Scalar>,
    beta: Option<Scalar>,
    gamma: Option<Scalar>,
}

struct WitnessPolys {
    a: Option<Polynomial>,
    b: Option<Polynomial>,
    c: Option<Polynomial>,
    z: Option<Polynomial>,
}

pub struct Prover {
    group_order: u64,
    program: Program,
    setup: Setup,
    pk: CommonPreprocessedInput,
    random_nums: RandomNums,
    witness_polys: WitnessPolys,
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
            },
            witness_polys: WitnessPolys {
                a: None,
                b: None,
                c: None,
                z: None,
            },
        }
    }
    pub fn round_1(
        &self,
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
            a_values[i] = *witness.get(constraint.wires.L.as_ref().unwrap()).unwrap();
            b_values[i] = *witness.get(constraint.wires.R.as_ref().unwrap()).unwrap();
            c_values[i] = *witness.get(constraint.wires.O.as_ref().unwrap()).unwrap();
        }
        let ax = Polynomial::new(a_values, Basis::Lagrange);
        let bx = Polynomial::new(b_values, Basis::Lagrange);
        let cx = Polynomial::new(c_values, Basis::Lagrange);
        let w_ax = self.setup.commit(ax);
        let w_bx = self.setup.commit(bx);
        let w_cx = self.setup.commit(cx);
        (w_ax, w_bx, w_cx)
    }

    pub fn round_2(&self) {
        //计算z(x)
        let mut z_values = vec![Scalar::one()];
        let roots_of_unity = roots_of_unity(self.program.group_order);
        for i in 0..self.program.group_order as usize {
            z_values.push(
                z_values[z_values.len() - 1]
                    * self.rlc(
                        self.witness_polys.a.as_ref().unwrap().values[i],
                        roots_of_unity[i],
                    )
                    * self.rlc(
                        self.witness_polys.b.as_ref().unwrap().values[i],
                        Scalar::from(2) * roots_of_unity[i],
                    )
                    * self.rlc(
                        self.witness_polys.c.as_ref().unwrap().values[i],
                        Scalar::from(3) * roots_of_unity[i],
                    )
                    * self
                        .rlc(
                            self.witness_polys.a.as_ref().unwrap().values[i],
                            self.pk.s1.values[i],
                        )
                        .invert()
                        .unwrap()
                    * self
                        .rlc(
                            self.witness_polys.b.as_ref().unwrap().values[i],
                            self.pk.s2.values[i],
                        )
                        .invert()
                        .unwrap()
                    * self
                        .rlc(
                            self.witness_polys.c.as_ref().unwrap().values[i],
                            self.pk.s3.values[i],
                        )
                        .invert()
                        .unwrap(),
            );
        }
    }

    //random linear combination
    pub fn rlc(&self, term1: Scalar, term2: Scalar) -> Scalar {
        term1 + term2 * self.random_nums.beta.unwrap() + self.random_nums.gamma.unwrap()
    }
}
