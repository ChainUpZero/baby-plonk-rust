use std::collections::HashMap;
use crate::assembly::GateWire;
use crate::polynomial::Basis;
use crate::utils::{roots_of_unity, Cell, Column};
use crate::{assembly::AssemblyEqn, polynomial::Polynomial};
use bls12_381::Scalar;

pub struct CommonPreprocessedInput {
    pub group_order: u64,
    pub ql: Polynomial,
    pub qr: Polynomial,
    pub qm: Polynomial,
    pub qo: Polynomial,
    pub qc: Polynomial,
    pub s1: Polynomial,
    pub s2: Polynomial,
    pub s3: Polynomial,

    pub s1_coeff: Option<Polynomial>,
    pub s2_coeff: Option<Polynomial>,
}
#[derive(Clone)]
pub struct Program {
    pub constraints: Vec<AssemblyEqn>,
    pub group_order: u64,
}
impl Program {
    pub fn new(constraints: Vec<AssemblyEqn>, group_order: u64) -> Program {
        Program {
            constraints,
            group_order,
        }
    }
    pub fn common_preprocessed_input(&self) -> CommonPreprocessedInput {
        let (ql, qr, qm, qo, qc) = self.make_gate_polynomials();
        let (s1, s2, s3) = self.make_s_polynomials();
        CommonPreprocessedInput {
            group_order: self.group_order,
            ql,
            qr,
            qm,
            qo,
            qc,
            s1,
            s2,
            s3,
            s1_coeff: None,
            s2_coeff: None,
        }
    }
    pub fn make_gate_polynomials(
        &self,
    ) -> (Polynomial, Polynomial, Polynomial, Polynomial, Polynomial) {
        //make L R M O C gate polynomials
        let mut L = vec![Scalar::zero(); self.group_order as usize];
        let mut R = vec![Scalar::zero(); self.group_order as usize];
        let mut M = vec![Scalar::zero(); self.group_order as usize];
        let mut O = vec![Scalar::zero(); self.group_order as usize];
        let mut C = vec![Scalar::zero(); self.group_order as usize];
        for (i, constraint) in self.constraints.iter().enumerate() {
            let gate = constraint.gate();
            L[i] = gate.L;
            R[i] = gate.R;
            M[i] = gate.M;
            O[i] = gate.O;
            C[i] = gate.C;
        }
        (
            Polynomial::new(L, Basis::Lagrange),
            Polynomial::new(R, Basis::Lagrange),
            Polynomial::new(M, Basis::Lagrange),
            Polynomial::new(O, Basis::Lagrange),
            Polynomial::new(C, Basis::Lagrange),
        )
    }
    pub fn make_s_polynomials(&self) -> (Polynomial, Polynomial, Polynomial) {
        let mut variable_uses = HashMap::new();
        //循环的目的是在variable_uses放variable所有所在的cell
        for (row, constraint) in self.constraints.iter().enumerate() {
            //每层循环，处理约束，用wires字段
            //L放在第一列，R放第二列，O放第三列
            for (column, variable) in constraint.wires.to_vec().into_iter().enumerate() {
                variable_uses.entry(variable).or_insert(vec![]).push(Cell {
                    column: (column + 1).into(),
                    row,
                });
            }
        }
        //现在已得到变量到他所在所有cell组成的vec的映射
        //下面的循环考虑所有为空的cell

        for row in self.constraints.len()..self.group_order as usize {
            for i in 1..=3 {
                variable_uses.entry(None).or_insert(vec![]).push(Cell {
                    column: i.into(),
                    row,
                })
            }
        }
        let mut s: HashMap<Column, Vec<Scalar>> = HashMap::new();
        s.insert(
            Column::LEFT,
            roots_of_unity(self.group_order)
                .into_iter()
                .map(|element| element)
                .collect(),
        );
        s.insert(
            Column::RIGHT,
            roots_of_unity(self.group_order)
                .into_iter()
                .map(|element| element * Scalar::from(2))
                .collect(),
        );
        s.insert(
            Column::OUTPUT,
            vec![Scalar::zero(); self.group_order as usize],
        );

        // exmaple
        // variable_uses = {"a":[Cell(1,3),Cell(3,4)],"b":[Cell(2,1)]
        for (_, uses) in variable_uses.iter() {
            // _ = "a"
            // uses = [Cell(1,3),Cell(3,4)]
            for (i, cell) in uses.iter().enumerate() {
                let next_i = (i + 1) % uses.len();
                let next_column = uses[next_i].column;
                let next_row = uses[next_i].row;
                if let Some(vec) = s.get_mut(&next_column) {
                    vec[next_row] = cell.label(self.group_order);
                }
            }
        }

        //生成s1,s2，s3
        let mut s1 = None;
        let mut s2 = None;
        let mut s3 = None;
        for (key, vec) in s.into_iter() {
            match key {
                Column::LEFT => s1 = Some(Polynomial::new(vec, Basis::Lagrange)),
                Column::RIGHT => s2 = Some(Polynomial::new(vec, Basis::Lagrange)),
                Column::OUTPUT => s3 = Some(Polynomial::new(vec, Basis::Lagrange)),
            }
        }
        (s1.unwrap(), s2.unwrap(), s3.unwrap())
    }

    pub fn coeffs(&self) -> Vec<HashMap<Option<String>, Scalar>> {
        let mut coeffs = Vec::new();
        for constraint in self.constraints.iter() {
            // let mut constraint_coeffs = HashMap::new();
            // constraint_coeffs.insert(Some("L".to_string()), constraint.coeffs.L);
            // constraint_coeffs.insert(Some("R".to_string()), constraint.coeffs.R);
            // constraint_coeffs.insert(Some("M".to_string()), constraint.coeffs.M);
            // constraint_coeffs.insert(Some("O".to_string()), constraint.coeffs.O);
            // constraint_coeffs.insert(Some("C".to_string()), constraint.coeffs.C);
            // coeffs.push(constraint_coeffs);
            coeffs.push(constraint.coeffs.clone());
        }
        coeffs
    }

    pub fn wires(&self) -> Vec<GateWire> {
        let mut wires = Vec::new();
        for constraint in self.constraints.iter() {
            wires.push(constraint.wires.clone());
        }
        return wires;
    }

    pub fn get_public_assignment(&self) -> Vec<Option<String>> {
        let coeffs = self.coeffs();
        let mut out = Vec::new();
        let mut no_more_allowed = false;
        for coeff in coeffs.iter() {
            if coeff.get(&Some("$public".to_string())) != None {
                if no_more_allowed {
                    panic!("Public var declarations must be at the top")
                }
                let mut var_name = Vec::new();
                for (key, _) in coeff.iter() {
                    if key.clone().unwrap().chars().next().unwrap() != '$' {
                        var_name.push(key.clone().unwrap());
                    }
                }

                out.push(Some(var_name.join("")));
            } else {
                no_more_allowed = true;
            }
        }
        out
    }
}

#[cfg(test)]
mod test {
    use bls12_381::Scalar;

    use crate::{assembly::AssemblyEqn, utils::roots_of_unity};

    use super::Program;

    #[test]
    fn test_make_s_polynomials() {
        //passed
        //L R  O
        //w 2w 3w
        //w^2 2w^2 3w^2

        //a b c
        //a e b
        let original_constriants = ["c <== a * b", "b <== a * e"];
        let mut assembly_eqns = Vec::new();
        for eq in original_constriants.iter() {
            let assembly_eqn = AssemblyEqn::eq_to_assembly(eq);
            assembly_eqns.push(assembly_eqn);
        }
        let program = Program::new(assembly_eqns, 8);
        let (s1, s2, s3) = program.make_s_polynomials();

        let unmoved_s1: Vec<_> = roots_of_unity(8);
        let unmoved_s2: Vec<_> = roots_of_unity(8)
            .into_iter()
            .map(|ele| ele * Scalar::from(2))
            .collect();
        let unmoved_s3: Vec<_> = roots_of_unity(8)
            .into_iter()
            .map(|ele| ele * Scalar::from(3))
            .collect();
        assert_eq!(s1.values[0], unmoved_s1[1]);

        assert_eq!(s2.values[0], unmoved_s3[1]);

        // println!("s1:{:?}", s1);
        // println!("s2:{:?}", s2);
        // println!("s3:{:?}", s3);
    }
    #[test]
    fn test_make_gate_polynomials() {
        let original_constriants = ["e public", "c <== a * b", "e <== c * d"];
        let mut assembly_eqns = Vec::new();
        for eq in original_constriants.iter() {
            let assembly_eqn = AssemblyEqn::eq_to_assembly(eq);
            assembly_eqns.push(assembly_eqn);
        }
        let program = Program::new(assembly_eqns, 8);
        let (l, r, m, o, c) = program.make_gate_polynomials();
        println!("l:{:?}", l);
        println!("r:{:?}", r);
        println!("m:{:?}", m);
        println!("o:{:?}", o);
        println!("c:{:?}", c);
    }
}
