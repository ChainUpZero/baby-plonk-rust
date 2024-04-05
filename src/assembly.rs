use crate::utils::{extract_number_and_variable, split_expression};
use bls12_381::Scalar;
use ff::Field;
#[derive(Debug)]
pub struct GateWire {
    pub L: Option<String>,
    pub R: Option<String>,
    pub O: Option<String>,
}
impl GateWire {
    pub fn to_vec(&self) -> Vec<Option<String>> {
        vec![self.L.clone(), self.R.clone(), self.O.clone()]
    }
}
#[derive(Debug)]
pub struct GateCoeffs {
    pub L: Scalar,
    pub R: Scalar,
    pub M: Scalar,
    pub O: Scalar,
    pub C: Scalar,
}

#[derive(Debug)]
pub struct AssemblyEqn {
    pub wires: GateWire,
    pub coeffs: GateCoeffs,
}

impl AssemblyEqn {
    pub fn eq_to_assembly(eq: &str) -> AssemblyEqn {
        //d <== a * c - 45 * a + 987
        let parts = split_expression(eq);
        let mut gate_wires = GateWire {
            L: None,
            R: None,
            O: None,
        };
        let mut gate_coeffs = GateCoeffs {
            L: Scalar::zero(),
            R: Scalar::zero(),
            M: Scalar::zero(),
            O: Scalar::zero(),
            C: Scalar::zero(),
        };

        for (i, part) in parts.iter().enumerate() {
            if i == 0 {
                //output
                let (coeffs, variable) = extract_number_and_variable(part).unwrap();

                assert_eq!(variable.len(), 1, "variable.len() not == 1");
                gate_wires.O = Some(variable[0].clone());
                gate_coeffs.O = -coeffs;
            } else if part.contains("==") {
                continue;
            } else {
                let (coeffs, variable) = extract_number_and_variable(part).unwrap();
                //4*a*b => 4, vec![a,b]
                assert_eq!(variable.len() <= 2, true, "variable.len() not <= 2");

                if variable.len() == 0 {
                    //C
                    gate_coeffs.C = coeffs;
                } else if variable.len() == 1 {
                    //L or R
                    if gate_coeffs.L.is_zero().into() {
                        gate_coeffs.L = coeffs;
                        gate_wires.L = Some(variable[0].clone());
                    } else if (gate_coeffs.R.is_zero().into()) {
                        gate_coeffs.R = coeffs;
                        gate_wires.R = Some(variable[0].clone());
                    } else {
                        panic!("only need 1 L and 1 R");
                    }
                } else {
                    //M
                    //有两个变量
                    //如果L和R都还没有，就将两个变量赋给他们
                    //如果L已经有了，R还没有：就检查L是否在这两个变量中，如果在就将另一个变量赋值给R；如果L不在这两个变量中，则报错
                    //如果L和R都有了，不操作
                    gate_coeffs.M = coeffs;
                    if gate_coeffs.L.is_zero().into() && gate_coeffs.R.is_zero().into() {
                        gate_wires.L = Some(variable[0].clone());
                        gate_wires.R = Some(variable[1].clone());
                    } else if gate_coeffs.R.is_zero().into() {
                        //L已经有，R还没有
                        if gate_wires.L == Some(variable[0].clone()) {
                            gate_wires.R = Some(variable[1].clone())
                        } else if gate_wires.L == Some(variable[1].clone()) {
                            gate_wires.R = Some(variable[0].clone());
                        } else {
                            panic!("only need 1 L and 1 R");
                        }
                    } else {
                        panic!("only need 1 L and 1 R");
                    }
                }
            }
        }
        AssemblyEqn {
            wires: gate_wires,
            coeffs: gate_coeffs,
        }
    }
}

#[cfg(test)]
mod tests {

    use super::AssemblyEqn;
    use crate::assembly::Scalar;
    #[test]
    fn test_eq_to_assembly() {
        //passed
        //45*c <== 2*a*b + 3*a + 53*b + 46
        // let eq = "45*c <== 2*a*b + 3*a + 53*b + 46";
        // let assembly_eqn = AssemblyEqn::eq_to_assembly(eq);
        // assert_eq!(assembly_eqn.coeffs.L, Scalar::from(3));
        // assert_eq!(assembly_eqn.coeffs.R, Scalar::from(53));
        // assert_eq!(assembly_eqn.coeffs.M, Scalar::from(2));
        // assert_eq!(assembly_eqn.coeffs.O, Scalar::from(45).neg());
        // assert_eq!(assembly_eqn.coeffs.C, Scalar::from(46));

        // assert_eq!(assembly_eqn.wires.L, Some("a".to_string()));
        // assert_eq!(assembly_eqn.wires.R, Some("b".to_string()));
        // assert_eq!(assembly_eqn.wires.O, Some("c".to_string()));

        println!(
            "'a <== b*c' to assembly_eqn:{:?}",
            AssemblyEqn::eq_to_assembly("a <== b*c")
        );
        println!(
            "'a <== 2*b*c + 56' to assembly_eqn:{:?}",
            AssemblyEqn::eq_to_assembly("a <== 2*b*c + 56")
        );
        println!(
            "'a <== 3 + b*c' to assembly_eqn:{:?}",
            AssemblyEqn::eq_to_assembly("a <== 3 + b*c")
        );
        println!(
            "'a <== 3 + abc' to assembly_eqn:{:?}",
            AssemblyEqn::eq_to_assembly("a <== 3 + abc")
        );
        println!(
            "'a <== c + d' to assembly_eqn:{:?}",
            AssemblyEqn::eq_to_assembly("a <== c + d")
        );
    }
}
