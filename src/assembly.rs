use crate::utils::{extract_number_and_variable, split_expression};
use bls12_381::Scalar;
use ff::Field;
use regex::Regex;
#[derive(Debug)]
pub struct GateWire {
    pub L: Option<String>,
    pub R: Option<String>,
    pub O: Option<String>,
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
    wires: GateWire,
    coeffs: GateCoeffs,
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
                gate_coeffs.O = -coeffs.unwrap();
            } else if part.contains("==") {
                continue;
            } else {
                let (coeffs, variable) = extract_number_and_variable(part).unwrap();
                //4*a*b => 4, vec![a,b]
                assert_eq!(variable.len() <= 2, true, "variable.len() not <= 2");
                if variable.len() == 0 {
                    //C
                    gate_coeffs.C = coeffs.unwrap();
                } else if variable.len() == 1 {
                    //L or R
                    if gate_coeffs.L.is_zero().into() {
                        gate_coeffs.L = coeffs.unwrap();
                        gate_wires.L = Some(variable[0].clone());
                    } else if (gate_coeffs.R.is_zero().into()) {
                        gate_coeffs.R = coeffs.unwrap();
                        gate_wires.R = Some(variable[0].clone());
                    } else {
                        panic!("only need 1 L and 1 R");
                    }
                } else {
                    //M
                    gate_coeffs.M = coeffs.unwrap();
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
        let eq = "45*c <== 2*a*b + 3*a + 53*b + 46";
        let assembly_eqn = AssemblyEqn::eq_to_assembly(eq);
        assert_eq!(assembly_eqn.coeffs.L, Scalar::from(3));
        assert_eq!(assembly_eqn.coeffs.R, Scalar::from(53));
        assert_eq!(assembly_eqn.coeffs.M, Scalar::from(2));
        assert_eq!(assembly_eqn.coeffs.O, Scalar::from(45).neg());
        assert_eq!(assembly_eqn.coeffs.C, Scalar::from(46));

        assert_eq!(assembly_eqn.wires.L, Some("a".to_string()));
        assert_eq!(assembly_eqn.wires.R, Some("b".to_string()));
        assert_eq!(assembly_eqn.wires.O, Some("c".to_string()));
    }
}
