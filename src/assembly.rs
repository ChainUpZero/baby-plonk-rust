use crate::utils::{extract_number_and_variable, split_expression};
use bls12_381::Scalar;
use ff::{Field, PrimeField};
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone)]
pub struct GateCoeffs {
    pub L: Scalar,
    pub R: Scalar,
    pub M: Scalar,
    pub O: Scalar,
    pub C: Scalar,
}

#[derive(Debug, Clone)]
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
                    } else if gate_coeffs.R.is_zero().into() {
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

use std::{collections::HashMap, panic};

fn evaluate(exprs: &Vec<&str>) -> HashMap<Option<String>, i64> {
    evaluate_inner(exprs, false)
}

fn evaluate_inner(exprs: &Vec<&str>, first_is_negative: bool) -> HashMap<Option<String>, i64> {
    match exprs.iter().any(|&x| x == "+") {
        true => {
            let idx = exprs.iter().position(|&x| x == "+").unwrap();
            let l = evaluate_inner(&exprs[..idx].to_vec(), first_is_negative);
            let r = evaluate_inner(&exprs[idx + 1..].to_vec(), false);
            return merge_maps(&l, &r);
        }
        false => match exprs.iter().any(|&x| x == "-") {
            true => {
                let idx = exprs.iter().position(|&x| x == "-").unwrap();
                let l = evaluate_inner(&exprs[..idx].to_vec(), first_is_negative);
                let r = evaluate_inner(&exprs[idx + 1..].to_vec(), true);
                return merge_maps(&l, &r);
            }
            false => match exprs.iter().any(|&x| x == "*") {
                true => {
                    let idx = exprs.iter().position(|&x| x == "*").unwrap();
                    let l = evaluate_inner(&exprs[..idx].to_vec(), first_is_negative);
                    let r = evaluate_inner(&exprs[idx + 1..].to_vec(), first_is_negative);
                    return multiply_maps(&l, &r);
                }
                false => {
                    if exprs.len() > 1 {
                        panic!("No ops, expected sub-expr to be a unit: {:?}", exprs[1]);
                    } else if exprs[0].starts_with('-') {
                        return evaluate_inner(&vec![&exprs[0][1..]], !first_is_negative);
                    } else if exprs[0].parse::<i64>().is_ok() {
                        let value = exprs[0].parse::<i64>().unwrap()
                            * if first_is_negative { -1 } else { 1 };
                        let mut result = HashMap::new();
                        result.insert(None, value);
                        return result;
                    } else if is_valid_variable_name(exprs[0]) {
                        let mut result = HashMap::new();
                        let value = if first_is_negative { -1 } else { 1i64 };
                        result.insert(Some(exprs[0].to_string()), value);
                        return result;
                    } else {
                        panic!("ok wtf is {}", exprs[0]);
                    }
                }
            },
        },
    }
}

fn merge_maps(
    map1: &HashMap<Option<String>, i64>,
    map2: &HashMap<Option<String>, i64>,
) -> HashMap<Option<String>, i64> {
    let mut merged = HashMap::new();
    for (key, val) in map1.iter().chain(map2.iter()) {
        *merged.entry(key.clone()).or_insert(0) += val;
    }
    merged
}

fn multiply_maps(
    map1: &HashMap<Option<String>, i64>,
    map2: &HashMap<Option<String>, i64>,
) -> HashMap<Option<String>, i64> {
    let mut result = HashMap::new();
    for (k1, v1) in map1.iter() {
        for (k2, v2) in map2.iter() {
            let product_key = get_product_key(k1.clone(), k2.clone());
            *result.entry(product_key).or_insert(0) += v1 * v2;
        }
    }
    result
}

fn get_product_key(key1: Option<String>, key2: Option<String>) -> Option<String> {
    match (key1, key2) {
        (Some(k1), Some(k2)) => {
            let members = {
                let mut members = Vec::new();
                members.extend(k1.split('*'));
                members.extend(k2.split('*'));
                members.sort();
                members
            };
            Some(
                members
                    .into_iter()
                    .filter(|x| !x.is_empty())
                    .collect::<Vec<&str>>()
                    .join("*"),
            )
        }
        (Some(k1), None) => Some(k1),
        (None, Some(k2)) => Some(k2),
        (None, None) => None,
    }
}

fn is_valid_variable_name(name: &str) -> bool {
    !name.is_empty()
        && name.chars().all(char::is_alphanumeric)
        && !name.chars().next().unwrap().is_numeric()
}

#[cfg(test)]
mod test_eval {
    use super::evaluate;
    #[test]
    fn test_evaluate() {
        let expr = "6000 - 700 - 80 + 9";
        let exprs = expr.split_whitespace().collect::<Vec<&str>>();
        assert_eq!(*evaluate(&exprs).values().into_iter().next().unwrap(), 5229);
        let expr = "-6000 + 700 + 80 - 9";
        let exprs = expr.split_whitespace().collect::<Vec<&str>>();
        assert_eq!(
            *evaluate(&exprs).values().into_iter().next().unwrap(),
            -5229
        );
        let expr = "1 + 2 * 3";
        let exprs = expr.split_whitespace().collect::<Vec<&str>>();
        assert_eq!(*evaluate(&exprs).values().into_iter().next().unwrap(), 7);
        let expr = "-1 + 2 * 3";
        let exprs = expr.split_whitespace().collect::<Vec<&str>>();
        assert_eq!(*evaluate(&exprs).values().into_iter().next().unwrap(), 5);
    }
}
