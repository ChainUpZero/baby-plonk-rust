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
pub struct Gate {
    pub L: Scalar,
    pub R: Scalar,
    pub M: Scalar,
    pub O: Scalar,
    pub C: Scalar,
}

#[derive(Debug, Clone)]
pub struct AssemblyEqn {
    pub wires: GateWire,
    pub coeffs: HashMap<Option<String>, Scalar>,
}

impl AssemblyEqn {
    pub fn l(&self) -> Scalar {
        let value = self.coeffs.get(&self.wires.L);
        match value {
            Some(_) => (*value.unwrap()).neg(),
            None => Scalar::zero(),
        }
    }
    pub fn r(&self) -> Scalar {
        if self.wires.R != self.wires.L {
            let value = self.coeffs.get(&self.wires.R);
            return match value {
                Some(_) => (*value.unwrap()).neg(),
                None => Scalar::zero(),
            };
        }
        Scalar::zero()
    }
    pub fn c(&self) -> Scalar {
        let value = self.coeffs.get(&None);
        match value {
            Some(_) => (*value.unwrap()).neg(),
            None => Scalar::zero(),
        }
    }
    pub fn o(&self) -> Scalar {
        let value = self.coeffs.get(&Some("$output_coeff".to_owned()));
        match value {
            Some(_) => *value.unwrap(),
            None => Scalar::one(),
        }
    }
    pub fn m(&self) -> Scalar {
        if !self.wires.to_vec().contains(&None) {
            let value = self
                .coeffs
                .get(&get_product_key(self.wires.L.clone(), self.wires.R.clone()));
            return match value {
                Some(_) => (*value.unwrap()).neg(),
                None => Scalar::zero(),
            };
        }
        Scalar::zero()
    }
    pub fn gate(&self) -> Gate {
        Gate {
            L: self.l(),
            R: self.r(),
            M: self.m(),
            O: self.o(),
            C: self.c(),
        }
    }

    // pub fn eq_to_assembly(eq: &str) -> AssemblyEqn {
    //     //d <== a * c - 45 * a + 987
    //     let parts = split_expression(eq);
    //     let mut gate_wires = GateWire {
    //         L: None,
    //         R: None,
    //         O: None,
    //     };
    //     let mut gate_coeffs = GateCoeffs {
    //         L: Scalar::zero(),
    //         R: Scalar::zero(),
    //         M: Scalar::zero(),
    //         O: Scalar::zero(),
    //         C: Scalar::zero(),
    //     };

    //     for (i, part) in parts.iter().enumerate() {
    //         if i == 0 {
    //             //output
    //             let (coeffs, variable) = extract_number_and_variable(part).unwrap();

    //             assert_eq!(variable.len(), 1, "variable.len() not == 1");
    //             gate_wires.O = Some(variable[0].clone());
    //             gate_coeffs.O = -coeffs;
    //         } else if part.contains("==") {
    //             continue;
    //         } else {
    //             let (coeffs, variable) = extract_number_and_variable(part).unwrap();
    //             //4*a*b => 4, vec![a,b]
    //             assert_eq!(variable.len() <= 2, true, "variable.len() not <= 2");

    //             if variable.len() == 0 {
    //                 //C
    //                 gate_coeffs.C = coeffs;
    //             } else if variable.len() == 1 {
    //                 //L or R
    //                 if gate_coeffs.L.is_zero().into() {
    //                     gate_coeffs.L = coeffs;
    //                     gate_wires.L = Some(variable[0].clone());
    //                 } else if gate_coeffs.R.is_zero().into() {
    //                     gate_coeffs.R = coeffs;
    //                     gate_wires.R = Some(variable[0].clone());
    //                 } else {
    //                     panic!("only need 1 L and 1 R");
    //                 }
    //             } else {
    //                 //M
    //                 //有两个变量
    //                 //如果L和R都还没有，就将两个变量赋给他们
    //                 //如果L已经有了，R还没有：就检查L是否在这两个变量中，如果在就将另一个变量赋值给R；如果L不在这两个变量中，则报错
    //                 //如果L和R都有了，不操作
    //                 gate_coeffs.M = coeffs;
    //                 if gate_coeffs.L.is_zero().into() && gate_coeffs.R.is_zero().into() {
    //                     gate_wires.L = Some(variable[0].clone());
    //                     gate_wires.R = Some(variable[1].clone());
    //                 } else if gate_coeffs.R.is_zero().into() {
    //                     //L已经有，R还没有
    //                     if gate_wires.L == Some(variable[0].clone()) {
    //                         gate_wires.R = Some(variable[1].clone())
    //                     } else if gate_wires.L == Some(variable[1].clone()) {
    //                         gate_wires.R = Some(variable[0].clone());
    //                     } else {
    //                         panic!("only need 1 L and 1 R");
    //                     }
    //                 } else {
    //                     panic!("only need 1 L and 1 R");
    //                 }
    //             }
    //         }
    //     }
    //     AssemblyEqn {
    //         wires: gate_wires,
    //         coeffs: gate_coeffs,
    //     }
    // }
    //new eq_to_assembly
    pub fn eq_to_assembly(eq: &str) -> AssemblyEqn {
        let tokens: Vec<&str> = eq.trim().split(" ").collect();
        if tokens[1] == "<==" || tokens[1] == "===" {
            // First token is the output variable
            let mut out = tokens[0];
            // Convert the expression to coefficient map form
            let mut coeffs = evaluate(&tokens[2..].to_vec());
            // Handle the "-x === a * b" case
            if out.chars().nth(0).unwrap() == '-' {
                out = &out[1..];
                coeffs.insert(Some("$output_coeff".to_string()), Scalar::one().neg());
            }
            // Check out variable name validity
            if !is_valid_variable_name(out) {
                panic!("Invalid out variable name: {}", out);
            }
            // Gather list of variables used in the expression
            let mut variables: Vec<&str> = Vec::new();
            for &t in tokens[2..].iter() {
                let var = &t.trim_start_matches("-");
                if is_valid_variable_name(var) && !variables.contains(var) {
                    variables.push(var);
                }
            }
            // Construct the list of allowed coefficients
            let mut allowed_coeffs: Vec<String> =
                variables.iter().map(|&s| s.to_string()).collect();
            allowed_coeffs.extend(vec!["".to_string(), "$output_coeff".to_string()]);

            if variables.is_empty() {
                todo!();
            } else if variables.len() == 1 {
                variables.push(variables[0]);
                let product_key =
                    get_product_key(Some(variables[0].to_owned()), Some(variables[1].to_owned()))
                        .unwrap();
                allowed_coeffs.push(product_key);
            } else if variables.len() == 2 {
                let product_key =
                    get_product_key(Some(variables[0].to_owned()), Some(variables[1].to_owned()))
                        .unwrap();
                allowed_coeffs.push(product_key);
            } else {
                panic!("Max 2 variables, found {}", variables.len());
            }

            // Check that only allowed coefficients are in the coefficient map
            for key_option in coeffs.keys() {
                // 使用 as_ref 将 Option<String> 转换为 Option<&String>
                // 这样可以安全地访问其中的 String 引用
                let key_ref = key_option.as_ref().unwrap(); // key_option 必须包含值，否则 panic

                // 检查 allowed_coeffs 是否包含这个引用
                if !allowed_coeffs.contains(key_ref) {
                    panic!("Disallowed multiplication");
                }
            }

            // Return output
            let variables_len = variables.len();
            let mut wires: Vec<Option<&str>> = variables
                .into_iter()
                .map(Some)
                .chain(vec![None; 2 - variables_len])
                .collect();
            wires.push(Some(out));

            return AssemblyEqn {
                wires: GateWire {
                    L: Some(wires[0].unwrap().to_string()),
                    R: Some(wires[1].unwrap().to_string()),
                    O: Some(wires[2].unwrap().to_string()),
                },
                coeffs,
            };
        } else if tokens[1] == "public" {
            let mut coeffs = HashMap::new();
            coeffs.insert(Some(tokens[0].to_string()), Scalar::one().neg());
            coeffs.insert(Some("$output_coeff".to_string()), Scalar::zero());
            coeffs.insert(Some("$public".to_string()), Scalar::one());
            return AssemblyEqn {
                wires: GateWire {
                    L: Some(tokens[0].to_string()),
                    R: None,
                    O: None,
                },
                coeffs,
            };
        } else {
            panic!("Unsupported op: {}", tokens[1]);
        }
    }
}

#[cfg(test)]
mod tests {

    use bls12_381::Scalar;

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

        // println!(
        //     "'a <== b*c' to assembly_eqn:{:?}",
        //     AssemblyEqn::eq_to_assembly("a <== b*c")
        // );
        // println!(
        //     "'a <== 2*b*c + 56' to assembly_eqn:{:?}",
        //     AssemblyEqn::eq_to_assembly("a <== 2*b*c + 56")
        // );
        // println!(
        //     "'a <== 3 + b*c' to assembly_eqn:{:?}",
        //     AssemblyEqn::eq_to_assembly("a <== 3 + b*c")
        // );
        // println!(
        //     "'a <== 3 + abc' to assembly_eqn:{:?}",
        //     AssemblyEqn::eq_to_assembly("a <== 3 + abc")
        // );
        // println!(
        //     "'a <== c + d' to assembly_eqn:{:?}",
        //     AssemblyEqn::eq_to_assembly("a <== c + d")
        // );
        let eq = "e public";
        let assembly_eqn = AssemblyEqn::eq_to_assembly(eq);
        println!("e public to assembly_eqn: {:?}", assembly_eqn);
        assert_eq!(
            assembly_eqn.coeffs.get(&Some("e".to_owned())),
            Some(&Scalar::one().neg())
        );

        let eq = "c <== a * b";
        let assembly_eqn = AssemblyEqn::eq_to_assembly(eq);
        println!("e public to assembly_eqn: {:?}", assembly_eqn);
        // assert_eq!(
        //     assembly_eqn.coeffs.get(&Some("e".to_owned())),
        //     Some(&Scalar::one().neg())
        // );
        let eq = "e <== c * d";
        let assembly_eqn = AssemblyEqn::eq_to_assembly(eq);
        println!("e public to assembly_eqn: {:?}", assembly_eqn);
    }
}

use std::{collections::HashMap, panic};

fn evaluate(exprs: &Vec<&str>) -> HashMap<Option<String>, Scalar> {
    evaluate_inner(exprs, false)
}

fn evaluate_inner(exprs: &Vec<&str>, first_is_negative: bool) -> HashMap<Option<String>, Scalar> {
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
                    } else if exprs[0].parse::<i128>().is_ok() {
                        let value = {
                            if first_is_negative {
                                Scalar::from_u128(exprs[0].parse::<i128>().unwrap().abs() as u128)
                                    .neg()
                            } else {
                                Scalar::from_u128(exprs[0].parse::<i128>().unwrap() as u128)
                            }
                        };
                        let mut result = HashMap::new();
                        result.insert(None, value);
                        return result;
                    } else if is_valid_variable_name(exprs[0]) {
                        let mut result = HashMap::new();
                        let value = if first_is_negative {
                            Scalar::one().neg()
                        } else {
                            Scalar::one()
                        };
                        result.insert(Some(exprs[0].to_string()), value);
                        return result;
                    } else {
                        println!("exprs:{:?}", exprs);
                        panic!("ok wtf is {}", exprs[0]);
                    }
                }
            },
        },
    }
}

fn merge_maps(
    map1: &HashMap<Option<String>, Scalar>,
    map2: &HashMap<Option<String>, Scalar>,
) -> HashMap<Option<String>, Scalar> {
    let mut merged = HashMap::new();
    for (key, val) in map1.iter().chain(map2.iter()) {
        *merged.entry(key.clone()).or_insert(Scalar::zero()) += val;
    }
    merged
}

fn multiply_maps(
    map1: &HashMap<Option<String>, Scalar>,
    map2: &HashMap<Option<String>, Scalar>,
) -> HashMap<Option<String>, Scalar> {
    let mut result = HashMap::new();
    for (k1, v1) in map1.iter() {
        for (k2, v2) in map2.iter() {
            let product_key = get_product_key(k1.clone(), k2.clone());
            *result.entry(product_key).or_insert(Scalar::zero()) += v1 * v2;
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
    use bls12_381::Scalar;
    use ff::PrimeField;

    use super::evaluate;
    #[test]
    fn test_evaluate() {
        //passed
        // let expr = "6000 - 700 - 80 + 9";
        // let exprs = expr.split_whitespace().collect::<Vec<&str>>();
        // assert_eq!(
        //     *evaluate(&exprs).values().into_iter().next().unwrap(),
        //     Scalar::from_u128(5229)
        // );
        // let expr = "-6000 + 700 + 80 - 9";
        // let exprs = expr.split_whitespace().collect::<Vec<&str>>();
        // assert_eq!(
        //     *evaluate(&exprs).values().into_iter().next().unwrap(),
        //     Scalar::from_u128(5229).neg()
        // );
        // let expr = "1 + 2 * 3";
        // let exprs = expr.split_whitespace().collect::<Vec<&str>>();
        // assert_eq!(
        //     *evaluate(&exprs).values().into_iter().next().unwrap(),
        //     Scalar::from_u128(7)
        // );
        // let expr = "-1 + 2 * 3";
        // let exprs = expr.split_whitespace().collect::<Vec<&str>>();
        // assert_eq!(
        //     *evaluate(&exprs).values().into_iter().next().unwrap(),
        //     Scalar::from_u128(5)
        // );

        //['a', '+', 'b', '*', 'c', '*', '5'] becomes {'a': 1, 'b*c': 5}
        let expr = "a + b * c * 5";
        let exprs = expr.split_whitespace().collect::<Vec<&str>>();

        println!("evaluate(&exprs):{:?}", evaluate(&exprs));
    }
}
