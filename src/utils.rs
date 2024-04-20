use crate::polynomial::Polynomial;
use bls12_381::Scalar;
use ff::PrimeField;
use regex::Regex;
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Column {
    LEFT,
    RIGHT,
    OUTPUT,
}
// impl Column {
//     pub fn value(&self) -> usize {
//         match self {
//             Column::LEFT => 1,
//             Column::RIGHT => 2,
//             Column::OUTPUT => 3,
//         }
//     }
// }
impl From<usize> for Column {
    fn from(value: usize) -> Self {
        match value {
            1 => Column::LEFT,
            2 => Column::RIGHT,
            3 => Column::OUTPUT,
            _ => panic!("wrong column"),
        }
    }
}
#[derive(Debug, Clone)]
pub struct Cell {
    pub column: Column,
    pub row: usize,
}

impl Cell {
    pub fn label(&self, group_order: u64) -> Scalar {
        roots_of_unity(group_order)[self.row]
            * match self.column {
                Column::LEFT => Scalar::from(1),
                Column::RIGHT => Scalar::from(2),
                Column::OUTPUT => Scalar::from(3),
            }
    }
}

pub fn root_of_unity(group_order: u64) -> Scalar {
    let generator = Scalar::ROOT_OF_UNITY; //阶为2^32的子群的生成元

    generator.pow(&[((u32::MAX as u64 + 1) / group_order), 0, 0, 0])
}

pub fn roots_of_unity(group_order: u64) -> Vec<Scalar> {
    let mut res = vec![Scalar::from(1)];
    let generator = root_of_unity(group_order);
    for _ in 1..group_order {
        res.push(res[res.len() - 1] * generator);
    }
    res
}

pub fn find_next_power_of_two(n: usize, m: usize) -> usize {
    let mut power = 1;
    let target = n + m + 1;
    while power < target {
        power <<= 1;
    }
    power
}
///系数到点值
pub fn ntt_381(elements: &Vec<Scalar>) -> Vec<Scalar> {
    let n = elements.len() as u64;
    assert!(is_power_of_two(n));
    let mut matrix: Vec<Vec<u64>> = vec![vec![0; n as usize]; n as usize];
    (0..n).for_each(|x| (0..n).for_each(|y| matrix[x as usize][y as usize] = x * y));
    // println!("{:#?}", matrix);
    matrix
        .iter()
        .map(|row| {
            elements
                .iter()
                .zip(row)
                .map(|(elem, ij)| {
                    elem * Scalar::ROOT_OF_UNITY.pow(&[*ij * ((u32::MAX as u64 + 1) / n), 0, 0, 0])
                })
                .sum::<Scalar>()
        })
        .collect::<Vec<Scalar>>()
}
fn is_power_of_two(n: u64) -> bool {
    n != 0 && (n & (n - 1)) == 0
}

/*
pub fn i_ntt(elements: &[u64]) -> Result<Vec<u64>, String> {
    let n = elements.len() as u64;
    let modulus = find_modulus(elements)?;
    let omega = find_primitive_root(n, modulus)?;
    Ok(dft_matrix(n)
        .iter()
        .map(|row| {
            elements
                .iter()
                .zip(row)
                .map(|(elem, ij)| elem * omega.inv_pow_mod(*ij, modulus))
                .sum::<u64>()
                * n.inv_pow_mod(1, modulus)
                % modulus
        })
        .collect::<Vec<u64>>())
}
 */
///点值到系数
pub fn i_ntt_381(elements: &Vec<Scalar>) -> Vec<Scalar> {
    let n = elements.len() as u64;
    assert!(is_power_of_two(n));
    let mut matrix: Vec<Vec<u64>> = vec![vec![0; n as usize]; n as usize];
    (0..n).for_each(|x| (0..n).for_each(|y| matrix[x as usize][y as usize] = x * y));
    matrix
        .iter()
        .map(|row| {
            elements
                .iter()
                .zip(row)
                .map(|(elem, ij)| {
                    elem * Scalar::ROOT_OF_UNITY_INV.pow(&[
                        *ij * ((u32::MAX as u64 + 1) / n),
                        0,
                        0,
                        0,
                    ])
                })
                .sum::<Scalar>()
                * Scalar::from(n).invert().unwrap()
        })
        .collect::<Vec<Scalar>>()
}

pub fn extract_number_and_variable(input: &str) -> Option<(Scalar, Vec<String>)> {
    let re = Regex::new(r"^(\d+)?((\*[a-zA-Z]+)*|([a-zA-Z]+(\*[a-zA-Z]+)*))$").unwrap();
    if let Some(caps) = re.captures(input) {
        let number = caps
            .get(1)
            .and_then(|m| m.as_str().parse::<u64>().ok())
            .map_or(Scalar::from(1), Scalar::from); // 如果没有数字，默认为1

        let variables = caps.get(2).map_or(vec![], |m| {
            m.as_str()
                .split('*')
                .filter(|s| !s.is_empty()) // 过滤掉空字符串
                .map(String::from)
                .collect()
        });

        return Some((number, variables));
    }

    None
}

pub fn split_expression(expr: &str) -> Vec<String> {
    let no_plus_expr = expr.replace("+", ""); // 首先移除表达式中所有的加号
    no_plus_expr
        .split_whitespace() // 然后按空格分割
        .map(String::from)
        .collect()
}

pub trait Rlc {
    fn rlc(&self, other: &Self) -> Self;
}
impl Rlc for Scalar {
    fn rlc(&self, other: &Self) -> Self {
        self + other * Scalar::from(3) + Scalar::from(4)
    }
}
impl Rlc for Polynomial {
    fn rlc(&self, other: &Self) -> Self {
        //polynomial_self + polynomial_other * 3 + 4

        self.clone() + other.clone() * Scalar::from(3) + Scalar::from(4)
    }
}

#[cfg(test)]
mod tests {

    use crate::utils::{extract_number_and_variable, split_expression};
    use bls12_381::Scalar;

    use super::root_of_unity;
    #[test]
    fn test_extract_number_and_variable() {
        //passed
        //2*a*b + 3*a + 53*b + 46 - 45*c == 0

        let examples = vec!["46", "2*a*b", "45*c", "53*bc", "ab", "a*b"];

        for (i, example) in examples.iter().enumerate() {
            let res = extract_number_and_variable(example).unwrap();
            match i {
                0 => assert_eq!(res, (Scalar::from(46), vec![])),
                1 => assert_eq!(
                    res,
                    (Scalar::from(2), vec!["a".to_string(), "b".to_string()])
                ),
                // 2 => {
                //     println!("a:{:?}", res);
                //     assert_eq!(res, (Some(Scalar::from(3)), vec!["a".to_string()]))
                // }
                2 => {
                    assert_eq!(res, (Scalar::from(45), vec!["c".to_string()]))
                }
                3 => assert_eq!(res, (Scalar::from(53), vec!["bc".to_string()])),
                4 => {
                    assert_eq!(res, (Scalar::from(1), vec!["ab".to_string()]))
                }
                5 => {
                    assert_eq!(
                        res,
                        (Scalar::from(1), vec!["a".to_string(), "b".to_string()])
                    )
                }
                _ => (),
            }
        }
    }
    #[test]
    fn test_split_expression() {
        //passed
        //45*c <== 2*a*b + 3*a + 53*b + 46
        let test_str = "45*c <== 2*a*b + 3*a + 53*b + -46";
        assert_eq!(
            split_expression(test_str),
            vec![
                "45*c".to_string(),
                "<==".to_string(),
                "2*a*b".to_string(),
                "3*a".to_string(),
                "53*b".to_string(),
                "-46".to_string()
            ]
        );
    }

    #[test]
    fn test_root_of_unity() {
        let root_of_unity = root_of_unity(4);
        assert_eq!(root_of_unity.pow(&[4, 0, 0, 0]), Scalar::from(1));
    }
}
