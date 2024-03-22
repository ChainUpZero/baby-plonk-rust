use bls12_381::Scalar;
use regex::Regex;
pub fn extract_number_and_variable(input: &str) -> Option<(Option<Scalar>, Vec<String>)> {
    let re = Regex::new(r"^(-?\d+)((\*[a-zA-Z]+)*)|([a-zA-Z]+(\*[a-zA-Z]+)*)$").unwrap();
    if let Some(caps) = re.captures(input) {
        let number = caps
            .get(1)
            .and_then(|m| m.as_str().parse::<u64>().ok())
            .map(Scalar::from);
        let variables = caps.get(2).map_or_else(
            || vec![],
            |m| m.as_str().split('*').skip(1).map(String::from).collect(),
        );

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
#[cfg(test)]
mod tests {

    use crate::utils::{extract_number_and_variable, split_expression};

    #[test]
    fn test_extract_number_and_variable() {
        //2*a*b + 3*a + 53*b + 46 - 45*c == 0

        let examples = vec!["46", "2*a*b", "3*a", "-45*c", "53*bc"];

        for example in examples {
            match extract_number_and_variable(example) {
                Some((coeffs, variables)) => println!(
                    "'{}' contains number {:?} and variables {:?}",
                    example, coeffs, variables
                ),
                Some((None, variables)) => {
                    println!("'{}' only contains variables {:?}", example, variables)
                }
                None => println!("'{}' did not match the pattern.", example),
            }
        }
    }
    #[test]
    fn test_split_expression() {
        //45*c <== 2*a*b + 3*a + 53*b + 46
        let test_str = "45*c <== 2*a*b + 3*a + 53*b + 46";

        println!(
            "convert {:?} to: {:?}",
            test_str,
            split_expression(test_str)
        );
    }
}
