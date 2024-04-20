use crate::utils::{find_next_power_of_two, i_ntt_381, ntt_381, roots_of_unity};
use bls12_381::Scalar;
use std::{
    clone, iter,
    ops::{Add, Div, Mul, Sub},
};
#[derive(Debug, Clone, PartialEq, Copy)]
pub enum Basis {
    Lagrange,
    Monomial,
}

#[derive(PartialEq, Debug, Clone)]
pub struct Polynomial {
    pub values: Vec<Scalar>,
    pub basis: Basis,
}
impl Polynomial {
    pub fn new(values: Vec<Scalar>, basis: Basis) -> Polynomial {
        Polynomial { values, basis }
    }
    pub fn shift_left(&mut self, n: usize) -> Vec<Scalar> {
        assert_eq!(self.basis, Basis::Lagrange);
        let len = self.values.len();
        let n = n % len;
        let mut new_values = self.values.clone();
        for i in 0..len {
            // 重新排列值
            let new_index = (i + len - n) % len;
            new_values[new_index] = self.values[i].clone();
        }
        new_values
    }
    pub fn coeffs_evaluate(&self, x: Scalar) -> Scalar {
        assert_eq!(self.basis, Basis::Monomial);
        let mut cur_expo = 0u64;
        let mut res = Scalar::zero();
        //比如y = 1+3x+2x^2的self.values是:
        //[1,3,2]，第一个expo是0，依次加1
        for coeff in self.values.iter() {
            res += coeff * x.pow(&[cur_expo, 0, 0, 0]);
            cur_expo += 1;
        }
        res
    }
    ///系数到点值
    pub fn ntt(&self) -> Polynomial {
        assert_eq!(self.basis, Basis::Monomial);
        Polynomial::new(ntt_381(&self.values), Basis::Lagrange)
    }
    ///点值到系数
    pub fn i_ntt(&self) -> Polynomial {
        assert_eq!(self.basis, Basis::Lagrange);
        Polynomial::new(i_ntt_381(&self.values), Basis::Monomial)
    }
}
impl Add<Scalar> for Polynomial {
    type Output = Polynomial;
    fn add(self, rhs: Scalar) -> Self::Output {
        let mut new_values = self.values.clone();
        match self.basis {
            Basis::Monomial => {
                new_values[0] += rhs;
            }
            Basis::Lagrange => {
                for value in new_values.iter_mut() {
                    *value += rhs;
                }
            }
        }

        Polynomial::new(new_values, self.basis)
    }
}

impl Add for Polynomial {
    type Output = Polynomial;

    fn add(self, other: Self) -> Self::Output {
        assert_eq!(self.basis, other.basis, "Basis must be the same");

        match self.basis {
            //点值表示
            Basis::Lagrange => {
                assert_eq!(
                    self.values.len(),
                    other.values.len(),
                    "Polynomials must have the same length"
                );
                Polynomial {
                    values: self
                        .values
                        .iter()
                        .zip(other.values.iter())
                        .map(|(a, b)| a + b)
                        .collect(),
                    basis: self.basis,
                }
            }
            Basis::Monomial => {
                // 系数表示
                let max_len = std::cmp::max(self.values.len(), other.values.len());
                let mut result = vec![Scalar::from(0); max_len];
                for (i, value) in self.values.iter().enumerate() {
                    result[i] += value;
                }
                for (i, value) in other.values.iter().enumerate() {
                    result[i] += value;
                }
                Polynomial {
                    values: result,
                    basis: self.basis,
                }
            }
        }
    }
}

impl Sub<Scalar> for Polynomial {
    type Output = Polynomial;
    fn sub(self, rhs: Scalar) -> Self::Output {
        let mut new_values = self.values.clone();
        if self.basis == Basis::Monomial {
            new_values[0] -= rhs;
        } else {
            for value in new_values.iter_mut() {
                *value += rhs;
            }
        }
        Polynomial::new(new_values, self.basis)
    }
}

impl Sub for Polynomial {
    type Output = Polynomial;
    fn sub(self, other: Self) -> Self::Output {
        assert_eq!(self.basis, other.basis, "Basis must be the same");

        match self.basis {
            //点值表示
            Basis::Lagrange => {
                assert_eq!(
                    self.values.len(),
                    other.values.len(),
                    "Polynomials must have the same length"
                );
                Polynomial {
                    values: self
                        .values
                        .iter()
                        .zip(other.values.iter())
                        .map(|(a, b)| a - b)
                        .collect(),
                    basis: self.basis,
                }
            }
            Basis::Monomial => {
                // 系数表示
                let max_len = std::cmp::max(self.values.len(), other.values.len());
                let mut result = vec![Scalar::from(0); max_len];
                for (i, value) in self.values.iter().enumerate() {
                    result[i] += value;
                }
                for (i, value) in other.values.iter().enumerate() {
                    result[i] -= value;
                }
                Polynomial {
                    values: result,
                    basis: self.basis,
                }
            }
        }
    }
}

impl Mul<Scalar> for Polynomial {
    type Output = Polynomial;
    fn mul(self, other: Scalar) -> Self::Output {
        let mut new_values = Vec::new();

        for value in self.values.iter() {
            new_values.push(*value * other);
        }

        Polynomial::new(new_values, self.basis)
    }
}

impl Mul for Polynomial {
    type Output = Polynomial;
    fn mul(self, other: Self) -> Self::Output {
        assert_eq!(self.basis, other.basis, "Basis must be the same");
        // let mut new_group_order;
        // let mut self_coeff;
        // let mut other_coeff;

        // match self.basis {
        //     Basis::Monomial => {
        //         let n = self.values.len() - 1; //阶等于系数个数-1
        //         let m = other.values.len() - 1;
        //         new_group_order = find_next_power_of_two(n, m);

        //         self_coeff = self.clone();
        //         other_coeff = other.clone();
        //     }
        //     Basis::Lagrange => {
        //         new_group_order = 2 * self.values.len();
        //         self_coeff = Polynomial::new(i_ntt_381(&self.values), Basis::Monomial);
        //         other_coeff = Polynomial::new(i_ntt_381(&other.values), Basis::Monomial);
        //     }
        // }
        // let new_roots_of_unity: Vec<Scalar> = roots_of_unity(new_group_order as u64);

        // let mut new_self_values = vec![Scalar::zero(); new_group_order];
        // let mut new_other_values = vec![Scalar::zero(); new_group_order];
        // for (i, x) in new_roots_of_unity.iter().enumerate() {
        //     new_self_values[i] = self_coeff.coeffs_evaluate(*x);
        //     new_other_values[i] = other_coeff.coeffs_evaluate(*x);
        // }

        // let product_lagrange_values: Vec<_> = new_self_values
        //     .iter()
        //     .zip(new_other_values.iter())
        //     .map(|(v1, v2)| v1 * v2)
        //     .collect();

        // match self.basis {
        //     Basis::Monomial => {
        //         let n = self.values.len() - 1; //阶等于系数个数-1
        //         let m = other.values.len() - 1;

        //         let product_monomial_values = i_ntt_381(&product_lagrange_values);

        //         Polynomial::new(product_monomial_values[0..=n + m].to_vec(), Basis::Monomial)
        //     }

        //     Basis::Lagrange => Polynomial::new(product_lagrange_values, Basis::Lagrange),
        // }

        match self.basis {
            Basis::Monomial => {
                //系数形式

                //设self的阶为n，对应n+1个点；other的阶为m，对应m+1个点
                //乘积多项式阶为n+m，对应n+m+1个点
                //所以需要有一个阶大于等于n+m+1的roots of unity，并且roots of unity的阶需要是2的次幂

                let n = self.values.len() - 1; //阶等于系数个数-1
                let m = other.values.len() - 1;
                let new_group_order = find_next_power_of_two(n, m);

                let new_roots_of_unity: Vec<Scalar> = roots_of_unity(new_group_order as u64);

                //对self和other这两个多项式在new_roots_of_unity求值
                let mut new_self_values = vec![Scalar::zero(); new_group_order];
                let mut new_other_values = vec![Scalar::zero(); new_group_order];
                for (i, x) in new_roots_of_unity.iter().enumerate() {
                    new_self_values[i] = self.coeffs_evaluate(*x);
                    new_other_values[i] = other.coeffs_evaluate(*x);
                }

                let product_lagrange_values: Vec<_> = new_self_values
                    .iter()
                    .zip(new_other_values.iter())
                    .map(|(v1, v2)| v1 * v2)
                    .collect();

                //product_values的阶为new_group_order（第一个大于等于n+m+1的2的次幂）。但是期望的系数多项式的阶为n+m，系数个数为n+m+1

                let product_monomial_values = i_ntt_381(&product_lagrange_values);

                Polynomial::new(product_monomial_values[0..=n + m].to_vec(), Basis::Monomial)
            }
            Basis::Lagrange => {
                todo!()
                // //n * n的点值表示,得到的系数表示为2n-2次
                // //也就是 n 个点要扩展成2n-1个点，已有 n 个点，需要再有 n-1个点
                // //先转化为系数表示，2nlogn
                // //然后求 2n 个评估，复杂度为 n
                // //然后对应点相乘，复杂度为 n
                // //然后再 转换成点值，复杂度为 2nlog2n
                // //总复杂度为2nlog2n

                // //1.先将两个n个点的点值多项式扩展成2n-1个点
                // let self_coeff = Polynomial::new(i_ntt_381(&self.values), Basis::Monomial);
                // let other_coeff = Polynomial::new(i_ntt_381(&other.values), Basis::Monomial);

                // let n = self.values.len();
                // let new_group_order = 2 * n;

                // let new_roots_of_unity: Vec<Scalar> = roots_of_unity(new_group_order as u64);

                // //对self和other这两个多项式在new_roots_of_unity求值
                // let mut new_self_values = vec![Scalar::zero(); new_group_order];
                // let mut new_other_values = vec![Scalar::zero(); new_group_order];
                // for (i, x) in new_roots_of_unity.iter().enumerate() {
                //     new_self_values[i] = self_coeff.coeffs_evaluate(*x);
                //     new_other_values[i] = other_coeff.coeffs_evaluate(*x);
                // }
                // let product_lagrange_values: Vec<_> = new_self_values
                //     .iter()
                //     .zip(new_other_values.iter())
                //     .map(|(v1, v2)| v1 * v2)
                //     .collect();
                // Polynomial::new(product_lagrange_values, Basis::Lagrange)

                // //2.然后将新的点值多项式相乘
                // //3.把结果多项式转换成点值表示
            }
        }
    }
}

impl Div for Polynomial {
    type Output = Polynomial;
    fn div(self, other: Self) -> Self::Output {
        assert_eq!(self.basis, other.basis, "Basis must be the same");

        assert_eq!(self.basis, Basis::Monomial);

        let mut c1 = self.values;
        let mut c2 = other.values;

        //c1 / c2

        // 移除c1和c2尾部的0
        while let Some(&last) = c1.last() {
            if last == Scalar::zero() {
                c1.pop();
            } else {
                break;
            }
        }

        while let Some(&last) = c2.last() {
            if last == Scalar::zero() {
                c2.pop();
            } else {
                break;
            }
        }

        if c2.last() == Some(&Scalar::zero()) {
            println!("c2:{:?}", c2);
            panic!("Division by zero polynomial");
        }

        let mut q = Vec::new();
        let mut r = c1;

        while r.len() >= c2.len() && *r.last().unwrap() != Scalar::zero() {
            let coeff = r.last().unwrap() * c2.last().unwrap().invert().unwrap();
            let degree_diff = r.len() - c2.len();
            let mut term = vec![Scalar::zero(); degree_diff];
            term.push(coeff.clone());

            // 生成subtrahend多项式
            let subtrahend: Vec<Scalar> = iter::repeat(Scalar::zero())
                .take(degree_diff)
                .chain(c2.iter().map(|ci| *ci * coeff.clone()))
                .collect();

            // 计算新的余数
            r = r
                .iter()
                .zip(subtrahend.iter().chain(iter::repeat(&Scalar::zero())))
                .map(|(a, b)| *a - b)
                .collect();

            // 移除余数的前导零
            while r.last() == Some(&Scalar::zero()) {
                r.pop();
            }

            // 更新商
            q.insert(0, coeff); // 直接在前面插入，避免之后的反转
        }
        Polynomial::new(q, Basis::Monomial)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_monomial_add() {
        //passed
        //monomial意思是系数表示
        let p1 = Polynomial::new(vec![Scalar::from(1), Scalar::from(2)], Basis::Monomial);
        let p2 = Polynomial::new(vec![Scalar::from(3), Scalar::from(4)], Basis::Monomial);
        let p3 = Polynomial::new(vec![Scalar::from(4), Scalar::from(6)], Basis::Monomial);
        assert_eq!(p1.clone() + p2.clone(), p3);

        let p1 = Polynomial::new(
            vec![Scalar::from(1), Scalar::from(2), Scalar::from(2)],
            Basis::Monomial,
        );
        let p2 = Polynomial::new(vec![Scalar::from(3), Scalar::from(4)], Basis::Monomial);
        let p3 = Polynomial::new(
            vec![Scalar::from(4), Scalar::from(6), Scalar::from(2)],
            Basis::Monomial,
        );
        assert_eq!(p1.clone() + p2.clone(), p3);
    }

    #[test]
    fn test_lagrange_add() {
        //passed
        //lagrange意思是点值表示
        let p1 = Polynomial::new(vec![Scalar::from(1), Scalar::from(2)], Basis::Lagrange);
        let p2 = Polynomial::new(vec![Scalar::from(3), Scalar::from(4)], Basis::Lagrange);
        let p3 = Polynomial::new(vec![Scalar::from(4), Scalar::from(6)], Basis::Lagrange);
        assert_eq!(p1.clone() + p2.clone(), p3);
    }

    #[test]
    fn test_monomial_sub() {
        //monomial意思是系数表示
        let p1 = Polynomial::new(vec![Scalar::from(3), Scalar::from(4)], Basis::Monomial);
        let p2 = Polynomial::new(vec![Scalar::from(1), Scalar::from(2)], Basis::Monomial);
        let p3 = Polynomial::new(vec![Scalar::from(2), Scalar::from(2)], Basis::Monomial);
        assert_eq!(p1.clone() - p2.clone(), p3);
    }

    #[test]
    fn test_poly_scalar_mul() {
        //passed
        //monomial意思是系数表示
        let p1 = Polynomial::new(vec![Scalar::from(1), Scalar::from(2)], Basis::Monomial);
        let scalar = Scalar::from(3);
        let p3 = Polynomial::new(vec![Scalar::from(3), Scalar::from(6)], Basis::Monomial);
        assert_eq!(p1.clone() * scalar, p3);
    }

    #[test]
    fn test_monomial_poly_poly_mul() {
        //passed
        //monomial意思是系数表示
        //p1 = 1 + x = [1,1]
        //p2 = 1 + x = [1,1]
        //expected result = 1 + 2x + x^2 = [1,2,1]
        let p1 = Polynomial::new(vec![Scalar::from(1), Scalar::from(1)], Basis::Monomial);

        let p2 = Polynomial::new(vec![Scalar::from(1), Scalar::from(1)], Basis::Monomial);
        let expected_product = Polynomial::new(
            vec![Scalar::from(1), Scalar::from(2), Scalar::from(1)],
            Basis::Monomial,
        );
        assert_eq!(p1 * p2, expected_product);
    }

    #[test]

    // c1 = (1,2,3)
    // c2 = (3,2,1)
    // c1 / c2 = (array([3.]), array([-8., -4.]))

    // c1 = x^2 - 1 = [-1,0,1,0,0,0]
    // c2 = x+1 = [1,1,0,0]
    // c1 / c2 = x-1 = [-1,1]
    fn test_monomial_div() {
        //monomial意思是系数表示
        //passed!
        let p1 = Polynomial::new(
            vec![
                Scalar::from(1).neg(),
                Scalar::from(0),
                Scalar::from(1),
                Scalar::zero(),
                Scalar::zero(),
                Scalar::zero(),
            ],
            Basis::Monomial,
        );
        let p2 = Polynomial::new(
            vec![
                Scalar::from(1),
                Scalar::from(1),
                Scalar::zero(),
                Scalar::zero(),
            ],
            Basis::Monomial,
        );

        assert_eq!(
            p1.clone() / p2.clone(),
            Polynomial::new(
                vec![Scalar::from(1).neg(), Scalar::from(1)],
                Basis::Monomial
            )
        );

        let p1 = Polynomial::new(
            vec![Scalar::from(1).neg(), Scalar::from(2), Scalar::from(3)],
            Basis::Monomial,
        );
        let p2 = Polynomial::new(
            vec![Scalar::from(3), Scalar::from(2), Scalar::from(1)],
            Basis::Monomial,
        );

        assert_eq!(
            p1.clone() / p2.clone(),
            Polynomial::new(vec![Scalar::from(3)], Basis::Monomial)
        );

        let p1 = Polynomial::new(
            vec![Scalar::from(1).neg(), Scalar::from(0), Scalar::from(1)],
            Basis::Monomial,
        );
        let p2 = Polynomial::new(vec![Scalar::from(1), Scalar::from(1)], Basis::Monomial);

        assert_eq!(
            p1.clone() / p2.clone(),
            Polynomial::new(
                vec![Scalar::from(1).neg(), Scalar::from(1)],
                Basis::Monomial
            )
        );
    }
    #[test]
    fn test_lagrange_div() {
        //c1 = [2,2] 次数为1
        //c2 = [1,1] 次数为1
        //c1 / c2 = [1,1]
        //

        let p1 = Polynomial::new(
            vec![Scalar::from(3), Scalar::from(6), Scalar::from(9)],
            Basis::Lagrange,
        );
        let p2 = Polynomial::new(
            vec![Scalar::from(1), Scalar::from(2), Scalar::from(3)],
            Basis::Lagrange,
        );
        assert_eq!(
            p1 / p2,
            Polynomial::new(vec![Scalar::from(3)], Basis::Lagrange)
        );
        let p1 = Polynomial::new(vec![Scalar::from(4), Scalar::from(2)], Basis::Lagrange);
        let p2 = Polynomial::new(vec![Scalar::from(2)], Basis::Lagrange);
        assert_eq!(
            p1 / p2,
            Polynomial::new(vec![Scalar::from(2), Scalar::from(1)], Basis::Lagrange)
        );
    }

    #[test]
    fn test_coeffs_evaluate() {
        //passed
        //1+3x+2x^2
        let p = Polynomial::new(
            vec![Scalar::from(1), Scalar::from(3), Scalar::from(2)],
            Basis::Monomial,
        );
        let x = Scalar::from(1);
        assert_eq!(p.coeffs_evaluate(x), Scalar::from(6));
    }
}
