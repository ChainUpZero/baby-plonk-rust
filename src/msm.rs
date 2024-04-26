use bls12_381::{G1Projective, Scalar};
use group::{
    ff::{Field, PrimeField},
    Group,
};

use rand::{rngs::StdRng, SeedableRng};
pub struct BucketMSM {}
impl BucketMSM {
    fn generate_random_points_and_scalars(num_pairs: usize) -> (Vec<G1Projective>, Vec<Scalar>) {
        // create random points in G1 and random scalars
        let mut rng = StdRng::seed_from_u64(12345);

        let points = (0..num_pairs)
            .map(|_| G1Projective::random(&mut rng)) // generate random points in G1
            .collect::<Vec<_>>();

        let scalars = (0..num_pairs)
            .map(|_| Scalar::random(&mut rng)) // generate random scalars in G1
            .collect::<Vec<_>>();
        (points, scalars)
    }
    fn c_bit_msm(points: &[G1Projective], scalars: &[u64], c: usize) -> G1Projective {
        // use 2^c - 1 buckets
        let num_buckets = (1 << c) - 1;
        let mut buckets = vec![G1Projective::identity(); num_buckets];

        // put points into correct buckets
        for (point, scalar) in points.iter().zip(scalars.iter()) {
            //scalar.to_bytes方法是小端序，低位存放在低位
            let scalar_value = *scalar as usize; // scalar is generally quite small.
            if scalar_value != 0 {
                buckets[scalar_value - 1] += point;
            }
        }
        let a = Scalar::ROOT_OF_UNITY;
        let mut accumulator = G1Projective::identity();

        let mut result = G1Projective::identity();

        //iterate reverselly
        for bucket in buckets.into_iter().rev() {
            accumulator += bucket;

            result += &accumulator;
        }

        result
    }

    fn bools_to_u64(bools: &[bool]) -> u64 {
        let mut result = 0u64;
        let len = bools.len();
        for (index, &value) in bools.iter().enumerate() {
            if value {
                // 设置对应的位为1
                result |= 1 << (len - 1 - index);
            }
            // 如果值为false，对应位已经是0，无需操作
        }
        result
    }

    fn u8_to_bool_array(input: &[u8]) -> Vec<bool> {
        let mut result = Vec::new();
        for &byte in input {
            // 遍历每一位
            for i in 0..8 {
                // 检查当前位是否为1，将结果转换为bool，并添加到结果向量中
                // 通过将1左移i位，然后与当前字节进行按位与操作，如果结果不为0，则当前位为1
                result.push(byte & (1 << (7 - i)) != 0);
            }
        }
        result
    }
    pub fn bucket_msm(
        points: &[G1Projective],
        scalars: &[Scalar],
        b: usize,
        c: usize,
    ) -> G1Projective {
        //scalars = a1,a2,a3 ... an

        let k = b / c;

        //result of
        let mut t_points: Vec<G1Projective> = Vec::new();

        //compute Ti for i = 0..k
        for i in 0..k {
            let mut scalars_c_bits = vec![0; scalars.len()];
            for (j, scalar) in scalars.iter().enumerate() {
                //example:
                //scalar == 010 011 001 100
                //get_c_bit_chunk(scalar,0,3) return 010
                //get_c_bit_chunk(scalar,1,3) return 011
                let c_bit_chunk = Self::get_c_bit_chunk(scalar, i, c);
                scalars_c_bits[j] = c_bit_chunk;
            }
            //

            // now scalars_c_bits = vectors of coefficient in Ti
            // use c_bit_msm to compute Ti and push Ti in to t_points array
            t_points.push(Self::c_bit_msm(points, &scalars_c_bits, c));
        }

        let mut result = t_points[0];

        //use T1,T2,...,Tk to compute T
        for j in 1..k {
            for _ in 0..c {
                result = result.double(); // double c times
            }
            result += &t_points[j];
        }

        result
    }
    fn get_c_bit_chunk(scalar: &Scalar, chunk_index: usize, chunk_size: usize) -> u64 {
        // compute the c-bit start bit and end bit index
        let start_bit = chunk_index * chunk_size;
        let end_bit = start_bit + chunk_size;

        // convert the scalar to big endian
        //but scalar.to_bytes 是小端序，把他reverse到大端序
        let mut bytes: [u8; 32] = scalar.to_bytes();

        bytes.reverse();

        let bits = Self::u8_to_bool_array(&bytes);

        //get the desired chunk
        let chunk_bits = bits[start_bit..end_bit].to_vec();

        //convert chunk_bits to appropraite representation in Fr
        let res: u64 = Self::bools_to_u64(&chunk_bits);

        res
    }
}
