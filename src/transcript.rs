use bls12_381::{G1Affine, G1Projective, Scalar};
use merlin::Transcript;

pub trait PlonkTranscript {
    fn append_point(&mut self, label: &'static [u8], point: G1Projective);
    fn get_and_append_challenge(&mut self, label: &'static [u8]) -> Scalar;
    fn append_scalar(&mut self, label: &'static [u8], scalar: Scalar);
    fn round_1(
        &mut self,
        a_1: G1Projective,
        b_1: G1Projective,
        c_1: G1Projective,
    ) -> (Scalar, Scalar) {
        self.append_point(b"a_1", a_1);
        self.append_point(b"b_1", b_1);
        self.append_point(b"c_1", c_1);

        let beta = self.get_and_append_challenge(b"beta");
        let gamma = self.get_and_append_challenge(b"gamma");
        (beta, gamma)
    }
    fn round_2(&mut self, z_1: G1Projective) -> Scalar {
        self.append_point(b"z_1", z_1);
        let alpha = self.get_and_append_challenge(b"z_1");
        alpha
    }
    fn round_3(
        &mut self,
        t_lo_1: G1Projective,
        t_mid_1: G1Projective,
        t_hi_1: G1Projective,
    ) -> Scalar {
        self.append_point(b"t_lo_1", t_lo_1);
        self.append_point(b"t_mid_1", t_mid_1);
        self.append_point(b"t_hi_1", t_hi_1);
        let zeta = self.get_and_append_challenge(b"zeta");
        zeta
    }
    fn round_4(
        &mut self,
        a_bar: Scalar,
        b_bar: Scalar,
        c_bar: Scalar,
        s1_bar: Scalar,
        s2_bar: Scalar,
        z_omega_bar: Scalar,
    ) -> Scalar {
        self.append_scalar(b"a_eval", a_bar);
        self.append_scalar(b"b_eval", b_bar);
        self.append_scalar(b"c_eval", c_bar);
        self.append_scalar(b"s1_eval", s1_bar);
        self.append_scalar(b"s2_eval", s2_bar);
        self.append_scalar(b"z_shifted_eval", z_omega_bar);
        let nu = self.get_and_append_challenge(b"nu");
        nu
    }
    fn round_5(&mut self, w_zeta_1: G1Projective, w_zeta_omega_1: G1Projective) -> Scalar {
        self.append_point(b"w_zeta_1", w_zeta_1);
        self.append_point(b"w_zeta_omega_1", w_zeta_omega_1);
        let mu = self.get_and_append_challenge(b"mu");
        mu
    }
}

impl PlonkTranscript for Transcript {
    fn append_point(&mut self, label: &'static [u8], point: G1Projective) {
        let message = G1Affine::from(point).to_compressed();
        self.append_message(label, &message);
    }
    fn get_and_append_challenge(&mut self, label: &'static [u8]) -> Scalar {
        let mut challenge_scalar;
        loop {
            let mut challeng_bytes = [0u8; 32];
            self.challenge_bytes(label, &mut challeng_bytes);
            challenge_scalar = Scalar::from_bytes(&challeng_bytes);
            if challenge_scalar.is_some().into() && challenge_scalar.unwrap() != Scalar::zero() {
                self.append_message(label, &challeng_bytes);
                break;
            }
        }
        challenge_scalar.unwrap()
    }
    fn append_scalar(&mut self, label: &'static [u8], scalar: Scalar) {
        self.append_message(label, &scalar.to_bytes());
    }
}
#[cfg(test)]
mod tests {
    use merlin::Transcript;

    // #[test]
    // fn test_transcript() {
    //     let mut transcript = Transcript::new(b"plonk");
    //     let mut challeng_bytes1 = [0u8; 32];
    //     let mut challeng_bytes2 = [0u8; 32];

    //     transcript.challenge_bytes(b"1", &mut challeng_bytes1);

    //     transcript.challenge_bytes(b"1", &mut challeng_bytes2);
    //     println!("challeng_bytes1:{:?}", challeng_bytes1);
    //     println!("challeng_bytes2:{:?}", challeng_bytes2);
    //     assert_eq!(challeng_bytes1, challeng_bytes2);
    // }
}
