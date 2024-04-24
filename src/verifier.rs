use bls12_381::{pairing, G1Projective, G2Affine, Scalar};
use merlin::Transcript;

use crate::{
    polynomial::{Basis, Polynomial},
    program::Program,
    setup::Setup,
    transcript::PlonkTranscript,
    utils::{i_ntt_381, root_of_unity, Rlc},
};

pub struct VerifierPreprocessedInput {
    qm_1: G1Projective,
    ql_1: G1Projective,
    qr_1: G1Projective,
    qo_1: G1Projective,
    qc_1: G1Projective,
    s1_1: G1Projective,
    s2_1: G1Projective,
    s3_1: G1Projective,
    x_2: G2Affine,
}
#[derive(Clone, Copy)]
pub struct Proof {
    pub a_1: G1Projective,
    pub b_1: G1Projective,
    pub c_1: G1Projective,
    pub z_1: G1Projective,
    pub t_lo_1: G1Projective,
    pub t_mid_1: G1Projective,
    pub t_hi_1: G1Projective,
    pub w_zeta_1: G1Projective,
    pub w_zeta_omega_1: G1Projective,
    pub a_bar: Scalar,
    pub b_bar: Scalar,
    pub c_bar: Scalar,
    pub s1_bar: Scalar,
    pub s2_bar: Scalar,
    pub z_omega_bar: Scalar,
}
pub struct Verifier {
    verifier_preprocessed_input: VerifierPreprocessedInput,
    proof: Proof,
    group_order: u64,
    k1: Scalar,
    k2: Scalar,
}
impl Verifier {
    pub fn new(setup: Setup, program: Program, proof: Proof) -> Verifier {
        let common_preprocessed_input = program.common_preprocessed_input();
        let ql = common_preprocessed_input.ql;
        let qr = common_preprocessed_input.qr;
        let qm = common_preprocessed_input.qm;
        let qo = common_preprocessed_input.qo;
        let qc = common_preprocessed_input.qc;
        let s1 = common_preprocessed_input.s1;
        let s2 = common_preprocessed_input.s2;
        let s3 = common_preprocessed_input.s3;

        let verifier_preprocessed_input = VerifierPreprocessedInput {
            ql_1: setup.commit(&Polynomial::new(i_ntt_381(&ql.values), Basis::Monomial)),
            qr_1: setup.commit(&Polynomial::new(i_ntt_381(&qr.values), Basis::Monomial)),
            qm_1: setup.commit(&Polynomial::new(i_ntt_381(&qm.values), Basis::Monomial)),
            qo_1: setup.commit(&Polynomial::new(i_ntt_381(&qo.values), Basis::Monomial)),
            qc_1: setup.commit(&Polynomial::new(i_ntt_381(&qc.values), Basis::Monomial)),
            s1_1: setup.commit(&Polynomial::new(i_ntt_381(&s1.values), Basis::Monomial)),
            s2_1: setup.commit(&Polynomial::new(i_ntt_381(&s2.values), Basis::Monomial)),
            s3_1: setup.commit(&Polynomial::new(i_ntt_381(&s3.values), Basis::Monomial)),
            x_2: setup.x_2.into(),
        };

        Verifier {
            verifier_preprocessed_input,
            proof,
            group_order: program.group_order,
            k1: Scalar::from(2),
            k2: Scalar::from(3),
        }
    }
    pub fn verify(&mut self) -> bool {
        println!("Verification started...");
        //step 4
        let (beta, gamma, alpha, zeta, nu, mu) = self.compute_challengs(self.proof);

        //step 5
        let z_h_zeta = zeta.pow(&[self.group_order, 0, 0, 0]) - Scalar::one();

        //step 6
        let omega = root_of_unity(self.group_order);
        let n = Scalar::from(self.group_order);
        let l_1_zeta = omega * (z_h_zeta) * (n * (zeta - omega)).invert().unwrap();

        //step 7
        //todo

        //step 8
        let a_bar = self.proof.a_bar;
        let s1_bar = self.proof.s1_bar;
        let b_bar = self.proof.b_bar;
        let s2_bar = self.proof.s2_bar;
        let c_bar = self.proof.c_bar;
        let z_omega_bar = self.proof.z_omega_bar;
        // ?疑点
        let r_0 = Scalar::zero()
            - l_1_zeta * alpha * alpha
            - alpha
                * (a_bar.rlc(&s1_bar, beta, gamma))
                * (b_bar.rlc(&s2_bar, beta, gamma))
                * (c_bar + gamma)
                * z_omega_bar;

        //step 9
        let qm_1 = self.verifier_preprocessed_input.qm_1;
        let ql_1 = self.verifier_preprocessed_input.ql_1;
        let qr_1 = self.verifier_preprocessed_input.qr_1;
        let qo_1 = self.verifier_preprocessed_input.qo_1;
        let qc_1 = self.verifier_preprocessed_input.qc_1;

        let z_1 = self.proof.z_1;
        let s3_1 = self.verifier_preprocessed_input.s3_1;

        let t_lo_1 = self.proof.t_lo_1;
        let t_mid_1 = self.proof.t_mid_1;
        let t_hi_1 = self.proof.t_hi_1;

        let d_1_1 = a_bar * b_bar * qm_1 + a_bar * ql_1 + b_bar * qr_1 + c_bar * qo_1 + qc_1;
        let d_1_2 = (a_bar.rlc(&zeta, beta, gamma)
            * b_bar.rlc(&(self.k1 * zeta), beta, gamma)
            * c_bar.rlc(&(self.k2 * zeta), beta, gamma)
            * alpha
            + l_1_zeta * alpha * alpha
            + mu)
            * z_1;
        let d_1_3 = a_bar.rlc(&s1_bar, beta, gamma)
            * b_bar.rlc(&s2_bar, beta, gamma)
            * alpha
            * beta
            * z_omega_bar
            * s3_1;
        let d_1_4 = z_h_zeta
            * (t_lo_1
                + zeta.pow(&[self.group_order, 0, 0, 0]) * t_mid_1
                + zeta.pow(&[2 * self.group_order, 0, 0, 0]) * t_hi_1);

        let d_1 = d_1_1 + d_1_2 - d_1_3 - d_1_4;

        //step 10
        let a_1 = self.proof.a_1;
        let b_1 = self.proof.b_1;
        let c_1 = self.proof.c_1;
        let s1_1 = self.verifier_preprocessed_input.s1_1;
        let s2_1 = self.verifier_preprocessed_input.s2_1;

        let f_1 = d_1
            + nu * a_1
            + nu.pow(&[2, 0, 0, 0]) * b_1
            + nu.pow(&[3, 0, 0, 0]) * c_1
            + nu.pow(&[4, 0, 0, 0]) * s1_1
            + nu.pow(&[5, 0, 0, 0]) * s2_1;

        //step 11
        let e_1 = (nu * a_bar
            + nu.pow(&[2, 0, 0, 0]) * b_bar
            + nu.pow(&[3, 0, 0, 0]) * c_bar
            + nu.pow(&[4, 0, 0, 0]) * s1_bar
            + nu.pow(&[5, 0, 0, 0]) * s2_bar
            + mu * z_omega_bar
            - r_0)
            * G1Projective::generator();

        //step 12
        let w_zeta_1 = self.proof.w_zeta_1;
        let w_zeta_omega_1 = self.proof.w_zeta_omega_1;

        let x_2 = self.verifier_preprocessed_input.x_2;

        pairing(&(w_zeta_1 + mu * w_zeta_omega_1).into(), &x_2)
            == pairing(
                &(zeta * w_zeta_1 + mu * zeta * omega * w_zeta_omega_1 + f_1 - e_1).into(),
                &G2Affine::generator(),
            )
    }
    fn compute_challengs(&self, proof: Proof) -> (Scalar, Scalar, Scalar, Scalar, Scalar, Scalar) {
        let mut transcript = Transcript::new(b"plonk");

        let (beta, gamma) = transcript.round_1(proof.a_1, proof.b_1, proof.c_1);
        let alpha = transcript.round_2(proof.z_1);
        let zeta = transcript.round_3(proof.t_lo_1, proof.t_mid_1, proof.t_hi_1);
        let nu = transcript.round_4(
            proof.a_bar,
            proof.b_bar,
            proof.c_bar,
            proof.s1_bar,
            proof.s2_bar,
            proof.z_omega_bar,
        );
        let mu = transcript.round_5(proof.w_zeta_1, proof.w_zeta_omega_1);
        (beta, gamma, alpha, zeta, nu, mu)
    }
}

#[cfg(test)]
mod tests {

    use bls12_381::G1Affine;

    use super::*;

    #[test]
    fn test_pairing() {
        //2*3 = 6*1

        assert_eq!(
            pairing(
                &(G1Affine::generator() * Scalar::from(2)).into(),
                &(Scalar::from(3) * G2Affine::generator()).into()
            ),
            pairing(
                &(Scalar::from(6) * G1Affine::generator()).into(),
                &G2Affine::generator()
            )
        )
    }
}
