use std::collections::HashMap;

use baby_plonk_rust::{
    assembly::AssemblyEqn,
    program::Program,
    setup::Setup,
    verifier::{Proof, Verifier},
    prover::Prover,
};
use bls12_381::Scalar;

#[test]
fn verify_proof_test() {
    //从1到tau^7*g1, tau = 1
    let setup = Setup::generate_srs(8, Scalar::from(1));

    //程序为：
    //c <== a*b
    //b <== a + d
    let constraints: Vec<_> = vec!["c <== a*b + a", "b <== a + d"]
        .into_iter()
        .map(AssemblyEqn::eq_to_assembly)
        .collect();

    println!("constraints:{:?}", constraints);

    //ql * a(x) + qr*b(x) + qm*a(x)*b(x) + qo*c(x) + qc=0
    // assert_eq!(constraints[0].wires.L, Some("a".to_string()));
    // assert_eq!(constraints[0].wires.R, Some("b".to_string()));
    // assert_eq!(constraints[0].wires.O, Some("c".to_string()));
    // assert_eq!(constraints[0].coeffs.L, Scalar::zero());
    // assert_eq!(constraints[0].coeffs.R, Scalar::zero());
    // assert_eq!(constraints[0].coeffs.M, Scalar::one());
    // assert_eq!(constraints[0].coeffs.O, Scalar::one().neg());
    // assert_eq!(constraints[0].coeffs.C, Scalar::zero());

    let program = Program::new(constraints, 8);
    let mut prover = Prover::new(setup.clone(), program.clone());

    let mut witness: HashMap<String, Scalar> = HashMap::new();
    witness.insert("a".to_owned(), Scalar::from(3));
    witness.insert("b".to_owned(), Scalar::from(5));
    witness.insert("c".to_owned(), Scalar::from(18));
    witness.insert("d".to_owned(), Scalar::from(2));

    let (a_1, b_1, c_1) = prover.round_1(witness);
    let z_1 = prover.round_2();
    let (t_lo_1, t_mid_1, t_hi_1) = prover.round_3();
    let (a_bar, b_bar, c_bar, s1_bar, s2_bar, z_omega_bar) = prover.round_4();
    let (w_zeta_1, w_zeta_omega_1) = prover.round_5();

    let proof = Proof {
        a_1,
        b_1,
        c_1,
        z_1,
        t_lo_1,
        t_mid_1,
        t_hi_1,
        w_zeta_1,
        w_zeta_omega_1,
        a_bar,
        b_bar,
        c_bar,
        s1_bar,
        s2_bar,
        z_omega_bar,
    };

    let mut verifier = Verifier::new(setup, program, proof);

    assert_eq!(verifier.verify(), true);
}
