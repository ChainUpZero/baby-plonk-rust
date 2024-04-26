use std::collections::HashMap;
use std::time::Instant;

use baby_plonk_rust::{
    assembly::AssemblyEqn,
    program::Program,
    prover::Prover,
    setup::Setup,
    verifier::{Proof, Verifier},
};
use bls12_381::Scalar;

#[test]
fn verify_proof_test() {
    //从1到tau^7*g1, tau = 1
    let setup = Setup::generate_srs(8 + 6, Scalar::from(10));

    //程序为：
    //c <== a * b
    //b <== a + d
    let constraints: Vec<_> = vec!["e public", "c <== a * b + b", "e <== c * d"]
        .into_iter()
        .map(AssemblyEqn::eq_to_assembly)
        .collect();

    let program = Program::new(constraints, 8);

    let mut prover = Prover::new(setup.clone(), program.clone());

    let mut witness: HashMap<String, Scalar> = HashMap::new();
    witness.insert("a".to_owned(), Scalar::from(3));
    witness.insert("b".to_owned(), Scalar::from(4));
    witness.insert("c".to_owned(), Scalar::from(16));
    witness.insert("d".to_owned(), Scalar::from(5));
    witness.insert("e".to_owned(), Scalar::from(80));

    let prove_start = Instant::now();
    let proof = prover.prove(witness);
    let prove_duration = prove_start.elapsed();

    let mut verifier = Verifier::new(setup, program, proof);

    let verify_start = Instant::now();
    assert_eq!(verifier.verify(vec![Scalar::from(80)]), true);
    let verify_duration = verify_start.elapsed();

    println!("Verification passed");
    println!("Prove time: {:?}", prove_duration);
    println!("Verify time: {:?}", verify_duration);
}
