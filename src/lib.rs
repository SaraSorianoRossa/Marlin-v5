#![cfg_attr(not(feature = "std"), no_std)]
//! A crate for the Marlin preprocessing zkSNARK for R1CS.
//!
//! # Note
//!
//! Currently, Marlin only supports R1CS instances where the number of inputs
//! is the same as the number of constraints (i.e., where the constraint
//! matrices are square). Furthermore, Marlin only supports instances where the
//! public inputs are of size one less than a power of 2 (i.e., 2^n - 1).
#![deny(unused_import_braces, unused_qualifications, trivial_casts)]
#![deny(trivial_numeric_casts)]
#![deny(stable_features, unreachable_pub, non_shorthand_field_patterns)]
#![deny(unused_attributes, unused_imports, unused_mut)]
#![deny(renamed_and_removed_lints, stable_features, unused_allocation)]
#![deny(unused_comparisons, bare_trait_objects, unused_must_use)]
//#![forbid(unsafe_code)]

#[macro_use]
extern crate ark_std;

use ark_ff::{to_bytes, PrimeField, UniformRand};
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit_new::Evaluations;
use ark_poly_commit_new::{LabeledCommitment, PCUniversalParams, PolynomialCommitment};
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_std::rand::RngCore;
use digest::Digest;
use ark_poly::Polynomial;

use ark_std::{
    format,
    marker::PhantomData,
    string::{String, ToString},
    vec,
    vec::Vec,
};

#[cfg(not(feature = "std"))]
macro_rules! eprintln {
    () => {};
    ($($arg: tt)*) => {};
}

/// Implements a Fiat-Shamir based Rng that allows one to incrementally update
/// the seed based on new messages in the proof transcript.
pub mod rng;
use rng::FiatShamirRng;

mod error;
pub use error::*;

mod data_structures;
pub use data_structures::*;

/// Implements an Algebraic Holographic Proof (AHP) for the R1CS indexed relation.
pub mod ahp;
pub use ahp::AHPForR1CS;
use ahp::EvaluationsProvider;

#[cfg(test)]
mod test;

/// The compiled argument system.
pub struct Marlin<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>, D: Digest>(
    #[doc(hidden)] PhantomData<F>,
    #[doc(hidden)] PhantomData<PC>,
    #[doc(hidden)] PhantomData<D>,
);

impl<F: PrimeField, PC: PolynomialCommitment<F, DensePolynomial<F>>, D: Digest> Marlin<F, PC, D> {
    /// The personalization string for this protocol. Used to personalize the
    /// Fiat-Shamir rng.
    pub const PROTOCOL_NAME: &'static [u8] = b"MARLIN-2019";

    /// Generate the universal prover and verifier keys for the
    /// argument system.
    pub fn universal_setup<R: RngCore>(
        num_constraints: usize,
        num_variables: usize,
        num_non_zero: usize,
        rng: &mut R,
    ) -> Result<UniversalSRS<F, PC>, Error<PC::Error>> {
        let max_degree = AHPForR1CS::<F>::max_degree(num_constraints, num_variables, num_non_zero)?;
        let setup_time = start_timer!(|| {
            format!(
            "Marlin::UniversalSetup with max_degree {}, computed for a maximum of {} constraints, {} vars, {} non_zero",
            max_degree, num_constraints, num_variables, num_non_zero,
        )
        });

        let srs = PC::setup(max_degree, None, rng).map_err(Error::from_pc_err);
        end_timer!(setup_time);
        srs
    }

    /// Generate the index-specific (i.e., circuit-specific) prover and verifier
    /// keys. This is a deterministic algorithm that anyone can rerun.
    pub fn index<C: ConstraintSynthesizer<F>>(
        srs: &UniversalSRS<F, PC>,
        c: C,
    ) -> Result<(IndexProverKey<F, PC>, IndexVerifierKey<F, PC>, Vec<Vec<(F, usize)>>, Vec<Vec<(F, usize)>>, Vec<Vec<(F, usize)>>), Error<PC::Error>> {
        let index_time = start_timer!(|| "Marlin::Index");

        let index = AHPForR1CS::index(c)?;
        if srs.max_degree() < index.max_degree() {
            Err(Error::IndexTooLarge)?;
        }

        let coeff_support = AHPForR1CS::get_degree_bounds(&index.index_info);
        // Marlin only needs degree 2 random polynomials
        let supported_hiding_bound = 1;
        let (committer_key, verifier_key) = PC::trim(
            &srs,
            index.max_degree(),
            supported_hiding_bound,
            Some(&coeff_support),
        )
        .map_err(Error::from_pc_err)?;

        let commit_time = start_timer!(|| "Commit to index polynomials");
        let (index_comms, index_comm_rands): (_, _) =
            PC::commit(&committer_key, index.iter(), None).map_err(Error::from_pc_err)?;
        end_timer!(commit_time);

        let index_comms = index_comms
            .into_iter()
            .map(|c| c.commitment().clone())
            .collect();
        let index_vk = IndexVerifierKey {
            index_info: index.index_info,
            index_comms,
            verifier_key,
        };

        let index_pk = IndexProverKey {
            index,
            index_comm_rands,
            index_vk: index_vk.clone(),
            committer_key,
        };

        end_timer!(index_time);

        let pk = index_pk.clone();
        let matrix_a = pk.index.a;
        let matrix_b = pk.index.b;
        let matrix_c = pk.index.c;

        Ok((index_pk, index_vk, matrix_a, matrix_b, matrix_c))
    }

    /// Create a zkSNARK asserting that the constraint system is satisfied.
    pub fn prove<C: ConstraintSynthesizer<F>, R: RngCore>(
        index_pk: &IndexProverKey<F, PC>,
        c: C,
        zk_rng: &mut R,
    ) -> Result<(Proof<F, PC>, F, F, F, F, F, F, usize, usize), Error<PC::Error>> {
        let prover_time = start_timer!(|| "Marlin::Prover");

        // Add check that c is in the correct mode.
        let (prover_init_state, num_constraints, num_input_variables) = AHPForR1CS::prover_init(&index_pk.index, c)?;
        let public_input = prover_init_state.public_input();
        let mut fs_rng = FiatShamirRng::<D>::from_seed(
            &to_bytes![&Self::PROTOCOL_NAME, &index_pk.index_vk, &public_input].unwrap(),
        );

        // --------------------------------------------------------------------
        // First round (prover: compute z_A, z_B and w - verifier: compute etas)

        let (prover_first_msg, prover_first_oracles, prover_state) =
            AHPForR1CS::prover_first_round(prover_init_state, zk_rng)?;
        
        // commitments
        let first_round_comm_time = start_timer!(|| "Committing to first round polys");
        let (first_comms, first_comm_rands) = PC::commit(
            &index_pk.committer_key,
            prover_first_oracles.iter(),
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(first_round_comm_time);

        fs_rng.absorb(&to_bytes![first_comms, prover_first_msg].unwrap());

        // verifier_first_msg is the alpha and the etas
        let (verifier_first_msg, verifier_state) =
            AHPForR1CS::verifier_first_round(index_pk.index_vk.index_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round

        let (prover_second_msg, prover_second_oracles, _prover_state, t_poly) =
            AHPForR1CS::prover_second_round(&verifier_first_msg, prover_state, zk_rng);

        // commitments
        let second_round_comm_time = start_timer!(|| "Committing to second round polys");
        let (second_comms, second_comm_rands) = PC::commit(
            &index_pk.committer_key,
            prover_second_oracles.iter(),
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;
        end_timer!(second_round_comm_time);

        fs_rng.absorb(&to_bytes![second_comms, prover_second_msg].unwrap());

        // verifier_second_msg is the beta_1
        let (verifier_second_msg, verifier_state) =
            AHPForR1CS::verifier_second_round(verifier_state, &mut fs_rng);

        let t_beta = t_poly.evaluate(&verifier_second_msg.beta);

        // --------------------------------------------------------------------
        // Gather prover polynomials in one vector.
        let polynomials: Vec<_> = index_pk
            .index
            .iter()
            .chain(prover_first_oracles.iter())
            .chain(prover_second_oracles.iter())
            .collect();

        // Gather commitments in one vector.
        #[rustfmt::skip]
        let commitments = vec![
            first_comms.iter().map(|p| p.commitment().clone()).collect(),
            second_comms.iter().map(|p| p.commitment().clone()).collect(),
        ];
        let labeled_comms: Vec<_> = index_pk
            .index_vk
            .iter()
            .cloned()
            .zip(&AHPForR1CS::<F>::INDEXER_POLYNOMIALS)
            .map(|(c, l)| LabeledCommitment::new(l.to_string(), c, None))
            .chain(first_comms.iter().cloned())
            .chain(second_comms.iter().cloned())
            .collect();

        // Gather commitment randomness together.
        let comm_rands: Vec<PC::Randomness> = index_pk
            .index_comm_rands
            .clone()
            .into_iter()
            .chain(first_comm_rands)
            .chain(second_comm_rands)
            .collect();

        // Compute the AHP verifier's query set.
        let (query_set, verifier_state) =
            AHPForR1CS::verifier_query_set(verifier_state, &mut fs_rng);
            
        let lc_s = AHPForR1CS::construct_linear_combinations(
            &public_input,
            &polynomials,
            &verifier_state,
            &t_beta
        )?;

        let eval_time = start_timer!(|| "Evaluating linear combinations over query set");
        let mut evaluations = Vec::new();

        for (label, (_, point)) in &query_set {
            let lc = lc_s
                .iter()
                .find(|lc| &lc.label == label)
                .ok_or(ahp::Error::MissingEval(label.to_string()))?;
            let eval = polynomials.get_lc_eval(&lc, *point)?;
            if !AHPForR1CS::<F>::LC_WITH_ZERO_EVAL.contains(&lc.label.as_ref()) {
                evaluations.push((label.to_string(), eval));
            }
        }

        evaluations.sort_by(|a, b| a.0.cmp(&b.0));
        let evaluations = evaluations.into_iter().map(|x| x.1).collect::<Vec<F>>();
        end_timer!(eval_time);

        fs_rng.absorb(&evaluations);
        let opening_challenge: F = u128::rand(&mut fs_rng).into();

        let pc_proof = PC::open_combinations(
            &index_pk.committer_key,
            &lc_s,
            polynomials,
            &labeled_comms,
            &query_set,
            opening_challenge,
            &comm_rands,
            Some(zk_rng),
        )
        .map_err(Error::from_pc_err)?;

        // Gather prover messages together.
        let prover_messages = vec![prover_first_msg, prover_second_msg];

        let proof = Proof::new(commitments, evaluations, prover_messages, pc_proof);
        proof.print_size_info();
        end_timer!(prover_time);

        Ok((proof, verifier_first_msg.alpha, verifier_first_msg.eta_a, verifier_first_msg.eta_b, verifier_first_msg.eta_c, 
            verifier_second_msg.beta, t_beta, num_constraints, num_input_variables))
    }

    /// Verify that a proof for the constrain system defined by `C` asserts that
    /// all constraints are satisfied.
    pub fn verify<R: RngCore>(
        index_vk: &IndexVerifierKey<F, PC>,
        public_input: &[F],
        proof: &Proof<F, PC>,
        rng: &mut R,
        t_beta: &F,
    ) -> Result<bool, Error<PC::Error>> {
        let verifier_time = start_timer!(|| "Marlin::Verify");
        
        let public_input = {
            let domain_x = GeneralEvaluationDomain::<F>::new(public_input.len() + 1).unwrap();

            let mut unpadded_input = public_input.to_vec();
            unpadded_input.resize(
                core::cmp::max(public_input.len(), domain_x.size() - 1),
                F::zero(),
            );

            unpadded_input
        };

        let mut fs_rng = FiatShamirRng::<D>::from_seed(
            &to_bytes![&Self::PROTOCOL_NAME, &index_vk, &public_input].unwrap(),
        );

        // --------------------------------------------------------------------
        // First round

        let first_comms = &proof.commitments[0];
        fs_rng.absorb(&to_bytes![first_comms, proof.prover_messages[0]].unwrap());

        let (_, verifier_state) =
            AHPForR1CS::verifier_first_round(index_vk.index_info, &mut fs_rng)?;
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
        // Second round
        let second_comms = &proof.commitments[1];
        fs_rng.absorb(&to_bytes![second_comms, proof.prover_messages[1]].unwrap());

        let (_, verifier_state) = AHPForR1CS::verifier_second_round(verifier_state, &mut fs_rng);
        // --------------------------------------------------------------------

        // --------------------------------------------------------------------
 
        // Collect degree bounds for commitments. Indexed polynomials have *no*
        // degree bounds because we know the committed index polynomial has the
        // correct degree.
        let index_info = index_vk.index_info;
        let degree_bounds = vec![None; index_vk.index_comms.len()]
            .into_iter()
            .chain(AHPForR1CS::prover_first_round_degree_bounds(&index_info))
            .chain(AHPForR1CS::prover_second_round_degree_bounds(&index_info))
            .collect::<Vec<_>>();

        // Gather commitments in one vector.
        let commitments: Vec<_> = index_vk
            .iter()
            .chain(first_comms)
            .chain(second_comms)
            .cloned()
            .zip(AHPForR1CS::<F>::polynomial_labels())
            .zip(degree_bounds)
            .map(|((c, l), d)| LabeledCommitment::new(l, c, d))
            .collect();

        let (query_set, verifier_state) =
            AHPForR1CS::verifier_query_set(verifier_state, &mut fs_rng);

        fs_rng.absorb(&proof.evaluations);
        let opening_challenge: F = u128::rand(&mut fs_rng).into();
        
        let mut evaluations = Evaluations::new();
        let mut evaluation_labels = Vec::new();
        for (poly_label, (_, point)) in query_set.iter().cloned() {
            if AHPForR1CS::<F>::LC_WITH_ZERO_EVAL.contains(&poly_label.as_ref()) {
                evaluations.insert((poly_label, point), F::zero());
            } else {
                evaluation_labels.push((poly_label, point));
            }
        }

        evaluation_labels.sort_by(|a, b| a.0.cmp(&b.0));
        for (q, eval) in evaluation_labels.into_iter().zip(&proof.evaluations) {
            evaluations.insert(q, *eval);
        }

        let lc_s = AHPForR1CS::construct_linear_combinations(
            &public_input,
            &evaluations,
            &verifier_state,
            &t_beta
        )?;

        let evaluations_are_correct = PC::check_combinations(
            &index_vk.verifier_key,
            &lc_s,
            &commitments,
            &query_set,
            &evaluations,
            &proof.pc_proof,
            opening_challenge,
            rng,
        )
        .map_err(Error::from_pc_err)?;

        if !evaluations_are_correct {
            eprintln!("PC::Check failed");
        }
        end_timer!(verifier_time, || format!(
            " PC::Check for AHP Verifier linear equations: {}",
            evaluations_are_correct
        ));
        Ok(evaluations_are_correct)
    }

    pub fn prove_accumulation<R: RngCore>(
        index_pk: &IndexProverKey<F, PC>,
        rng: &mut R,
        matrices: Vec<Vec<Vec<(F, usize)>>>,
        all_variables: Vec<Vec<F>>,
        num_constraints: usize,
        num_input_variables: usize
    ) -> () {

        let mut fs_rng = FiatShamirRng::<D>::from_seed(
            &to_bytes![&Self::PROTOCOL_NAME, &index_pk.index_vk].unwrap(),
        );

        let (prover_first_msg_acc, y_1, y_2) = AHPForR1CS::prover_first_round_accumulation(matrices.clone(), all_variables.clone(), num_constraints, num_input_variables);  
        
        fs_rng.absorb(&to_bytes![y_1, y_2].unwrap());

        let gamma = AHPForR1CS::verifier_first_round_accumulation(rng);
        
        let (prover_second_msg_acc, prover_first_oracles_acc) = AHPForR1CS::prover_second_round_accumulation(matrices.clone(), all_variables.clone(), gamma, num_constraints, num_input_variables); 
        
        let first_comms = PC::commit(
            &index_pk.committer_key,
            prover_first_oracles_acc.iter(),
            Some(rng),
        ).map_err(Error::from_pc_err);

        let (first_comms, first_comm_rands) = match first_comms {
            Ok((comms, randomness)) => (comms, randomness),
            Err(err) => {
                panic!("Error en first_comms: {:?}", err);
            }
        };

        fs_rng.absorb(&to_bytes![first_comms].unwrap());
    
        let beta = AHPForR1CS::verifier_second_round_accumulation(rng);

        let (prover_third_msg_acc, q_beta_alpha_1, q_beta_alpha_2) = AHPForR1CS::prover_third_round_accumulation(matrices.clone(), all_variables.clone(), gamma, beta, num_constraints, num_input_variables); 

        let alpha: F = AHPForR1CS::verifier_third_round_accumulation(rng);

        let _q_beta_alpha = AHPForR1CS::prover_last_round_accumulation(matrices.clone(), all_variables.clone(), gamma, beta, alpha, num_constraints, num_input_variables); 

        let polynomials: Vec<_> = index_pk
            .index
            .iter()
            .chain(prover_first_oracles_acc.iter())
            .collect();

        #[rustfmt::skip]
        let commitments = vec![
            first_comms.iter().map(|p| p.commitment().clone()).collect(),
        ];
        
        let labeled_comms: Vec<_> = index_pk
            .index_vk
            .iter()
            .cloned()
            .zip(&AHPForR1CS::<F>::ACCUMULATION_POLYNOMIALS)
            .map(|(c, l)| LabeledCommitment::new(l.to_string(), c, None))
            .chain(first_comms.iter().cloned())
            .collect();

        let comm_rands: Vec<PC::Randomness> = index_pk
            .index_comm_rands
            .clone()
            .into_iter()
            .chain(first_comm_rands)
            .collect();
        
        let query_set =
            AHPForR1CS::verifier_query_set_accumulation(all_variables.clone(), beta, &mut fs_rng);
            
        let lc_s = AHPForR1CS::construct_linear_combinations_accumulation(
            all_variables.clone(),
            y_1,
            y_2,
            gamma,
            beta,
            q_beta_alpha_1,
            q_beta_alpha_2,
            &polynomials,
        );

        let lc_s = match lc_s {
            Ok(linear_combination) => linear_combination,
            Err(err) => {
                panic!("Error en second_comms: {:?}", err);
            }
        };

        let mut evaluations = Vec::new();

        for (label, (_, point)) in &query_set {
            let lc = lc_s
                .iter()
                .find(|lc| &lc.label == label)
                .ok_or(ahp::Error::MissingEval(label.to_string()));
            let lc = match lc {
                Ok(linear_combination) => linear_combination,
                Err(err) => {
                    panic!("Error en lc: {:?}", err);
                }
            };
            let eval = polynomials.get_lc_eval(&lc, *point);
            let eval = match eval {
                Ok(evaluation) => evaluation,
                Err(err) => {
                    panic!("Error en eval: {:?}", err);
                }
            };
            if !AHPForR1CS::<F>::LC_WITH_ZERO_EVAL.contains(&lc.label.as_ref()) {
                evaluations.push((label.to_string(), eval));
            }
        }

        evaluations.sort_by(|a, b| a.0.cmp(&b.0));
        let evaluations = evaluations.into_iter().map(|x| x.1).collect::<Vec<F>>();

        fs_rng.absorb(&evaluations);
        let opening_challenge: F = u128::rand(&mut fs_rng).into();

        let pc_proof = PC::open_combinations(
            &index_pk.committer_key,
            &lc_s,
            polynomials,
            &labeled_comms,
            &query_set,
            opening_challenge,
            &comm_rands,
            Some(rng),
        )
        .map_err(Error::from_pc_err);

        let pc_proof: ark_poly_commit_new::BatchLCProof<F, DensePolynomial<F>, _> = match pc_proof {
            Ok(proof) => proof,
            Err(err) => {
                panic!("Error en second_comms: {:?}", err);
            }
        };

        let prover_messages = vec![prover_first_msg_acc, prover_second_msg_acc, prover_third_msg_acc];

        let proof = Proof::new(commitments, evaluations, prover_messages, pc_proof);
        proof.print_size_info();
    }
}
