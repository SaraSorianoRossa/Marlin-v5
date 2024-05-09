#![allow(non_snake_case)]

use crate::ahp::indexer::IndexInfo;
use crate::ahp::*;
use ark_std::rand::RngCore;

use ark_ff::PrimeField;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit::QuerySet;

/// State of the AHP verifier
pub struct VerifierState<F: PrimeField> {
    pub(crate) domain_h: GeneralEvaluationDomain<F>,

    pub(crate) first_round_msg: Option<VerifierFirstMsg<F>>,
    pub(crate) second_round_msg: Option<VerifierSecondMsg<F>>,

}

/// First message of the verifier.
#[derive(Copy, Clone)]
pub struct VerifierFirstMsg<F> {
    /// Query for the random polynomial.
    pub alpha: F,
    /// Randomizer for the lincheck for `A`.
    pub eta_a: F,
    /// Randomizer for the lincheck for `B`.
    pub eta_b: F,
    /// Randomizer for the lincheck for `C`.
    pub eta_c: F,
}

/// Second verifier message.
#[derive(Copy, Clone)]
pub struct VerifierSecondMsg<F> {
    /// Query for the second round of polynomials.
    pub beta: F,
}

impl<F: PrimeField> AHPForR1CS<F> {
    /// Output the first message and next round state.
    pub fn verifier_first_round<R: RngCore>(
        index_info: IndexInfo<F>,
        rng: &mut R,
    ) -> Result<(VerifierFirstMsg<F>, VerifierState<F>), Error> {
        if index_info.num_constraints != index_info.num_variables {
            return Err(Error::NonSquareMatrix);
        }

        let domain_h = GeneralEvaluationDomain::new(index_info.num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let alpha = domain_h.sample_element_outside_domain(rng);
        let eta_a = F::rand(rng);
        let eta_b = F::rand(rng);
        let eta_c = F::rand(rng);

        let msg = VerifierFirstMsg {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        };

        let new_state = VerifierState {
            domain_h,
            first_round_msg: Some(msg),
            second_round_msg: None,
        };

        Ok((msg, new_state))
    }

    /// Output the second message and next round state.
    pub fn verifier_second_round<R: RngCore>(
        mut state: VerifierState<F>,
        rng: &mut R,
    ) -> (VerifierSecondMsg<F>, VerifierState<F>) {
        let beta = state.domain_h.sample_element_outside_domain(rng);
        let msg = VerifierSecondMsg { beta };
        state.second_round_msg = Some(msg);

        (msg, state)
    }

    /// Output the query state and next round state.
    pub fn verifier_query_set<'a, R: RngCore>(
        state: VerifierState<F>,
        _: &'a mut R,
    ) -> (QuerySet<F>, VerifierState<F>) {
        let beta = state.second_round_msg.unwrap().beta;

        let mut query_set = QuerySet::new();
        // For the first linear combination
        // Outer sumcheck test:
        //   s(beta) + r(alpha, beta) * (sum_M eta_M z_M(beta)) - t(beta) * z(beta)
        // = h_1(beta) * v_H(beta) + beta * g_1(beta)
        //
        // Note that z is the interpolation of x || w, so it equals x + v_X * w
        // We also use an optimization: instead of explicitly calculating z_c, we
        // use the "virtual oracle" z_b * z_c
        //
        // LinearCombination::new(
        //      outer_sumcheck
        //      vec![
        //          (F::one(), "mask_poly".into()),
        //
        //          (r_alpha_at_beta * (eta_a + eta_c * z_b_at_beta), "z_a".into()),
        //          (r_alpha_at_beta * eta_b * z_b_at_beta, LCTerm::One),
        //
        //          (-t_at_beta * v_X_at_beta, "w".into()),
        //          (-t_at_beta * x_at_beta, LCTerm::One),
        //
        //          (-v_H_at_beta, "h_1".into()),
        //          (-beta * g_1_at_beta, LCTerm::One),
        //      ],
        //  )
        //  LinearCombination::new("z_b", vec![(F::one(), z_b)])
        //  LinearCombination::new("g_1", vec![(F::one(), g_1)], rhs::new(g_1_at_beta))
        //  LinearCombination::new("t", vec![(F::one(), t)])
        query_set.insert(("g_1".into(), ("beta".into(), beta)));
        query_set.insert(("z_b".into(), ("beta".into(), beta)));

        query_set.insert(("outer_sumcheck".into(), ("beta".into(), beta)));

        (query_set, state)
    }

    pub fn verifier_first_round_accumulation<R: RngCore>(
        rng: &mut R,
    ) -> F {
    
        let gamma = F::rand(rng);
        gamma
    }
    
    pub fn verifier_second_round_accumulation<R: RngCore>(
        rng: &mut R,
    ) -> F {
    
        let beta = F::rand(rng);
        beta
    }
    
    pub fn verifier_third_round_accumulation<R: RngCore>(
        rng: &mut R,
        ) -> F {
    
        let alpha = F::rand(rng);
        alpha
    }

    pub fn verifier_query_set_accumulation<'a, R: RngCore>(
        all_variables: Vec<Vec<F>>,
        beta: F,
        _: &'a mut R,
    ) -> QuerySet<F> {

        let mut query_set = QuerySet::new();

        query_set.insert(("q_alphas_beta_1".into(), ("beta_1".into(), all_variables[0][4])));
        query_set.insert(("q_alphas_beta_2".into(), ("beta_2".into(), all_variables[1][4])));
        
        query_set.insert(("q_alphas_beta".into(), ("beta".into(), beta)));

        query_set
    }
    
}
