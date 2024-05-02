use crate::{String, ToString, Vec};
use ark_ff::{Field, PrimeField};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_poly_commit_new::{LCTerm, LinearCombination};
use ark_relations::r1cs::SynthesisError;
use ark_std::{borrow::Borrow, cfg_iter_mut, format, marker::PhantomData, vec};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

pub(crate) mod constraint_systems;
/// Describes data structures and the algorithms used by the AHP indexer.
pub mod indexer;
/// Describes data structures and the algorithms used by the AHP prover.
pub mod prover;
/// Describes data structures and the algorithms used by the AHP verifier.
pub mod verifier;

/// A labeled DensePolynomial with coefficients over `F`
pub type LabeledPolynomial<F> = ark_poly_commit_new::LabeledPolynomial<F, DensePolynomial<F>>;

/// The algebraic holographic proof defined in [CHMMVW19](https://eprint.iacr.org/2019/1047).
/// Currently, this AHP only supports inputs of size one
/// less than a power of 2 (i.e., of the form 2^n - 1).
pub struct AHPForR1CS<F: Field> {
    field: PhantomData<F>,
}

impl<F: PrimeField> AHPForR1CS<F> {
    /// The labels for the polynomials output by the AHP indexer.
    #[rustfmt::skip]
    pub const INDEXER_POLYNOMIALS: [&'static str; 0] = [
    ];

    /// The labels for the polynomials output by the AHP prover.
    #[rustfmt::skip]
    pub const PROVER_POLYNOMIALS: [&'static str; 5] = [
        // First sumcheck
        "w", "z_a", "z_b", "g_1", "h_1",
    ];

    #[rustfmt::skip]
    pub const ACCUMULATION_POLYNOMIALS: [&'static str; 3] = [
        "q_alphas_beta_1", "q_alphas_beta_2", "q_alphas_beta",
    ];

    /// THe linear combinations that are statically known to evaluate to zero.
    pub const LC_WITH_ZERO_EVAL: [&'static str; 0] = [];

    pub(crate) fn polynomial_labels() -> impl Iterator<Item = String> {
        Self::INDEXER_POLYNOMIALS
            .iter()
            .chain(&Self::PROVER_POLYNOMIALS)
            .map(|s| s.to_string())
    }

    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn num_formatted_public_inputs_is_admissible(num_inputs: usize) -> bool {
        num_inputs.count_ones() == 1
    }

    /// Check that the (formatted) public input is of the form 2^n for some integer n.
    pub fn formatted_public_input_is_admissible(input: &[F]) -> bool {
        Self::num_formatted_public_inputs_is_admissible(input.len())
    }

    /// The maximum degree of polynomials produced by the indexer and prover
    /// of this protocol.
    /// The number of the variables must include the "one" variable. That is, it
    /// must be with respect to the number of formatted public inputs.
    pub fn max_degree(
        num_constraints: usize,
        num_variables: usize,
        num_non_zero: usize,
    ) -> Result<usize, Error> {
        let padded_matrix_dim =
            constraint_systems::padded_matrix_dim(num_variables, num_constraints);
        let zk_bound = 1;
        let domain_h_size = GeneralEvaluationDomain::<F>::compute_size_of_domain(padded_matrix_dim)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        let domain_k_size = GeneralEvaluationDomain::<F>::compute_size_of_domain(num_non_zero)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        Ok(*[
            2 * domain_h_size + zk_bound - 2,
            3 * domain_h_size + 2 * zk_bound - 3, 
            domain_h_size,
            domain_h_size,
            3 * domain_k_size - 3,
        ]
        .iter()
        .max()
        .unwrap())
    }

    /// Get all the strict degree bounds enforced in the AHP.
    pub fn get_degree_bounds(info: &indexer::IndexInfo<F>) -> [usize; 2] {
        let mut degree_bounds = [0usize; 2];
        let num_constraints = info.num_constraints;
        let num_non_zero = info.num_non_zero;
        let h_size = GeneralEvaluationDomain::<F>::compute_size_of_domain(num_constraints).unwrap();
        let k_size = GeneralEvaluationDomain::<F>::compute_size_of_domain(num_non_zero).unwrap();

        degree_bounds[0] = h_size - 2;
        degree_bounds[1] = k_size - 2;
        degree_bounds
    }

    /// Construct the linear combinations that are checked by the AHP.
    #[allow(non_snake_case)]
    pub fn construct_linear_combinations<E>(
        public_input: &[F],
        evals: &E,
        state: &verifier::VerifierState<F>,
        t_at_beta: &F,
    ) -> Result<Vec<LinearCombination<F>>, Error>
    where
        E: EvaluationsProvider<F>,
    {
        let domain_h = state.domain_h;

        let public_input = constraint_systems::format_public_input(public_input);
        if !Self::formatted_public_input_is_admissible(&public_input) {
            return Err(Error::InvalidPublicInputLength);
        }
        let x_domain = GeneralEvaluationDomain::new(public_input.len())
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        let first_round_msg = state.first_round_msg.unwrap();
        let alpha = first_round_msg.alpha;
        let eta_a = first_round_msg.eta_a;
        let eta_b = first_round_msg.eta_b;
        let eta_c = first_round_msg.eta_c;

        let beta = state.second_round_msg.unwrap(). beta;

        let mut linear_combinations = Vec::new();

        // Outer sumcheck:
        let z_b = LinearCombination::new("z_b", vec![(F::one(), "z_b")]);
        let g_1 = LinearCombination::new("g_1", vec![(F::one(), "g_1")]);

        let r_alpha_at_beta = domain_h.eval_unnormalized_bivariate_lagrange_poly(alpha, beta);
        let v_H_at_beta = domain_h.evaluate_vanishing_polynomial(beta);
        let v_X_at_beta = x_domain.evaluate_vanishing_polynomial(beta);

        let z_b_at_beta = evals.get_lc_eval(&z_b, beta)?;
        let g_1_at_beta = evals.get_lc_eval(&g_1, beta)?;

        let x_at_beta = x_domain
            .evaluate_all_lagrange_coefficients(beta)
            .into_iter()
            .zip(public_input)
            .map(|(l, x)| l * &x)
            .fold(F::zero(), |x, y| x + &y);

        #[rustfmt::skip]
        let outer_sumcheck = LinearCombination::new(
            "outer_sumcheck",
            vec![
                (r_alpha_at_beta * (eta_a + eta_c * z_b_at_beta), "z_a".into()),
                (r_alpha_at_beta * eta_b * z_b_at_beta, LCTerm::One),

                (-*t_at_beta * v_X_at_beta, "w".into()),
                (-*t_at_beta * x_at_beta, LCTerm::One),

                (-v_H_at_beta, "h_1".into()),
                (-beta * g_1_at_beta, LCTerm::One),
            ],
        );
        debug_assert!(evals.get_lc_eval(&outer_sumcheck, beta)?.is_zero());

        linear_combinations.push(z_b);
        linear_combinations.push(g_1);
        linear_combinations.push(outer_sumcheck);
    
        linear_combinations.sort_by(|a, b| a.label.cmp(&b.label));
        Ok(linear_combinations)
    }

    #[allow(non_snake_case)]
    pub fn construct_linear_combinations_accumulation<E>(
        all_variables: Vec<Vec<F>>,
        y_1: F,
        y_2: F,
        gamma: F,
        beta: F,
        q_beta_alpha_1: F,
        q_beta_alpha_2: F,
        evals: &E,
    ) -> Result<Vec<LinearCombination<F>>, Error>
    where
        E: EvaluationsProvider<F>,
    {
        let y1 = all_variables[0][5];
        let y2 = all_variables[1][5];

        let mut linear_combinations = Vec::new();

        // Alphas sumcheck:
        let q_alphas_beta_2 = LinearCombination::new("q_alphas_beta_2", vec![(F::one(), "q_alphas_beta_2")]);

        let q_alphas_beta_2_eval = evals.get_lc_eval(&q_alphas_beta_2, all_variables[1][4])?;

        let q_alphas_beta_1 = LinearCombination::new("q_alphas_beta_1", vec![(F::one(), "q_alphas_beta_1")]);
        let q_alphas_beta_1_eval = evals.get_lc_eval(&q_alphas_beta_1, all_variables[0][4])?;
        let alphas_sumcheck = y1 + gamma * y_1 + gamma * gamma * y_2 + gamma * gamma * gamma * y2 - gamma * q_alphas_beta_2_eval - q_alphas_beta_1_eval;
        
        debug_assert!(alphas_sumcheck.is_zero());

        linear_combinations.push(q_alphas_beta_2);
        linear_combinations.push(q_alphas_beta_1);

        // Betas sumcheck:
        let q_alphas_beta = LinearCombination::new("q_alphas_beta", vec![(F::one(), "q_alphas_beta")]);
        let q_alphas_beta_eval = evals.get_lc_eval(&q_alphas_beta, beta)?;
        let betas_sumcheck = q_beta_alpha_1 + gamma * q_beta_alpha_2 - q_alphas_beta_eval;
        assert!(betas_sumcheck.is_zero());

        linear_combinations.push(q_alphas_beta);
    
        linear_combinations.sort_by(|a, b| a.label.cmp(&b.label));
        
        Ok(linear_combinations)
    }
}

/// Abstraction that provides evaluations of (linear combinations of) polynomials
///
/// Intended to provide a common interface for both the prover and the verifier
/// when constructing linear combinations via `AHPForR1CS::construct_linear_combinations`.
pub trait EvaluationsProvider<F: Field> {
    /// Get the evaluation of linear combination `lc` at `point`.
    fn get_lc_eval(&self, lc: &LinearCombination<F>, point: F) -> Result<F, Error>;
}

impl<'a, F: Field> EvaluationsProvider<F> for ark_poly_commit_new::Evaluations<F, F> {
    fn get_lc_eval(&self, lc: &LinearCombination<F>, point: F) -> Result<F, Error> {
        let key = (lc.label.clone(), point);
        self.get(&key)
            .map(|v| *v)
            .ok_or(Error::MissingEval(lc.label.clone()))
    }
}

impl<F: Field, T: Borrow<LabeledPolynomial<F>>> EvaluationsProvider<F> for Vec<T> {
    fn get_lc_eval(&self, lc: &LinearCombination<F>, point: F) -> Result<F, Error> {
        let mut eval = F::zero();
        for (coeff, term) in lc.iter() {
            let value = if let LCTerm::PolyLabel(label) = term {
                self.iter()
                    .find(|p| {
                        let p: &LabeledPolynomial<F> = (*p).borrow();
                        p.label() == label
                    })
                    .ok_or(Error::MissingEval(format!(
                        "Missing {} for {}",
                        label, lc.label
                    )))?
                    .borrow()
                    .evaluate(&point)
            } else {
                assert!(term.is_one());
                F::one()
            };
            eval += *coeff * value
        }
        Ok(eval)
    }
}

/// Describes the failure modes of the AHP scheme.
#[derive(Debug)]
pub enum Error {
    /// During verification, a required evaluation is missing
    MissingEval(String),
    /// The number of public inputs is incorrect.
    InvalidPublicInputLength,
    /// The instance generated during proving does not match that in the index.
    InstanceDoesNotMatchIndex,
    /// Currently we only support square constraint matrices.
    NonSquareMatrix,
    /// An error occurred during constraint generation.
    ConstraintSystemError(SynthesisError),
}

impl From<SynthesisError> for Error {
    fn from(other: SynthesisError) -> Self {
        Error::ConstraintSystemError(other)
    }
}

/// The derivative of the vanishing polynomial
pub trait UnnormalizedBivariateLagrangePoly<F: ark_ff::FftField> {
    /// Evaluate the polynomial
    fn eval_unnormalized_bivariate_lagrange_poly(&self, x: F, y: F) -> F;

    /// Evaluate over a batch of inputs
    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(&self, x: F) -> Vec<F>;

    /// Evaluate the magic polynomial over `self`
    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs(&self) -> Vec<F>;
}

impl<F: PrimeField> UnnormalizedBivariateLagrangePoly<F> for GeneralEvaluationDomain<F> {
    fn eval_unnormalized_bivariate_lagrange_poly(&self, x: F, y: F) -> F {
        if x != y {
            (self.evaluate_vanishing_polynomial(x) - self.evaluate_vanishing_polynomial(y))
                / (x - y)
        } else {
            self.size_as_field_element() * x.pow(&[(self.size() - 1) as u64])
        }
    }

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(&self, x: F) -> Vec<F> {
        let vanish_x = self.evaluate_vanishing_polynomial(x);
        let mut inverses: Vec<F> = self.elements().map(|y| x - y).collect();
        ark_ff::batch_inversion(&mut inverses);

        cfg_iter_mut!(inverses).for_each(|denominator| *denominator *= vanish_x);
        inverses
    }

    fn batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs(&self) -> Vec<F> {
        let mut elems: Vec<F> = self
            .elements()
            .map(|e| e * self.size_as_field_element())
            .collect();
        elems[1..].reverse();
        elems
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use ark_ff::{One, UniformRand, Zero};
    use ark_poly::{
        univariate::{DenseOrSparsePolynomial, DensePolynomial},
        Polynomial, UVPolynomial,
    };

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly() {
        for domain_size in 1..10 {
            let domain = GeneralEvaluationDomain::<Fr>::new(1 << domain_size).unwrap();
            let manual: Vec<_> = domain
                .elements()
                .map(|elem| domain.eval_unnormalized_bivariate_lagrange_poly(elem, elem))
                .collect();
            let fast = domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_same_inputs();
            assert_eq!(fast, manual);
        }
    }

    #[test]
    fn domain_unnormalized_bivariate_lagrange_poly_diff_inputs() {
        let rng = &mut ark_std::test_rng();
        for domain_size in 1..10 {
            let domain = GeneralEvaluationDomain::<Fr>::new(1 << domain_size).unwrap();
            let x = Fr::rand(rng);
            let manual: Vec<_> = domain
                .elements()
                .map(|y| domain.eval_unnormalized_bivariate_lagrange_poly(x, y))
                .collect();
            let fast = domain.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(x);
            assert_eq!(fast, manual);
        }
    }

    #[test]
    fn test_summation() {
        let rng = &mut ark_std::test_rng();
        let size = 1 << 4;
        let domain = GeneralEvaluationDomain::<Fr>::new(1 << 4).unwrap();
        let size_as_fe = domain.size_as_field_element();
        let poly = DensePolynomial::rand(size, rng);

        let mut sum: Fr = Fr::zero();
        for eval in domain.elements().map(|e| poly.evaluate(&e)) {
            sum += eval;
        }
        let first = poly.coeffs[0] * size_as_fe;
        let last = *poly.coeffs.last().unwrap() * size_as_fe;
        println!("sum: {:?}", sum);
        println!("a_0: {:?}", first);
        println!("a_n: {:?}", last);
        println!("first + last: {:?}\n", first + last);
        assert_eq!(sum, first + last);
    }

    #[test]
    fn test_alternator_polynomial() {
        use ark_poly::Evaluations;
        let domain_k = GeneralEvaluationDomain::<Fr>::new(1 << 4).unwrap();
        let domain_h = GeneralEvaluationDomain::<Fr>::new(1 << 3).unwrap();
        let domain_h_elems = domain_h
            .elements()
            .collect::<std::collections::HashSet<_>>();
        let alternator_poly_evals = domain_k
            .elements()
            .map(|e| {
                if domain_h_elems.contains(&e) {
                    Fr::one()
                } else {
                    Fr::zero()
                }
            })
            .collect();
        let v_k: DenseOrSparsePolynomial<_> = domain_k.vanishing_polynomial().into();
        let v_h: DenseOrSparsePolynomial<_> = domain_h.vanishing_polynomial().into();
        let (divisor, remainder) = v_k.divide_with_q_and_r(&v_h).unwrap();
        assert!(remainder.is_zero());
        println!("Divisor: {:?}", divisor);
        println!(
            "{:#?}",
            divisor
                .coeffs
                .iter()
                .filter_map(|f| if !f.is_zero() {
                    Some(f.into_repr())
                } else {
                    None
                })
                .collect::<Vec<_>>()
        );

        for e in domain_h.elements() {
            println!("{:?}", divisor.evaluate(&e));
        }
        // Let p = v_K / v_H;
        // The alternator polynomial is p * t, where t is defined as
        // the LDE of p(h)^{-1} for all h in H.
        //
        // Because for each h in H, p(h) equals a constant c, we have that t
        // is the constant polynomial c^{-1}.
        //
        // Q: what is the constant c? Why is p(h) constant? What is the easiest
        // way to calculate c?
        let alternator_poly =
            Evaluations::from_vec_and_domain(alternator_poly_evals, domain_k).interpolate();
        let (quotient, remainder) = DenseOrSparsePolynomial::from(alternator_poly.clone())
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(divisor))
            .unwrap();
        assert!(remainder.is_zero());
        println!("quotient: {:?}", quotient);
        println!(
            "{:#?}",
            quotient
                .coeffs
                .iter()
                .filter_map(|f| if !f.is_zero() {
                    Some(f.into_repr())
                } else {
                    None
                })
                .collect::<Vec<_>>()
        );

        println!("{:?}", alternator_poly);
    }
}
