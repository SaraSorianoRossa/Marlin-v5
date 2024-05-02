#![allow(non_snake_case)]

use crate::ahp::indexer::*;
use crate::ahp::verifier::*;
use crate::ahp::*;

use crate::ahp::constraint_systems::{
    make_matrices_square_for_prover, pad_input_for_indexer_and_prover, unformat_public_input,
};
use crate::{ToString, Vec};
use ark_ff::{Field, PrimeField, Zero};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Evaluations as EvaluationsOnDomain,
    GeneralEvaluationDomain, Polynomial, UVPolynomial,
};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, OptimizationGoal, SynthesisError,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::rand::RngCore;
use ark_std::{
    cfg_into_iter, cfg_iter_mut,
    io::{Read, Write},
};

/// State for the AHP prover.
pub struct ProverState<'a, F: PrimeField> {
    formatted_input_assignment: Vec<F>,
    witness_assignment: Vec<F>,
    /// Az
    z_a: Option<Vec<F>>,
    /// Bz
    z_b: Option<Vec<F>>,
    /// query bound b
    zk_bound: usize,

    w_poly: Option<LabeledPolynomial<F>>,
    mz_polys: Option<(LabeledPolynomial<F>, LabeledPolynomial<F>)>,

    index: &'a Index<F>,

    /// the random values sent by the verifier in the first round
    verifier_first_msg: Option<VerifierFirstMsg<F>>,

    /// domain X, sized for the public input
    domain_x: GeneralEvaluationDomain<F>,

    /// domain H, sized for constraints
    domain_h: GeneralEvaluationDomain<F>,
}

impl<'a, F: PrimeField> ProverState<'a, F> {
    /// Get the public input.
    pub fn public_input(&self) -> Vec<F> {
        unformat_public_input(&self.formatted_input_assignment)
    }
}

/// Each prover message that is not a list of oracles is a list of field elements.
#[derive(Clone)]
pub enum ProverMsg<F: Field> {
    /// Some rounds, the prover sends only oracles. (This is actually the case for all
    /// rounds in Marlin.)
    EmptyMessage,
    /// Otherwise, it's one or more field elements.
    FieldElements(Vec<F>),
}

impl<F: Field> ark_ff::ToBytes for ProverMsg<F> {
    fn write<W: Write>(&self, w: W) -> ark_std::io::Result<()> {
        match self {
            ProverMsg::EmptyMessage => Ok(()),
            ProverMsg::FieldElements(field_elems) => field_elems.write(w),
        }
    }
}

impl<F: Field> CanonicalSerialize for ProverMsg<F> {
    fn serialize<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        let res: Option<Vec<F>> = match self {
            ProverMsg::EmptyMessage => None,
            ProverMsg::FieldElements(v) => Some(v.clone()),
        };
        res.serialize(&mut writer)
    }

    fn serialized_size(&self) -> usize {
        let res: Option<Vec<F>> = match self {
            ProverMsg::EmptyMessage => None,
            ProverMsg::FieldElements(v) => Some(v.clone()),
        };
        res.serialized_size()
    }

    fn serialize_unchecked<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        let res: Option<Vec<F>> = match self {
            ProverMsg::EmptyMessage => None,
            ProverMsg::FieldElements(v) => Some(v.clone()),
        };
        res.serialize_unchecked(&mut writer)
    }

    fn serialize_uncompressed<W: Write>(&self, mut writer: W) -> Result<(), SerializationError> {
        let res: Option<Vec<F>> = match self {
            ProverMsg::EmptyMessage => None,
            ProverMsg::FieldElements(v) => Some(v.clone()),
        };
        res.serialize_uncompressed(&mut writer)
    }

    fn uncompressed_size(&self) -> usize {
        let res: Option<Vec<F>> = match self {
            ProverMsg::EmptyMessage => None,
            ProverMsg::FieldElements(v) => Some(v.clone()),
        };
        res.uncompressed_size()
    }
}

impl<F: Field> CanonicalDeserialize for ProverMsg<F> {
    fn deserialize<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        let res = Option::<Vec<F>>::deserialize(&mut reader)?;

        if let Some(res) = res {
            Ok(ProverMsg::FieldElements(res))
        } else {
            Ok(ProverMsg::EmptyMessage)
        }
    }

    fn deserialize_unchecked<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        let res = Option::<Vec<F>>::deserialize_unchecked(&mut reader)?;

        if let Some(res) = res {
            Ok(ProverMsg::FieldElements(res))
        } else {
            Ok(ProverMsg::EmptyMessage)
        }
    }

    fn deserialize_uncompressed<R: Read>(mut reader: R) -> Result<Self, SerializationError> {
        let res = Option::<Vec<F>>::deserialize_uncompressed(&mut reader)?;

        if let Some(res) = res {
            Ok(ProverMsg::FieldElements(res))
        } else {
            Ok(ProverMsg::EmptyMessage)
        }
    }
}

/// The first set of prover oracles.
pub struct ProverFirstOracles<F: Field> {
    /// The LDE of `w`.
    pub w: LabeledPolynomial<F>,
    /// The LDE of `Az`.
    pub z_a: LabeledPolynomial<F>,
    /// The LDE of `Bz`.
    pub z_b: LabeledPolynomial<F>,
}

impl<F: Field> ProverFirstOracles<F> {
    /// Iterate over the polynomials output by the prover in the first round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        vec![&self.w, &self.z_a, &self.z_b].into_iter()
    }
}

/// The second set of prover oracles.
pub struct ProverSecondOracles<F: Field> {
    /// The polynomial `g` resulting from the first sumcheck.
    pub g_1: LabeledPolynomial<F>,
    /// The polynomial `h` resulting from the first sumcheck.
    pub h_1: LabeledPolynomial<F>,
}

impl<F: Field> ProverSecondOracles<F> {
    /// Iterate over the polynomials output by the prover in the second round.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        vec![&self.g_1, &self.h_1].into_iter()
    }
}

pub struct ProverSecondOraclesAcc<F: Field> {
    pub q_alphas_beta_1: LabeledPolynomial<F>,
    pub q_alphas_beta_2: LabeledPolynomial<F>,
    pub q_alphas_beta: LabeledPolynomial<F>,
}

impl<F: Field> ProverSecondOraclesAcc<F> {
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        vec![&self.q_alphas_beta_1, &self.q_alphas_beta_2, &self.q_alphas_beta].into_iter()
    }
}

impl<F: PrimeField> AHPForR1CS<F> {
    /// Initialize the AHP prover.
    pub fn prover_init<'a, C: ConstraintSynthesizer<F>>(
        index: &'a Index<F>,
        c: C,
    ) -> Result<(ProverState<'a, F>, usize, usize), Error> {
        let init_time = start_timer!(|| "AHP::Prover::Init");

        let constraint_time = start_timer!(|| "Generating constraints and witnesses");
        let pcs = ConstraintSystem::new_ref();
        pcs.set_optimization_goal(OptimizationGoal::Weight);
        pcs.set_mode(ark_relations::r1cs::SynthesisMode::Prove {
            construct_matrices: true,
        });
        c.generate_constraints(pcs.clone())?;
        end_timer!(constraint_time);

        let padding_time = start_timer!(|| "Padding matrices to make them square");
        pad_input_for_indexer_and_prover(pcs.clone());
        pcs.finalize();
        make_matrices_square_for_prover(pcs.clone());
        end_timer!(padding_time);

        let (formatted_input_assignment, witness_assignment, num_constraints) = {
            let pcs = pcs.borrow().unwrap();
            (
                pcs.instance_assignment.as_slice().to_vec(),
                pcs.witness_assignment.as_slice().to_vec(),
                pcs.num_constraints,
            )
        };

        let num_input_variables = formatted_input_assignment.len();
        let num_witness_variables = witness_assignment.len();
        if index.index_info.num_constraints != num_constraints
            || num_input_variables + num_witness_variables != index.index_info.num_variables
        {
            return Err(Error::InstanceDoesNotMatchIndex);
        }

        if !Self::formatted_public_input_is_admissible(&formatted_input_assignment) {
            return Err(Error::InvalidPublicInputLength);
        }

        // Perform matrix multiplications
        let inner_prod_fn = |row: &[(F, usize)]| {
            let mut acc = F::zero();
            for &(ref coeff, i) in row {
                let tmp = if i < num_input_variables {
                    formatted_input_assignment[i]
                } else {
                    witness_assignment[i - num_input_variables]
                };

                acc += &(if coeff.is_one() { tmp } else { tmp * coeff });
            }
            acc
        };

        let eval_z_a_time = start_timer!(|| "Evaluating z_A");
        let z_a = index.a.iter().map(|row| inner_prod_fn(row)).collect();
        end_timer!(eval_z_a_time);

        let eval_z_b_time = start_timer!(|| "Evaluating z_B");
        let z_b = index.b.iter().map(|row| inner_prod_fn(row)).collect();
        end_timer!(eval_z_b_time);

        let zk_bound = 1; // One query is sufficient for our desired soundness

        let domain_h = GeneralEvaluationDomain::new(num_constraints)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
        
        let domain_x = GeneralEvaluationDomain::new(num_input_variables)
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;

        end_timer!(init_time);

        Ok((ProverState {
            formatted_input_assignment,
            witness_assignment,
            z_a: Some(z_a),
            z_b: Some(z_b),
            w_poly: None,
            mz_polys: None,
            zk_bound,
            index,
            verifier_first_msg: None,
            domain_h,
            domain_x,
        }, num_constraints, num_input_variables))
    }

    /// Output the first round message and the next state.
    pub fn prover_first_round<'a, R: RngCore>(
        mut state: ProverState<'a, F>,
        _rng: &mut R,
    ) -> Result<(ProverMsg<F>, ProverFirstOracles<F>, ProverState<'a, F>), Error> {
        let round_time = start_timer!(|| "AHP::Prover::FirstRound");
        let domain_h = state.domain_h;
        let zk_bound = state.zk_bound;

        let x_time = start_timer!(|| "Computing x polynomial and evals");
        let domain_x = state.domain_x;
        let x_poly = EvaluationsOnDomain::from_vec_and_domain(
            state.formatted_input_assignment.clone(),
            domain_x,
        )
        .interpolate();
        let x_evals = domain_h.fft(&x_poly);
        end_timer!(x_time);

        let ratio = domain_h.size() / domain_x.size();

        let mut w_extended = state.witness_assignment.clone();
        w_extended.extend(vec![
            F::zero();
            domain_h.size()
                - domain_x.size()
                - state.witness_assignment.len()
        ]);

        let w_poly_time = start_timer!(|| "Computing w polynomial");
        let w_poly_evals = cfg_into_iter!(0..domain_h.size())
            .map(|k| {
                if k % ratio == 0 {
                    F::zero()
                } else {
                    w_extended[k - (k / ratio) - 1] - &x_evals[k]
                }
            })
            .collect();

        let w_poly = &EvaluationsOnDomain::from_vec_and_domain(w_poly_evals, domain_h)
            .interpolate();
        let (w_poly, remainder) = w_poly.divide_by_vanishing_poly(domain_x).unwrap();
        assert!(remainder.is_zero());
        end_timer!(w_poly_time);

        let z_a_poly_time = start_timer!(|| "Computing z_A polynomial");
        let z_a = state.z_a.clone().unwrap();
        let z_a_poly = EvaluationsOnDomain::from_vec_and_domain(z_a, domain_h).interpolate();
        end_timer!(z_a_poly_time);

        let z_b_poly_time = start_timer!(|| "Computing z_B polynomial");
        let z_b = state.z_b.clone().unwrap();
        let z_b_poly = EvaluationsOnDomain::from_vec_and_domain(z_b, domain_h).interpolate();
        end_timer!(z_b_poly_time);

        let msg = ProverMsg::EmptyMessage;

        assert!(w_poly.degree() < domain_h.size() - domain_x.size() + zk_bound);
        assert!(z_a_poly.degree() < domain_h.size() + zk_bound);
        assert!(z_b_poly.degree() < domain_h.size() + zk_bound);

        let w = LabeledPolynomial::new("w".to_string(), w_poly, None, Some(1));
        let z_a = LabeledPolynomial::new("z_a".to_string(), z_a_poly, None, Some(1));
        let z_b = LabeledPolynomial::new("z_b".to_string(), z_b_poly, None, Some(1));

        // prover sends w, z_A and z_B to verifier        
        let oracles = ProverFirstOracles {
            w: w.clone(),
            z_a: z_a.clone(),
            z_b: z_b.clone(),
        };

        state.w_poly = Some(w);
        state.mz_polys = Some((z_a, z_b));
        end_timer!(round_time);

        Ok((msg, oracles, state))
    }

    // we compute t(X)
    fn calculate_t<'a>(
        matrices: impl Iterator<Item = &'a Matrix<F>>,
        matrix_randomizers: &[F],
        input_domain: GeneralEvaluationDomain<F>,
        domain_h: GeneralEvaluationDomain<F>,
        r_alpha_x_on_h: Vec<F>
    ) -> DensePolynomial<F> {
        let mut t_evals_on_h = vec![F::zero(); domain_h.size()];
        for (matrix, eta) in matrices.zip(matrix_randomizers) {
            for (r, row) in matrix.iter().enumerate() {
                for (coeff, c) in row.iter() {
                    let index = domain_h.reindex_by_subdomain(input_domain, *c);
                    t_evals_on_h[index] += *eta * coeff * r_alpha_x_on_h[r]; //sum all matrices * r
                }
            }
        }
        EvaluationsOnDomain::from_vec_and_domain(t_evals_on_h, domain_h).interpolate()
    }

    /// Output the number of oracles sent by the prover in the first round.
    pub fn prover_num_first_round_oracles() -> usize {
        3
    }

    /// Output the degree bounds of oracles in the first round.
    pub fn prover_first_round_degree_bounds(
        _info: &IndexInfo<F>,
    ) -> impl Iterator<Item = Option<usize>> {
        vec![None; 3].into_iter()
    }

    /// Output the second round message and the next state.
    pub fn prover_second_round<'a, R: RngCore>(
        ver_message: &VerifierFirstMsg<F>,
        mut state: ProverState<'a, F>,
        _r: &mut R,
    ) -> (ProverMsg<F>, ProverSecondOracles<F>, ProverState<'a, F>, DensePolynomial<F>) {
        let round_time = start_timer!(|| "AHP::Prover::SecondRound");

        let domain_h = state.domain_h;
        let zk_bound = state.zk_bound;

        // the prover receives alpha and all the etas from the verifier
        let VerifierFirstMsg {
            alpha,
            eta_a,
            eta_b,
            eta_c,
        } = *ver_message;

        let summed_z_m_poly_time = start_timer!(|| "Compute z_m poly");
        let (z_a_poly, z_b_poly) = state.mz_polys.as_ref().unwrap();
        let z_c_poly = z_a_poly.polynomial() * z_b_poly.polynomial();

        let mut summed_z_m_coeffs = z_c_poly.coeffs;
        // Note: Can't combine these two loops, because z_c_poly has 2x the degree
        // of z_a_poly and z_b_poly, so the second loop gets truncated due to
        // the `zip`s.
        cfg_iter_mut!(summed_z_m_coeffs).for_each(|c| *c *= &eta_c);
        cfg_iter_mut!(summed_z_m_coeffs)
            .zip(&z_a_poly.polynomial().coeffs)
            .zip(&z_b_poly.polynomial().coeffs)
            .for_each(|((c, a), b)| *c += &(eta_a * a + &(eta_b * b)));

        let summed_z_m = DensePolynomial::from_coefficients_vec(summed_z_m_coeffs); // sum eta * z_M where M is A,B or C
        end_timer!(summed_z_m_poly_time);

        let r_alpha_x_evals_time = start_timer!(|| "Compute r_alpha_x evals");
        let r_alpha_x_evals =
            domain_h.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(alpha);
        end_timer!(r_alpha_x_evals_time);

        let r_alpha_poly_time = start_timer!(|| "Compute r_alpha_x poly");
        let r_alpha_poly = DensePolynomial::from_coefficients_vec(domain_h.ifft(&r_alpha_x_evals));
        end_timer!(r_alpha_poly_time);

        // we call the function to compute t(X)
        let t_poly_time = start_timer!(|| "Compute t poly");
        let t_poly = Self::calculate_t(
            vec![&state.index.a, &state.index.b, &state.index.c].into_iter(),
            &[eta_a, eta_b, eta_c],
            state.domain_x,
            state.domain_h,
            r_alpha_x_evals.to_vec(),
        );
        end_timer!(t_poly_time);

        let z_poly_time = start_timer!(|| "Compute z poly");

        let domain_x = GeneralEvaluationDomain::new(state.formatted_input_assignment.len())
            .ok_or(SynthesisError::PolynomialDegreeTooLarge)
            .unwrap();
        let x_poly = EvaluationsOnDomain::from_vec_and_domain(
            state.formatted_input_assignment.clone(),
            domain_x,
        )
        .interpolate();
        let w_poly = state.w_poly.as_ref().unwrap();
        let mut z_poly = w_poly.polynomial().mul_by_vanishing_poly(domain_x);
        cfg_iter_mut!(z_poly.coeffs)
            .zip(&x_poly.coeffs)
            .for_each(|(z, x)| *z += x);
        assert!(z_poly.degree() < domain_h.size() + zk_bound);

        end_timer!(z_poly_time);

        let q_1_time = start_timer!(|| "Compute q_1 poly"); // the first part of the equal

        let mul_domain_size = *[
            r_alpha_poly.coeffs.len() + summed_z_m.coeffs.len(),
            t_poly.coeffs.len() + z_poly.len(),
        ]
        .iter()
        .max()
        .unwrap();
        let mul_domain = GeneralEvaluationDomain::new(mul_domain_size)
            .expect("field is not smooth enough to construct domain");
        let mut r_alpha_evals = r_alpha_poly.evaluate_over_domain_by_ref(mul_domain); // r(alpha, X)
        let summed_z_m_evals = summed_z_m.evaluate_over_domain_by_ref(mul_domain);     // summed_z_m evaluated X
        let z_poly_evals = z_poly.evaluate_over_domain_by_ref(mul_domain);          // z^hat(X)
        let t_poly_m_evals = t_poly.evaluate_over_domain_by_ref(mul_domain);        // t(X)

        cfg_iter_mut!(r_alpha_evals.evals)
            .zip(&summed_z_m_evals.evals)
            .zip(&z_poly_evals.evals)
            .zip(&t_poly_m_evals.evals)
            .for_each(|(((a, b), &c), d)| {
                *a *= b;
                *a -= c * d;
            });
        let rhs = r_alpha_evals.interpolate();
        let q_1 = &rhs;
        end_timer!(q_1_time);
        
        // we compute the first sumcheck where we compute g_1 and h_1
        let sumcheck_time = start_timer!(|| "Compute sumcheck h and g polys");
        let (h_1, x_g_1) = q_1.divide_by_vanishing_poly(domain_h).unwrap();
        let g_1 = DensePolynomial::from_coefficients_slice(&x_g_1.coeffs[1..]);
        end_timer!(sumcheck_time);

        let msg = ProverMsg::EmptyMessage;

        assert!(g_1.degree() <= domain_h.size() - 2);
        assert!(h_1.degree() <= 2 * domain_h.size() + 2 * zk_bound - 2);

        // prover sends g_1 and h_1 to verifier
        let oracles = ProverSecondOracles {
            g_1: LabeledPolynomial::new("g_1".into(), g_1, Some(domain_h.size() - 2), Some(1)),
            h_1: LabeledPolynomial::new("h_1".into(), h_1, None, None),
        };

        state.w_poly = None;
        state.verifier_first_msg = Some(*ver_message);
        end_timer!(round_time);

        (msg, oracles, state, t_poly)
    }

    /// Output the number of oracles sent by the prover in the second round.
    pub fn prover_num_second_round_oracles() -> usize {
        2
    }

    /// Output the degree bounds of oracles in the second round.
    pub fn prover_second_round_degree_bounds(
        info: &IndexInfo<F>,
    ) -> impl Iterator<Item = Option<usize>> {
        let h_domain_size =
            GeneralEvaluationDomain::<F>::compute_size_of_domain(info.num_constraints).unwrap();

        vec![Some(h_domain_size - 2), None].into_iter()
    }

    fn calculate_y<'a>(
        matrices: impl Iterator<Item = &'a Matrix<F>>,
        matrix_randomizers: &[F],
        input_domain: GeneralEvaluationDomain<F>,
        domain_h: GeneralEvaluationDomain<F>,
        r_alpha_x_on_h: Vec<F>
    ) -> DensePolynomial<F> {
        let mut y_evals_on_h = vec![F::zero(); domain_h.size()];
        for (matrix, eta) in matrices.zip(matrix_randomizers) {
            for (r, row) in matrix.iter().enumerate() {
                for (coeff, c) in row.iter() {
                    let index = domain_h.reindex_by_subdomain(input_domain, *c);
                    y_evals_on_h[index] += *eta * coeff * r_alpha_x_on_h[r];
                }
            }
        }
        EvaluationsOnDomain::from_vec_and_domain(y_evals_on_h, domain_h).interpolate()
    }   

    // Output the first accumulation step
    pub fn prover_first_round_accumulation<'a> (
        matrices: Vec<Vec<Vec<(F, usize)>>>,
        all_variables: Vec<Vec<F>>,
        num_constraints: usize,
        num_input_variables: usize)
        -> (ProverMsg<F>, F, F)
        {        
        let domain_h: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(num_constraints).unwrap();
        let domain_x: GeneralEvaluationDomain<F>  = GeneralEvaluationDomain::new(num_input_variables).unwrap();
    
        let r_alpha1_x_evals =
            domain_h.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(all_variables[0][0]);

        let r_alpha2_x_evals =
            domain_h.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(all_variables[1][0]);
        
        let y_11_ = Self::calculate_y(
            vec![&matrices[0], &matrices[1], &matrices[2]].into_iter(),
            &[all_variables[0][1], all_variables[0][2], all_variables[0][3]],
            domain_x,
            domain_h,
            r_alpha1_x_evals.to_vec(),
        );

        let y_12_ = Self::calculate_y(
            vec![&matrices[0], &matrices[1], &matrices[2]].into_iter(),
            &[all_variables[0][1], all_variables[0][2], all_variables[0][3]],
            domain_x,
            domain_h,
            r_alpha2_x_evals.to_vec(),
        );

        let y_21_ = Self::calculate_y(
            vec![&matrices[0], &matrices[1], &matrices[2]].into_iter(),
            &[all_variables[1][1], all_variables[1][2], all_variables[1][3]],
            domain_x,
            domain_h,
            r_alpha1_x_evals.to_vec(),
        );

        let y_22_ = Self::calculate_y(
            vec![&matrices[0], &matrices[1], &matrices[2]].into_iter(),
            &[all_variables[1][1], all_variables[1][2], all_variables[1][3]],
            domain_x,
            domain_h,
            r_alpha2_x_evals.to_vec(),
        );

        let y_112 = y_11_.evaluate(&all_variables[1][4]);
        let y_121 = y_12_.evaluate(&all_variables[0][4]);
        let y_211 = y_21_.evaluate(&all_variables[0][4]);
        let y_122 = y_12_.evaluate(&all_variables[1][4]);
        let y_221 = y_22_.evaluate(&all_variables[0][4]);
        let y_212 = y_21_.evaluate(&all_variables[1][4]);        
        
        let y_1 = y_112 + y_121 + y_211;
        let y_2 = y_122 + y_212 + y_221;
      
        (ProverMsg::EmptyMessage, y_1, y_2)
    }

    pub fn prover_second_round_accumulation <'a>(
        matrices: Vec<Vec<Vec<(F, usize)>>>, 
        all_variables: Vec<Vec<F>>,
        gamma: F,
        num_constraints: usize,
        num_input_variables: usize) 
        -> (ProverMsg<F>, ProverSecondOraclesAcc<F>){
        let domain_h: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(num_constraints).unwrap();
        let domain_x: GeneralEvaluationDomain<F>  = GeneralEvaluationDomain::new(num_input_variables).unwrap();
    
        let r_alpha1_x_evals =
            domain_h.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(all_variables[0][0]);

        let r_alpha2_x_evals =
            domain_h.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(all_variables[1][0]);
        
        let mut r_alphas_x_evals = Vec::new();

        for i in 0..r_alpha1_x_evals.len(){
            r_alphas_x_evals.push(r_alpha1_x_evals[i] + gamma * r_alpha2_x_evals[i])
        }

        let q_alphas = Self::calculate_y(
            vec![&matrices[0], &matrices[1], &matrices[2]].into_iter(),
            &[(all_variables[0][1] + gamma * all_variables[1][1]), (all_variables[0][2] + gamma * all_variables[1][2]), (all_variables[0][3] + gamma * all_variables[1][3])],
            domain_x,
            domain_h,
            r_alphas_x_evals.to_vec(),
        );

        let oracles = ProverSecondOraclesAcc {
            q_alphas_beta_1: LabeledPolynomial::new("q_alphas_beta_1".into(), q_alphas.clone(), None, None),
            q_alphas_beta_2: LabeledPolynomial::new("q_alphas_beta_2".into(), q_alphas.clone(), None, None),
            q_alphas_beta: LabeledPolynomial::new("q_alphas_beta".into(), q_alphas.clone(), None, None),
        };

        (ProverMsg::EmptyMessage, oracles)
    }
    
    pub fn prover_third_round_accumulation <'a>(
        matrices: Vec<Vec<Vec<(F, usize)>>>,
        all_variables: Vec<Vec<F>>,
        gamma: F,
        beta: F,
        num_constraints: usize,
        num_input_variables: usize) 
        -> (ProverMsg<F>, F, F){
        let domain_h: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(num_constraints).unwrap();
        let domain_x: GeneralEvaluationDomain<F>  = GeneralEvaluationDomain::new(num_input_variables).unwrap();
    
        let r_alpha1_x_evals =
            domain_h.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(all_variables[0][0]);

        let r_alpha2_x_evals =
            domain_h.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(all_variables[1][0]);

        let q_beta_alpha1 = Self::calculate_y(
            vec![&matrices[0], &matrices[1], &matrices[2]].into_iter(),
            &[(all_variables[0][1] + gamma * all_variables[1][1]), (all_variables[0][2] + gamma * all_variables[1][2]), (all_variables[0][3] + gamma * all_variables[1][3])],
            domain_x,
            domain_h,
            r_alpha1_x_evals.to_vec(),
        );

        let q_beta_alpha2 = Self::calculate_y(
            vec![&matrices[0], &matrices[1], &matrices[2]].into_iter(),
            &[(all_variables[0][1] + gamma * all_variables[1][1]), (all_variables[0][2] + gamma * all_variables[1][2]), (all_variables[0][3] + gamma * all_variables[1][3])],
            domain_x,
            domain_h,
            r_alpha2_x_evals.to_vec(),
        );

        let q_beta_alpha1 = q_beta_alpha1.evaluate(&beta);
        let q_beta_alpha2 = q_beta_alpha2.evaluate(&beta);

        (ProverMsg::EmptyMessage, q_beta_alpha1, q_beta_alpha2)
    }

    pub fn prover_last_round_accumulation <'a>(
        matrices: Vec<Vec<Vec<(F, usize)>>>,
        all_variables: Vec<Vec<F>>,
        gamma: F,
        beta: F,
        alpha: F,
        num_constraints: usize,
        num_input_variables: usize) 
        -> (ProverMsg<F>, F){
        let domain_h: GeneralEvaluationDomain<F> = GeneralEvaluationDomain::new(num_constraints).unwrap();
        let domain_x: GeneralEvaluationDomain<F>  = GeneralEvaluationDomain::new(num_input_variables).unwrap();
    
        let r_alpha_x_evals =
            domain_h.batch_eval_unnormalized_bivariate_lagrange_poly_with_diff_inputs(alpha);

        let q_beta_alpha = Self::calculate_y(
            vec![&matrices[0], &matrices[1], &matrices[2]].into_iter(),
            &[(all_variables[0][1] + gamma * all_variables[1][1]), (all_variables[0][2] + gamma * all_variables[1][2]), (all_variables[0][3] + gamma * all_variables[1][3])],
            domain_x,
            domain_h,
            r_alpha_x_evals.to_vec(),
        );

        let q_beta_alpha = q_beta_alpha.evaluate(&beta);

        (ProverMsg::EmptyMessage, q_beta_alpha)
    }
}
