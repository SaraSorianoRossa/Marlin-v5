#![allow(non_snake_case)]

use crate::ahp::{
    AHPForR1CS, Error, LabeledPolynomial,
};
use crate::Vec;
use ark_ff::PrimeField;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, OptimizationGoal, SynthesisMode,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::{
    io::{Read, Write},
    marker::PhantomData,
};
use derivative::Derivative;

use crate::ahp::constraint_systems::{
    balance_matrices, make_matrices_square_for_indexer, num_non_zero,
    pad_input_for_indexer_and_prover,
};

/// Information about the index, including the field of definition, the number of
/// variables, the number of constraints, and the maximum number of non-zero
/// entries in any of the constraint matrices.
#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(Clone(bound = ""), Copy(bound = ""))]
pub struct IndexInfo<F> {
    /// The total number of variables in the constraint system.
    pub num_variables: usize,
    /// The number of constraints.
    pub num_constraints: usize,
    /// The maximum number of non-zero entries in any constraint matrix.
    pub num_non_zero: usize,
    /// The number of input elements.
    pub num_instance_variables: usize,

    #[doc(hidden)]
    f: PhantomData<F>,
}

impl<F: PrimeField> ark_ff::ToBytes for IndexInfo<F> {
    fn write<W: Write>(&self, mut w: W) -> ark_std::io::Result<()> {
        (self.num_variables as u64).write(&mut w)?;
        (self.num_constraints as u64).write(&mut w)?;
        (self.num_non_zero as u64).write(&mut w)
    }
}

impl<F: PrimeField> IndexInfo<F> {
    /// The maximum degree of polynomial required to represent this index in the
    /// the AHP.
    pub fn max_degree(&self) -> usize {
        AHPForR1CS::<F>::max_degree(self.num_constraints, self.num_variables, self.num_non_zero)
            .unwrap()
    }
}

/// Represents a matrix.
pub type Matrix<F> = Vec<Vec<(F, usize)>>;

#[derive(Derivative)]
#[derivative(Clone(bound = "F: PrimeField"))]
/// The indexed version of the constraint system.
/// This struct contains three kinds of objects:
/// 1) `index_info` is information about the index, such as the size of the
///     public input
/// 2) `{a,b,c}` are the matrices defining the R1CS instance
/// 3) `{a,b,c}_star_arith` are structs containing information about A^*, B^*, and C^*,
/// which are matrices defined as `M^*(i, j) = M(j, i) * u_H(j, j)`.
#[derive(CanonicalSerialize, CanonicalDeserialize)]
pub struct Index<F: PrimeField> {
    /// Information about the index.
    pub index_info: IndexInfo<F>,

    /// The A matrix for the R1CS instance
    pub a: Matrix<F>,
    /// The B matrix for the R1CS instance
    pub b: Matrix<F>,
    /// The C matrix for the R1CS instance
    pub c: Matrix<F>,
}

impl<F: PrimeField> Index<F> {
    /// The maximum degree required to represent polynomials of this index.
    pub fn max_degree(&self) -> usize {
        self.index_info.max_degree()
    }

    /// Iterate over the indexed polynomials.
    pub fn iter(&self) -> impl Iterator<Item = &LabeledPolynomial<F>> {
        ark_std::vec![
        ]
        .into_iter()
    }
}

impl<F: PrimeField> AHPForR1CS<F> {
    /// Generate the index for this constraint system.
    pub fn index<C: ConstraintSynthesizer<F>>(c: C) -> Result<Index<F>, Error> {
        let index_time = start_timer!(|| "AHP::Index");

        let constraint_time = start_timer!(|| "Generating constraints");
        let ics = ConstraintSystem::new_ref();
        ics.set_optimization_goal(OptimizationGoal::Weight);
        ics.set_mode(SynthesisMode::Setup);
        c.generate_constraints(ics.clone())?;
        end_timer!(constraint_time);

        let padding_time = start_timer!(|| "Padding matrices to make them square");
        pad_input_for_indexer_and_prover(ics.clone());
        end_timer!(padding_time);
        let matrix_processing_time: ark_std::perf_trace::TimerInfo = start_timer!(|| "Processing matrices");
        ics.finalize();
        make_matrices_square_for_indexer(ics.clone());
        let matrices = ics.to_matrices().expect("should not be `None`");
        let num_non_zero_val = num_non_zero::<F>(&matrices);
        let (mut a, mut b, c) = (matrices.a, matrices.b, matrices.c);
        balance_matrices(&mut a, &mut b);
        end_timer!(matrix_processing_time);

        let (num_formatted_input_variables, num_witness_variables, num_constraints, num_non_zero) = (
            ics.num_instance_variables(),
            ics.num_witness_variables(),
            ics.num_constraints(),
            num_non_zero_val,
        );
        let num_variables = num_formatted_input_variables + num_witness_variables;

        if num_constraints != num_formatted_input_variables + num_witness_variables {
            eprintln!(
                "number of (formatted) input_variables: {}",
                num_formatted_input_variables
            );
            eprintln!("number of witness_variables: {}", num_witness_variables);
            eprintln!("number of num_constraints: {}", num_constraints);
            eprintln!("number of num_non_zero: {}", num_non_zero);
            return Err(Error::NonSquareMatrix);
        }

        if !Self::num_formatted_public_inputs_is_admissible(num_formatted_input_variables) {
            return Err(Error::InvalidPublicInputLength);
        }

        let index_info = IndexInfo {
            num_variables,
            num_constraints,
            num_non_zero,
            num_instance_variables: num_formatted_input_variables,

            f: PhantomData,
        };

        end_timer!(index_time);
        Ok(Index {
            index_info,

            a,
            b,
            c,
        })
    }
}
