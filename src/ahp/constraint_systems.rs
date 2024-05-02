#![allow(non_snake_case)]

use crate::ahp::indexer::Matrix;
use crate::ahp::*;
use ark_ff::{Field, PrimeField};
use ark_relations::{
    lc,
    r1cs::{ConstraintMatrices, ConstraintSystemRef},
};

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

pub(crate) fn balance_matrices<F: Field>(a_matrix: &mut Matrix<F>, b_matrix: &mut Matrix<F>) {
    let mut a_density: usize = a_matrix.iter().map(|row| row.len()).sum();
    let mut b_density: usize = b_matrix.iter().map(|row| row.len()).sum();
    let mut max_density = core::cmp::max(a_density, b_density);
    let mut a_is_denser = a_density == max_density;
    for (a_row, b_row) in a_matrix.iter_mut().zip(b_matrix) {
        if a_is_denser {
            let a_row_size = a_row.len();
            let b_row_size = b_row.len();
            core::mem::swap(a_row, b_row);
            a_density = a_density - a_row_size + b_row_size;
            b_density = b_density - b_row_size + a_row_size;
            max_density = core::cmp::max(a_density, b_density);
            a_is_denser = a_density == max_density;
        }
    }
}

pub(crate) fn num_non_zero<F: PrimeField>(matrices: &ConstraintMatrices<F>) -> usize {
    *[
        matrices.a_num_non_zero,
        matrices.b_num_non_zero,
        matrices.c_num_non_zero,
    ]
    .iter()
    .max()
    .unwrap()
}

pub(crate) fn make_matrices_square_for_indexer<F: PrimeField>(cs: ConstraintSystemRef<F>) {
    let num_variables = cs.num_instance_variables() + cs.num_witness_variables();
    let matrix_dim = padded_matrix_dim(num_variables, cs.num_constraints());
    make_matrices_square(cs.clone(), num_variables);
    assert_eq!(
        cs.num_instance_variables() + cs.num_witness_variables(),
        cs.num_constraints(),
        "padding failed!"
    );
    assert_eq!(
        cs.num_instance_variables() + cs.num_witness_variables(),
        matrix_dim,
        "padding does not result in expected matrix size!"
    );
}

/// This must *always* be in sync with `make_matrices_square`.
pub(crate) fn padded_matrix_dim(num_formatted_variables: usize, num_constraints: usize) -> usize {
    core::cmp::max(num_formatted_variables, num_constraints)
}

pub(crate) fn pad_input_for_indexer_and_prover<F: PrimeField>(cs: ConstraintSystemRef<F>) {
    let formatted_input_size = cs.num_instance_variables();

    let domain_x = GeneralEvaluationDomain::<F>::new(formatted_input_size);
    assert!(domain_x.is_some());

    let padded_size = domain_x.unwrap().size();

    if padded_size > formatted_input_size {
        for _ in 0..(padded_size - formatted_input_size) {
            cs.new_input_variable(|| Ok(F::zero())).unwrap();
        }
    }
}

pub(crate) fn make_matrices_square<F: Field>(
    cs: ConstraintSystemRef<F>,
    num_formatted_variables: usize,
) {
    let num_constraints = cs.num_constraints();
    let matrix_padding = ((num_formatted_variables as isize) - (num_constraints as isize)).abs();

    if num_formatted_variables > num_constraints {
        // Add dummy constraints of the form 0 * 0 == 0
        for _ in 0..matrix_padding {
            cs.enforce_constraint(lc!(), lc!(), lc!())
                .expect("enforce 0 * 0 == 0 failed");
        }
    } else {
        // Add dummy unconstrained variables
        for _ in 0..matrix_padding {
            let _ = cs
                .new_witness_variable(|| Ok(F::one()))
                .expect("alloc failed");
        }
    }
}

/* ************************************************************************* */
/* ************************************************************************* */
/* ************************************************************************* */

/// Formats the public input according to the requirements of the constraint
/// system
pub(crate) fn format_public_input<F: PrimeField>(public_input: &[F]) -> Vec<F> {
    let mut input = vec![F::one()];
    input.extend_from_slice(public_input);
    input
}

/// Takes in a previously formatted public input and removes the formatting
/// imposed by the constraint system.
pub(crate) fn unformat_public_input<F: PrimeField>(input: &[F]) -> Vec<F> {
    input[1..].to_vec()
}

pub(crate) fn make_matrices_square_for_prover<F: PrimeField>(cs: ConstraintSystemRef<F>) {
    let num_variables = cs.num_instance_variables() + cs.num_witness_variables();
    make_matrices_square(cs.clone(), num_variables);
    assert_eq!(
        cs.num_instance_variables() + cs.num_witness_variables(),
        cs.num_constraints(),
        "padding failed!"
    );
}
