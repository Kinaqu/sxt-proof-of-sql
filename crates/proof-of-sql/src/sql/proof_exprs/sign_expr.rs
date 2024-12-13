use super::is_within_acceptable_range;
use crate::{
    base::{
        bit::{
            bit_mask_utils::{is_bit_mask_negative_representation, make_bit_mask},
            compute_varying_bit_matrix, BitDistribution,
        },
        proof::ProofError,
        scalar::{Scalar, ScalarExt},
    },
    sql::proof::{CountBuilder, FinalRoundBuilder, SumcheckSubpolynomialType, VerificationBuilder},
};
use alloc::{boxed::Box, vec, vec::Vec};
use bnum::types::U256;
use bumpalo::Bump;

/// Count the number of components needed to prove a sign decomposition
pub fn count_sign(builder: &mut CountBuilder) -> Result<(), ProofError> {
    let dist = builder.consume_bit_distribution()?;
    if !is_within_acceptable_range(&dist) {
        return Err(ProofError::VerificationError {
            error: "bit distribution outside of acceptable range",
        });
    }
    if dist.num_varying_bits() == 0 {
        return Ok(());
    }
    builder.count_intermediate_mles(dist.num_varying_bits());
    builder.count_subpolynomials(dist.num_varying_bits());
    if dist.num_varying_bits() > 0 {
        builder.count_degree(3);
    }
    Ok(())
}

/// Compute the sign bit for a column of scalars.
///
/// # Panics
/// Panics if `bits.last()` is `None` or if `result.len()` does not match `table_length`.
///
/// todo! make this more efficient and targeted at just the sign bit rather than all bits to create a proof
pub fn result_evaluate_sign<'a, S: Scalar>(
    table_length: usize,
    alloc: &'a Bump,
    expr: &'a [S],
) -> &'a [bool] {
    assert_eq!(table_length, expr.len());
    let signs = expr
        .iter()
        .map(|s| make_bit_mask(*s))
        .map(is_bit_mask_negative_representation)
        .collect::<Vec<_>>();
    assert_eq!(table_length, signs.len());
    alloc.alloc_slice_copy(&signs)
}

/// Prove the sign decomposition for a column of scalars.
///
/// # Panics
/// Panics if `bits.last()` is `None`.
///
/// If x1, ..., xn denotes the data, prove the column of
/// booleans, i.e. sign bits, s1, ..., sn where si == 1 if xi > MID and
/// `si == 1` if `xi <= MID` and `MID` is defined in `base/bit/abs_bit_mask.rs`
///
/// Note: We can only prove the sign bit for non-zero scalars, and we restict
/// the range of non-zero scalar so that there is a unique sign representation.
pub fn prover_evaluate_sign<'a, S: Scalar>(
    builder: &mut FinalRoundBuilder<'a, S>,
    alloc: &'a Bump,
    expr: &'a [S],
) -> &'a [bool] {
    // bit_distribution
    let dist = BitDistribution::new::<S, _>(expr);
    builder.produce_bit_distribution(dist.clone());

    if dist.num_varying_bits() > 0 {
        // prove that the bits are binary
        let bits = compute_varying_bit_matrix(alloc, expr, &dist);
        prove_bits_are_binary(builder, &bits);
    }

    // This might panic if `bits.last()` returns `None`.

    let signs = expr
        .iter()
        .map(|s| make_bit_mask(*s))
        .map(is_bit_mask_negative_representation)
        .collect::<Vec<_>>();
    alloc.alloc_slice_copy(&signs)
}

/// Verify the sign decomposition for a column of scalars.
///
/// # Panics
/// Panics if `bit_evals.last()` is `None`.
///
/// See [`prover_evaluate_sign`].
pub fn verifier_evaluate_sign<S: Scalar>(
    builder: &mut VerificationBuilder<S>,
    eval: S,
    one_eval: S,
) -> Result<S, ProofError> {
    // bit_distribution
    let dist = builder.consume_bit_distribution();
    let num_varying_bits = dist.num_varying_bits();

    // extract evaluations and commitmens of the multilinear extensions for the varying
    // bits of the expression
    let mut bit_evals = Vec::with_capacity(num_varying_bits);
    for _ in 0..num_varying_bits {
        let eval = builder.consume_intermediate_mle();
        bit_evals.push(eval);
    }

    // establish that the bits are binary
    verify_bits_are_binary(builder, &bit_evals);

    verify_bit_decomposition(eval, one_eval, &bit_evals, &dist)
        .then(|| dist.sign_eval(&bit_evals))
        .ok_or(ProofError::VerificationError {
            error: "invalid bit_decomposition",
        })
}

fn prove_bits_are_binary<'a, S: Scalar>(
    builder: &mut FinalRoundBuilder<'a, S>,
    bits: &[&'a [bool]],
) {
    for &seq in bits {
        builder.produce_intermediate_mle(seq);
        builder.produce_sumcheck_subpolynomial(
            SumcheckSubpolynomialType::Identity,
            vec![
                (S::one(), vec![Box::new(seq)]),
                (-S::one(), vec![Box::new(seq), Box::new(seq)]),
            ],
        );
    }
}

fn verify_bits_are_binary<S: Scalar>(builder: &mut VerificationBuilder<S>, bit_evals: &[S]) {
    for bit_eval in bit_evals {
        builder.produce_sumcheck_subpolynomial_evaluation(
            SumcheckSubpolynomialType::Identity,
            *bit_eval - *bit_eval * *bit_eval,
        );
    }
}

/// # Panics
/// Panics if `bit_evals.last()` returns `None`.
///
/// This function checks the consistency of the bit evaluations with the expression evaluation.
fn verify_bit_decomposition<S: ScalarExt>(
    expr_eval: S,
    one_eval: S,
    bit_evals: &[S],
    dist: &BitDistribution,
) -> bool {
    let mut eval = expr_eval;
    let sign_eval = dist.sign_eval(bit_evals);
    eval += one_eval
        * (S::from_wrapping(U256::ONE << 255)
            - ((S::ONE - sign_eval) * S::from_wrapping(dist.inverse_sign_mask())
                + sign_eval * S::from_wrapping(dist.sign_mask())));

    dist.for_enumerated_vary_mask(|vary_index, bit_index: u8| {
        let mult = U256::ONE << bit_index;
        let bit_eval = bit_evals[vary_index];
        eval -= S::from_wrapping(mult) * bit_eval;
    });
    eval == S::ZERO
}
