/// Provides trait implementations for Curve25519Scalar
pub mod curve_25519_scalar;
#[cfg(test)]
mod curve_25519_scalar_tests;
/// The implementations for InnerProductProof
pub mod inner_product_proof;
/// Provides trait implementations for RistrettoPoint
pub mod ristretto_point;

/// Provides a test accessor that is inner product specific
pub mod inner_product_test_accessor;

#[cfg(test)]
mod inner_product_proof_tests;
