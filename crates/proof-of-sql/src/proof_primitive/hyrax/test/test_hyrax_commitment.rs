use super::test_hyrax_configuration::TestHyraxConfiguration;
use crate::{
    proof_primitive::hyrax::{
        base::hyrax_commitment::HyraxCommitment,
    },
};
pub type TestHyraxCommitment = HyraxCommitment<TestHyraxConfiguration>;
