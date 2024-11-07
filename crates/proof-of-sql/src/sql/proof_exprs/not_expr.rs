use super::{DynProofExpr, ProofExpr};
use crate::{
    base::{
        commitment::Commitment,
        database::{
            Column, ColumnRef, ColumnType, ColumnarValue, CommitmentAccessor, DataAccessor,
        },
        map::IndexSet,
        proof::ProofError,
        scalar::Scalar,
    },
    sql::proof::{CountBuilder, FinalRoundBuilder, VerificationBuilder},
};
use alloc::boxed::Box;
use bumpalo::Bump;
use serde::{Deserialize, Serialize};

/// Provable logical NOT expression
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct NotExpr {
    expr: Box<DynProofExpr>,
}

impl NotExpr {
    /// Create logical NOT expression
    pub fn new(expr: Box<DynProofExpr>) -> Self {
        Self { expr }
    }
}

impl ProofExpr for NotExpr {
    fn count(&self, builder: &mut CountBuilder) -> Result<(), ProofError> {
        self.expr.count(builder)
    }

    fn data_type(&self) -> ColumnType {
        ColumnType::Boolean
    }

    #[tracing::instrument(name = "NotExpr::result_evaluate", level = "debug", skip_all)]
    fn result_evaluate<'a, S: Scalar>(
        &self,
        alloc: &'a Bump,
        accessor: &'a dyn DataAccessor<S>,
    ) -> ColumnarValue<'a, S> {
        let expr_columnar_value: ColumnarValue<'a, S> = self.expr.result_evaluate(alloc, accessor);
        expr_columnar_value
            .apply_boolean_unary_operator(|l| !*l, alloc)
            .expect("Failed to apply boolean unary operator")
    }

    #[tracing::instrument(name = "NotExpr::prover_evaluate", level = "debug", skip_all)]
    fn prover_evaluate<'a, S: Scalar>(
        &self,
        builder: &mut FinalRoundBuilder<'a, S>,
        alloc: &'a Bump,
        accessor: &'a dyn DataAccessor<S>,
    ) -> Column<'a, S> {
        let expr_column: Column<'a, S> = self.expr.prover_evaluate(builder, alloc, accessor);
        let expr = expr_column.as_boolean().expect("expr is not boolean");
        Column::Boolean(alloc.alloc_slice_fill_with(expr.len(), |i| !expr[i]))
    }

    fn verifier_evaluate<C: Commitment>(
        &self,
        builder: &mut VerificationBuilder<C>,
        accessor: &dyn CommitmentAccessor<C>,
    ) -> Result<C::Scalar, ProofError> {
        let eval = self.expr.verifier_evaluate(builder, accessor)?;
        Ok(builder.mle_evaluations.input_one_evaluation - eval)
    }

    fn get_column_references(&self, columns: &mut IndexSet<ColumnRef>) {
        self.expr.get_column_references(columns);
    }
}
