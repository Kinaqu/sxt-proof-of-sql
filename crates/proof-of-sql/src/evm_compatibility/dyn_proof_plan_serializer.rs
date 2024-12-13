use crate::{
    base::{
        database::{ColumnRef, LiteralValue, TableRef},
        map::{IndexMap, IndexSet},
        scalar::Scalar,
    },
    sql::{
        parse::QueryExpr,
        proof::ProofPlan,
        proof_exprs::{
            AliasedDynProofExpr, ColumnExpr, DynProofExpr, EqualsExpr, LiteralExpr, TableExpr,
        },
        proof_plans::{DynProofPlan, FilterExec},
    },
};
use core::{fmt::Debug, marker::PhantomData};
use snafu::{OptionExt, Snafu};
use std::convert::TryFrom;
use zerocopy::AsBytes;

const FILTER_EXEC_NUM: u8 = 0;
const COLUMN_EXPR_NUM: u8 = 0;
const EQUALS_EXPR_NUM: u8 = 1;
const LITERAL_EXPR_NUM: u8 = 2;
const BIGINT_TYPE_NUM: u8 = 0;

#[derive(Debug, Snafu)]
/// Errors that can occur during serialization
pub enum SerializationError {
    #[snafu(display("Not supported"))]
    /// A SQL expression that is not supported by the serialization
    NotSupported,
    #[snafu(display("Too many results"))]
    /// The number of results in a filter expression is too large
    TooManyResults,
    #[snafu(display("Too many tables"))]
    /// The number of tables in a plan is too large
    TooManyTables,
    #[snafu(display("Too many columns"))]
    /// The number of columns in a plan is too large
    TooManyColumns,
    #[snafu(display("Table not found"))]
    /// A table reference was not found
    TableNotFound,
    #[snafu(display("Column not found"))]
    /// A column reference was not found
    ColumnNotFound,
}

impl<S: Scalar> TryFrom<&QueryExpr> for SerializedDynProofPlan<S> {
    type Error = SerializationError;
    fn try_from(expr: &QueryExpr) -> Result<Self, Self::Error> {
        if expr.postprocessing().is_empty() {
            expr.proof_expr().try_into()
        } else {
            NotSupportedSnafu.fail()
        }
    }
}

impl<S: Scalar> TryFrom<&DynProofPlan> for SerializedDynProofPlan<S> {
    type Error = SerializationError;
    fn try_from(plan: &DynProofPlan) -> Result<Self, Self::Error> {
        SerializedDynProofPlan::try_new(plan.get_table_references(), plan.get_column_references())?
            .serialize_dyn_proof_plan(plan)
    }
}

/// A serialized proof plan
pub struct SerializedDynProofPlan<S: Scalar> {
    table_refs: IndexMap<TableRef, u8>,
    column_refs: IndexMap<ColumnRef, u8>,
    data: Vec<u8>,
    _phantom: PhantomData<S>,
}
impl<S: Scalar> SerializedDynProofPlan<S> {
    /// Convert the serialized plan into a byte vector
    pub fn into_bytes(self) -> Vec<u8> {
        self.data
    }
    fn try_new(
        table_refs: IndexSet<TableRef>,
        column_refs: IndexSet<ColumnRef>,
    ) -> Result<Self, SerializationError> {
        if u8::try_from(table_refs.len()).is_err() {
            TooManyTablesSnafu.fail()?;
        }
        if u8::try_from(column_refs.len()).is_err() {
            TooManyColumnsSnafu.fail()?;
        }
        Ok(Self {
            table_refs: table_refs.into_iter().zip(0..).collect(),
            column_refs: column_refs.into_iter().zip(0..).collect(),
            data: Vec::new(),
            _phantom: PhantomData,
        })
    }
    fn serialize_u8(mut self, value: u8) -> Self {
        self.data.push(value);
        self
    }
    fn serialize_scalar(mut self, value: S) -> Self {
        let mut limbs: [u64; 4] = value.into();
        limbs.as_bytes_mut().reverse();
        self.data.extend_from_slice(limbs.as_bytes());
        self
    }
    fn serialize_dyn_proof_plan(self, plan: &DynProofPlan) -> Result<Self, SerializationError> {
        match plan {
            DynProofPlan::Filter(filter_exec) => self
                .serialize_u8(FILTER_EXEC_NUM)
                .serialize_filter_exec(filter_exec),
            _ => NotSupportedSnafu.fail(),
        }
    }

    fn serialize_filter_exec(self, filter_exec: &FilterExec) -> Result<Self, SerializationError> {
        let result_count = u8::try_from(filter_exec.aliased_results.len())
            .ok()
            .context(TooManyResultsSnafu)?;

        filter_exec
            .aliased_results
            .iter()
            .try_fold(
                self.serialize_table_expr(&filter_exec.table)?
                    .serialize_u8(result_count),
                Self::serialize_aliased_dyn_proof_expr,
            )?
            .serialize_dyn_proof_expr(&filter_exec.where_clause)
    }

    fn serialize_dyn_proof_expr(self, expr: &DynProofExpr) -> Result<Self, SerializationError> {
        match expr {
            DynProofExpr::Column(column_expr) => self
                .serialize_u8(COLUMN_EXPR_NUM)
                .serialize_column_expr(column_expr),
            DynProofExpr::Equals(equals_expr) => self
                .serialize_u8(EQUALS_EXPR_NUM)
                .serialize_equals_expr(equals_expr),
            DynProofExpr::Literal(literal_expr) => self
                .serialize_u8(LITERAL_EXPR_NUM)
                .serialize_literal_expr(literal_expr),
            _ => NotSupportedSnafu.fail(),
        }
    }

    fn serialize_aliased_dyn_proof_expr(
        self,
        aliased_expr: &AliasedDynProofExpr,
    ) -> Result<Self, SerializationError> {
        self.serialize_dyn_proof_expr(&aliased_expr.expr)
    }

    fn serialize_table_expr(self, table_expr: &TableExpr) -> Result<Self, SerializationError> {
        let table_number = self
            .table_refs
            .get(&table_expr.table_ref)
            .copied()
            .context(TableNotFoundSnafu)?;
        Ok(self.serialize_u8(table_number))
    }
    fn serialize_column_expr(self, column_expr: &ColumnExpr) -> Result<Self, SerializationError> {
        let column_number = self
            .column_refs
            .get(&column_expr.column_ref)
            .copied()
            .context(ColumnNotFoundSnafu)?;
        Ok(self.serialize_u8(column_number))
    }

    fn serialize_equals_expr(self, equals_expr: &EqualsExpr) -> Result<Self, SerializationError> {
        self.serialize_dyn_proof_expr(equals_expr.lhs.as_ref())?
            .serialize_dyn_proof_expr(equals_expr.rhs.as_ref())
    }

    fn serialize_literal_expr(
        self,
        literal_expr: &LiteralExpr,
    ) -> Result<Self, SerializationError> {
        match literal_expr.value {
            LiteralValue::BigInt(value) => Ok(self
                .serialize_u8(BIGINT_TYPE_NUM)
                .serialize_scalar(value.into())),
            _ => NotSupportedSnafu.fail(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        SerializationError, SerializedDynProofPlan, BIGINT_TYPE_NUM, COLUMN_EXPR_NUM,
        EQUALS_EXPR_NUM, FILTER_EXEC_NUM, LITERAL_EXPR_NUM,
    };
    use crate::{
        base::{
            database::{ColumnRef, ColumnType, LiteralValue},
            scalar::test_scalar::TestScalar,
        },
        sql::{
            parse::QueryExpr,
            postprocessing::{OwnedTablePostprocessing, SlicePostprocessing},
            proof_exprs::{
                AliasedDynProofExpr, ColumnExpr, DynProofExpr, EqualsExpr, LiteralExpr, TableExpr,
            },
            proof_plans::{DynProofPlan, FilterExec},
        },
    };
    use core::iter;
    use itertools::Itertools;

    #[test]
    fn we_can_generate_serialized_proof_plan_for_simple_filter() {
        let table_ref = "namespace.table".parse().unwrap();
        let identifier_a = "a".parse().unwrap();
        let identifier_b = "b".parse().unwrap();
        let identifier_alias = "alias".parse().unwrap();

        let column_ref_a = ColumnRef::new(table_ref, identifier_a, ColumnType::BigInt);
        let column_ref_b = ColumnRef::new(table_ref, identifier_b, ColumnType::BigInt);

        let query_expr = QueryExpr::new(
            DynProofPlan::Filter(FilterExec::new(
                vec![AliasedDynProofExpr {
                    expr: DynProofExpr::Column(ColumnExpr::new(column_ref_b)),
                    alias: identifier_alias,
                }],
                TableExpr { table_ref },
                DynProofExpr::Equals(EqualsExpr::new(
                    Box::new(DynProofExpr::Column(ColumnExpr::new(column_ref_a))),
                    Box::new(DynProofExpr::Literal(LiteralExpr::new(
                        LiteralValue::BigInt(5),
                    ))),
                )),
            )),
            vec![],
        );
        let result = SerializedDynProofPlan::<TestScalar>::try_from(&query_expr).unwrap();
        let bytes = result.into_bytes();
        let expected_bytes = iter::empty::<u8>()
            .chain([FILTER_EXEC_NUM, 0, 1]) // filter expr, table number, result count
            .chain([COLUMN_EXPR_NUM, 0]) // column expr, column a (#0)
            .chain([EQUALS_EXPR_NUM]) // equals expr
            .chain([COLUMN_EXPR_NUM, 1]) // column expr, column b (#1)
            .chain([LITERAL_EXPR_NUM, BIGINT_TYPE_NUM]) // literal expr, literal type
            .chain([0; 31]) // leading 0s of literal value
            .chain([5]) // literal value
            .collect_vec();
        assert_eq!(bytes, expected_bytes);
    }

    #[test]
    fn we_cannot_generate_serialized_proof_plan_for_unsupported_plan() {
        let table_ref = "namespace.table".parse().unwrap();
        let identifier_a = "a".parse().unwrap();
        let identifier_b = "b".parse().unwrap();
        let identifier_alias = "alias".parse().unwrap();

        let column_ref_a = ColumnRef::new(table_ref, identifier_a, ColumnType::SmallInt);
        let column_ref_b = ColumnRef::new(table_ref, identifier_b, ColumnType::SmallInt);

        let query_expr = QueryExpr::new(
            DynProofPlan::Filter(FilterExec::new(
                vec![AliasedDynProofExpr {
                    expr: DynProofExpr::Column(ColumnExpr::new(column_ref_b)),
                    alias: identifier_alias,
                }],
                TableExpr { table_ref },
                DynProofExpr::Equals(EqualsExpr::new(
                    Box::new(DynProofExpr::Column(ColumnExpr::new(column_ref_a))),
                    Box::new(DynProofExpr::Literal(LiteralExpr::new(
                        LiteralValue::SmallInt(5),
                    ))),
                )),
            )),
            vec![],
        );
        let result = SerializedDynProofPlan::<TestScalar>::try_from(&query_expr);
        assert!(matches!(result, Err(SerializationError::NotSupported)));
    }

    #[test]
    fn we_cannot_generate_serialized_proof_plan_for_postprocessing() {
        let table_ref = "namespace.table".parse().unwrap();
        let identifier_a = "a".parse().unwrap();
        let identifier_b = "b".parse().unwrap();
        let identifier_alias = "alias".parse().unwrap();

        let column_ref_a = ColumnRef::new(table_ref, identifier_a, ColumnType::BigInt);
        let column_ref_b = ColumnRef::new(table_ref, identifier_b, ColumnType::BigInt);

        let query_expr = QueryExpr::new(
            DynProofPlan::Filter(FilterExec::new(
                vec![AliasedDynProofExpr {
                    expr: DynProofExpr::Column(ColumnExpr::new(column_ref_b)),
                    alias: identifier_alias,
                }],
                TableExpr { table_ref },
                DynProofExpr::Equals(EqualsExpr::new(
                    Box::new(DynProofExpr::Column(ColumnExpr::new(column_ref_a))),
                    Box::new(DynProofExpr::Literal(LiteralExpr::new(
                        LiteralValue::BigInt(5),
                    ))),
                )),
            )),
            vec![OwnedTablePostprocessing::Slice(SlicePostprocessing::new(
                None, None,
            ))],
        );
        let result = SerializedDynProofPlan::<TestScalar>::try_from(&query_expr);
        assert!(matches!(result, Err(SerializationError::NotSupported)));
    }
}
