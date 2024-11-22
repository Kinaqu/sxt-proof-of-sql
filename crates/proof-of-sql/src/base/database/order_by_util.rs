//! Contains the utility functions for ordering.
use crate::base::{
    database::{Column, ColumnOperationError, ColumnOperationResult, OwnedColumn},
    scalar::{Scalar, ScalarExt},
};
use alloc::vec::Vec;
use core::cmp::Ordering;
use proof_of_sql_parser::intermediate_ast::OrderByDirection;

/// Compares the tuples `(order_by[0][i], order_by[1][i], ...)` and
/// `(order_by[0][j], order_by[1][j], ...)` in lexicographic order.
pub(crate) fn compare_indexes_by_columns<S: Scalar>(
    order_by: &[Column<S>],
    i: usize,
    j: usize,
) -> Ordering {
    order_by
        .iter()
        .map(|col| match col {
            Column::Boolean(col) => col[i].cmp(&col[j]),
            Column::TinyInt(col) => col[i].cmp(&col[j]),
            Column::SmallInt(col) => col[i].cmp(&col[j]),
            Column::Int(col) => col[i].cmp(&col[j]),
            Column::BigInt(col) | Column::TimestampTZ(_, _, col) => col[i].cmp(&col[j]),
            Column::Int128(col) => col[i].cmp(&col[j]),
            Column::Decimal75(_, _, col) => col[i].signed_cmp(&col[j]),
            Column::Scalar(col) => col[i].cmp(&col[j]),
            Column::VarChar((col, _)) => col[i].cmp(col[j]),
        })
        .find(|&ord| ord != Ordering::Equal)
        .unwrap_or(Ordering::Equal)
}

/// Compares the tuples `(left[0][i], left[1][i], ...)` and
/// `(right[0][j], right[1][j], ...)` in lexicographic order.
pub(crate) fn compare_indexes_in_two_tables_by_columns<S: Scalar> {
    (
        left: &[Column<S>],
        right: &[Column<S>],
        i: usize,
        j: usize,
    ) -> ColumnOperationResult<Ordering> {
        // The two tables should have the same schema on the shared columns.
        if left.len() != right.len() {
            return Err(ColumnOperationError::ColumnLengthMismatch);
        }
        left.iter()
            .zip(right.iter())
            .map(|(left_col, right_col)| match (left_col, right_col) {
                (Column::Boolean(left_col), Column::Boolean(right_col)) => {
                    left_col[i].cmp(&right_col[j])
                }
                (Column::TinyInt(left_col), Column::TinyInt(right_col)) => {
                    left_col[i].cmp(&right_col[j])
                }
                (Column::SmallInt(left_col), Column::SmallInt(right_col)) => {
                    left_col[i].cmp(&right_col[j])
                }
                (Column::Int(left_col), Column::Int(right_col)) => {
                    left_col[i].cmp(&right_col[j])
                }
                (Column::BigInt(left_col), Column::BigInt(right_col))
                | (Column::TimestampTZ(_, _, left_col), Column::TimestampTZ(_, _, right_col)) => {
                    left_col[i].cmp(&right_col[j])
                }
                (Column::Int128(left_col), Column::Int128(right_col)) => {
                    left_col[i].cmp(&right_col[j])
                }
                (Column::Decimal75(_, _, left_col), Column::Decimal75(_, _, right_col)) => {
                    left_col[i].signed_cmp(&right_col[j])
                }
                (Column::Scalar(left_col), Column::Scalar(right_col)) => {
                    left_col[i].cmp(&right_col[j])
                }
                (Column::VarChar((left_col, _)), Column::VarChar((right_col, _))) => {
                    left_col[i].cmp(right_col[j])
                }
                _ => unreachable!(),
            })
            .find(|&ord| ord != Ordering::Equal)
            .unwrap_or(Ordering::Equal)
    }
}

/// Compares the tuples `(order_by[0][i], order_by[1][i], ...)` and
/// `(order_by[0][j], order_by[1][j], ...)` in lexicographic order.
///
/// Identical in functionality to [`compare_indexes_by_columns`]
pub(crate) fn compare_indexes_by_owned_columns<S: Scalar>(
    order_by: &[&OwnedColumn<S>],
    i: usize,
    j: usize,
) -> Ordering {
    let order_by_pairs = order_by
        .iter()
        .map(|&col| (col.clone(), OrderByDirection::Asc))
        .collect::<Vec<_>>();
    compare_indexes_by_owned_columns_with_direction(&order_by_pairs, i, j)
}

/// Compares the tuples `(left[0][i], left[1][i], ...)` and
/// `(right[0][j], right[1][j], ...)` in lexicographic order.
/// Note that direction flips the ordering.
pub(crate) fn compare_indexes_by_owned_columns_with_direction<S: Scalar>(
    order_by_pairs: &[(OwnedColumn<S>, OrderByDirection)],
    i: usize,
    j: usize,
) -> Ordering {
    order_by_pairs
        .iter()
        .map(|(col, direction)| {
            let ordering = match col {
                OwnedColumn::Boolean(col) => col[i].cmp(&col[j]),
                OwnedColumn::TinyInt(col) => col[i].cmp(&col[j]),
                OwnedColumn::SmallInt(col) => col[i].cmp(&col[j]),
                OwnedColumn::Int(col) => col[i].cmp(&col[j]),
                OwnedColumn::BigInt(col) | OwnedColumn::TimestampTZ(_, _, col) => {
                    col[i].cmp(&col[j])
                }
                OwnedColumn::Int128(col) => col[i].cmp(&col[j]),
                OwnedColumn::Decimal75(_, _, col) => col[i].signed_cmp(&col[j]),
                OwnedColumn::Scalar(col) => col[i].cmp(&col[j]),
                OwnedColumn::VarChar(col) => col[i].cmp(&col[j]),
            };
            match direction {
                OrderByDirection::Asc => ordering,
                OrderByDirection::Desc => ordering.reverse(),
            }
        })
        .find(|&ord| ord != Ordering::Equal)
        .unwrap_or(Ordering::Equal)
}
