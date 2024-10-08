use crate::base::{
    database::{Column, ColumnType, OwnedColumn},
    math::decimal::Precision,
    ref_into::RefInto,
    scalar::Scalar,
};
use alloc::vec::Vec;
#[cfg(feature = "blitzar")]
use blitzar::sequence::Sequence;
use proof_of_sql_parser::posql_time::{PoSQLTimeUnit, PoSQLTimeZone};

/// Column data in "committable form".
///
/// For some column types, transformations need to be applied before commitments are created.
/// These transformations require allocating new memory.
/// This is a problem since blitzar only borrows slices of data to commit to.
/// Normal column types don't store their data in "committable" form, so they cannot interface with
/// blitzar directly.
///
/// This type acts as an intermediate column type that *can* be used with blitzar directly.
/// For column types that need to be transformed, their "committable form" is owned here.
/// For column types that don't need to allocate new memory, their data is only borrowed here.
#[non_exhaustive]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CommittableColumn<'a> {
    /// Borrowed Bool column, mapped to `bool`.
    Boolean(&'a [bool]),
    /// Borrowed `TinyInt` column, mapped to `i8`.
    TinyInt(&'a [i8]),
    /// Borrowed `SmallInt` column, mapped to `i16`.
    SmallInt(&'a [i16]),
    /// Borrowed `Int` column, mapped to `i32`.
    Int(&'a [i32]),
    /// Borrowed `BigInt` column, mapped to `i64`.
    BigInt(&'a [i64]),
    /// Borrowed Int128 column, mapped to `i128`.
    Int128(&'a [i128]),
    /// Borrowed Decimal75(precion, scale, column), mapped to 'i256'
    Decimal75(Precision, i8, Vec<[u64; 4]>),
    /// Column of big ints for committing to, montgomery-reduced from a Scalar column.
    Scalar(Vec<[u64; 4]>),
    /// Column of limbs for committing to scalars, hashed from a `VarChar` column.
    VarChar(Vec<[u64; 4]>),
    /// Borrowed Timestamp column with Timezone, mapped to `i64`.
    TimestampTZ(PoSQLTimeUnit, PoSQLTimeZone, &'a [i64]),
    /// Borrowed byte column, mapped to `u8`. This is not a `PoSQL`
    /// type, we need this to commit to words in the range check.
    RangeCheckWord(&'a [u8]),
    /// Borrowed `FixedSizeBinary` column, mapped to a slice of bytes.
    /// - The i32 specifies the number of bytes per value.
    FixedSizeBinary(i32, &'a [u8]),
}

impl<'a> CommittableColumn<'a> {
    /// Returns the length of the column.
    #[must_use]
    #[allow(clippy::missing_panics_doc)]
    pub fn len(&self) -> usize {
        match self {
            CommittableColumn::TinyInt(col) => col.len(),
            CommittableColumn::SmallInt(col) => col.len(),
            CommittableColumn::Int(col) => col.len(),
            CommittableColumn::BigInt(col) | CommittableColumn::TimestampTZ(_, _, col) => col.len(),
            CommittableColumn::Int128(col) => col.len(),
            CommittableColumn::Decimal75(_, _, col)
            | CommittableColumn::Scalar(col)
            | CommittableColumn::VarChar(col) => col.len(),
            CommittableColumn::Boolean(col) => col.len(),
            CommittableColumn::RangeCheckWord(col) => col.len(),
            CommittableColumn::FixedSizeBinary(byte_width, col) => {
                assert!(*byte_width > 0, "Byte width must be greater than zero");
                col.len() / *byte_width as usize
            }
        }
    }

    /// Returns true if the column is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the type of the column.
    #[must_use]
    pub fn column_type(&self) -> ColumnType {
        self.into()
    }
}

impl<'a> From<&CommittableColumn<'a>> for ColumnType {
    fn from(value: &CommittableColumn<'a>) -> Self {
        match value {
            CommittableColumn::TinyInt(_) => ColumnType::TinyInt,
            CommittableColumn::SmallInt(_) => ColumnType::SmallInt,
            CommittableColumn::Int(_) => ColumnType::Int,
            CommittableColumn::BigInt(_) => ColumnType::BigInt,
            CommittableColumn::Int128(_) => ColumnType::Int128,
            CommittableColumn::Decimal75(precision, scale, _) => {
                ColumnType::Decimal75(*precision, *scale)
            }
            CommittableColumn::Scalar(_) => ColumnType::Scalar,
            CommittableColumn::VarChar(_) => ColumnType::VarChar,
            CommittableColumn::Boolean(_) => ColumnType::Boolean,
            CommittableColumn::TimestampTZ(tu, tz, _) => ColumnType::TimestampTZ(*tu, *tz),
            CommittableColumn::FixedSizeBinary(size, _) => ColumnType::FixedSizeBinary(*size),
            CommittableColumn::RangeCheckWord(_) => {
                unimplemented!("Range check words are not a column type.")
            }
        }
    }
}

impl<'a, S: Scalar> From<&Column<'a, S>> for CommittableColumn<'a> {
    fn from(value: &Column<'a, S>) -> Self {
        match value {
            Column::Boolean(bools) => CommittableColumn::Boolean(bools),
            Column::TinyInt(ints) => CommittableColumn::TinyInt(ints),
            Column::SmallInt(ints) => CommittableColumn::SmallInt(ints),
            Column::Int(ints) => CommittableColumn::Int(ints),
            Column::BigInt(ints) => CommittableColumn::BigInt(ints),
            Column::Int128(ints) => CommittableColumn::Int128(ints),
            Column::Decimal75(precision, scale, decimals) => {
                let as_limbs: Vec<_> = decimals.iter().map(RefInto::<[u64; 4]>::ref_into).collect();
                CommittableColumn::Decimal75(*precision, *scale, as_limbs)
            }
            Column::Scalar(scalars) => (scalars as &[_]).into(),
            Column::VarChar((_, scalars)) => {
                let as_limbs: Vec<_> = scalars.iter().map(RefInto::<[u64; 4]>::ref_into).collect();
                CommittableColumn::VarChar(as_limbs)
            }
            Column::TimestampTZ(tu, tz, times) => CommittableColumn::TimestampTZ(*tu, *tz, times),
            Column::FixedSizeBinary(byte_width, bytes) => {
                CommittableColumn::FixedSizeBinary(*byte_width, bytes)
            }
        }
    }
}

impl<'a, S: Scalar> From<Column<'a, S>> for CommittableColumn<'a> {
    fn from(value: Column<'a, S>) -> Self {
        (&value).into()
    }
}

impl<'a, S: Scalar> From<&'a OwnedColumn<S>> for CommittableColumn<'a> {
    fn from(value: &'a OwnedColumn<S>) -> Self {
        match value {
            OwnedColumn::Boolean(bools) => CommittableColumn::Boolean(bools),
            OwnedColumn::TinyInt(ints) => (ints as &[_]).into(),
            OwnedColumn::SmallInt(ints) => (ints as &[_]).into(),
            OwnedColumn::Int(ints) => (ints as &[_]).into(),
            OwnedColumn::BigInt(ints) => (ints as &[_]).into(),
            OwnedColumn::Int128(ints) => (ints as &[_]).into(),
            OwnedColumn::Decimal75(precision, scale, decimals) => CommittableColumn::Decimal75(
                *precision,
                *scale,
                decimals
                    .iter()
                    .map(Into::<S>::into)
                    .map(Into::<[u64; 4]>::into)
                    .collect(),
            ),
            OwnedColumn::Scalar(scalars) => (scalars as &[_]).into(),
            OwnedColumn::VarChar(strings) => CommittableColumn::VarChar(
                strings
                    .iter()
                    .map(Into::<S>::into)
                    .map(Into::<[u64; 4]>::into)
                    .collect(),
            ),
            OwnedColumn::TimestampTZ(tu, tz, times) => {
                CommittableColumn::TimestampTZ(*tu, *tz, times as &[_])
            }
            OwnedColumn::FixedSizeBinary(byte_width, bytes) => {
                CommittableColumn::FixedSizeBinary(*byte_width, bytes)
            }
        }
    }
}

impl<'a> From<&'a [u8]> for CommittableColumn<'a> {
    fn from(value: &'a [u8]) -> Self {
        CommittableColumn::RangeCheckWord(value)
    }
}
impl<'a> From<&'a [i8]> for CommittableColumn<'a> {
    fn from(value: &'a [i8]) -> Self {
        CommittableColumn::TinyInt(value)
    }
}
impl<'a> From<&'a [i16]> for CommittableColumn<'a> {
    fn from(value: &'a [i16]) -> Self {
        CommittableColumn::SmallInt(value)
    }
}
impl<'a> From<&'a [i32]> for CommittableColumn<'a> {
    fn from(value: &'a [i32]) -> Self {
        CommittableColumn::Int(value)
    }
}

impl<'a> From<&'a [i64]> for CommittableColumn<'a> {
    fn from(value: &'a [i64]) -> Self {
        CommittableColumn::BigInt(value)
    }
}

impl<'a> From<&'a [i128]> for CommittableColumn<'a> {
    fn from(value: &'a [i128]) -> Self {
        CommittableColumn::Int128(value)
    }
}
impl<'a, S: Scalar> From<&'a [S]> for CommittableColumn<'a> {
    fn from(value: &'a [S]) -> Self {
        CommittableColumn::Scalar(value.iter().map(RefInto::<[u64; 4]>::ref_into).collect())
    }
}
impl<'a> From<&'a [bool]> for CommittableColumn<'a> {
    fn from(value: &'a [bool]) -> Self {
        CommittableColumn::Boolean(value)
    }
}

#[cfg(feature = "blitzar")]
impl<'a, 'b> From<&'a CommittableColumn<'b>> for Sequence<'a> {
    fn from(value: &'a CommittableColumn<'b>) -> Self {
        match value {
            CommittableColumn::TinyInt(ints) => Sequence::from(*ints),
            CommittableColumn::SmallInt(ints) => Sequence::from(*ints),
            CommittableColumn::Int(ints) => Sequence::from(*ints),
            CommittableColumn::BigInt(ints) => Sequence::from(*ints),
            CommittableColumn::Int128(ints) => Sequence::from(*ints),
            CommittableColumn::Decimal75(_, _, limbs)
            | CommittableColumn::Scalar(limbs)
            | CommittableColumn::VarChar(limbs) => Sequence::from(limbs),
            CommittableColumn::Boolean(bools) => Sequence::from(*bools),
            CommittableColumn::TimestampTZ(_, _, times) => Sequence::from(*times),
            CommittableColumn::RangeCheckWord(words) => Sequence::from(*words),
            // FIXME: Is this the correct way to convert a FixedSizeBinary column to a Sequence?
            CommittableColumn::FixedSizeBinary(_, bytes) => Sequence::from(*bytes),
        }
    }
}

#[cfg(all(test, feature = "blitzar"))]
mod tests {
    use super::*;
    use crate::{base::scalar::Curve25519Scalar, proof_primitive::dory::DoryScalar};
    use blitzar::compute::compute_curve25519_commitments;
    use curve25519_dalek::ristretto::CompressedRistretto;

    #[test]
    fn we_can_convert_from_owned_decimal75_column_to_committable_column() {
        let decimals = vec![
            Curve25519Scalar::from(-1),
            Curve25519Scalar::from(1),
            Curve25519Scalar::from(2),
        ];
        let decimal_column = OwnedColumn::Decimal75(Precision::new(75).unwrap(), -1, decimals);

        let res_committable_column: CommittableColumn = (&decimal_column).into();
        let test_committable_column: CommittableColumn = CommittableColumn::Decimal75(
            Precision::new(75).unwrap(),
            -1,
            [-1, 1, 2]
                .map(<Curve25519Scalar>::from)
                .map(<[u64; 4]>::from)
                .into(),
        );

        assert_eq!(res_committable_column, test_committable_column);
    }

    #[test]
    fn we_can_get_type_and_length_of_timestamp_column() {
        // empty case
        let committable_column =
            CommittableColumn::TimestampTZ(PoSQLTimeUnit::Second, PoSQLTimeZone::Utc, &[]);
        assert_eq!(committable_column.len(), 0);
        assert!(committable_column.is_empty());
        assert_eq!(
            committable_column.column_type(),
            ColumnType::TimestampTZ(PoSQLTimeUnit::Second, PoSQLTimeZone::Utc)
        );

        let committable_column = CommittableColumn::TimestampTZ(
            PoSQLTimeUnit::Second,
            PoSQLTimeZone::Utc,
            &[12, 34, 56],
        );
        assert_eq!(committable_column.len(), 3);
        assert!(!committable_column.is_empty());
        assert_eq!(
            committable_column.column_type(),
            ColumnType::TimestampTZ(PoSQLTimeUnit::Second, PoSQLTimeZone::Utc)
        );
    }

    #[test]
    fn we_can_get_type_and_length_of_tinyint_column() {
        // empty case
        let tinyint_committable_column = CommittableColumn::TinyInt(&[]);
        assert_eq!(tinyint_committable_column.len(), 0);
        assert!(tinyint_committable_column.is_empty());
        assert_eq!(
            tinyint_committable_column.column_type(),
            ColumnType::TinyInt
        );

        let tinyint_committable_column = CommittableColumn::TinyInt(&[12, 34, 56]);
        assert_eq!(tinyint_committable_column.len(), 3);
        assert!(!tinyint_committable_column.is_empty());
        assert_eq!(
            tinyint_committable_column.column_type(),
            ColumnType::TinyInt
        );
    }

    #[test]
    fn we_can_get_type_and_length_of_smallint_column() {
        // empty case
        let smallint_committable_column = CommittableColumn::SmallInt(&[]);
        assert_eq!(smallint_committable_column.len(), 0);
        assert!(smallint_committable_column.is_empty());
        assert_eq!(
            smallint_committable_column.column_type(),
            ColumnType::SmallInt
        );

        let smallint_committable_column = CommittableColumn::SmallInt(&[12, 34, 56]);
        assert_eq!(smallint_committable_column.len(), 3);
        assert!(!smallint_committable_column.is_empty());
        assert_eq!(
            smallint_committable_column.column_type(),
            ColumnType::SmallInt
        );
    }

    #[test]
    fn we_can_get_type_and_length_of_int_column() {
        // empty case
        let int_committable_column = CommittableColumn::Int(&[]);
        assert_eq!(int_committable_column.len(), 0);
        assert!(int_committable_column.is_empty());
        assert_eq!(int_committable_column.column_type(), ColumnType::Int);

        let int_committable_column = CommittableColumn::Int(&[12, 34, 56]);
        assert_eq!(int_committable_column.len(), 3);
        assert!(!int_committable_column.is_empty());
        assert_eq!(int_committable_column.column_type(), ColumnType::Int);
    }

    #[test]
    fn we_can_get_type_and_length_of_bigint_column() {
        // empty case
        let bigint_committable_column = CommittableColumn::BigInt(&[]);
        assert_eq!(bigint_committable_column.len(), 0);
        assert!(bigint_committable_column.is_empty());
        assert_eq!(bigint_committable_column.column_type(), ColumnType::BigInt);

        let bigint_committable_column = CommittableColumn::BigInt(&[12, 34, 56]);
        assert_eq!(bigint_committable_column.len(), 3);
        assert!(!bigint_committable_column.is_empty());
        assert_eq!(bigint_committable_column.column_type(), ColumnType::BigInt);
    }

    #[test]
    fn we_can_get_type_and_length_of_decimal_column() {
        // empty case
        let decimal_committable_column =
            CommittableColumn::Decimal75(Precision::new(1).unwrap(), 0, [].to_vec());
        assert_eq!(decimal_committable_column.len(), 0);
        assert!(decimal_committable_column.is_empty());
        assert_eq!(
            decimal_committable_column.column_type(),
            ColumnType::Decimal75(Precision::new(1).unwrap(), 0)
        );
        let decimal_committable_column = CommittableColumn::Decimal75(
            Precision::new(10).unwrap(),
            10,
            vec![[12, 0, 0, 0], [34, 0, 0, 0], [56, 0, 0, 0]],
        );
        assert_eq!(decimal_committable_column.len(), 3);
        assert!(!decimal_committable_column.is_empty());
        assert_eq!(
            decimal_committable_column.column_type(),
            ColumnType::Decimal75(Precision::new(10).unwrap(), 10)
        );
    }

    #[test]
    fn we_can_get_type_and_length_of_int128_column() {
        // empty case
        let bigint_committable_column = CommittableColumn::Int128(&[]);
        assert_eq!(bigint_committable_column.len(), 0);
        assert!(bigint_committable_column.is_empty());
        assert_eq!(bigint_committable_column.column_type(), ColumnType::Int128);

        let bigint_committable_column = CommittableColumn::Int128(&[12, 34, 56]);
        assert_eq!(bigint_committable_column.len(), 3);
        assert!(!bigint_committable_column.is_empty());
        assert_eq!(bigint_committable_column.column_type(), ColumnType::Int128);
    }

    #[test]
    fn we_can_get_type_and_length_of_varchar_column() {
        // empty case
        let bigint_committable_column = CommittableColumn::VarChar(Vec::new());
        assert_eq!(bigint_committable_column.len(), 0);
        assert!(bigint_committable_column.is_empty());
        assert_eq!(bigint_committable_column.column_type(), ColumnType::VarChar);

        let bigint_committable_column = CommittableColumn::VarChar(
            ["12", "34", "56"]
                .map(Into::<String>::into)
                .map(Into::<Curve25519Scalar>::into)
                .map(Into::<[u64; 4]>::into)
                .into(),
        );
        assert_eq!(bigint_committable_column.len(), 3);
        assert!(!bigint_committable_column.is_empty());
        assert_eq!(bigint_committable_column.column_type(), ColumnType::VarChar);
    }

    #[test]
    fn we_can_get_type_and_length_of_fixed_size_binary_column() {
        let byte_width = 16; // Example byte width

        // Empty case
        let fixed_size_binary_committable_column =
            CommittableColumn::FixedSizeBinary(byte_width, &[]);
        assert_eq!(fixed_size_binary_committable_column.len(), 0);
        assert!(fixed_size_binary_committable_column.is_empty());
        assert_eq!(
            fixed_size_binary_committable_column.column_type(),
            ColumnType::FixedSizeBinary(byte_width)
        );

        // Non-empty case
        let fixed_size_binary_data = [
            vec![0u8; byte_width as usize],
            vec![1u8; byte_width as usize],
            vec![2u8; byte_width as usize],
        ];
        let concatenated_data: Vec<u8> = fixed_size_binary_data.concat();
        let fixed_size_binary_committable_column =
            CommittableColumn::FixedSizeBinary(byte_width, &concatenated_data);
        assert_eq!(fixed_size_binary_committable_column.len(), 3);
        assert!(!fixed_size_binary_committable_column.is_empty());
        assert_eq!(
            fixed_size_binary_committable_column.column_type(),
            ColumnType::FixedSizeBinary(byte_width)
        );
    }

    #[test]
    fn we_can_get_type_and_length_of_scalar_column() {
        // empty case
        let bigint_committable_column = CommittableColumn::Scalar(Vec::new());
        assert_eq!(bigint_committable_column.len(), 0);
        assert!(bigint_committable_column.is_empty());
        assert_eq!(bigint_committable_column.column_type(), ColumnType::Scalar);

        let bigint_committable_column = CommittableColumn::Scalar(
            [12, 34, 56]
                .map(<Curve25519Scalar>::from)
                .map(<[u64; 4]>::from)
                .into(),
        );
        assert_eq!(bigint_committable_column.len(), 3);
        assert!(!bigint_committable_column.is_empty());
        assert_eq!(bigint_committable_column.column_type(), ColumnType::Scalar);
    }

    #[test]
    fn we_can_get_type_and_length_of_boolean_column() {
        // empty case
        let bool_committable_column = CommittableColumn::Boolean(&[]);
        assert_eq!(bool_committable_column.len(), 0);
        assert!(bool_committable_column.is_empty());
        assert_eq!(bool_committable_column.column_type(), ColumnType::Boolean);

        let bool_committable_column = CommittableColumn::Boolean(&[true, false, true]);
        assert_eq!(bool_committable_column.len(), 3);
        assert!(!bool_committable_column.is_empty());
        assert_eq!(bool_committable_column.column_type(), ColumnType::Boolean);
    }

    #[test]
    fn we_can_get_length_of_rangecheckword_column() {
        // empty case
        let bool_committable_column = CommittableColumn::RangeCheckWord(&[]);
        assert_eq!(bool_committable_column.len(), 0);
        assert!(bool_committable_column.is_empty());

        let bool_committable_column = CommittableColumn::RangeCheckWord(&[12, 34, 56]);
        assert_eq!(bool_committable_column.len(), 3);
        assert!(!bool_committable_column.is_empty());
    }

    #[test]
    fn we_can_convert_from_borrowing_timestamp_column() {
        // empty case
        let from_borrowed_column =
            CommittableColumn::from(&Column::<Curve25519Scalar>::TimestampTZ(
                PoSQLTimeUnit::Second,
                PoSQLTimeZone::Utc,
                &[],
            ));
        assert_eq!(
            from_borrowed_column,
            CommittableColumn::TimestampTZ(PoSQLTimeUnit::Second, PoSQLTimeZone::Utc, &[])
        );

        // non-empty case
        let timestamps = [1_625_072_400, 1_625_076_000, 1_625_083_200];
        let from_borrowed_column =
            CommittableColumn::from(&Column::<Curve25519Scalar>::TimestampTZ(
                PoSQLTimeUnit::Second,
                PoSQLTimeZone::Utc,
                &timestamps,
            ));
        assert_eq!(
            from_borrowed_column,
            CommittableColumn::TimestampTZ(PoSQLTimeUnit::Second, PoSQLTimeZone::Utc, &timestamps)
        );
    }

    #[test]
    fn we_can_convert_from_borrowing_bigint_column() {
        // empty case
        let from_borrowed_column =
            CommittableColumn::from(&Column::<Curve25519Scalar>::BigInt(&[]));
        assert_eq!(from_borrowed_column, CommittableColumn::BigInt(&[]));

        let from_borrowed_column =
            CommittableColumn::from(&Column::<Curve25519Scalar>::BigInt(&[12, 34, 56]));
        assert_eq!(
            from_borrowed_column,
            CommittableColumn::BigInt(&[12, 34, 56])
        );
    }

    #[test]
    fn we_can_convert_from_borrowing_tinyint_column() {
        // empty case
        let from_borrowed_column =
            CommittableColumn::from(&Column::<Curve25519Scalar>::TinyInt(&[]));
        assert_eq!(from_borrowed_column, CommittableColumn::TinyInt(&[]));

        let from_borrowed_column =
            CommittableColumn::from(&Column::<Curve25519Scalar>::TinyInt(&[12, 34, 56]));
        assert_eq!(
            from_borrowed_column,
            CommittableColumn::TinyInt(&[12, 34, 56])
        );
    }

    #[test]
    fn we_can_convert_from_borrowing_smallint_column() {
        // empty case
        let from_borrowed_column =
            CommittableColumn::from(&Column::<Curve25519Scalar>::SmallInt(&[]));
        assert_eq!(from_borrowed_column, CommittableColumn::SmallInt(&[]));

        let from_borrowed_column =
            CommittableColumn::from(&Column::<Curve25519Scalar>::SmallInt(&[12, 34, 56]));
        assert_eq!(
            from_borrowed_column,
            CommittableColumn::SmallInt(&[12, 34, 56])
        );
    }

    #[test]
    fn we_can_convert_from_borrowing_int_column() {
        // empty case
        let from_borrowed_column = CommittableColumn::from(&Column::<Curve25519Scalar>::Int(&[]));
        assert_eq!(from_borrowed_column, CommittableColumn::Int(&[]));

        let from_borrowed_column =
            CommittableColumn::from(&Column::<Curve25519Scalar>::Int(&[12, 34, 56]));
        assert_eq!(from_borrowed_column, CommittableColumn::Int(&[12, 34, 56]));
    }

    #[test]
    fn we_can_convert_from_borrowing_decimal_column() {
        // Define a non-empty array of Curve25519Scalars
        let binding = vec![
            Curve25519Scalar::from(-1),
            Curve25519Scalar::from(34),
            Curve25519Scalar::from(56),
        ];

        let precision = Precision::new(75).unwrap();
        let from_borrowed_column =
            CommittableColumn::from(&Column::Decimal75(precision, 0, &binding));

        let expected_decimals = binding
            .iter()
            .map(|&scalar| scalar.into())
            .collect::<Vec<[u64; 4]>>();

        assert_eq!(
            from_borrowed_column,
            CommittableColumn::Decimal75(Precision::new(75).unwrap(), 0, expected_decimals)
        );
    }

    #[test]
    fn we_can_convert_from_borrowing_int128_column() {
        // empty case
        let from_borrowed_column =
            CommittableColumn::from(&Column::<Curve25519Scalar>::Int128(&[]));
        assert_eq!(from_borrowed_column, CommittableColumn::Int128(&[]));

        let from_borrowed_column =
            CommittableColumn::from(&Column::<Curve25519Scalar>::Int128(&[12, 34, 56]));
        assert_eq!(
            from_borrowed_column,
            CommittableColumn::Int128(&[12, 34, 56])
        );
    }

    #[test]
    fn we_can_convert_from_borrowing_varchar_column() {
        // empty case
        let from_borrowed_column =
            CommittableColumn::from(&Column::<Curve25519Scalar>::VarChar((&[], &[])));
        assert_eq!(from_borrowed_column, CommittableColumn::VarChar(Vec::new()));

        let varchar_data = ["12", "34", "56"];
        let scalars = varchar_data.map(Curve25519Scalar::from);
        let from_borrowed_column =
            CommittableColumn::from(&Column::VarChar((&varchar_data, &scalars)));
        assert_eq!(
            from_borrowed_column,
            CommittableColumn::VarChar(scalars.map(<[u64; 4]>::from).into())
        );
    }

    #[test]
    fn we_can_convert_from_borrowing_fixed_size_binary_column() {
        let byte_width = 16;

        // Empty case
        let from_borrowed_column = CommittableColumn::from(
            &Column::<Curve25519Scalar>::FixedSizeBinary(byte_width, &[]),
        );
        assert_eq!(
            from_borrowed_column,
            CommittableColumn::FixedSizeBinary(byte_width, &[])
        );

        // Non-empty case
        let fixed_size_binary_data = [
            vec![0u8; byte_width as usize],
            vec![1u8; byte_width as usize],
            vec![2u8; byte_width as usize],
        ];
        let concatenated_data: Vec<u8> = fixed_size_binary_data.concat();
        let from_borrowed_column = CommittableColumn::from(
            &Column::<Curve25519Scalar>::FixedSizeBinary(byte_width, &concatenated_data),
        );
        assert_eq!(
            from_borrowed_column,
            CommittableColumn::FixedSizeBinary(byte_width, &concatenated_data)
        );
    }

    #[test]
    fn we_can_convert_from_borrowing_scalar_column() {
        // empty case
        let from_borrowed_column =
            CommittableColumn::from(&Column::<Curve25519Scalar>::Scalar(&[]));
        assert_eq!(from_borrowed_column, CommittableColumn::Scalar(Vec::new()));

        let scalars = [12, 34, 56].map(Curve25519Scalar::from);
        let from_borrowed_column = CommittableColumn::from(&Column::Scalar(&scalars));
        assert_eq!(
            from_borrowed_column,
            CommittableColumn::Scalar(scalars.map(<[u64; 4]>::from).into())
        );
    }

    #[test]
    fn we_can_convert_from_borrowing_boolean_column() {
        // empty case
        let from_borrowed_column =
            CommittableColumn::from(&Column::<Curve25519Scalar>::Boolean(&[]));
        assert_eq!(from_borrowed_column, CommittableColumn::Boolean(&[]));

        let from_borrowed_column =
            CommittableColumn::from(&Column::<Curve25519Scalar>::Boolean(&[true, false, true]));
        assert_eq!(
            from_borrowed_column,
            CommittableColumn::Boolean(&[true, false, true])
        );
    }

    #[test]
    fn we_can_convert_from_owned_bigint_column() {
        // empty case
        let owned_column = OwnedColumn::<Curve25519Scalar>::BigInt(Vec::new());
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(from_owned_column, CommittableColumn::BigInt(&[]));

        let owned_column = OwnedColumn::<Curve25519Scalar>::BigInt(vec![12, 34, 56]);
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(from_owned_column, CommittableColumn::BigInt(&[12, 34, 56]));
    }

    #[test]
    fn we_can_convert_from_owned_tinyint_column() {
        // empty case
        let owned_column = OwnedColumn::<DoryScalar>::TinyInt(Vec::new());
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(from_owned_column, CommittableColumn::TinyInt(&[]));

        let owned_column = OwnedColumn::<DoryScalar>::TinyInt(vec![12, 34, 56]);
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(from_owned_column, CommittableColumn::TinyInt(&[12, 34, 56]));
    }

    #[test]
    fn we_can_convert_from_owned_smallint_column() {
        // empty case
        let owned_column = OwnedColumn::<DoryScalar>::SmallInt(Vec::new());
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(from_owned_column, CommittableColumn::SmallInt(&[]));

        let owned_column = OwnedColumn::<DoryScalar>::SmallInt(vec![12, 34, 56]);
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(
            from_owned_column,
            CommittableColumn::SmallInt(&[12, 34, 56])
        );
    }

    #[test]
    fn we_can_convert_from_owned_timestamp_column() {
        // empty case
        let owned_column = OwnedColumn::<Curve25519Scalar>::TimestampTZ(
            PoSQLTimeUnit::Second,
            PoSQLTimeZone::Utc,
            Vec::new(),
        );
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(
            from_owned_column,
            CommittableColumn::TimestampTZ(PoSQLTimeUnit::Second, PoSQLTimeZone::Utc, &[])
        );

        // non-empty case
        let timestamps = vec![1_625_072_400, 1_625_076_000, 1_625_083_200];
        let owned_column = OwnedColumn::<Curve25519Scalar>::TimestampTZ(
            PoSQLTimeUnit::Second,
            PoSQLTimeZone::Utc,
            timestamps.clone(),
        );
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(
            from_owned_column,
            CommittableColumn::TimestampTZ(PoSQLTimeUnit::Second, PoSQLTimeZone::Utc, &timestamps)
        );
    }

    #[test]
    fn we_can_convert_from_owned_int_column() {
        // empty case
        let owned_column = OwnedColumn::<DoryScalar>::Int(Vec::new());
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(from_owned_column, CommittableColumn::Int(&[]));

        let owned_column = OwnedColumn::<DoryScalar>::Int(vec![12, 34, 56]);
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(from_owned_column, CommittableColumn::Int(&[12, 34, 56]));
    }

    #[test]
    fn we_can_convert_from_owned_int128_column() {
        // empty case
        let owned_column = OwnedColumn::<Curve25519Scalar>::Int128(Vec::new());
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(from_owned_column, CommittableColumn::Int128(&[]));

        let owned_column = OwnedColumn::<Curve25519Scalar>::Int128(vec![12, 34, 56]);
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(from_owned_column, CommittableColumn::Int128(&[12, 34, 56]));
    }

    #[test]
    fn we_can_convert_from_owned_varchar_column() {
        // empty case
        let owned_column = OwnedColumn::<Curve25519Scalar>::VarChar(Vec::new());
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(from_owned_column, CommittableColumn::VarChar(Vec::new()));

        let strings = ["12", "34", "56"].map(String::from);
        let owned_column = OwnedColumn::<Curve25519Scalar>::VarChar(strings.to_vec());
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(
            from_owned_column,
            CommittableColumn::VarChar(
                strings
                    .map(Curve25519Scalar::from)
                    .map(<[u64; 4]>::from)
                    .into()
            )
        );
    }

    #[test]
    fn we_can_convert_from_owned_fixed_size_binary_column() {
        let byte_width = 16;

        // Empty case
        let owned_column = OwnedColumn::<Curve25519Scalar>::FixedSizeBinary(byte_width, Vec::new());
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(
            from_owned_column,
            CommittableColumn::FixedSizeBinary(byte_width, &[])
        );

        // Non-empty case
        let fixed_size_binary_data = [
            vec![0u8; byte_width as usize],
            vec![1u8; byte_width as usize],
            vec![2u8; byte_width as usize],
        ];
        let concatenated_data: Vec<u8> = fixed_size_binary_data.concat();
        let owned_column =
            OwnedColumn::<Curve25519Scalar>::FixedSizeBinary(byte_width, concatenated_data.clone());
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(
            from_owned_column,
            CommittableColumn::FixedSizeBinary(byte_width, &concatenated_data)
        );
    }

    #[test]
    fn we_can_convert_from_owned_scalar_column() {
        // empty case
        let owned_column = OwnedColumn::<Curve25519Scalar>::Scalar(Vec::new());
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(from_owned_column, CommittableColumn::Scalar(Vec::new()));

        let scalars = [12, 34, 56].map(Curve25519Scalar::from);
        let owned_column = OwnedColumn::Scalar(scalars.to_vec());
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(
            from_owned_column,
            CommittableColumn::Scalar(scalars.map(<[u64; 4]>::from).into())
        );
    }

    #[test]
    fn we_can_convert_from_owned_boolean_column() {
        // empty case
        let owned_column = OwnedColumn::<DoryScalar>::Boolean(Vec::new());
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(from_owned_column, CommittableColumn::Boolean(&[]));

        let booleans = [true, false, true];
        let owned_column: OwnedColumn<DoryScalar> = OwnedColumn::Boolean(booleans.to_vec());
        let from_owned_column = CommittableColumn::from(&owned_column);
        assert_eq!(from_owned_column, CommittableColumn::Boolean(&booleans));
    }

    #[test]
    fn we_can_commit_to_bigint_column_through_committable_column() {
        // empty case
        let committable_column = CommittableColumn::BigInt(&[]);
        let sequence = Sequence::from(&committable_column);
        let mut commitment_buffer = [CompressedRistretto::default()];
        compute_curve25519_commitments(&mut commitment_buffer, &[sequence], 0);
        assert_eq!(commitment_buffer[0], CompressedRistretto::default());

        // nonempty case
        let values = [12, 34, 56];
        let committable_column = CommittableColumn::BigInt(&values);

        let sequence_actual = Sequence::from(&committable_column);
        let sequence_expected = Sequence::from(values.as_slice());
        let mut commitment_buffer = [CompressedRistretto::default(); 2];
        compute_curve25519_commitments(
            &mut commitment_buffer,
            &[sequence_actual, sequence_expected],
            0,
        );
        assert_eq!(commitment_buffer[0], commitment_buffer[1]);
    }

    #[test]
    fn we_can_commit_to_rangecheckword_column_through_committable_column() {
        // empty case
        let committable_column = CommittableColumn::RangeCheckWord(&[]);
        let sequence = Sequence::from(&committable_column);
        let mut commitment_buffer = [CompressedRistretto::default()];
        compute_curve25519_commitments(&mut commitment_buffer, &[sequence], 0);
        assert_eq!(commitment_buffer[0], CompressedRistretto::default());

        // nonempty case
        let values = [12, 34, 56];
        let committable_column = CommittableColumn::RangeCheckWord(&values);

        let sequence_actual = Sequence::from(&committable_column);
        let sequence_expected = Sequence::from(values.as_slice());
        let mut commitment_buffer = [CompressedRistretto::default(); 2];
        compute_curve25519_commitments(
            &mut commitment_buffer,
            &[sequence_actual, sequence_expected],
            0,
        );
        assert_eq!(commitment_buffer[0], commitment_buffer[1]);
    }

    #[test]
    fn we_can_commit_to_tinyint_column_through_committable_column() {
        // empty case
        let committable_column = CommittableColumn::TinyInt(&[]);
        let sequence = Sequence::from(&committable_column);
        let mut commitment_buffer = [CompressedRistretto::default()];
        compute_curve25519_commitments(&mut commitment_buffer, &[sequence], 0);
        assert_eq!(commitment_buffer[0], CompressedRistretto::default());

        // nonempty case
        let values = [12, 34, 56];
        let committable_column = CommittableColumn::TinyInt(&values);

        let sequence_actual = Sequence::from(&committable_column);
        let sequence_expected = Sequence::from(values.as_slice());
        let mut commitment_buffer = [CompressedRistretto::default(); 2];
        compute_curve25519_commitments(
            &mut commitment_buffer,
            &[sequence_actual, sequence_expected],
            0,
        );
        assert_eq!(commitment_buffer[0], commitment_buffer[1]);
    }

    #[test]
    fn we_can_commit_to_smallint_column_through_committable_column() {
        // empty case
        let committable_column = CommittableColumn::SmallInt(&[]);
        let sequence = Sequence::from(&committable_column);
        let mut commitment_buffer = [CompressedRistretto::default()];
        compute_curve25519_commitments(&mut commitment_buffer, &[sequence], 0);
        assert_eq!(commitment_buffer[0], CompressedRistretto::default());

        // nonempty case
        let values = [12, 34, 56];
        let committable_column = CommittableColumn::SmallInt(&values);

        let sequence_actual = Sequence::from(&committable_column);
        let sequence_expected = Sequence::from(values.as_slice());
        let mut commitment_buffer = [CompressedRistretto::default(); 2];
        compute_curve25519_commitments(
            &mut commitment_buffer,
            &[sequence_actual, sequence_expected],
            0,
        );
        assert_eq!(commitment_buffer[0], commitment_buffer[1]);
    }

    #[test]
    fn we_can_commit_to_int_column_through_committable_column() {
        // empty case
        let committable_column = CommittableColumn::Int(&[]);
        let sequence = Sequence::from(&committable_column);
        let mut commitment_buffer = [CompressedRistretto::default()];
        compute_curve25519_commitments(&mut commitment_buffer, &[sequence], 0);
        assert_eq!(commitment_buffer[0], CompressedRistretto::default());

        // nonempty case
        let values = [12, 34, 56];
        let committable_column = CommittableColumn::Int(&values);

        let sequence_actual = Sequence::from(&committable_column);
        let sequence_expected = Sequence::from(values.as_slice());
        let mut commitment_buffer = [CompressedRistretto::default(); 2];
        compute_curve25519_commitments(
            &mut commitment_buffer,
            &[sequence_actual, sequence_expected],
            0,
        );
        assert_eq!(commitment_buffer[0], commitment_buffer[1]);
    }

    #[test]
    fn we_can_commit_to_decimal_column_through_committable_column() {
        // empty case
        let committable_column =
            CommittableColumn::Decimal75(Precision::new(1).unwrap(), 0, [].to_vec());
        let sequence = Sequence::from(&committable_column);
        let mut commitment_buffer = [CompressedRistretto::default()];
        compute_curve25519_commitments(&mut commitment_buffer, &[sequence], 0);
        assert_eq!(commitment_buffer[0], CompressedRistretto::default());

        // nonempty case
        let values = [
            Curve25519Scalar::from(12),
            Curve25519Scalar::from(34),
            Curve25519Scalar::from(56),
        ]
        .map(<[u64; 4]>::from);
        let committable_column =
            CommittableColumn::Decimal75(Precision::new(1).unwrap(), 0, (values).to_vec());

        let sequence_actual = Sequence::from(&committable_column);
        let sequence_expected = Sequence::from(values.as_slice());
        let mut commitment_buffer = [CompressedRistretto::default(); 2];
        compute_curve25519_commitments(
            &mut commitment_buffer,
            &[sequence_actual, sequence_expected],
            0,
        );
        assert_eq!(commitment_buffer[0], commitment_buffer[1]);
    }

    // Committing to Int128 columns is blocked by PROOF-772 without a workaround
    #[test]
    #[ignore]
    fn we_can_commit_to_int128_column_through_committable_column() {
        // empty case
        let committable_column = CommittableColumn::Int128(&[]);
        let sequence = Sequence::from(&committable_column);
        let mut commitment_buffer = [CompressedRistretto::default()];
        compute_curve25519_commitments(&mut commitment_buffer, &[sequence], 0);
        assert_eq!(commitment_buffer[0], CompressedRistretto::default());

        // nonempty case
        let values = [12, 34, 56];
        let committable_column = CommittableColumn::Int128(&values);

        let sequence_actual = Sequence::from(&committable_column);
        let sequence_expected = Sequence::from(values.as_slice());
        let mut commitment_buffer = [CompressedRistretto::default(); 2];
        compute_curve25519_commitments(
            &mut commitment_buffer,
            &[sequence_actual, sequence_expected],
            0,
        );
        assert_eq!(commitment_buffer[0], commitment_buffer[1]);
    }

    #[test]
    fn we_can_commit_to_varchar_column_through_committable_column() {
        // empty case
        let committable_column = CommittableColumn::VarChar(vec![]);
        let sequence = Sequence::from(&committable_column);
        let mut commitment_buffer = [CompressedRistretto::default()];
        compute_curve25519_commitments(&mut commitment_buffer, &[sequence], 0);
        assert_eq!(commitment_buffer[0], CompressedRistretto::default());

        // nonempty case
        let values = ["12", "34", "56"].map(String::from);
        let owned_column = OwnedColumn::<Curve25519Scalar>::VarChar(values.to_vec());
        let committable_column = CommittableColumn::from(&owned_column);

        let sequence_actual = Sequence::from(&committable_column);
        let scalars = values.map(Curve25519Scalar::from).map(<[u64; 4]>::from);
        let sequence_expected = Sequence::from(scalars.as_slice());
        let mut commitment_buffer = [CompressedRistretto::default(); 2];
        compute_curve25519_commitments(
            &mut commitment_buffer,
            &[sequence_actual, sequence_expected],
            0,
        );
        assert_eq!(commitment_buffer[0], commitment_buffer[1]);
    }

    #[test]
    fn we_can_commit_to_fixed_size_binary_column_through_committable_column() {
        let byte_width = 16;

        // Empty case
        let committable_column = CommittableColumn::FixedSizeBinary(byte_width, &[]);
        let sequence = Sequence::from(&committable_column);
        let mut commitment_buffer = [CompressedRistretto::default()];
        compute_curve25519_commitments(&mut commitment_buffer, &[sequence], 0);
        assert_eq!(commitment_buffer[0], CompressedRistretto::default());

        // Non-empty case
        let fixed_size_binary_data = [
            vec![0u8; byte_width as usize],
            vec![1u8; byte_width as usize],
            vec![2u8; byte_width as usize],
        ];
        let concatenated_data: Vec<u8> = fixed_size_binary_data.concat();
        let committable_column = CommittableColumn::FixedSizeBinary(byte_width, &concatenated_data);

        let sequence_actual = Sequence::from(&committable_column);
        let sequence_expected = Sequence::from(concatenated_data.as_slice());
        let mut commitment_buffer = [CompressedRistretto::default(); 2];
        compute_curve25519_commitments(
            &mut commitment_buffer,
            &[sequence_actual, sequence_expected],
            0,
        );
        assert_eq!(commitment_buffer[0], commitment_buffer[1]);
    }

    #[test]
    fn we_can_commit_to_scalar_column_through_committable_column() {
        // empty case
        let committable_column = CommittableColumn::Scalar(vec![]);
        let sequence = Sequence::from(&committable_column);
        let mut commitment_buffer = [CompressedRistretto::default()];
        compute_curve25519_commitments(&mut commitment_buffer, &[sequence], 0);
        assert_eq!(commitment_buffer[0], CompressedRistretto::default());

        // nonempty case
        let values = [12, 34, 56].map(Curve25519Scalar::from);
        let owned_column = OwnedColumn::Scalar(values.to_vec());
        let committable_column = CommittableColumn::from(&owned_column);

        let sequence_actual = Sequence::from(&committable_column);
        let scalars = values.map(Curve25519Scalar::from).map(<[u64; 4]>::from);
        let sequence_expected = Sequence::from(scalars.as_slice());
        let mut commitment_buffer = [CompressedRistretto::default(); 2];
        compute_curve25519_commitments(
            &mut commitment_buffer,
            &[sequence_actual, sequence_expected],
            0,
        );
        assert_eq!(commitment_buffer[0], commitment_buffer[1]);
    }

    #[test]
    fn we_can_commit_to_boolean_column_through_committable_column() {
        // empty case
        let committable_column = CommittableColumn::Boolean(&[]);
        let sequence = Sequence::from(&committable_column);
        let mut commitment_buffer = [CompressedRistretto::default()];
        compute_curve25519_commitments(&mut commitment_buffer, &[sequence], 0);
        assert_eq!(commitment_buffer[0], CompressedRistretto::default());

        // nonempty case
        let values = [true, false, true];
        let committable_column = CommittableColumn::Boolean(&values);

        let sequence_actual = Sequence::from(&committable_column);
        let sequence_expected = Sequence::from(values.as_slice());
        let mut commitment_buffer = [CompressedRistretto::default(); 2];
        compute_curve25519_commitments(
            &mut commitment_buffer,
            &[sequence_actual, sequence_expected],
            0,
        );
        assert_eq!(commitment_buffer[0], commitment_buffer[1]);
    }

    #[test]
    fn we_can_commit_to_timestamp_column_through_committable_column() {
        // Empty case
        let committable_column =
            CommittableColumn::TimestampTZ(PoSQLTimeUnit::Second, PoSQLTimeZone::Utc, &[]);
        let sequence = Sequence::from(&committable_column);
        let mut commitment_buffer = [CompressedRistretto::default()];
        compute_curve25519_commitments(&mut commitment_buffer, &[sequence], 0);
        assert_eq!(commitment_buffer[0], CompressedRistretto::default());

        // Non-empty case
        let timestamps = [1_625_072_400, 1_625_076_000, 1_625_083_200];
        let committable_column =
            CommittableColumn::TimestampTZ(PoSQLTimeUnit::Second, PoSQLTimeZone::Utc, &timestamps);

        let sequence_actual = Sequence::from(&committable_column);
        let sequence_expected = Sequence::from(timestamps.as_slice());
        let mut commitment_buffer = [CompressedRistretto::default(); 2];
        compute_curve25519_commitments(
            &mut commitment_buffer,
            &[sequence_actual, sequence_expected],
            0,
        );
        assert_eq!(commitment_buffer[0], commitment_buffer[1]);
    }
}
