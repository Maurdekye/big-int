//! Various utility macros for testing.

/// Create a list of pairs of randomly generated ints, constrained 
/// by the sizes of the associated int types passed.
#[macro_export(local_inner_macros)]
macro_rules! test_pairs {
    ($([$t:ty; $n:literal]),*) => {
        {
            let mut rng = thread_rng();
            std::iter::empty()$(.chain((0..$n).map(|_| (
                rand::random::<$t>() as i128,
                rand::random::<$t>() as i128
            ))))*
        }
    };
}

/// Create a list of randomly generated ints, constrained 
/// by the sizes of the associated int types passed.
#[macro_export(local_inner_macros)]
macro_rules! test_values {
    ($([$t:ty; $n:literal]),*) => {
        {
            let mut rng = thread_rng();
            std::iter::empty()$(.chain((0..$n).map(|_| 
                rand::random::<$t>() as i128,
            )))*
        }
    };
}

/// Format out a vec of bytes as a list of binary numbers.
#[macro_export(local_inner_macros)]
macro_rules! bytestr {
    ($d:expr) => {
        $d.iter().map(|d| format!("{d:08b}")).collect::<Vec<_>>().join(" ");
    }
}
