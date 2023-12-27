#[macro_export]
macro_rules! test_pairs {
    ($([$t:ident; $n:expr]),*) => {
        {
            let mut rng = thread_rng();
            std::iter::empty()$(.chain((0..$n).map(|_| (
                rand::random::<$t>() as i128,
                rand::random::<$t>() as i128
            ))))*
        }
    };
}

#[macro_export]
macro_rules! test_values {
    ($([$t:ident; $n:expr]),*) => {
        {
            let mut rng = thread_rng();
            std::iter::empty()$(.chain((0..$n).map(|_| 
                rand::random::<$t>() as i128,
            )))*
        }
    };
}
