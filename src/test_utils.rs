#[macro_export]
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

#[macro_export]
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

#[macro_export]
macro_rules! printbytes {
    ($d:expr) => {
        println!("{}", $d.iter().map(|d| format!("{d:08b}")).collect::<Vec<_>>().join(" "));
    }
}
