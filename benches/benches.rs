#![feature(test)]

extern crate test;

#[cfg(test)]
mod benches {
    use big_int::{
        loose::{Loose, LooseInt},
        BigInt, Digit,
    };
    use rand::prelude::*;
    use test::Bencher;

    const STRESS_TEST_BASE: usize = 1 << 3;
    const STRESS_TEST_DIGITS: usize = 1 << 2;

    #[bench]
    fn fuzzy_div_rem_stress_test(bench: &mut Bencher) {
        let mut rng = thread_rng();
        bench.iter(|| {
            let a: LooseInt<STRESS_TEST_BASE> = BigInt::from(unsafe {
                Loose::from_raw_parts(
                    (0..STRESS_TEST_DIGITS)
                        .map(|_| rng.gen::<Digit>() % STRESS_TEST_BASE as Digit)
                        .collect(),
                )
            })
            .normalized();
            let b: LooseInt<STRESS_TEST_BASE> = BigInt::from(unsafe {
                Loose::from_raw_parts(
                    (0..STRESS_TEST_DIGITS / 2)
                        .map(|_| rng.gen::<Digit>() % STRESS_TEST_BASE as Digit)
                        .collect(),
                )
            })
            .normalized();
            a.clone().div_rem(b.clone())
        });
    }
}
