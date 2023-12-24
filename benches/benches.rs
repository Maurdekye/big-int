#![feature(test)]

extern crate test;

#[cfg(test)]
mod benches {
    use big_int::*;
    use rand::prelude::*;
    use test::Bencher;

    const STRESS_TEST_BASE: usize = 1 << 13;
    const STRESS_TEST_DIGITS: usize = 1 << 9;

    #[bench]
    fn fuzzy_div_rem_2_stress_test(bench: &mut Bencher) {
        let mut rng = thread_rng();
        let a: BigInt<STRESS_TEST_BASE> = unsafe {
            BigInt::from_raw_parts((0..STRESS_TEST_DIGITS).map(|_| rng.gen::<u16>()).collect())
        }.normalized();
        let b: BigInt<STRESS_TEST_BASE> = unsafe {
            BigInt::from_raw_parts(
                (0..STRESS_TEST_DIGITS / 2)
                    .map(|_| rng.gen::<u16>())
                    .collect(),
            )
        }.normalized();
        bench.iter(|| {
            a.clone().div_rem_2(b.clone())
        });
    }

    #[bench]
    fn fuzzy_div_rem_stress_test(bench: &mut Bencher) {
        let mut rng = thread_rng();
        let a: BigInt<STRESS_TEST_BASE> = unsafe {
            BigInt::from_raw_parts((0..STRESS_TEST_DIGITS).map(|_| rng.gen::<u16>()).collect())
        }.normalized();
        let b: BigInt<STRESS_TEST_BASE> = unsafe {
            BigInt::from_raw_parts(
                (0..STRESS_TEST_DIGITS / 2)
                    .map(|_| rng.gen::<u16>())
                    .collect(),
            )
        }.normalized();
        bench.iter(|| {
            a.clone().div_rem(b.clone())
        });
    }
}
