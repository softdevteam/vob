#![feature(test)]

extern crate rand;
extern crate rand_pcg;
extern crate test;
extern crate vob;

use rand::{Rng, SeedableRng};
use rand_pcg::Pcg64Mcg;
use test::Bencher;
use vob::*;

const N: usize = 100000;
const RNG_SEED: u64 = 15770844968783748344;

#[bench]
fn empty(bench: &mut Bencher) {
    bench.iter(|| Vob::with_capacity(N));
}

#[bench]
fn extend(bench: &mut Bencher) {
    // first initialise the source vector to drain
    let mut v1 = Vob::with_capacity(N);
    v1.extend((0..N).map(|i| i % 2 == 0));

    bench.iter(|| {
        let mut v2 = Vob::with_capacity(N);
        v2.extend(v1.iter())
    });
}

#[bench]
fn extend_vob_aligned(bench: &mut Bencher) {
    // first initialise the source vector to drain
    let mut v1 = Vob::with_capacity(N);
    v1.extend((0..N).map(|i| i % 2 == 0));

    bench.iter(|| {
        let mut v2 = Vob::with_capacity(N);
        v2.extend_from_vob(&v1)
    });
}

#[bench]
fn extend_vob_not_aligned(bench: &mut Bencher) {
    // first initialise the source vector to drain
    let mut v1 = Vob::with_capacity(N);
    v1.extend((0..N).map(|i| i % 2 == 0));

    bench.iter(|| {
        let mut v2 = vob![true];
        v2.extend_from_vob(&v1)
    });
}

#[bench]
fn split_off(bench: &mut Bencher) {
    let mut v1 = Vob::with_capacity(N);
    v1.extend((0..N).map(|i| i % 2 == 0));

    bench.iter(|| {
        let mut v2 = v1.clone();
        v2.split_off(N / 2)
    });
}

#[bench]
fn xor(bench: &mut Bencher) {
    let mut v1 = Vob::with_capacity(N);
    let mut rng = Pcg64Mcg::seed_from_u64(RNG_SEED);
    v1.extend((0..N).map(|_| rng.gen::<bool>()));
    let mut v2 = Vob::with_capacity(N);
    v2.extend((0..N).map(|_| rng.gen::<bool>()));

    bench.iter(|| {
        v1.xor(&v2);
    });
}

#[bench]
fn or(bench: &mut Bencher) {
    let mut v1 = Vob::with_capacity(N);
    let mut rng = Pcg64Mcg::seed_from_u64(RNG_SEED);
    v1.extend((0..N).map(|_| rng.gen::<bool>()));
    let mut v2 = Vob::with_capacity(N);
    v2.extend((0..N).map(|_| rng.gen::<bool>()));

    bench.iter(|| {
        v1.or(&v2);
    });
}

#[bench]
fn and(bench: &mut Bencher) {
    let mut v1 = Vob::with_capacity(N);
    let mut rng = Pcg64Mcg::seed_from_u64(RNG_SEED);
    v1.extend((0..N).map(|_| rng.gen::<bool>()));
    let mut v2 = Vob::with_capacity(N);
    v2.extend((0..N).map(|_| rng.gen::<bool>()));

    bench.iter(|| {
        v1.and(&v2);
    });
}

#[bench]
fn from_bytes(bench: &mut Bencher) {
    let mut rng = rand::thread_rng();
    let mut v1 = [0u8; 1024];
    rng.fill(&mut v1);

    bench.iter(|| Vob::from_bytes(&v1));
}

#[bench]
fn iter_set_bits(bench: &mut Bencher) {
    let mut a = Vob::with_capacity(N);
    let mut rng = Pcg64Mcg::seed_from_u64(RNG_SEED);
    a.extend((0..N).map(|_| rng.gen::<bool>()));
    bench.iter(|| a.iter_set_bits(..).count());
}

#[bench]
fn iter_set_bits_u8(bench: &mut Bencher) {
    let mut a = Vob::<u8>::new_with_storage_type(N);
    let mut rng = Pcg64Mcg::seed_from_u64(RNG_SEED);
    a.extend((0..N).map(|_| rng.gen::<bool>()));
    bench.iter(|| a.iter_set_bits(..).count());
}

#[bench]
fn iter_all_set_bits(bench: &mut Bencher) {
    let a = Vob::from_elem(N, true);
    bench.iter(|| a.iter_set_bits(..).count());
}

#[bench]
fn iter_all_unset_bits(bench: &mut Bencher) {
    let a = Vob::from_elem(N, true);
    bench.iter(|| a.iter_unset_bits(..).count());
}
