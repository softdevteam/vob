#![feature(test)]

#[macro_use]
extern crate vob;
extern crate rand;
extern crate test;

use rand::Rng;
use test::Bencher;
use vob::*;

const N: usize = 100000;

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
    let mut rng = rand::thread_rng();
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
    let mut rng = rand::thread_rng();
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
    let mut rng = rand::thread_rng();
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
    let mut rng = rand::thread_rng();
    a.extend((0..N).map(|_| rng.gen::<bool>()));
    bench.iter(|| a.iter_set_bits(..).count());
}
