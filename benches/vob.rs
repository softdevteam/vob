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
fn empty(b: &mut Bencher) {
    b.iter(|| Vob::with_capacity(N));
}

#[bench]
fn extend(b: &mut Bencher) {
    // first initialise the source vector to drain
    let mut source = Vob::with_capacity(N);
    source.extend((0..N).map(|i| i % 2 == 0));

    b.iter(|| {
        let mut vector = Vob::with_capacity(N);
        vector.extend(source.iter())
    });
}

#[bench]
fn extend_vob_aligned(b: &mut Bencher) {
    // first initialise the source vector to drain
    let mut source = Vob::with_capacity(N);
    source.extend((0..N).map(|i| i % 2 == 0));

    b.iter(|| {
        let mut vector = Vob::with_capacity(N);
        vector.extend_from_vob(&source)
    });
}

#[bench]
fn extend_vob_not_aligned(b: &mut Bencher) {
    // first initialise the source vector to drain
    let mut source = Vob::with_capacity(N);
    source.extend((0..N).map(|i| i % 2 == 0));

    b.iter(|| {
        let mut vector = vob![true];
        vector.extend_from_vob(&source)
    });
}

#[bench]
fn split_off(b: &mut Bencher) {
    let mut source = Vob::with_capacity(N);
    source.extend((0..N).map(|i| i % 2 == 0));

    b.iter(|| {
        let mut a = source.clone();
        a.split_off(N / 2)
    });
}

#[bench]
fn xor(bench: &mut Bencher) {
    let mut a = Vob::with_capacity(N);
    let mut rng = rand::thread_rng();
    a.extend((0..N).map(|_| rng.gen::<bool>()));
    let mut b = Vob::with_capacity(N);
    b.extend((0..N).map(|_| rng.gen::<bool>()));

    bench.iter(|| {
        a.xor(&b);
    });
}

#[bench]
fn or(bench: &mut Bencher) {
    let mut a = Vob::with_capacity(N);
    let mut rng = rand::thread_rng();
    a.extend((0..N).map(|_| rng.gen::<bool>()));
    let mut b = Vob::with_capacity(N);
    b.extend((0..N).map(|_| rng.gen::<bool>()));

    bench.iter(|| {
        a.or(&b);
    });
}

#[bench]
fn and(bench: &mut Bencher) {
    let mut a = Vob::with_capacity(N);
    let mut rng = rand::thread_rng();
    a.extend((0..N).map(|_| rng.gen::<bool>()));
    let mut b = Vob::with_capacity(N);
    b.extend((0..N).map(|_| rng.gen::<bool>()));

    bench.iter(|| {
        a.and(&b);
    });
}

#[bench]
fn from_bytes(b: &mut Bencher) {
    let mut rng = rand::thread_rng();
    let mut source = [0u8; 1024];
    rng.fill(&mut source);

    b.iter(|| Vob::from_bytes(&source));
}
