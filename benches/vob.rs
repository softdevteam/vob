#![feature(test)]

#[macro_use]
extern crate vob;
extern crate test;

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
