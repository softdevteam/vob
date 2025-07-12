use criterion::{criterion_group, criterion_main, Criterion};

use rand::{Rng, SeedableRng};
use rand_pcg::Pcg64Mcg;
use vob::*;

const N: usize = 100000;
const RNG_SEED: u64 = 15770844968783748344;

fn empty(c: &mut Criterion) {
    c.bench_function("empty", |b| b.iter(|| Vob::with_capacity(N)));
}

fn extend(c: &mut Criterion) {
    // first initialise the source vector to drain
    let mut v1 = Vob::with_capacity(N);
    v1.extend((0..N).map(|i| i % 2 == 0));

    c.bench_function("extend", |b| {
        b.iter(|| {
            let mut v2 = Vob::with_capacity(N);
            v2.extend(v1.iter())
        })
    });
}

fn extend_vob_aligned(c: &mut Criterion) {
    // first initialise the source vector to drain
    let mut v1 = Vob::with_capacity(N);
    v1.extend((0..N).map(|i| i % 2 == 0));

    c.bench_function("extend_vob_aligned", |b| {
        b.iter(|| {
            let mut v2 = Vob::with_capacity(N);
            v2.extend_from_vob(&v1)
        })
    });
}

fn extend_vob_not_aligned(c: &mut Criterion) {
    // first initialise the source vector to drain
    let mut v1 = Vob::with_capacity(N);
    v1.extend((0..N).map(|i| i % 2 == 0));

    c.bench_function("extend_vob_not_aligned", |b| {
        b.iter(|| {
            let mut v2 = vob![true];
            v2.extend_from_vob(&v1)
        })
    });
}

fn split_off(c: &mut Criterion) {
    let mut v1 = Vob::with_capacity(N);
    v1.extend((0..N).map(|i| i % 2 == 0));

    c.bench_function("split_off", |b| {
        b.iter(|| {
            let mut v2 = v1.clone();
            v2.split_off(N / 2)
        })
    });
}

fn xor(c: &mut Criterion) {
    let mut v1 = Vob::with_capacity(N);
    let mut rng = Pcg64Mcg::seed_from_u64(RNG_SEED);
    v1.extend((0..N).map(|_| rng.random::<bool>()));
    let mut v2 = Vob::with_capacity(N);
    v2.extend((0..N).map(|_| rng.random::<bool>()));

    c.bench_function("xor", |b| {
        b.iter(|| {
            v1.xor(&v2);
        })
    });
}

fn or(c: &mut Criterion) {
    let mut v1 = Vob::with_capacity(N);
    let mut rng = Pcg64Mcg::seed_from_u64(RNG_SEED);
    v1.extend((0..N).map(|_| rng.random::<bool>()));
    let mut v2 = Vob::with_capacity(N);
    v2.extend((0..N).map(|_| rng.random::<bool>()));

    c.bench_function("or", |b| {
        b.iter(|| {
            v1.or(&v2);
        })
    });
}

fn and(c: &mut Criterion) {
    let mut v1 = Vob::with_capacity(N);
    let mut rng = Pcg64Mcg::seed_from_u64(RNG_SEED);
    v1.extend((0..N).map(|_| rng.random::<bool>()));
    let mut v2 = Vob::with_capacity(N);
    v2.extend((0..N).map(|_| rng.random::<bool>()));

    c.bench_function("and", |b| {
        b.iter(|| {
            v1.and(&v2);
        })
    });
}

fn from_bytes(c: &mut Criterion) {
    let mut rng = rand::rng();
    let mut v1 = [0u8; 1024];
    rng.fill(&mut v1);
    c.bench_function("from_bytes", |b| b.iter(|| Vob::from_bytes(&v1)));
}

fn iter_set_bits(c: &mut Criterion) {
    let mut a = Vob::with_capacity(N);
    let mut rng = Pcg64Mcg::seed_from_u64(RNG_SEED);
    a.extend((0..N).map(|_| rng.random::<bool>()));
    c.bench_function("iter_set_bits", |b| {
        b.iter(|| a.iter_set_bits(..).filter(|_| true).count())
    });
}

fn count_set_bits(c: &mut Criterion) {
    let mut a = Vob::with_capacity(N);
    let mut rng = Pcg64Mcg::seed_from_u64(RNG_SEED);
    a.extend((0..N).map(|_| rng.random::<bool>()));
    c.bench_function("count_set_bits", |b| b.iter(|| a.iter_set_bits(..).count()));
}

fn iter_set_bits_u8(c: &mut Criterion) {
    let mut a = Vob::<u8>::new_with_storage_type(N);
    let mut rng = Pcg64Mcg::seed_from_u64(RNG_SEED);
    a.extend((0..N).map(|_| rng.random::<bool>()));
    c.bench_function("iter_set_bits_u8", |b| {
        b.iter(|| a.iter_set_bits(..).filter(|_| true).count())
    });
}

fn count_set_bits_u8(c: &mut Criterion) {
    let mut a = Vob::<u8>::new_with_storage_type(N);
    let mut rng = Pcg64Mcg::seed_from_u64(RNG_SEED);
    a.extend((0..N).map(|_| rng.random::<bool>()));
    c.bench_function("count_set_bits_u8", |b| {
        b.iter(|| a.iter_set_bits(..).count())
    });
}

fn iter_all_set_bits(c: &mut Criterion) {
    let a = Vob::from_elem(true, N);
    c.bench_function("iter_all_set_bits", |b| {
        b.iter(|| a.iter_set_bits(..).filter(|_| true).count())
    });
}

fn count_all_set_bits(c: &mut Criterion) {
    let a = Vob::from_elem(true, N);
    c.bench_function("count_all_set_bits", |b| {
        b.iter(|| a.iter_set_bits(..).count())
    });
}

fn iter_all_unset_bits(c: &mut Criterion) {
    let a = Vob::from_elem(true, N);
    c.bench_function("iter_all_unset_bits", |b| {
        b.iter(|| a.iter_unset_bits(..).filter(|_| true).count())
    });
}

fn count_all_unset_bits(c: &mut Criterion) {
    let a = Vob::from_elem(true, N);
    c.bench_function("count_all_unset_bits", |b| {
        b.iter(|| a.iter_unset_bits(..).count())
    });
}

criterion_group!(
    benches,
    empty,
    extend,
    extend_vob_aligned,
    extend_vob_not_aligned,
    split_off,
    xor,
    or,
    and,
    from_bytes,
    iter_set_bits,
    count_set_bits,
    iter_set_bits_u8,
    count_set_bits_u8,
    iter_all_set_bits,
    count_all_set_bits,
    iter_all_unset_bits,
    count_all_unset_bits
);
criterion_main!(benches);
