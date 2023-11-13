use criterion::{criterion_group, criterion_main, Criterion};
use rand::prelude::*;
use std::collections::HashSet;

const SIZE: usize = 10000;

/// This benchmark compares the performance of HashSet, Vob, and Vec
/// in a scenario where an algorithm needs to keep track of visited indices.
#[cfg(test)]
fn comparative(c: &mut Criterion) {
    // Generate 10000 random (seeded) points
    let mut rng: StdRng = SeedableRng::from_seed([42; 32]);
    let mut indices: Vec<usize> = (0..SIZE).collect();

    indices.shuffle(&mut rng);

    c.bench_function("HashSet comparative", |b| {
        b.iter(|| {
            let mut hash_set = HashSet::new();
            // set half of the set to "true"
            for index in indices.iter().skip(SIZE / 2) {
                hash_set.insert(index);
            }

            for index in indices.iter().take(SIZE / 2) {
                assert!(
                    !hash_set.contains(index),
                    "index {} is supposed to be cleared",
                    index
                );
            }
            for index in indices.iter().skip(SIZE / 2) {
                assert!(
                    hash_set.contains(index),
                    "index {} is supposed to be set",
                    index
                );
            }
        })
    });

    c.bench_function("Vob comparative", |b| {
        b.iter(|| {
            let mut vob: vob::Vob<u32> = vob::Vob::new_with_storage_type(SIZE);
            vob.resize(SIZE, false);

            // set half of the vob to true
            for index in indices.iter().skip(SIZE / 2) {
                vob.set(*index, true);
            }

            for index in indices.iter().take(SIZE / 2) {
                assert!(!vob[*index], "index {} is supposed to be cleared", index);
            }
            for index in indices.iter().skip(SIZE / 2) {
                assert!(vob[*index], "index {} is supposed to be set", index);
            }
        })
    });

    c.bench_function("Vec comparative", |b| {
        b.iter(|| {
            let mut vec: Vec<bool> = vec![false; SIZE];

            // set half of the vec to true
            for index in indices.iter().skip(SIZE / 2) {
                vec[*index] = true;
            }

            for index in indices.iter().take(SIZE / 2) {
                assert!(!vec[*index], "index {} is supposed to be cleared", index);
            }
            for index in indices.iter().skip(SIZE / 2) {
                assert!(vec[*index], "index {} is supposed to be set", index);
            }
        })
    });
}

criterion_group!(benches, comparative);
criterion_main!(benches);
