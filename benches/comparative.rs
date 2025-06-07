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
            let mut vob = vob::Vob::<u32>::from_elem_with_storage_type(false, SIZE);

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

    c.bench_function("Vob unchecked comparative", |b| {
        b.iter(|| {
            let mut vob = vob::Vob::<u32>::from_elem_with_storage_type(false, SIZE);

            unsafe {
                // set half of the vob to true
                for index in indices.iter().skip(SIZE / 2) {
                    vob.set_unchecked(*index, true);
                }

                for index in indices.iter().take(SIZE / 2) {
                    assert!(
                        !vob.get_unchecked(*index),
                        "index {} is supposed to be cleared",
                        index
                    );
                }
                for index in indices.iter().skip(SIZE / 2) {
                    assert!(
                        vob.get_unchecked(*index),
                        "index {} is supposed to be set",
                        index
                    );
                }
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

    c.bench_function("Vec unchecked comparative", |b| {
        b.iter(|| {
            let mut vec: Vec<bool> = vec![false; SIZE];
            unsafe {
                // set half of the vec to true
                for index in indices.iter().skip(SIZE / 2) {
                    *vec.get_unchecked_mut(*index) = true;
                }

                for index in indices.iter().take(SIZE / 2) {
                    assert!(
                        !vec.get_unchecked(*index),
                        "index {} is supposed to be cleared",
                        index
                    );
                }
                for index in indices.iter().skip(SIZE / 2) {
                    assert!(
                        vec.get_unchecked(*index),
                        "index {} is supposed to be set",
                        index
                    );
                }
            }
        })
    });
}

criterion_group!(benches, comparative);
criterion_main!(benches);
