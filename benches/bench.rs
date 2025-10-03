use criterion::{black_box, criterion_group, criterion_main, Criterion};
use unchecked_refcell::UncheckedRefCell;
use std::cell::RefCell;

const ITER: usize = 1_000_000;

fn borrow_bench_std(c: &mut Criterion) {
    let cell = RefCell::new(42usize);

    c.bench_function("std_refcell_borrow", |b| {
        b.iter(|| {
            for _ in 0..ITER {
                let val1 = cell.borrow();
                black_box(*val1);
                let val2 = cell.borrow();
                black_box(*val2);
                let val3 = cell.borrow();
                black_box(*val3);
                black_box(val3);
                black_box(val2);
                black_box(val1);
            }
        })
    });

    c.bench_function("std_refcell_borrow_mut", |b| {
        b.iter(|| {
            for _ in 0..ITER {
                let mut val1 = cell.borrow_mut();
                black_box(*val1);
                *val1 = 1;
                black_box(*val1);
                black_box(val1);
                let mut val2 = cell.borrow_mut();
                black_box(*val2);
                *val2 = 2;
                black_box(*val2);
                black_box(val2);
                let mut val3 = cell.borrow_mut();
                black_box(*val3);
                *val3 = 3;
                black_box(*val3);
                black_box(val3);
            }
        })
    });
}

fn borrow_bench_unchecked(c: &mut Criterion) {
    let cell = UncheckedRefCell::new(42usize);

    c.bench_function("unchecked_refcell_borrow", |b| {
        b.iter(|| {
            for _ in 0..ITER {
                let val1 = cell.borrow();
                black_box(*val1);
                let val2 = cell.borrow();
                black_box(*val2);
                let val3 = cell.borrow();
                black_box(*val3);
                black_box(val3);
                black_box(val2);
                black_box(val1);
            }
        })
    });

    c.bench_function("unchecked_refcell_borrow_mut", |b| {
        b.iter(|| {
            for _ in 0..ITER {
                let mut val1 = cell.borrow_mut();
                black_box(*val1);
                *val1 = 1;
                black_box(*val1);
                black_box(val1);
                let mut val2 = cell.borrow_mut();
                black_box(*val2);
                *val2 = 2;
                black_box(*val2);
                black_box(val2);
                let mut val3 = cell.borrow_mut();
                black_box(*val3);
                *val3 = 3;
                black_box(*val3);
                black_box(val3);
            }
        })
    });
}

criterion_group!(
    benches,
    borrow_bench_std,
    borrow_bench_unchecked
);
criterion_main!(benches);
