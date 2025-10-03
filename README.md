# `unchecked-refcell`

[<img alt="github" src="https://img.shields.io/badge/github-mcmah309/unchecked_refcell-8da0cb?style=for-the-badge&labelColor=555555&logo=github" height="20">](https://github.com/mcmah309/unchecked_refcell)
[<img alt="crates.io" src="https://img.shields.io/crates/v/unchecked_refcell.svg?style=for-the-badge&color=fc8d62&logo=rust" height="20">](https://crates.io/crates/unchecked_refcell)
[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-unchecked_refcell-66c2a5?style=for-the-badge&labelColor=555555&logo=docs.rs" height="20">](https://docs.rs/unchecked_refcell)
[<img alt="test status" src="https://img.shields.io/github/actions/workflow/status/mcmah309/unchecked_refcell/rust.yml?branch=master&style=for-the-badge" height="20">](https://github.com/mcmah309/unchecked_refcell/actions?query=branch%3Amaster)

`UncheckedRefCell` is a drop-in alternative to `core::cell::RefCell` for **performance-critical code** where it is certain no borrowing rules are violated.

* In **debug builds** or when the `checked` feature is enabled, it behaves exactly like `RefCell`, enforcing Rust’s borrow rules.
* In **release builds** without `checked`, all borrow checks are **skipped** for maximum performance. Use this only when you are certain borrow violations cannot occur as otherwise this may lead to **undefined behavior** if multiple mutable references exist simultaneously.

It provides all the same APIs as `RefCell`, including:
`borrow`, `borrow_mut`, `try_borrow`, `try_borrow_mut`, `replace`, `replace_with`, `swap`, `get_mut`, `take`, etc.

## Features

* `checked` — enable runtime borrow checking, identical to `RefCell`.
* `debug_refcell` — enables tracking of borrow origins for debugging purposes.

## Benchmarks

Benchmarks comparing `UncheckedRefCell` with `std::cell::RefCell` (release build):

```console
std_refcell_borrow:   [2.1578 ms 2.1597 ms 2.1618 ms]

std_refcell_borrow_mut:   [2.9351 ms 2.9377 ms 2.9406 ms]

unchecked_refcell_borrow:  [677.66 µs 678.54 µs 679.50 µs]

unchecked_refcell_borrow_mut:   [1.0260 ms 1.0268 ms 1.0276 ms]
```

> In release builds without `checked`, `UncheckedRefCell` is roughly **2–4x faster** than `RefCell`.