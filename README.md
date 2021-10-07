# option-operations ![CI](https://github.com/fengalin/option-operations/workflows/CI/badge.svg)

`option-operations` provides traits and auto-implementations to
improve arithmetic operations usability when dealing with `Option`s.

## Example

Dealing with two `Option`s, can lead to verbose espressions:

``` rust
let lhs = Some(1u64);
let rhs = Some(u64::MAX);

assert_eq!(
    lhs.zip(rhs).map(|(lhs, rhs)| lhs.wrapping_add(rhs)),
    Some(0),
);
```

Thanks to the trait [`OptionWrappingAdd`] we can write:

``` rust
assert_eq!(
    lhs.opt_wrapping_add(rhs),
    Some(0),
);
```

## Alternative to `PartialOrd` for `Option<T>`

Another purpose is to workaround the `PartiaOrd` implementation
for `Option<T>`, which uses the declaration order of the variants
for `Option`. `None` appearing before `Some(_)`, it results in
the following behavior:

``` rust
let some_0 = Some(0);
let none: Option<u64> = None;

assert_eq!(none.partial_cmp(&some_0), Some(Ordering::Less));
assert_eq!(some_0.partial_cmp(&none), Some(Ordering::Greater));
```

In some cases, we might consider that `None` reflects a value which
is not defined and thus can not be compared with `Some(_)`.

``` rust
assert_eq!(none.opt_cmp(&some_0), None);
assert_eq!(some_0.opt_cmp(&none), None);
```

## LICENSE

This crate is licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or
   http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or
   http://opensource.org/licenses/MIT)

at your option.
