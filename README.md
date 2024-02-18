# lower

lowers expressions to their "desugared" form.

e.g

`a * b + c` => `(a.mul(b)).add(c)`

note that it is *extremely pervasive*, so
```rust
lower::math! { fn main() -> u8 {
    const X: u8 = 31 * 2;
    return 2 * X + 2;
} }
```
expands to
```rust
fn main() -> u8 {
    const X: u8 = 31.mul(2);
    return (2.mul(X)).add(2);
}
```
it should work for most expressions.

## why

well, you see, i made a [crate for arrays](https://crates.io/crates/atools).
then, i added `add`/`mul`/…, and got annoyed when i had to call them manually.
now, you can do amazing things such as `lower::math! { 2 * ([5, 2] + 5) }`.