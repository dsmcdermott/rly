
- [ ] ~~Change reserved parser specification identifiers from `start` and `eof` to
anything with the prefix `Parse`, as well as rust's disallowed raw identifier values.~~

- [x] Change `start` to `Start`.

- [ ] Change `eof` to `$` so that it does not conflict with any legal identifiers.

- [ ] Make rust's disallowed raw identifier values reserved.

- [ ] Change `NonTerm` variant names from `N_<name>` to use raw identifiers.

- [ ] Merge `IntoUsize` and `FromUsize` into a single trait in the public interface, and
add an error type that can be propagated for `FromUsize`.
