% Pattern matching

### Dereference `match` targets when possible. [FIXME: needs RFC]

Prefer

~~~~ignore
match *foo {
    X(...) => ...
    Y(...) => ...
}
~~~~

over

~~~~ignore
match foo {
    box X(...) => ...
    box Y(...) => ...
}
~~~~

<!-- ### Clearly indicate important scopes. **[FIXME: needs RFC]** -->

<!-- If it is important that the destructor for a value be executed at a specific -->
<!-- time, clearly bind that value using a standalone `let` -->
