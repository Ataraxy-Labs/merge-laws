# merge-laws

Machine-checked proofs, in Lean 4, of the rules behind [weave](https://github.com/Ataraxy-Labs/weave) (merging code one function at a time) and [land](https://useland.dev) (reusing and batching test results). A test then checks that the real weave binary follows the proven rules.

```sh
lake build                                      # checks every proof; fails if any is wrong
lake exe gencases 20000 | python3 diff/run.py   # does weave agree with the model?
```

## What is proved

**weave's merge, one entity at a time** (`MergeLaws/Merge.lean`)

- Two sides that changed different functions never conflict, and the result is the base with both changes applied.
- A conflict happens exactly when both sides changed the same function, differently.
- Swapping ours and theirs only swaps the sides of a conflict.
- A clean result is always one side's version, never something new.
- A change merged with itself, or with an untouched side, is that change.

**land reusing a test result** (`MergeLaws/Carry.lean`)

- If a test's verdict depends only on the files it reads, a result reused because none of those files changed equals a fresh run.
- Edits outside a test's read set never change its verdict.

**land checking several changes together** (`MergeLaws/Batch.lean`)

- Two changes that write different files give the same repository in either order.
- A change that writes nothing a test reads cannot move that test's verdict, so a verdict checked for one change still holds when an unrelated change lands beside it.
- Batching never lets a broken change through, and never fails a change that passed.

## Does weave follow the model?

`gencases` runs the proven decision function itself to produce random three-way merges and the outcome the model expects. `diff/run.py` writes each as three real files, one function per entity, merges them with `weave-driver`, and compares every function.

On weave 0.7.0, 20,000 merges and 100,000 functions all agreed, every kind of case included: one side changed, both changed alike, both changed differently, added on one side, added on both, deleted against modified. In 3 of them the base file was empty, so there were no functions to match on and weave fell back to an ordinary line merge. That is coarser than the model but loses nothing, and the test checks that every function either side wrote is still in the result.

## What is not proved

- **The Rust code itself.** These theorems are about a model of weave's decision. The differential test is what ties the model to the binary, and it samples cases rather than proving them all.
- **weave's finer merges.** When the decision says conflict, weave can still resolve some cases by merging inside the function (diff3, statement and footprint merges). Those are not modelled.
- **Renames.** weave detects a function that moved to a new name. The model has no renames, so the test gives every function a body no other function has.
- **Hermeticity.** The land theorems assume a test's verdict depends only on what it reads. land backs that by running tests offline in a microVM, recording every file they read, and refusing a test that fails and then passes on the same code.

## License

Apache-2.0 or MIT, at your option.
