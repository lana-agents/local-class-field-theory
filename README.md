# local-class-field-theory

Local class field theory for mixed-characteristic local fields.

## Status

**Not started.** The repository is the initial project scaffold (a single commit,
2026-07-20). The library `LocalClassFieldTheory` contains only the placeholder module
`LocalClassFieldTheory/Basic.lean`, which has no declarations: there are no definitions or theorems yet
(and so no `sorry`, `axiom` or `admit`). Everything under *Goals* below is planned, not
formalised.

No lana-agents repository depends on this one: `iut` and its pinned lana-agents
dependencies do not `require` it.

## Goals

Formalise local class field theory for finite extensions of `ℚ_p`.

Construct inertia and the unramified quotient, arithmetic Frobenius, and the topological Artin reciprocity map

```
Kˣ → Gal(K^ab/K)
```

with its characterising properties: units map isomorphically to inertia, uniformisers map to arithmetic Frobenius modulo inertia, and reciprocity is compatible with norms for finite extensions.

## Established sources

* Serre, *Local Fields*, Chapters XIV–XV.
* Neukirch, *Algebraic Number Theory*, Chapter VI.

## Related repositories

Intended to build on `continuous-kummer-theory` (also not started); it does not
`require` it yet.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`
(commit `81a5d25`), its only direct dependency.
Library sources live under `LocalClassFieldTheory/`, and every file must be imported from
the root module `LocalClassFieldTheory.lean`.

```bash
lake exe cache get                       # fetch the Mathlib build cache
lake build                               # build the library
lake exe mk_all --lib LocalClassFieldTheory --git   # regenerate the root module after adding files
```

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to
check that a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is
  imported (`mk_all --check`), and that everything builds with warnings as
  errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#12](https://taxis.lana.merten.dev/issues/12)
