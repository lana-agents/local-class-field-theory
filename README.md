# local-class-field-theory

Local class field theory for mixed-characteristic local fields.

## Goals

Formalise local class field theory for finite extensions of `ℚ_p`.

Construct inertia and the unramified quotient, arithmetic Frobenius, and the topological Artin reciprocity map

```
Kˣ → Gal(K^ab/K)
```

with its characterising properties: units map isomorphically to inertia, uniformisers map to arithmetic Frobenius modulo inertia, and reciprocity is compatible with norms for finite extensions.

A concrete integration target is to replace the specification-level `sorry`s in `AnabelianAlgorithms/AnabelianAlgorithms/LCFT.lean` (and the corresponding `otriangle` file) by constructions and proofs.

## Established sources

* Serre, *Local Fields*, Chapters XIV–XV.
* Neukirch, *Algebraic Number Theory*, Chapter VI.

## Related repositories

Depends on `continuous-kummer-theory`.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`.
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
