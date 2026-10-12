# local-class-field-theory

Local class field theory for mixed-characteristic local fields.

## Status

**In progress.** Local reciprocity `Kˣ/N_{L/K} Lˣ ≃ Gal(L/K)` is formalised for every finite
abelian `L` inside a fixed algebraic closure `Ω`; the global Artin map `Kˣ → Gal(K^ab/K)` and the
existence theorem are **not** formalised yet. The Artin map `PadicField.artin : Kˣ →* Gal(K^ab/K)`
is constructed, continuous, sends uniformisers to the arithmetic Frobenius modulo inertia and units
into inertia (onto inertia at every finite level), and is compatible with norms for finite
Galois `K'/K` (`PadicField.artin_baseChange`); the existence theorem is open. What is proved (no `sorry`, no
`axiom`), all in the concrete setting of fields `K` with `[Algebra ℚ_[p] K]
[FiniteDimensional ℚ_[p] K]` (see `Blueprint.md` for the route and lemma-level status):

* `LocalClassFieldTheory/PadicField/`: the absolute value `PadicField.nrm` (Mathlib's spectral
  norm), the normalised valuation `PadicField.v`, the ring of integers `𝒪 p K` as a discrete
  valuation ring with finite residue field, uniformisers, completeness and Hensel's lemma,
  Teichmüller representatives; for extensions `L/K`: `𝒪 p L` is the integral closure of `𝒪 p K`,
  `e * f = [L : K]`, `v_K (N_{L/K} x) = f * v_L x`; unramified extensions are Galois (splitting
  field of `X^Q - X`); for Galois `L/K` the map `Gal(L/K) → Gal(𝓴 L/𝓴 K)` is surjective with
  kernel the inertia group, an isomorphism for unramified `L/K`, and the arithmetic Frobenius
  `PadicField.frob` generates `Gal(L/K)`.
* `LocalClassFieldTheory/ClassFieldAxiom/`: the **class field axiom** for cyclic extensions,
  `PadicField.index_normGroup_of_isCyclic : (normGroup K L).index = Module.finrank K L`, i.e.
  `[Kˣ : N_{L/K} Lˣ] = [L : K]`, via `h(𝒪ˣ_L) = 1` (normal-basis lattice and successive
  approximation), `h(Lˣ) = [L : K]`, and Hilbert 90.
* `LocalClassFieldTheory/Herbrand/`: Tate groups `Ĥ⁰`, `Ĥ⁻¹` and Herbrand quotients for a group
  with an automorphism of finite order: multiplicativity in short exact sequences, value `1` on
  finite and induced modules, value `n` on `ℤ`.

* Inside a fixed algebraic closure `Ω`: the unramified extension `K_n` of each degree (unique),
  `K^ur` with its arithmetic Frobenius (topologically generating `Gal(K^ur/K)`), the absolute
  inertia group `absInertia p K Ω = Gal(Ω/K^ur)`, the unramified quotient
  `Gal(Ω/K)/I ≃ Gal(K^ur/K)` and the arithmetic Frobenius `arithFrob` modulo inertia.
* Reciprocity at a standard level (`LocalClassFieldTheory/Reciprocity/`): the second inequality
  `[Kˣ : N Lˣ] ≤ [L : K]` for abelian `L/K`; norm groups of unramified extensions; for a
  "standard" extension `F = M·U` (`M/K` cyclic totally ramified, `U/K` unramified) an explicit
  surjective homomorphism `ρ_F : Kˣ → Gal(F/K)` with kernel in `N_{F/K} Fˣ`, Neukirch's formula
  `ρ_F(N_{Σ/K} π_Σ) = τ` for Frobenius lifts `τ`, and for every cyclic `L ⊆ M·K_N ⊆ F`:
  `ρ_F⁻¹(Gal(F/L)) = N_{L/K} Lˣ` (`PadicField.comap_rhoF_fixingSubgroup`), i.e. local
  reciprocity `Kˣ/N Lˣ ≃ Gal(L/K)` for such `L`.

* Reciprocity inside `Ω` (`Reciprocity/{OmegaLevel,LevelNeukirch,Embedding,CyclicRec,Abelian}.lean`):
  every cyclic `L ⊆ Ω` lies in a standard level (`PadicField.exists_totRam_le_sup`); the
  restriction of `ρ_F` to `L` does not depend on the level (`PadicField.StdLevel.rho_res_eq_of_le`);
  the cyclic reciprocity map `PadicField.cycRec L` (kernel `N Lˣ`, surjective, Neukirch's formula
  `PadicField.cycRec_norm_frobLift`); for finite abelian `L ⊆ Ω` the reciprocity map
  `PadicField.abRec L : Kˣ →* Gal(L/K)` with kernel `N_{L/K} Lˣ` (`PadicField.ker_abRec`),
  surjective, compatible with restriction, i.e. `PadicField.abRecEquiv : Kˣ ⧸ N Lˣ ≃* Gal(L/K)`.

* The Artin map (`Reciprocity/{Artin,ArtinContinuous}.lean`, `PadicField/Powers.lean`):
  `PadicField.maxAbelian`, `PadicField.artin`, `PadicField.artin_apply`,
  `PadicField.continuous_artin`, `PadicField.mk_eq_arithFrob_of_artin`,
  `PadicField.mem_absInertia_of_artin`, `PadicField.exists_unit_abRec_eq`; norm compatibility
  (`Reciprocity/{FrobLiftPow,BaseChange,NormCompat}.lean`): `PadicField.cycRec_baseChange`,
  `PadicField.abRec_baseChange`, `PadicField.artin_baseChange` (finite Galois `K'/K`).

Not yet done: norm compatibility for non-Galois `K'/K`, units *onto* the full
inertia group of `Gal(K^ab/K)` (needs compactness of `𝒪ˣ`), and the existence theorem.

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

Intended to build on `continuous-kummer-theory` (for the existence theorem); it does not
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

License: Apache 2.0 (see LICENSE).
