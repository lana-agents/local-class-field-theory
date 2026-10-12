# local-class-field-theory

Local class field theory for mixed-characteristic local fields.

## Status

**Main results done.** Local reciprocity `Kˣ/N_{L/K} Lˣ ≃ Gal(L/K)` is formalised for every
finite abelian `L` inside a fixed algebraic closure `Ω`, together with the Artin map
`PadicField.artin : Kˣ →* Gal(K^ab/K)`: it is continuous, injective with dense image, sends
uniformisers to the arithmetic Frobenius modulo inertia, maps the units isomorphically onto the
inertia group `Gal(K^ab/K^ur)` (`PadicField.unitsInertiaEquiv`), is compatible with norms for every
finite `K'/K` (`PadicField.artin_baseChange`), and satisfies conjugation functoriality
(`PadicField.abRec_conj`). The **existence theorem** holds: every subgroup of finite index of `Kˣ`
is the norm group of a finite abelian extension (`PadicField.existence`), and `L ↦ N_{L/K} Lˣ` is
an order-reversing bijection onto the subgroups of finite index
(`PadicField.le_iff_normGroup_le`, `PadicField.existsUnique_normGroup_eq`). The Artin map extends
to an isomorphism of topological groups from the **profinite completion of `Kˣ`** onto
`Gal(K^ab/K)` (`PadicField.artinCompletionEquiv`), it is **characterised** by the Frobenius and
norm properties (`PadicField.eq_artin_of_forall`), and it does **not depend on `Ω`**: it is
transported along any `K`-isomorphism `Ω ≃ Ω'` (`PadicField.galMaxAbelianEquiv_artin`).

What is proved (no `sorry`, no `axiom`), all in the concrete setting of fields `K` with `[Algebra ℚ_[p] K]
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
  `PadicField.abRec_baseChange`, `PadicField.artin_baseChange` (every finite `K'/K`).
* The existence theorem (`Reciprocity/{Existence,Kummer,Conjugation,NormLimitation,
  ExistenceTheorem}.lean`): norm groups are upward closed and closed under intersections, and
  existence reduces to `(Kˣ)^n` (`PadicField.existence_of_pow`); Kummer case `μ_n ⊆ K`:
  `N(K((Kˣ)^{1/n})) = (Kˣ)^n` (`PadicField.exists_abFin_normGroup_eq_pow`); conjugation
  functoriality `PadicField.abRec_conj`; a norm limitation step for cyclic `K'/K`
  (`PadicField.exists_abFin_le_norm`); descent along cyclic steps of `K(μ_n)/K`
  (`PadicField.exists_abFin_normGroup_le_pow'`); `PadicField.existence`.
* `Reciprocity/ArtinInertia.lean`: `PadicField.eq_one_of_forall_pow` (`⋂ (Kˣ)ⁿ = 1`),
  `PadicField.artin_injective`, `PadicField.exists_unit_artin_eq` (compactness of the unit
  sphere), `PadicField.unitsInertiaEquiv`, `PadicField.denseRange_artin`.

* `Reciprocity/{ProfiniteCompletion,ArtinUnique,OmegaIndependence,UnitFiltration}.lean`:
  `PadicField.artinCompletionEquiv : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Kˣ)
  ≃ₜ* Gal(K^ab/K)` with `PadicField.artinCompletionEquiv_eta` (`K`, `Ω` in one universe);
  uniqueness `PadicField.eq_of_frob_of_norm`, `PadicField.eq_artin_of_forall`,
  `PadicField.eq_artin_iff`; independence of `Ω`: `PadicField.maxAbelianEquiv`,
  `PadicField.galMaxAbelianEquiv`, `PadicField.galMaxAbelianEquiv_artin`, `PadicField.abRec_map`;
  the unit filtration `PadicField.unitFiltration` (`U^(0) = 𝒪ˣ`, antitone, trivial intersection)
  and the existence of conductors `PadicField.exists_unitFiltration_le_normGroup`.


**Brauer groups (work package P9, `LocalClassFieldTheory/Brauer/`).** Second cohomology with
locally constant cochains `ContH2 G M` (multiplicative model), inflation injectivity and
inflation–restriction in degree two, periodicity `H²(G, M) ≃ Ĥ⁰(G, M)` for cyclic `G`
(`ContH2.cyclicEquiv`); relative Brauer groups `Brauer.RelBr K L = H²(Gal(L/K), Lˣ)` with
`Br(L/K) ≃ Kˣ/N Lˣ` for cyclic `L/K`; the Brauer group `Brauer.Br K Ω = H²(Gal(Ω/K), Ωˣ)` as the
union of the `Br(L/K)` (`Brauer.exists_infl_eq`, `Brauer.infl_injective`); the solvability input
(`PadicField.isCyclic_or_exists_normal`: tame character, wild inertia is a `p`-group) and the bound
`|H²(H, Lˣ)| ≤ |H|`; **the invariant map `PadicField.invEquiv : Br(K) ≃* ℚ/ℤ`** with
`|Br(L/K)| = [L:K]` (`PadicField.card_relBr_eq`), `Br(L/K) = Br(K_{[L:K]}/K)` inside `Br(K)`
(`PadicField.range_infl_eq`), `inv_{K'} ∘ res = [K':K] · inv_K` (`PadicField.invEquiv_res`) and the
fundamental class `PadicField.fundClass` (`inv = 1/[L:K]`, generating `Br(L/K)`). Kummer sequence in
degree two and **cyclotomic rigidity** `PadicField.h2MuEquiv : H²(Gal(Ω/K), μ_n) ≃* ℤ/n`
(`H²(K, μ_n) ≃ Br(K)[n]`, `Brauer.toBr_injective`, `Brauer.mem_range_toBr_iff`); the **local duality
pairing** `PadicField.pairing : H¹(K, ℤ/n) × Kˣ → ℤ/n`, `(χ, a) ↦ χ ∪ κ(a)`, bilinear and perfect
modulo `(Kˣ)ⁿ` (`PadicField.eq_one_of_forall_pairing_eq_zero`,
`PadicField.exists_pairing_ne_zero_of_not_mem_pow`), with `⟨χ, a⟩ = 0 ⟺ a ∈ N_{L_χ}`
(`PadicField.pairing_eq_zero_iff`; the cup product with a Kummer class is the carry class of the
cyclic field `L_χ`, `Brauer.toBr_mk_cupKummer`, `Brauer.carryClass_eq_infl`), and **the pairing computes
the Artin map**: `⟨χ, a⟩ = χ(artin a)` (`PadicField.pairing_eq_artinChar`); on continuous cohomology
`H¹(K, ℤ/n) × H¹(K, μ_n) → H²(K, μ_n) ≃ ℤ/n` (`Brauer.cupH1`, `PadicField.pairingH1`,
`PadicField.pairingH1_kummer`) it is perfect (`PadicField.eq_one_of_forall_pairingH1_eq_zero`,
`PadicField.eq_one_of_forall_pairingH1_eq_zero'`). The isomorphisms `H²(K, μ_n) ≃ ℤ/n` are compatible
with `μ_n ⊆ μ_m`, `ζ ↦ ζ^{m/n}` and restriction (`PadicField.h2MuEquiv_h2MuIncl`,
`PadicField.h2MuEquiv_h2MuPow`, `PadicField.h2MuEquiv_resMu`). Corestriction `ContH2.cor`
(`cor ∘ res = [G:H]`, `ContH2.cor_res`) and `Brauer.corBr : Br(K') → Br(K)` with
`inv_K ∘ cor = inv_{K'}` (`PadicField.invEquiv_corBr`). For discrete `G`, `ContH2 G M` agrees with
Mathlib's `groupCohomology.H2` (`ContH2.addEquivH2`). For cyclic `L/K` with generator `σ`,
`inv(infl cup_σ(a)) = k/[L:K]` when `abRec_L(a) = σ^k` (`PadicField.invEquiv_infl_cupClass`), and the
fundamental class inverts the reciprocity map: `relCyclicEquiv σ u_{L/K} = (abRecEquiv L)⁻¹ σ`
(`PadicField.relCyclicEquiv_fundClass`).

Not done (outside the scope of this repository's goals, possible future work): the explicit
decomposition `Gal(K^ab/K) ≅ 𝒪ˣ × Ẑ` (needs the profinite completion of `𝒪ˣ × ℤ` and
`Gal(K^ur/K) ≅ Ẑ`), higher ramification groups (upper numbering) and the conductor–ramification
correspondence, Lubin–Tate theory (explicit `K^ab = K^ur · K_π`), local class field theory in
positive characteristic.

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

Requires `continuous-kummer-theory` (pinned at `98b67df`) for the finiteness of `Kˣ/(Kˣ)ⁿ`
(`KummerTheory.finiteKummerQuotients_of_isDiscreteValuationRing`), used in the Kummer case of the
existence theorem.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`
(commit `81a5d25`) and `continuous-kummer-theory` (`98b67df`, same Mathlib) as dependencies.
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
