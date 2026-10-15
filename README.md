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

* **Galois groups as profinite groups** (`Galois/ZHat.lean`, `PadicField/UnramifiedZHat.lean`,
  `Reciprocity/GaloisStructure.lean`): `Ẑ = lim ℤ/n` (`Brauer.ZHat`) is compact with `ℤ` dense
  (`Brauer.denseRange_intToZHat`); for every profinite group `G` and `g ∈ G` the continuous
  homomorphism `a ↦ g ^ a` from `Ẑ` (`Brauer.zhatPow`, unique: `Brauer.eq_zhatPow`).
  **`PadicField.galMaxUnramifiedEquiv : Gal(K^ur/K) ≃ₜ* Ẑ`** (Krull topology), sending the
  Frobenius to the topological generator `1` (`PadicField.galMaxUnramifiedEquiv_frobUr`); `σ` acting
  on `K_n` as `Frob^k` has `n`-th component `k mod n`
  (`PadicField.galMaxUnramifiedEquiv_apply_of_eq_pow`). After choosing a uniformiser `π`,
  **`PadicField.galAbEquiv : Gal(K^ab/K) ≃ₜ* 𝒪ˣ × Ẑ`** (`𝒪ˣ = PadicField.unitGroup` with the
  topology of the absolute value, compact: `PadicField.unitGroup.compactSpace`), inverse
  `(u, a) ↦ artin(u) · artin(π)^a`, with `galAbEquiv (artin (u π^k)) = (u, k)`
  (`PadicField.galAbEquiv_artin`, `PadicField.galAbEquiv_artin'`), `Ẑ`-component the restriction to
  `K^ur` followed by `Gal(K^ur/K) ≅ Ẑ` (`PadicField.galAbEquiv_snd`), and inertia corresponding to
  `𝒪ˣ × 1` (`PadicField.galAbEquiv_snd_eq_one_iff`); `Gal(K^ab/K)` is abelian
  (`PadicField.gal_maxAbelian_mul_comm`).


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
(`PadicField.relCyclicEquiv_fundClass`). More generally, for **finite abelian** `L/K` and every
`g ∈ Gal(L/K)`, `[∏_τ u(τ, g)] = (abRecEquiv L)⁻¹ g` in `Kˣ/N Lˣ` for any cocycle `u` representing
`u_{L/K}` (`PadicField.relNak_fundClass`; `∏_τ u(τ, g)` is the explicit formula for the cup product
`Ĥ⁻²(G, ℤ) ≅ G → Ĥ⁰(G, Lˣ)` with `u_{L/K}`, `ContH2.nakHom`; the identification of `Ĥ⁻²` itself is not
formalised), proved by reduction to the cyclic extension `L/L^{⟨g⟩}`. `H²(K, Ẑ(1))`, defined as
`lim_n H²(K, μ_n)` (`Brauer.H2ZHatOne`), is isomorphic to `Ẑ = lim_n ℤ/n`
(`PadicField.h2ZHatOneEquiv`), with restriction acting as multiplication by `[K':K]`
(`PadicField.h2ZHatOneEquiv_res`). The comparison with Mathlib's `groupCohomology.H2` is stated for
`G M : Type` because Mathlib's group cohomology requires the ring, group and module in one universe.

**Local duality, Tate–Nakayama, Euler characteristic (`LocalClassFieldTheory/Duality/`,
`Brauer/TateNakayamaDegrees.lean`, `PadicField/PowIndex*.lean`).**
* The index of `n`-th powers: `[Kˣ : (Kˣ)ⁿ] = n · #μ_n(K) · p^{v_p(n) [K:ℚ_p]}`
  (`PadicField.index_range_pow`; for any complete DVR with finite residue field
  `PowIndex.index_range_pow_field`: `[Kˣ : (Kˣ)ⁿ] = n · #(R/nR) · #μ_n(K)`).
* Cup products `H⁰ × H² → H²`, `H² × H⁰ → H²`, `H¹ × H¹ → H²` for an equivariant pairing
  (`Brauer.cup02`, `Brauer.cup20`, `Brauer.cup11`, graded commutativity `Brauer.cup11_swap`), the
  Cartier dual `M^∨ = Hom(M, μ_n)` (`Brauer.CartierDual`, smooth for finite smooth `M`) and the
  precise statements **`PadicField.LocalTateDuality`** (perfectness of
  `H^i(K, M) × H^{2-i}(K, M^∨) → H²(K, μ_n) ≃ ℤ/n` for all finite `M`, `i = 0, 1, 2`) and
  **`PadicField.LocalEulerCharacteristic`** (`#H⁰ · #H² / #H¹ = |#M|_K`) — these general
  statements are **not proved**.
* Proved cases: for `M = ℤ/n` (trivial action) duality in degrees `0, 1`
  (`PadicField.perfectDeg0_eval_trivZMod`, `PadicField.perfectDeg1_eval_trivZMod`), for
  `M = μ_n` in degrees `1, 2` (`PadicField.perfectDeg1_eval_mu`, `PadicField.perfectDeg2_eval_mu`),
  and all degrees when `μ_n ⊆ K` (`PadicField.tateDualityFor_trivZMod`,
  `PadicField.tateDualityFor_mu`); the Euler characteristic formula for `μ_n`
  (`PadicField.eulerCharacteristicFor_mu`) and, when `μ_n ⊆ K`, for `ℤ/n`
  (`PadicField.eulerCharacteristicFor_trivZMod`); `#H¹(K, ℤ/n) = #H¹(K, μ_n) = [Kˣ : (Kˣ)ⁿ]`
  (`PadicField.card_h1_trivZMod`, `PadicField.card_h1_mu_eq`).
* Long exact sequence: for `0 → A → B → C → 0` (`Brauer.GShortExact`) the connecting maps
  `Brauer.GShortExact.delta0`, `Brauer.GShortExact.delta1` and exactness of
  `H⁰(A) ↪ H⁰(B) → H⁰(C) → H¹(A) → H¹(B) → H¹(C) → H²(A) → H²(B) → H²(C)`
  (`exact_h0B`, …, `exact_h2B`); dévissage `χ(B) = χ(A) χ(C)`
  (`PadicField.eulerCharacteristicFor_of_shortExact`, assuming `H²(B) → H²(C)` surjective, which
  holds for split sequences), products, finite products, isomorphisms; the Euler characteristic
  formula for `∏ μ_{n_j}` (`PadicField.eulerCharacteristicFor_pi_mu`) and for trivial modules when
  `K` contains the `exp(M)`-th roots of unity (`PadicField.eulerCharacteristicFor_of_trivial`).
* Without roots of unity in `K`: restriction to an open subgroup of index prime to `n` is
  injective on `H²` (`ContH2.res_injective_of_coprime`), inner automorphisms act trivially
  (`ContH2.conj_res`), and **`H²(K, ℤ/ℓ) = 0` if `μ_ℓ ⊄ K`** for a prime `ℓ`
  (`PadicField.h2_trivZMod_prime_eq_one`, via `K(μ_ℓ)` and the twist by the cyclotomic
  character), so `#H²(K, ℤ/ℓ) = #μ_ℓ(K)`. Hence, with no condition on `K`: local Tate duality in
  all degrees for `ℤ/ℓ` and `μ_ℓ` (`PadicField.tateDualityFor_trivZMod_prime`,
  `PadicField.tateDualityFor_mu_prime`), for products and isomorphic modules
  (`PadicField.tateDualityFor_prod`, `PadicField.tateDualityFor_of_equiv`) and for trivial modules
  killed by `ℓ` (`PadicField.tateDualityFor_of_trivial_prime`); the Euler characteristic formula
  for `ℤ/n`, `n` squarefree, and for trivial modules of squarefree exponent
  (`PadicField.eulerCharacteristicFor_of_trivial_of_squarefree`; in general it suffices that
  `μ_{ℓ^e} ⊆ K` for the prime powers `ℓ^e ∣ exp(M)` with `e ≥ 2`,
  `PadicField.eulerCharacteristicFor_of_trivial_of_primePow`).
* Surjectivity of `H²` without `H³`: for the extensions `0 → ℤ/ℓ^e → ℤ/ℓ^{e+1} → ℤ/ℓ → 0`,
  `H²(K, ℤ/ℓ^{e+1}) → H²(K, ℤ/ℓ)` is onto (`PadicField.h2_castMulHom_surjective`: a Bockstein
  class `δ¹(χ) ≠ 0`, found by counting `#H¹(K, ℤ/n)`, generates `H²(K, ℤ/ℓ)`; naturality
  `Brauer.GShortExact.delta1_natural`). Hence, **with no condition on `K`**: the Euler
  characteristic formula for `ℤ/n` for every `n` and for **every finite module with trivial action**
  (`PadicField.eulerCharacteristicFor_trivZMod_all`, `PadicField.eulerCharacteristicFor_of_trivial_all`),
  `#H²(K, ℤ/n) = #μ_n(K) = #H⁰(K, (ℤ/n)^∨)` (`PadicField.card_h2_trivZMod`,
  `PadicField.card_h2_eq_card_h0_dual_trivZMod`), and **local Tate duality for `ℤ/n` and `μ_n` in all
  degrees for every `n`** (`PadicField.tateDualityFor_trivZMod_all`, `PadicField.tateDualityFor_mu_all`).
  Conversely, Euler for `A, B, C` implies `H²(B) → H²(C)` onto (`PadicField.h2Hom_surjective_of_euler`).
* `H³` in cocycle form (`Duality/H3Vanishing.lean`): `ContH2.H3Trivial G A` (locally constant
  `3`-cocycles are coboundaries) implies `H²(B) → H²(C)` onto
  (`Brauer.GShortExact.h2Hom_surjective_of_h3Trivial`); the statement
  **`PadicField.LocalH3Vanishing K Ω`** (`cd(G_K) ≤ 2` in this form); given it, the
  Euler characteristic formula is closed under all extensions
  (`PadicField.eulerCharacteristicFor_of_shortExact_of_localH3Vanishing`).
* `cd(G_K) ≤ 2` (`Duality/H3Devissage.lean`, `H3Cores.lean`, `H3Kummer.lean`, `H3Local.lean`,
  `H3Inflation.lean`, `EulerReduction.lean`): **`PadicField.localH3Vanishing_of_finiteLevel`**
  derives `LocalH3Vanishing K Ω` from **`PadicField.H3FiniteLevelVanishing K Ω`**
  (`H³(Gal(L/K'), Lˣ) = 0` for all finite Galois levels `L/K'`, Tate's theorem, **not proved**
  here), via the degree-three long exact sequence (`Brauer.GShortExact.h3Trivial`), corestriction
  in degree three (`ContH2.corFun3_res`, `ContH2.h3Trivial_of_res`), Sylow reduction to `ℤ/ℓ ≅ μ_ℓ`
  (`Brauer.h3Trivial_of_pgroup_action`), the Kummer sequence and divisibility of `Br(K') = ℚ/ℤ`
  (`PadicField.h3Trivial_mu`, from `Brauer.H3UnitsVanishing`: `H³(K', Ωˣ) = 0`) and inflation
  (`Brauer.h3UnitsVanishing_of_finite`). Moreover **`PadicField.localEulerCharacteristic_of_simple`**:
  `LocalH3Vanishing` and the Euler formula for simple modules imply `LocalEulerCharacteristic`.
* **Tate's theorem `H³(Gal(E/F), Eˣ) = 0` and `cd(G_K) ≤ 2`** (`Duality/Shapiro.lean`,
  `Duality/TateH3.lean`, `Duality/TateH3Local.lean`): Shapiro's lemma in degrees two and three for
  the coinduced module `Map(G/H, A)` (`ContH2.CoInd.shapiro_injective`, `ContH2.CoInd.h3Trivial`;
  cocycle form, via the prism homotopy for the retraction `G → H`); for a finite group `G` and a
  `G`-module `A`: Sylow reduction (`ContH2.h3Trivial_of_forall_prime`) and the `ℓ`-step
  (`ContH2.h3Trivial_of_index_prime`: `H ⊴ G` of prime index, `H¹(G, A) = 0`, `H²(G, A)`
  cyclic of order `|G|`, `|H²(H, A)| ≤ |H|`, `H³(H, A) = 0` ⇒ `H³(G, A) = 0`, using the trace and the
  difference operator on `Map(G/H, A)`); `Br(E/F)` is cyclic of order `[E:F]`
  (`PadicField.isCyclic_relBr_and_card`). Hence **`PadicField.h3Trivial_units`**
  (`H³(Gal(E/F), Eˣ) = 0` for every finite Galois extension of finite extensions of `ℚ_p`),
  **`PadicField.h3FiniteLevelVanishing`**, **`PadicField.h3UnitsVanishing`** (`H³(K, Ωˣ) = 0`),
  **`PadicField.localH3Vanishing`** (`cd(G_K) ≤ 2` in cocycle form), the surjectivity of
  `H²(K, B) → H²(K, C)` for every extension with finite kernel (`PadicField.h2Hom_surjective`),
  the Euler characteristic formula closed under all extensions
  (`PadicField.eulerCharacteristicFor_of_shortExact'`) and reduced to simple modules
  (`PadicField.localEulerCharacteristic_of_simple'`).
* **The Artin map commutes with the transfer** (`Brauer/ArtinTransfer.lean`): for a finite
  `K'/K` inside `Ω`, `a ∈ Kˣ` and any lift `g ∈ Gal(Ω/K)` of `artin_K(a)`,
  **`PadicField.artin_transfer`**: `artin_{K'}(a) = Ver(g)` in `Gal(K'^ab/K')`, where
  `PadicField.ver` is Mathlib's `MonoidHom.transfer` to `Gal(Ω/K')` followed by restriction
  (`ContH2.transfer_eq_prod_kappa`: `Ver(g) = ∏_c κ(c, g)`). Proof: the projection formula
  `cor(χ ∪ κ(a)) = (χ ∘ Ver) ∪ κ(a)` for carry cocycles (`PadicField.corBr_carryClass`),
  `inv ∘ cor = inv` and `⟨χ, a⟩ = χ(artin a)` give
  `⟨χ ∘ Ver, a⟩_K = ⟨χ, a⟩_{K'}`
  (`PadicField.pairing_corLocChar`); characters of finite abelian quotients separate points.
* Tate–Nakayama: degree `0`, `ℤ/[L:K] ≃ Br(L/K)`, `k ↦ u_{L/K}^k`, for every finite Galois `L/K`
  (`PadicField.fundClassPowEquiv`, `inv = k/[L:K]`: `PadicField.invEquiv_infl_fundClassPowEquiv`);
  degree `-2` for abelian `L/K` (`PadicField.bijective_relNak_fundClass`).

Not done (outside the scope of this repository's goals, possible future work): local Tate
duality and the Euler characteristic formula for general finite Galois modules (stated as
`PadicField.LocalTateDuality`, `PadicField.LocalEulerCharacteristic`; with `cd(G_K) ≤ 2` now
proved, what is missing is the Euler formula for simple `𝔽_ℓ[G_K]`-modules not reached by
dévissage (Brauer characters / the Galois-module structure of `Lˣ/(Lˣ)^ℓ`), Shapiro's lemma for
`G_K` and open subgroups as an isomorphism in degrees `0, 1, 2`, and the compatibility of cup
products with the connecting maps and with corestriction); Tate–Nakayama in degree `-2` for
non-abelian
`L/K` and in positive degrees; higher ramification groups (upper numbering) and the
conductor–ramification correspondence, Lubin–Tate theory (explicit `K^ab = K^ur · K_π`), local
class field theory in positive characteristic.

Downstream: `iut` requires this repository (`lakefile.toml` of `iut`, pinned at a commit of
`main`).

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
