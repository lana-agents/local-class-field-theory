/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.H3Kummer

/-!
# `cd(G_K) = 2` in cocycle form, from `H³(K', Ωˣ) = 0`

Let `K` be finite over `ℚ_p`, `Ω` an algebraic closure and `G = Gal(Ω/K)`. We prove

**`PadicField.localH3Vanishing_of_h3UnitsVanishing`** : if `H³(K', Ωˣ) = 0` (cocycle form,
`Brauer.H3UnitsVanishing K' Ω`) for every finite extension `K' ⊆ Ω` of `K`, then
`PadicField.LocalH3Vanishing K Ω` holds: every locally constant `3`-cocycle of `G` with values in
a finite discrete `G`-module is a coboundary.

Proof (Serre, *Galois cohomology* I.3.3 and II.4.3, in cocycle form):

* dévissage (`Brauer.finite_module_induction`, `Brauer.GShortExact.h3Trivial`) reduces to simple
  modules, which are killed by a prime `ℓ`;
* for `A` killed by `ℓ`, let `U ⊴ G` be the open kernel of the action on `A` and on `μ_ℓ`,
  `P` an `ℓ`-Sylow subgroup of `G/U` and `H` its preimage: an open subgroup of index prime to
  `ℓ`, so restriction to `H` is injective on `H³(-, A)` (`ContH2.h3Trivial_of_res`);
* `H` acts on `A` and `μ_ℓ` through the `ℓ`-group `P`, hence fixes `μ_ℓ` and has non-trivial
  fixed points on every non-trivial quotient of `A` (`Brauer.card_modEq_card_fixedPoints`); so as an
  `H`-module `A` is an iterated extension of copies of `ℤ/ℓ ≅ μ_ℓ`
  (`Brauer.h3Trivial_of_pgroup_action`);
* `H = Gal(Ω/K')` for a finite `K' ⊆ Ω` (`PadicField.exists_fixingSubgroup_eq`), and
  `H³(K', μ_ℓ) = 0` by the Kummer sequence (`PadicField.h3Trivial_fixingSubgroup_mu`).

The remaining input `H³(K', Ωˣ) = 0` (Tate) is not proved in this repository.
-/

open ContH2 groupCohomology KummerTheory

set_option linter.unusedSectionVars false

namespace Brauer

universe u v

/-! ### Fixed points of `ℓ`-groups -/

/-- If every element of `H` acts on the finite set `X` with order a power of `ℓ`, then
`#X ≡ #X^H mod ℓ`. -/
theorem card_modEq_card_fixedPoints {H X : Type*} [Group H] [MulAction H X] [Finite X]
    {ℓ : ℕ} [Fact ℓ.Prime] (hC : ∀ h : H, ∃ k : ℕ, ∀ x : X, h ^ (ℓ ^ k) • x = x) :
    Nat.card X ≡ Nat.card (MulAction.fixedPoints H X) [MOD ℓ] := by
  set R := (MulAction.toPermHom H X).range
  have hR : IsPGroup ℓ R := by
    rintro ⟨σ, h, rfl⟩
    obtain ⟨k, hk⟩ := hC h
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← map_pow, OneMemClass.coe_one]
    exact Equiv.ext fun x => hk x
  have := hR.card_modEq_card_fixedPoints X
  have hset : MulAction.fixedPoints R X = MulAction.fixedPoints H X := by
    ext x
    simp only [MulAction.mem_fixedPoints]
    constructor
    · intro hx h
      exact hx ⟨MulAction.toPermHom H X h, h, rfl⟩
    · rintro hx ⟨σ, h, rfl⟩
      exact hx h
  rwa [hset] at this

/-- If every element of `H` acts with `ℓ`-power order on a group `X` of order `ℓ`, then `H`
acts trivially. -/
theorem smul_eq_of_card_eq_prime {H X : Type*} [Group H] [Group X] [MulDistribMulAction H X]
    [Finite X] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hX : Nat.card X = ℓ)
    (hC : ∀ h : H, ∃ k : ℕ, ∀ x : X, h ^ (ℓ ^ k) • x = x) (h : H) (x : X) : h • x = x := by
  have hmod := card_modEq_card_fixedPoints hC
  set F := MulAction.fixedPoints H X
  have h1 : (1 : X) ∈ F := fun g => smul_one g
  have hpos : 0 < Nat.card F := Nat.card_pos_iff.2 ⟨⟨1, h1⟩, inferInstance⟩
  have hle : Nat.card F ≤ ℓ := by
    rw [Nat.card_coe_set_eq, ← hX, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  have hdvd : ℓ ∣ Nat.card F := by
    rw [hX] at hmod
    exact Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))
  have hF : Nat.card F = ℓ := le_antisymm hle (Nat.le_of_dvd hpos hdvd)
  have huniv : F = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, hX, ← Nat.card_coe_set_eq, hF]
  have : x ∈ F := huniv ▸ Set.mem_univ x
  exact this h

/-! ### `H³` for modules on which `H` acts through an `ℓ`-group -/

/-- **`H³ = 0` for `ℓ`-torsion modules on which `H` acts through an `ℓ`-group**, given
`H³(H, μ) = 0` for one module `μ` of order `ℓ` with trivial action. -/
theorem h3Trivial_of_pgroup_action (H : Type*) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (μ : Type v) [CommGroup μ]
    [MulDistribMulAction H μ] (hμc : Nat.card μ = ℓ) (hμ : ∀ (h : H) (x : μ), h • x = x)
    (hμ3 : H3Trivial H μ) (B : Type u) [CommGroup B] [MulDistribMulAction H B] [Finite B]
    [SmoothAction H B] (hB : ∀ b : B, b ^ ℓ = 1)
    (hC : ∀ h : H, ∃ k : ℕ, ∀ b : B, h ^ (ℓ ^ k) • b = b) : H3Trivial H B := by
  revert hB hC
  refine finite_module_induction (G := H)
    (fun B _ _ => (∀ b : B, b ^ ℓ = 1) → (∀ h : H, ∃ k : ℕ, ∀ b : B, h ^ (ℓ ^ k) • b = b) →
      H3Trivial H B) (fun _ _ _ _ _ _ => h3Trivial_of_subsingleton) ?_ ?_ B
  · intro B _ _ _ _ hsim hexp hcond
    obtain ⟨hnt, hsimple⟩ := hsim
    have hcardB : ℓ ∣ Nat.card B := by
      obtain ⟨b, hb⟩ := exists_ne (1 : B)
      rw [← orderOf_eq_prime (hexp b) hb]
      exact orderOf_dvd_natCard b
    have hmod := card_modEq_card_fixedPoints hcond
    set F := MulAction.fixedPoints H B
    have hdvd : ℓ ∣ Nat.card F :=
      Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hcardB))
    obtain ⟨b0, hb0F, hb01⟩ : ∃ b0 ∈ F, b0 ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hsub : F ⊆ {1} := fun b hb => hcon b hb
      have h1 : Nat.card F ≤ 1 := by
        rw [Nat.card_coe_set_eq]
        exact (Set.ncard_le_ncard hsub).trans (Set.ncard_singleton _).le
      have hpos : 0 < Nat.card F := Nat.card_pos_iff.2 ⟨⟨1, fun g => smul_one g⟩, inferInstance⟩
      have h2 := Nat.le_of_dvd hpos hdvd
      have h3 := hℓ.out.two_le
      omega
    have hstable : IsGStable (G := H) (Subgroup.zpowers b0) := by
      rintro h b ⟨k, rfl⟩
      exact ⟨k, by simp only [smul_zpow', hb0F h]⟩
    have htop : Subgroup.zpowers b0 = ⊤ := by
      rcases hsimple _ hstable with h | h
      · exact absurd (h ▸ Subgroup.mem_zpowers b0) (by rw [Subgroup.mem_bot]; exact hb01)
      · exact h
    have hfix : ∀ (h : H) (b : B), h • b = b := by
      intro h b
      obtain ⟨k, rfl⟩ := (htop ▸ Subgroup.mem_top b : b ∈ Subgroup.zpowers b0)
      simp only [smul_zpow', hb0F h]
    have hcard : Nat.card B = ℓ := by
      rw [← Subgroup.card_top (G := B), ← htop, Nat.card_zpowers, orderOf_eq_prime (hexp b0) hb01]
    let τ : μ ≃* B := mulEquivOfPrimeCardEq hμc hcard
    exact h3Trivial_of_mulEquiv τ (fun h x => by rw [hμ, hfix]) hμ3
  · intro A B C _ _ _ _ _ _ _ _ _ _ _ _ S hA hC' hexp hcond
    refine S.h3Trivial (hA (fun a => S.injective ?_) fun h => ?_) (hC' (fun c => ?_) fun h => ?_)
    · rw [map_pow, hexp, map_one]
    · obtain ⟨k, hk⟩ := hcond h
      exact ⟨k, fun a => S.injective (by rw [S.map_smul_i, hk])⟩
    · obtain ⟨b, rfl⟩ := S.surjective c
      rw [← map_pow, hexp, map_one]
    · obtain ⟨k, hk⟩ := hcond h
      refine ⟨k, fun c => ?_⟩
      obtain ⟨b, rfl⟩ := S.surjective c
      rw [← S.map_smul_π, hk]

/-! ### Open kernels -/

theorem isOpen_ker_toPermHom {G A : Type*} [Group G] [TopologicalSpace G] [MulAction G A]
    [Finite A] [SmoothAction G A] : IsOpen ((MulAction.toPermHom G A).ker : Set G) := by
  have : ((MulAction.toPermHom G A).ker : Set G) = ⋂ a : A, (fun g : G => g • a) ⁻¹' {a} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage,
      Set.mem_singleton_iff, Equiv.Perm.ext_iff, MulAction.toPermHom_apply,
      MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq]
  rw [this]
  exact isOpen_iInter_of_finite fun a =>
    (SmoothAction.isLocallyConstant_smul (G := G) a).isOpen_fiber a

theorem smul_eq_of_mem_ker {G A : Type*} [Group G] [MulAction G A] {g : G}
    (hg : g ∈ (MulAction.toPermHom G A).ker) (a : A) : g • a = a := by
  rw [MonoidHom.mem_ker] at hg
  exact congrArg (fun σ : Equiv.Perm A => σ a) hg

end Brauer

namespace PadicField

open Brauer IntermediateField

universe u

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

/-- **Open subgroups of `Gal(Ω/K)` are the `Gal(Ω/K')` of finite extensions `K' ⊆ Ω`.** -/
theorem exists_fixingSubgroup_eq (H : Subgroup (Ω ≃ₐ[K] Ω)) (hH : IsOpen (H : Set (Ω ≃ₐ[K] Ω))) :
    ∃ K' : IntermediateField K Ω, FiniteDimensional K K' ∧ K'.fixingSubgroup = H := by
  have heq : (fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen hH⟩
  refine ⟨fixedField H, (InfiniteGalois.isOpen_iff_finite _).1 ?_, heq⟩
  change IsOpen ((fixedField H).fixingSubgroup : Set (Ω ≃ₐ[K] Ω))
  rw [heq]
  exact hH

variable (p) in
include hp in
/-- `H³(H, μ_n) = 0` for every open subgroup `H ≤ Gal(Ω/K)`, given `H³(K', Ωˣ) = 0` for finite
`K' ⊆ Ω`. -/
theorem h3Trivial_open_mu
    (hU : ∀ K' : IntermediateField K Ω, FiniteDimensional K K' → H3UnitsVanishing K' Ω)
    (H : Subgroup (Ω ≃ₐ[K] Ω)) (hH : IsOpen (H : Set (Ω ≃ₐ[K] Ω))) {n : ℕ} (hn : 0 < n) :
    H3Trivial H (Mu n Ω) := by
  obtain ⟨K', hK', rfl⟩ := exists_fixingSubgroup_eq H hH
  exact h3Trivial_fixingSubgroup_mu p K' (hU K' hK') hn

variable (p) in
include hp in
/-- **`H³(K, A) = 0` for finite modules killed by a prime `ℓ`**, given `H³(K', Ωˣ) = 0` for
all finite `K' ⊆ Ω`. -/
theorem h3Trivial_of_exponent
    (hU : ∀ K' : IntermediateField K Ω, FiniteDimensional K K' → H3UnitsVanishing K' Ω)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (A : Type*) [CommGroup A] [Finite A]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) A] [SmoothAction (Ω ≃ₐ[K] Ω) A]
    (hA : ∀ a : A, a ^ ℓ = 1) : H3Trivial (Ω ≃ₐ[K] Ω) A := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  set G := Ω ≃ₐ[K] Ω
  set U : Subgroup G :=
    (MulAction.toPermHom G A).ker ⊓ (MulAction.toPermHom G (Mu ℓ Ω)).ker with hU_def
  have hUo : IsOpen (U : Set G) := isOpen_ker_toPermHom.inter isOpen_ker_toPermHom
  obtain ⟨L, hLfin, hLU⟩ := exists_fixingSubgroup_eq U hUo
  haveI : U.FiniteIndex := ⟨by rw [← hLU, index_fixingSubgroup]; exact Module.finrank_pos.ne'⟩
  haveI : Finite (G ⧸ U) := Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨P⟩ : Nonempty (Sylow ℓ (G ⧸ U)) := inferInstance
  set H : Subgroup G := (P : Subgroup (G ⧸ U)).comap (QuotientGroup.mk' U) with hH_def
  have hUH : U ≤ H := fun u hu => by
    rw [hH_def, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).2 hu]
    exact one_mem _
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_mono hUH hUo
  have hindex : H.index = (P : Subgroup (G ⧸ U)).index :=
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective U)
  have hndvd : ¬ ℓ ∣ H.index := hindex ▸ P.not_dvd_index
  haveI : H.FiniteIndex := ⟨by rw [hindex]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hcardH : Fintype.card (G ⧸ H) = H.index := by
    rw [← Nat.card_eq_fintype_card, Subgroup.index]
  -- elements of `H` have `ℓ`-power order modulo `U`
  have hpow : ∀ h : H, ∃ k : ℕ, ((h : G) ^ (ℓ ^ k)) ∈ U := by
    intro h
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨QuotientGroup.mk' U (h : G), h.2⟩
    refine ⟨k, (QuotientGroup.eq_one_iff _).1 ?_⟩
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, OneMemClass.coe_one, ← map_pow] at this
    exact this
  have hcondA : ∀ h : H, ∃ k : ℕ, ∀ a : A, h ^ (ℓ ^ k) • a = a := fun h => by
    obtain ⟨k, hk⟩ := hpow h
    exact ⟨k, fun a => smul_eq_of_mem_ker (Subgroup.mem_inf.1 hk).1 a⟩
  have hcondμ : ∀ h : H, ∃ k : ℕ, ∀ x : Mu ℓ Ω, h ^ (ℓ ^ k) • x = x := fun h => by
    obtain ⟨k, hk⟩ := hpow h
    exact ⟨k, fun a => smul_eq_of_mem_ker (Subgroup.mem_inf.1 hk).2 a⟩
  have hμc : Nat.card (Mu ℓ Ω) = ℓ := card_mu (p := p) ℓ
  have hμ : ∀ (h : H) (x : Mu ℓ Ω), h • x = x := smul_eq_of_card_eq_prime hμc hcondμ
  haveI : SmoothAction H A :=
    ⟨fun a => (SmoothAction.isLocallyConstant_smul (G := G) a).comp_continuous
      continuous_subtype_val⟩
  have hHA : H3Trivial H A := h3Trivial_of_pgroup_action H ℓ (Mu ℓ Ω) hμc hμ
    (h3Trivial_open_mu p hU H hHo hℓ.out.pos) A hA hcondA
  refine h3Trivial_of_res H hHo (fun a ha => ?_) hHA
  have hcop : Nat.Coprime ℓ (Fintype.card (G ⧸ H)) := by
    rw [hcardH]; exact (Nat.Prime.coprime_iff_not_dvd hℓ.out).2 hndvd
  have := pow_gcd_eq_one.2 ⟨hA a, ha⟩
  rwa [hcop, pow_one] at this

variable (p) in
include hp in
/-- **`cd(G_K) = 2` in cocycle form, from `H³(K', Ωˣ) = 0`**: if every finite extension
`K' ⊆ Ω` of `K` satisfies `H3UnitsVanishing K' Ω`, then every locally constant `3`-cocycle of
`Gal(Ω/K)` with values in a finite discrete module is a coboundary. -/
theorem localH3Vanishing_of_h3UnitsVanishing
    (hU : ∀ K' : IntermediateField K Ω, FiniteDimensional K K' → H3UnitsVanishing K' Ω) :
    LocalH3Vanishing.{u} K Ω := by
  intro A _ _ _ _ _ _
  refine finite_module_induction (G := Ω ≃ₐ[K] Ω)
    (fun A _ _ => H3Trivial (Ω ≃ₐ[K] Ω) A) (fun _ _ _ _ => h3Trivial_of_subsingleton) ?_
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ S hA hC => S.h3Trivial hA hC) A
  intro A _ _ _ _ hsim
  obtain ⟨hnt, hsimple⟩ := hsim
  obtain ⟨ℓ, hℓ, hℓdvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := A)).ne'
  haveI := Fact.mk hℓ
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hℓdvd
  set B := (powMonoidHom ℓ : A →* A).ker
  have hB : IsGStable (G := Ω ≃ₐ[K] Ω) B := fun g b hb => by
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at hb ⊢
    rw [← smul_pow', hb, smul_one]
  have hxB : x ∈ B := by
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← hx]
    exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx
    exact hℓ.one_lt.ne hx
  rcases hsimple B hB with h | h
  · exact absurd (h ▸ hxB) (by rw [Subgroup.mem_bot]; exact hx1)
  · refine h3Trivial_of_exponent p hU ℓ A fun a => ?_
    have : a ∈ B := h ▸ Subgroup.mem_top a
    rwa [MonoidHom.mem_ker, powMonoidHom_apply] at this

end PadicField
