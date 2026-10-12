/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.Cyclic
import LocalClassFieldTheory.Reciprocity.SecondInequality

/-!
# Relative Brauer groups `H²(Gal(L/K), Lˣ)`

For a finite Galois extension `L/K` we put `Brauer.RelBr K L = H²(Gal(L/K), Lˣ)` (the relative
Brauer group, computed with `ContH2` for the discrete group `Gal(L/K)`).

* `Brauer.fixedUnitsEquiv : Kˣ ≃* (Lˣ)^{Gal(L/K)}` and `Brauer.hhat0Equiv :
  Ĥ⁰(Gal(L/K), Lˣ) ≃* Kˣ ⧸ N_{L/K} Lˣ` (via `Algebra.norm_eq_prod_automorphisms`).
* `Brauer.relCyclicEquiv σ hσ : RelBr K L ≃* Kˣ ⧸ N_{L/K} Lˣ` for cyclic `L/K` with generator
  `σ`: the class of `f` goes to `∏_{i<n} f(σ^i, σ)`.
* For local fields (finite over `ℚ_[p]`): `PadicField.card_rel_of_isCyclic : |Br(L/K)| = [L:K]`
  for cyclic `L/K` (class field axiom), and for unramified `L/K` of degree `n` the
  **invariant** `PadicField.invUnr h : Br(L/K) →* Multiplicative (ℚ/ℤ)`,
  `[f] ↦ v_K(∏_{i<n} f(Frob^i, Frob)) / n`, which is injective with image `(1/n)ℤ/ℤ`
  (`PadicField.invUnr_injective`, `PadicField.invUnr_mk_cup`).
-/

open ContH2 Finset

namespace Brauer

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The relative Brauer group `H²(Gal(L/K), Lˣ)`. -/
abbrev RelBr : Type _ := ContH2 (L ≃ₐ[K] L) Lˣ

/-- `ℚ/ℤ`, the target of the invariant map. -/
abbrev QZ : Type := AddCircle (1 : ℚ)

theorem smul_units_coe (σ : L ≃ₐ[K] L) (u : Lˣ) : ((σ • u : Lˣ) : L) = σ u := by
  rw [AlgEquiv.smul_units_def]
  rfl

variable [FiniteDimensional K L] [IsGalois K L]

/-- The map `Kˣ → (Lˣ)^{Gal(L/K)}`. -/
noncomputable def toFixedUnits : Kˣ →* fixedSubgroup (L ≃ₐ[K] L) Lˣ where
  toFun a := ⟨Units.map (algebraMap K L : K →* L) a, fun σ => by
    ext
    rw [smul_units_coe]
    simp⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

omit [FiniteDimensional K L] [IsGalois K L] in
theorem coe_toFixedUnits (a : Kˣ) :
    ((toFixedUnits K L a : Lˣ) : L) = algebraMap K L a := rfl

theorem toFixedUnits_bijective : Function.Bijective (toFixedUnits K L) := by
  constructor
  · intro a b hab
    have := congrArg (fun u : fixedSubgroup (L ≃ₐ[K] L) Lˣ => ((u : Lˣ) : L)) hab
    simp only [coe_toFixedUnits] at this
    exact Units.ext ((algebraMap K L).injective this)
  · rintro ⟨u, hu⟩
    have hmem : (u : L) ∈ (⊥ : IntermediateField K L) := by
      rw [IsGalois.mem_bot_iff_fixed]
      intro σ
      rw [← smul_units_coe, hu σ]
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 hmem
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact (Units.ne_zero u) (by simpa using ha.symm)
    refine ⟨Units.mk0 a ha0, ?_⟩
    ext
    simp [coe_toFixedUnits, ha]

/-- `Kˣ ≃* (Lˣ)^{Gal(L/K)}`. -/
noncomputable def fixedUnitsEquiv : Kˣ ≃* fixedSubgroup (L ≃ₐ[K] L) Lˣ :=
  MulEquiv.ofBijective _ (toFixedUnits_bijective K L)

theorem coe_fixedUnitsEquiv (a : Kˣ) :
    ((fixedUnitsEquiv K L a : Lˣ) : L) = algebraMap K L a := rfl

theorem coe_normMap (u : Lˣ) :
    ((normMap (L ≃ₐ[K] L) Lˣ u : Lˣ) : L) = algebraMap K L (Algebra.norm K (u : L)) := by
  rw [Algebra.norm_eq_prod_automorphisms, normMap_apply, Units.coe_prod]
  simp only [smul_units_coe]

theorem map_subgroupOf_normMap :
    ((normMap (L ≃ₐ[K] L) Lˣ).range.subgroupOf (fixedSubgroup (L ≃ₐ[K] L) Lˣ)).map
      (fixedUnitsEquiv K L).symm.toMonoidHom = PadicField.normGroup K L := by
  ext a
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf,
    MonoidHom.mem_range, PadicField.mem_normGroup]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, (algebraMap K L).injective ?_⟩
    rw [← coe_normMap, hu, coe_fixedUnitsEquiv]
  · rintro ⟨u, hu⟩
    refine ⟨u, Units.ext ?_⟩
    rw [coe_normMap, hu, coe_fixedUnitsEquiv]

/-- `Ĥ⁰(Gal(L/K), Lˣ) ≃* Kˣ ⧸ N_{L/K} Lˣ`. -/
noncomputable def hhat0Equiv : Hhat0 (L ≃ₐ[K] L) Lˣ ≃* Kˣ ⧸ PadicField.normGroup K L :=
  QuotientGroup.congr _ _ (fixedUnitsEquiv K L).symm (map_subgroupOf_normMap K L)

theorem hhat0Equiv_mk (a : Kˣ) :
    hhat0Equiv K L (QuotientGroup.mk (fixedUnitsEquiv K L a)) = QuotientGroup.mk a := by
  simp [hhat0Equiv]

variable {K L}

/-- **Periodicity for cyclic extensions**: `Br(L/K) ≃* Kˣ ⧸ N_{L/K} Lˣ` for a generator `σ`. -/
noncomputable def relCyclicEquiv (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    RelBr K L ≃* Kˣ ⧸ PadicField.normGroup K L :=
  (cyclicEquiv σ hσ).trans (hhat0Equiv K L)

/-- The element of `Kˣ` corresponding to `∏_{i<n} f(σ^i, σ)` for a cocycle `f`. -/
noncomputable def phiUnits (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (f : cocycles (L ≃ₐ[K] L) Lˣ) : Kˣ :=
  (fixedUnitsEquiv K L).symm ⟨phiFun σ f, phiFun_mem_fixedSubgroup σ hσ (isMulCocycle₂ f)⟩

theorem algebraMap_phiUnits (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (f : cocycles (L ≃ₐ[K] L) Lˣ) :
    algebraMap K L (phiUnits σ hσ f) = ((phiFun σ f : Lˣ) : L) := by
  rw [← coe_fixedUnitsEquiv, phiUnits, MulEquiv.apply_symm_apply]

theorem relCyclicEquiv_mk (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (f : cocycles (L ≃ₐ[K] L) Lˣ) :
    relCyclicEquiv σ hσ (mk f) = QuotientGroup.mk (phiUnits σ hσ f) := by
  rw [relCyclicEquiv, MulEquiv.trans_apply, cyclicEquiv_mk, ← hhat0Equiv_mk, phiUnits,
    MulEquiv.apply_symm_apply]

end Brauer

namespace PadicField

open Brauer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L]

include hp in
/-- `|Br(L/K)| = [L : K]` for a cyclic extension of local fields. -/
theorem card_rel_of_isCyclic [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    Nat.card (RelBr K L) = Module.finrank K L := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  rw [Nat.card_congr (relCyclicEquiv σ hσ).toEquiv, ← Subgroup.index,
    index_normGroup_of_isCyclic (p := p)]

variable (p K) in
/-- `x ↦ v_K(x) / n ∈ ℚ/ℤ`. -/
noncomputable def vQZ (n : ℕ) : Kˣ →* Multiplicative QZ where
  toFun a := Multiplicative.ofAdd (((v p (a : K) : ℚ) / n : ℚ) : QZ)
  map_one' := by simp [v_one]
  map_mul' a b := by
    rw [← ofAdd_add, ← QuotientAddGroup.mk_add, Units.val_mul, v_mul a.ne_zero b.ne_zero]
    push_cast
    rw [add_div]

theorem vQZ_apply (n : ℕ) (a : Kˣ) :
    vQZ p K n a = Multiplicative.ofAdd (((v p (a : K) : ℚ) / n : ℚ) : QZ) := rfl

theorem vQZ_eq_one_iff {n : ℕ} (hn : n ≠ 0) (a : Kˣ) : vQZ p K n a = 1 ↔ a ∈ vDvd p K n := by
  rw [vQZ_apply, mem_vDvd, ← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq,
    AddCircle.coe_eq_zero_iff]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, mul_one, eq_div_iff hn'] at hk
    exact_mod_cast hk.symm.trans (mul_comm _ _)
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [zsmul_eq_mul, mul_one, eq_div_iff hn', hk]
    push_cast
    ring

theorem vDvd_le_ker_vQZ (n : ℕ) : vDvd p K n ≤ (vQZ p K n).ker := by
  intro a ha
  rcases eq_or_ne n 0 with rfl | hn
  · rw [MonoidHom.mem_ker, vQZ_apply]
    simp
  · exact (vQZ_eq_one_iff hn a).2 ha

section Unramified

variable [FiniteDimensional K L] [IsGalois K L] (h : IsUnramified p K L)

omit [FiniteDimensional K L] [IsGalois K L] in
include h in
theorem mem_zpowers_frob (g : L ≃ₐ[K] L) : g ∈ Subgroup.zpowers (frob h) := by
  rw [zpowers_frob h]
  trivial

omit [FiniteDimensional K L] [IsGalois K L] in
include h in
theorem normGroup_le_ker_vQZ :
    normGroup K L ≤ (vQZ p K (Module.finrank K L)).ker := by
  rw [normGroup_of_isUnramified h]
  exact vDvd_le_ker_vQZ _

/-- The **invariant** of an unramified extension of degree `n`:
`Br(L/K) → ℚ/ℤ`, `[f] ↦ v_K(∏_{i<n} f(Frob^i, Frob)) / n`. -/
noncomputable def invUnr : RelBr K L →* Multiplicative QZ :=
  (QuotientGroup.lift _ (vQZ p K (Module.finrank K L)) (normGroup_le_ker_vQZ h)).comp
    (relCyclicEquiv (frob h) (mem_zpowers_frob h)).toMonoidHom

/-- The class in `Br(L/K)` of `a ∈ Kˣ` (with respect to the Frobenius). -/
noncomputable def unrClass (a : Kˣ) : RelBr K L :=
  (relCyclicEquiv (frob h) (mem_zpowers_frob h)).symm (QuotientGroup.mk a)

theorem invUnr_unrClass (a : Kˣ) :
    invUnr h (unrClass h a) = vQZ p K (Module.finrank K L) a := by
  simp [invUnr, unrClass]

theorem unrClass_surjective : Function.Surjective (unrClass h) := by
  intro α
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective
    (relCyclicEquiv (frob h) (mem_zpowers_frob h) α)
  exact ⟨a, by rw [unrClass, ha, MulEquiv.symm_apply_apply]⟩

theorem invUnr_injective : Function.Injective (invUnr h) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro α hα
  obtain ⟨a, rfl⟩ := unrClass_surjective h α
  rw [MonoidHom.mem_ker, invUnr_unrClass, vQZ_eq_one_iff Module.finrank_pos.ne',
    ← normGroup_of_isUnramified h] at hα
  rw [Subgroup.mem_bot, unrClass, MulEquiv.symm_apply_eq, map_one,
    QuotientGroup.eq_one_iff]
  exact hα

end Unramified

end PadicField
