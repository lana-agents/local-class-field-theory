/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.Conjugation

/-!
# A norm limitation step

Let `K'/K` be a cyclic extension and `L/K'` a finite abelian extension with `L/K` Galois, all
inside `Ω`. Let `G = Gal(L/K)` and let `B ⊆ G` be the image under `abRec_L` of the elements of
norm one in `K'ˣ`. By conjugation functoriality (`PadicField.abRec_conj`), `B` is normal and
contains all commutators `[g, a]` with `a ∈ Gal(L/K')`; since `G / Gal(L/K')` is cyclic, `G / B`
is abelian. Its fixed field `M` is a finite abelian extension of `K` with

`N_{M/K} Mˣ ⊆ N_{K'/K} (N_{L/K'} Lˣ)`  (`PadicField.exists_abFin_le_norm`).
-/

set_option linter.unusedSectionVars false

open IntermediateField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

variable (K' : IntermediateField K Ω) [FiniteDimensional K K'] [IsGalois K K']
variable (L : IntermediateField K' Ω) [FiniteDimensional K' L] [IsAbelianGalois K' L]

/-- Elements of `Gal(L/K)` trivial on `K'` come from `Gal(L/K')`. -/
theorem mem_range_toK [Normal K (L.restrictScalars K)]
    (g : L.restrictScalars K ≃ₐ[K] L.restrictScalars K)
    (hg : resHom (le_restrictScalars K' L) g = 1) : g ∈ (toK K' L).range := by
  refine ⟨{ (g : L.restrictScalars K ≃ₐ[K] L.restrictScalars K) with
    commutes' := fun k ↦ ?_ }, ?_⟩
  · have h1 := resHom_apply (le_restrictScalars K' L) g k
    rw [hg, AlgEquiv.one_apply] at h1
    exact Subtype.ext h1.symm
  · ext y; rfl

theorem toK_injective : Function.Injective (toK K' L) := fun _ _ h ↦
  AlgEquiv.ext fun y ↦ Subtype.ext (congrArg (fun g ↦ ((g y : L.restrictScalars K) : Ω)) h)

/-- The norm `K'ˣ → Kˣ` is invariant under `K`-automorphisms of `K'`. -/
theorem normU_map_algEquiv (σ : K' ≃ₐ[K] K') (u : K'ˣ) :
    normU K' (Units.map (σ : K' →* K') u) = normU K' u :=
  Units.ext (Algebra.norm_eq_of_algEquiv σ (u : K'))

variable (p) in
/-- The image `B ⊆ Gal(L/K)` of the elements of norm one under the reciprocity map. -/
noncomputable def normOneImage :
    Subgroup (L.restrictScalars K ≃ₐ[K] L.restrictScalars K) :=
  (normU K').ker.map ((toK K' L).comp (abRec p L))

variable [Normal K (L.restrictScalars K)]

include hp in
theorem conj_mem_normOneImage (g : L.restrictScalars K ≃ₐ[K] L.restrictScalars K)
    {b : L.restrictScalars K ≃ₐ[K] L.restrictScalars K} (hb : b ∈ normOneImage p K' L) :
    g * b * g⁻¹ ∈ normOneImage p K' L := by
  obtain ⟨u, hu, rfl⟩ := hb
  refine ⟨Units.map (resHom (le_restrictScalars K' L) g : K' →* K') u, ?_, ?_⟩
  · rw [SetLike.mem_coe, MonoidHom.mem_ker, normU_map_algEquiv]; exact hu
  · exact abRec_conj K' L g u

instance normOneImage_normal : (normOneImage p K' L).Normal :=
  ⟨fun _ hb g ↦ conj_mem_normOneImage K' L g hb⟩

include hp in
theorem commutator_mem_normOneImage (g a : L.restrictScalars K ≃ₐ[K] L.restrictScalars K)
    (ha : a ∈ (toK K' L).range) : g * a * g⁻¹ * a⁻¹ ∈ normOneImage p K' L := by
  obtain ⟨σ, rfl⟩ := ha
  obtain ⟨w, rfl⟩ := abRec_surjective (p := p) L σ
  refine ⟨Units.map (resHom (le_restrictScalars K' L) g : K' →* K') w * w⁻¹, ?_, ?_⟩
  · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, normU_map_algEquiv, mul_inv_cancel]
  · change toK K' L (abRec p L (_ * w⁻¹)) = _
    rw [map_mul, map_mul, map_inv, map_inv, abRec_conj]

include hp in
/-- For cyclic `K'/K`, all commutators of `Gal(L/K)` lie in `B`. -/
theorem commutator_mem_normOneImage' [IsCyclic (K' ≃ₐ[K] K')]
    (g h : L.restrictScalars K ≃ₐ[K] L.restrictScalars K) :
    g * h * g⁻¹ * h⁻¹ ∈ normOneImage p K' L := by
  obtain ⟨σ₀, hσ₀⟩ := IsCyclic.exists_generator (α := K' ≃ₐ[K] K')
  obtain ⟨g₀, hg₀⟩ := resHom_surjective (le_restrictScalars K' L) σ₀
  have hdec : ∀ x : L.restrictScalars K ≃ₐ[K] L.restrictScalars K,
      ∃ i : ℤ, g₀ ^ (-i) * x ∈ (toK K' L).range := by
    intro x
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hσ₀ (resHom (le_restrictScalars K' L) x))
    refine ⟨i, mem_range_toK K' L _ ?_⟩
    rw [map_mul, map_zpow, hg₀, ← hi, zpow_neg, inv_mul_cancel]
  set π := QuotientGroup.mk' (normOneImage p K' L)
  have hcent : ∀ a ∈ (toK K' L).range, ∀ x, Commute (π x) (π a) := by
    intro a ha x
    have h1 : π (x * a * x⁻¹ * a⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (commutator_mem_normOneImage K' L x a ha)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hπ : ∀ x : L.restrictScalars K ≃ₐ[K] L.restrictScalars K, ∀ i : ℤ,
      π x = π g₀ ^ i * π (g₀ ^ (-i) * x) := by
    intro x i
    rw [← map_zpow, ← map_mul, ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  obtain ⟨i, hi⟩ := hdec g
  obtain ⟨j, hj⟩ := hdec h
  have hc : Commute (π g) (π h) := by
    rw [hπ g i, hπ h j]
    refine Commute.mul_left (Commute.mul_right (Commute.zpow_zpow_self _ i j)
      ((hcent _ hj g₀).zpow_left i)) (Commute.mul_right ((hcent _ hi g₀).symm.zpow_right j)
      (hcent _ hi _).symm)
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
  change π (g * h * g⁻¹ * h⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc.eq, mul_inv_cancel_right, mul_inv_cancel]

/-- Restriction to `M ⊆ L` (as extensions of `K`). -/
theorem fixes_lift_fixedField (b : L.restrictScalars K ≃ₐ[K] L.restrictScalars K)
    (hb : b ∈ normOneImage p K' L) (y : L.restrictScalars K)
    (hy : (y : Ω) ∈ lift (fixedField (normOneImage p K' L))) : b y = y :=
  (mem_lift y).1 hy ⟨b, hb⟩

/-- `K' ⊆ M`. -/
theorem le_lift_fixedField :
    K' ≤ lift (fixedField (normOneImage p K' L)) := by
  intro x hx
  refine (mem_lift ⟨x, le_restrictScalars K' L hx⟩).2 ?_
  rintro ⟨_, ⟨u, -, rfl⟩⟩
  exact Subtype.ext (congrArg Subtype.val ((abRec p L u).commutes ⟨x, hx⟩))

include hp in
/-- **Norm limitation step**: for cyclic `K'/K` and finite abelian `L/K'` with `L/K` Galois, there
is a finite abelian `M/K` (`M ⊆ L`) with `N_{M/K} Mˣ ⊆ N_{K'/K} (N_{L/K'} Lˣ)`. -/
theorem exists_abFin_le_norm [IsCyclic (K' ≃ₐ[K] K')] :
    ∃ M : AbFin K Ω, M.1 ≤ L.restrictScalars K ∧
      ∀ x ∈ normGroup K M.1, ∃ z ∈ normGroup K' L, normU K' z = x := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  haveI : FiniteDimensional K (L.restrictScalars K) :=
    (FiniteDimensional.trans K K' L : FiniteDimensional K L)
  haveI : IsGalois K (L.restrictScalars K) := ⟨⟩
  set B := normOneImage p K' L
  set M := lift (fixedField B)
  let εM : fixedField B ≃ₐ[K] M := liftAlgEquiv _
  haveI : FiniteDimensional K M := LinearEquiv.finiteDimensional εM.toLinearEquiv
  haveI : IsGalois K M := IsGalois.of_algEquiv εM
  have hML : M ≤ L.restrictScalars K := lift_le _
  haveI : IsAbelianGalois K M := by
    refine { toIsGalois := inferInstance, toIsMulCommutative := ⟨⟨fun σ τ ↦ ?_⟩⟩ }
    obtain ⟨g, rfl⟩ := resHom_surjective hML σ
    obtain ⟨h, rfl⟩ := resHom_surjective hML τ
    have h1 : resHom hML (g * h * g⁻¹ * h⁻¹) = 1 := by
      rw [resHom_eq_iff]
      intro y
      rw [AlgEquiv.one_apply]
      exact congrArg Subtype.val (fixes_lift_fixedField K' L _
        (commutator_mem_normOneImage' K' L g h) _ y.2)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  refine ⟨⟨M, inferInstance, inferInstance⟩, hML, fun x hx ↦ ?_⟩
  have hK'M : K' ≤ M := le_lift_fixedField K' L
  -- `x` is a norm from `K'`
  obtain ⟨z₀, hz₀⟩ := (mem_normGroup_iff).1 (normGroup_le_of_algHom (inclusion hK'M) hx)
  have hxz : normU K' z₀ = x := Units.ext hz₀
  -- `abRec_L z₀` is trivial on `M`
  have hbc : baseChange K' M ≤ L := fun y hy ↦ by
    have := (mem_baseChange K' M).1 hy
    exact (sup_le hML (le_restrictScalars K' L) : M ⊔ K' ≤ L.restrictScalars K) this
  have h1 := abRec_baseChange (p := p) K' M z₀
  rw [hxz, (MonoidHom.mem_ker).1 ((ker_abRec (p := p) M).symm ▸ hx :
    x ∈ (abRec p M).ker)] at h1
  have h2 := resHom_abRec_of_le (p := p) L (baseChange K' M) hbc z₀
  have hfix : toK K' L (abRec p L z₀) ∈ fixingSubgroup (fixedField B) := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hyM : (y : Ω) ∈ M := (mem_lift y).2 hy
    have h3 := resBaseChange_apply K' M (abRec p (baseChange K' M) z₀) ⟨y, hyM⟩
    rw [h1, AlgEquiv.one_apply, ← h2, resHom_apply] at h3
    exact Subtype.ext h3.symm
  rw [fixingSubgroup_fixedField] at hfix
  obtain ⟨u, hu, hu'⟩ := hfix
  have hu'' : abRec p L u = abRec p L z₀ := toK_injective K' L hu'
  refine ⟨z₀ * u⁻¹, ?_, ?_⟩
  · rw [← ker_abRec (p := p), MonoidHom.mem_ker, map_mul, map_inv, hu'', mul_inv_cancel]
  · rw [map_mul, map_inv, (MonoidHom.mem_ker).1 hu, inv_one, mul_one, hxz]

end PadicField
