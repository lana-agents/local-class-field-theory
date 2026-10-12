/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.UnitMap

/-!
# The reciprocity map at a standard level

For a standard extension `F = M U` (`M/K` cyclic totally ramified of degree `e`, `U/K` unramified
of degree `t` with `e ∣ t`):

* `PadicField.stdProd : Gal(F/U) × Gal(F/M) ≃* Gal(F/K)` (the two subgroups commute and
  intersect trivially);
* `PadicField.rhoF : Kˣ →* Gal(F/K)`, `x ↦ (Ψ(x ϖ^{-v x}), φ^{v x})` where `ϖ = N_{M/K}(π_M)`;
  it is surjective with kernel `N_{F/K} Fˣ`.
-/

set_option linter.unusedSectionVars false

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]

variable {K M U F : Type*} [Field K] [Field M] [Field U] [Field F]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] M] [Algebra ℚ_[p] U] [Algebra ℚ_[p] F]
  [Algebra K M] [Algebra K U] [Algebra K F] [Algebra M F] [Algebra U F]
  [IsScalarTower ℚ_[p] K M] [IsScalarTower ℚ_[p] K U] [IsScalarTower ℚ_[p] K F]
  [IsScalarTower ℚ_[p] M F] [IsScalarTower ℚ_[p] U F]
  [IsScalarTower K M F] [IsScalarTower K U F]
  [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] M] [FiniteDimensional ℚ_[p] U]
  [FiniteDimensional ℚ_[p] F] [IsGalois K F] [IsGalois K M] [IsCyclic (M ≃ₐ[K] M)]

variable (hM : e p K M = Module.finrank K M) (hU : IsUnramified p K U)
  (hdeg : Module.finrank K F = Module.finrank K M * Module.finrank K U)
include hM hU hdeg

/-- The product map `Gal(F/U) × Gal(F/M) → Gal(F/K)`. -/
noncomputable def stdProdHom : (F ≃ₐ[U] F) × (F ≃ₐ[M] F) →* (F ≃ₐ[K] F) where
  toFun gh := gh.1.restrictScalars K * gh.2.restrictScalars K
  map_one' := by ext; simp
  map_mul' a b := by
    ext x
    simp only [Prod.fst_mul, Prod.snd_mul, AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]
    rw [std_comm hM hU hdeg b.1 a.2]

theorem stdProdHom_apply (g : F ≃ₐ[U] F) (h : F ≃ₐ[M] F) (x : F) :
    stdProdHom hM hU hdeg (g, h) x = g (h x) := rfl

theorem stdProdHom_bijective : Function.Bijective (stdProdHom hM hU hdeg) := by
  haveI := finiteDimensional_tower (p := p) K F
  haveI := finiteDimensional_tower (p := p) U F
  haveI := finiteDimensional_tower (p := p) M F
  haveI : IsGalois U F := IsGalois.tower_top_of_isGalois K U F
  haveI : IsGalois M F := IsGalois.tower_top_of_isGalois K M F
  have hinj : Function.Injective (stdProdHom hM hU hdeg) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨g, h⟩ hgh
    have hh : h = 1 := by
      apply (stdResU_bijective hM hU hdeg).1
      rw [map_one]
      ext u
      apply (algebraMap U F).injective
      rw [stdResU_apply]
      have := congrArg (fun σ : F ≃ₐ[K] F ↦ σ (algebraMap U F u)) hgh
      simp only [stdProdHom_apply, AlgEquiv.one_apply] at this
      rw [← stdResU_apply hU h u, g.commutes] at this
      rw [← stdResU_apply hU h u, this, AlgEquiv.one_apply]
    subst hh
    have hg : g = 1 := by
      ext x
      have := congrArg (fun σ : F ≃ₐ[K] F ↦ σ x) hgh
      simpa [stdProdHom_apply] using this
    rw [hg]; rfl
  refine hinj.bijective_of_nat_card_le ?_
  rw [Nat.card_prod, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    IsGalois.card_aut_eq_finrank, std_finrank_U hM hU hdeg, std_finrank_M hM hU hdeg, hdeg]

/-- `Gal(F/U) × Gal(F/M) ≃* Gal(F/K)`. -/
noncomputable def stdProd : (F ≃ₐ[U] F) × (F ≃ₐ[M] F) ≃* (F ≃ₐ[K] F) :=
  MulEquiv.ofBijective _ (stdProdHom_bijective hM hU hdeg)

theorem stdProd_apply (g : F ≃ₐ[U] F) (h : F ≃ₐ[M] F) (x : F) :
    stdProd hM hU hdeg (g, h) x = g (h x) := rfl


omit hU hdeg [IsGalois K F] [IsGalois K M] [IsCyclic (M ≃ₐ[K] M)] in
/-- `ϖ = N_{M/K}(π_M)`, a uniformiser of `K`. -/
noncomputable def stdVarpi : Kˣ :=
  Units.map (Algebra.norm K : M →* K) (Units.mk0 _ (uniformizer_spec (p := p) (K := M)).ne_zero)

omit hU hdeg [IsGalois K F] [IsGalois K M] [IsCyclic (M ≃ₐ[K] M)] in
theorem v_stdVarpi : v p ((stdVarpi (p := p) (K := K) (M := M) : Kˣ) : K) = 1 := by
  haveI := finiteDimensional_tower (p := p) K M
  have hπ := uniformizer_spec (p := p) (K := M)
  have hf : f p K M = 1 := by
    have := e_mul_f (p := p) (K := K) (L := M)
    rw [hM] at this
    exact (Nat.mul_eq_left Module.finrank_pos.ne').1 this
  change v p (Algebra.norm K (uniformizer p M)) = 1
  rw [v_norm hπ.ne_zero, hf, hπ]; rfl

omit hU hdeg [IsGalois K F] [IsGalois K M] [IsCyclic (M ≃ₐ[K] M)] in
/-- `x ↦ x ϖ^{-v x}`, the unit part of `x`. -/
noncomputable def unitPart : Kˣ →* unitGroup p K where
  toFun x := ⟨x * stdVarpi (p := p) (M := M) ^ (-v p (x : K)), by
    rw [mem_unitGroup, Units.val_mul, Units.val_zpow_eq_zpow_val, nrm_mul, nrm_zpow]
    rw [nrm_eq_nrm_uniformizer_zpow (π := ((stdVarpi (p := p) (M := M) : Kˣ) : K))
      (v_stdVarpi hM) x.ne_zero, ← zpow_add₀ (nrm_pos_iff.2 (Units.ne_zero _)).ne']
    simp⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Units.val_mul, Subgroup.coe_mul, Units.val_zpow_eq_zpow_val,
      v_mul a.ne_zero b.ne_zero, neg_add, zpow_add₀ (Units.ne_zero _)]
    ring

omit hU hdeg [IsGalois K F] [IsGalois K M] [IsCyclic (M ≃ₐ[K] M)] in
theorem unitPart_apply (x : Kˣ) :
    ((unitPart hM x : unitGroup p K) : Kˣ) = x * stdVarpi (p := p) (M := M) ^ (-v p (x : K)) :=
  rfl

/-- The valuation as a homomorphism to `Multiplicative ℤ`. -/
noncomputable def vMul (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] : Kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (v p (x : K))
  map_one' := by simp
  map_mul' a b := by simp [v_mul a.ne_zero b.ne_zero, ofAdd_add]

variable (s : M ≃ₐ[K] M) (hs : ∀ g, g ∈ Subgroup.zpowers s)
  (he : Module.finrank K M ∣ Module.finrank K U)

/-- **The reciprocity map at a standard level**: `x ↦ (Ψ(x ϖ^{-v x}), φ^{v x})`. -/
noncomputable def rhoF : Kˣ →* (F ≃ₐ[K] F) :=
  (stdProd hM hU hdeg).toMonoidHom.comp <| MonoidHom.prod
    ((MulEquiv.ofBijective _ (stdResM_bijective hM hU hdeg)).symm.toMonoidHom.comp
      ((psi hM hU hdeg s hs he).comp (unitPart hM)))
    ((zpowersHom _ (stdFrob hM hU hdeg)).comp (vMul p K))

theorem rhoF_apply (x : Kˣ) :
    rhoF hM hU hdeg s hs he x = stdProd hM hU hdeg
      ((MulEquiv.ofBijective _ (stdResM_bijective hM hU hdeg)).symm
        (psi hM hU hdeg s hs he (unitPart hM x)), stdFrob hM hU hdeg ^ v p (x : K)) := rfl

theorem rhoF_surjective : Function.Surjective (rhoF hM hU hdeg s hs he) := by
  haveI := finiteDimensional_tower (p := p) M F
  intro τ
  obtain ⟨⟨g, h⟩, rfl⟩ := (stdProd hM hU hdeg).surjective τ
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (stdFrob_generates hM hU hdeg h)
  obtain ⟨u, hu⟩ := psi_surjective hM hU hdeg s hs he (stdResM (K := K) g)
  refine ⟨(u : Kˣ) * stdVarpi (p := p) (M := M) ^ j, ?_⟩
  have hv : v p (((u : Kˣ) * stdVarpi (p := p) (M := M) ^ j : Kˣ) : K) = j := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, v_mul u.1.ne_zero (zpow_ne_zero _
      (Units.ne_zero _)), v_zpow (Units.ne_zero _), v_stdVarpi hM,
      (nrm_eq_one_iff_v_eq_zero u.1.ne_zero).1 u.2]
    ring
  have hup : unitPart hM ((u : Kˣ) * stdVarpi (p := p) (M := M) ^ j) = u := by
    ext
    rw [unitPart_apply, hv]
    group
  rw [rhoF_apply, hv, hup, hu]
  congr
  exact (MulEquiv.ofBijective _ (stdResM_bijective hM hU hdeg)).symm_apply_apply g

/-- The kernel of `ρ_F` consists of norms from `F`. -/
theorem mem_normGroup_of_rhoF_eq_one (x : Kˣ) (hx : rhoF hM hU hdeg s hs he x = 1) :
    x ∈ normGroup K F := by
  haveI := finiteDimensional_tower (p := p) K M
  haveI := finiteDimensional_tower (p := p) M F
  have h2 := congrArg (fun τ ↦ ((stdProd hM hU hdeg).symm τ)) hx
  simp only [rhoF_apply, MulEquiv.symm_apply_apply, map_one, Prod.ext_iff, Prod.fst_one,
    Prod.snd_one] at h2
  obtain ⟨hpsi, hφ⟩ := h2
  have hpsi' : psi hM hU hdeg s hs he (unitPart hM x) = 1 := by
    have := congrArg (MulEquiv.ofBijective _ (stdResM_bijective hM hU hdeg)) hpsi
    simpa using this
  -- `t ∣ v x`
  have ht : (Module.finrank K U : ℤ) ∣ v p (x : K) := by
    have hord : orderOf (stdFrob hM hU hdeg) = Module.finrank K U := by
      rw [stdFrob, orderOf_frob, std_finrank_M hM hU hdeg]
    rw [zpow_eq_one_iff_modEq, hord] at hφ
    have := Int.ModEq.dvd hφ.symm
    simpa using this
  obtain ⟨j, hj⟩ := ht
  -- the unit part is a norm from `M`
  obtain ⟨m, hm⟩ := mem_normGroup.1
    (mem_normGroup_of_psi_eq_one hM hU hdeg s hs he (unitPart hM x) hpsi')
  have hπ := uniformizer_spec (p := p) (K := M)
  set πM : Mˣ := Units.mk0 _ hπ.ne_zero
  -- `m π_M ^ (v x)` is a norm from `F`
  have hmv : (m * πM ^ v p (x : K) : Mˣ) ∈ normGroup M F := by
    rw [normGroup_of_isUnramified (std_isUnramified_top hM hU hdeg), mem_vDvd,
      std_finrank_M hM hU hdeg, Units.val_mul, Units.val_zpow_eq_zpow_val,
      v_mul m.ne_zero (zpow_ne_zero _ (Units.ne_zero _)), v_zpow (Units.ne_zero _)]
    have hm0 : v p (m : M) = 0 := by
      rw [← nrm_eq_one_iff_v_eq_zero m.ne_zero]
      refine nrm_eq_one_of_norm (L := K) ?_
      rw [hm]; exact (unitPart hM x).2
    rw [hm0, Units.val_mk0, hπ, mul_one, zero_add, hj]
    exact dvd_mul_right _ _
  rw [normGroup_tower (E := M)]
  refine ⟨_, hmv, ?_⟩
  have hm' : Units.map (Algebra.norm K : M →* K) m = (unitPart hM x : Kˣ) := Units.ext hm
  have hπv : Units.map (Algebra.norm K : M →* K) πM = stdVarpi (p := p) (K := K) (M := M) := rfl
  rw [map_mul, map_zpow, hm', hπv, unitPart_apply]
  group

end PadicField
