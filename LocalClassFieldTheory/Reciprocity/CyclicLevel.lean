/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.Neukirch

/-!
# Reciprocity for cyclic subextensions of a standard level

Let `F = M U` be a standard extension, `N ≥ 1` such that `[M:K] k ∣ [U:K]` for all
`1 ≤ k ≤ N`, and `E = M K_N ⊆ F` the fixed field of `(1, φ^N)`. For every cyclic `L/K` with
`L ⊆ E`, the preimage under `ρ_F` of `Gal(F/L)` is exactly `N_{L/K} Lˣ`
(`PadicField.comap_rhoF_fixingSubgroup`). Consequently `ρ_F` induces
`Kˣ / N_{L/K} Lˣ ≃ Gal(L/K)`.
-/

set_option linter.unusedSectionVars false

open IntermediateField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]

section Mono

variable {K F : Type*} [Field K] [Field F] [Algebra ℚ_[p] K] [Algebra ℚ_[p] F]
  [Algebra K F] [IsScalarTower ℚ_[p] K F] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] F]

include hp in
/-- Norm groups shrink in towers (for intermediate fields). -/
theorem normGroup_le_of_le {L L' : IntermediateField K F} (h : L ≤ L') :
    normGroup K L' ≤ normGroup K L := by
  letI : Algebra L L' := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower ℚ_[p] L L' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := finiteDimensional_tower (p := p) K L
  haveI := finiteDimensional_tower (p := p) L L'
  rw [normGroup_tower (E := L)]
  rintro _ ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

include hp in
/-- Norms from `F` are norms from any intermediate field. -/
theorem normGroup_top_le (L : IntermediateField K F) : normGroup K F ≤ normGroup K L := by
  haveI := finiteDimensional_tower (p := p) K L
  haveI := finiteDimensional_tower (p := p) L F
  rw [normGroup_tower (E := L)]
  rintro _ ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

end Mono

variable {K M U F : Type*} [Field K] [Field M] [Field U] [Field F]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] M] [Algebra ℚ_[p] U] [Algebra ℚ_[p] F]
  [Algebra K M] [Algebra K U] [Algebra K F] [Algebra M F] [Algebra U F]
  [IsScalarTower ℚ_[p] K M] [IsScalarTower ℚ_[p] K U] [IsScalarTower ℚ_[p] K F]
  [IsScalarTower ℚ_[p] M F] [IsScalarTower ℚ_[p] U F]
  [IsScalarTower K M F] [IsScalarTower K U F]
  [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] M] [FiniteDimensional ℚ_[p] U]
  [FiniteDimensional ℚ_[p] F] [IsGalois K F] [IsGalois K M] [IsCyclic (M ≃ₐ[K] M)]
  [FiniteDimensional U F]

variable (hM : e p K M = Module.finrank K M) (hU : IsUnramified p K U)
  (hdeg : Module.finrank K F = Module.finrank K M * Module.finrank K U)
  (s : M ≃ₐ[K] M) (hs : ∀ g, g ∈ Subgroup.zpowers s)
  (he : Module.finrank K M ∣ Module.finrank K U)
include hM hU hdeg

theorem rhoF_stdVarpi :
    rhoF hM hU hdeg s hs he (stdVarpi (p := p) (K := K) (M := M)) =
      tau hM hU hdeg 1 1 := by
  have hup : unitPart hM (stdVarpi (p := p) (K := K) (M := M)) = 1 := by
    ext
    rw [unitPart_apply, v_stdVarpi hM]
    simp
  rw [rhoF_apply, hup, map_one, v_stdVarpi hM, tau]
  congr 2
  exact (MulEquiv.ofBijective _ (stdResM_bijective hM hU hdeg)).symm.map_one

variable (N : ℕ) (hN0 : 0 < N)
  (hNt : ∀ k, 0 < k → k ≤ N → Module.finrank K M * k ∣ Module.finrank K U)
include hN0 hNt

/-- `ϖ ^ N` is a norm from `E = M K_N`. -/
theorem stdVarpi_pow_mem_normGroup :
    stdVarpi (p := p) (K := K) (M := M) ^ N ∈
      normGroup K (fixedField (Subgroup.zpowers (tau hM hU hdeg 1 N))) := by
  have hπ := uniformizer_spec (p := p) (K := M)
  set E := fixedField (Subgroup.zpowers (tau hM hU hdeg 1 N))
  have hmem : algebraMap M F (uniformizer p M) ∈ E := by
    rintro ⟨_, j, rfl⟩
    change (tau hM hU hdeg 1 N ^ j) (algebraMap M F (uniformizer p M)) = _
    refine zpow_apply_eq_of_apply_eq ?_ j
    rw [tau, stdProd_apply, AlgEquiv.commutes, AlgEquiv.one_apply]
  set y : E := ⟨_, hmem⟩
  have hy0 : y ≠ 0 := fun h ↦ hπ.ne_zero
    ((map_eq_zero_iff _ (algebraMap M F).injective).1 (congrArg Subtype.val h))
  refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
  apply (algebraMap K F).injective
  change algebraMap K F (Algebra.norm K y) = _
  rw [algebraMap_norm_tau hM hU hdeg 1 N hN0 (hNt N hN0 le_rfl) y]
  have hNU : algebraMap U F (Algebra.norm U (y : F)) =
      algebraMap K F (stdVarpi (p := p) (K := K) (M := M) : K) := by
    change algebraMap U F (Algebra.norm U (algebraMap M F (uniformizer p M))) = _
    rw [std_norm_M hM hU hdeg, ← IsScalarTower.algebraMap_apply]
    rfl
  rw [hNU]
  have hfix : ∀ j : ℕ, (stdFrob hM hU hdeg ^ j)
      (algebraMap K F (stdVarpi (p := p) (K := K) (M := M) : K)) =
      algebraMap K F (stdVarpi (p := p) (K := K) (M := M) : K) := fun j ↦ by
    rw [IsScalarTower.algebraMap_apply K M F]; exact AlgEquiv.commutes _ _
  simp_rw [hfix]
  rw [Finset.prod_const, Finset.card_range, Units.val_pow_eq_pow_val, map_pow]


omit hN0 hNt in
theorem tau_one_pow (n : ℕ) : tau hM hU hdeg 1 1 ^ n = tau hM hU hdeg 1 n := by
  rw [tau, tau, ← map_pow, Prod.pow_mk, one_pow, pow_one]

/-- **Reciprocity for a cyclic subextension of a standard level**: `ρ_F⁻¹(Gal(F/L)) = N Lˣ`. -/
theorem comap_rhoF_fixingSubgroup (L : IntermediateField K F)
    (hLE : L ≤ fixedField (Subgroup.zpowers (tau hM hU hdeg 1 N)))
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    L.fixingSubgroup.comap (rhoF hM hU hdeg s hs he) = normGroup K L := by
  haveI := finiteDimensional_tower (p := p) K F
  set E := fixedField (Subgroup.zpowers (tau hM hU hdeg 1 N))
  set ϖ := stdVarpi (p := p) (K := K) (M := M)
  have hϖN : ϖ ^ N ∈ normGroup K L :=
    normGroup_le_of_le (p := p) hLE (stdVarpi_pow_mem_normGroup hM hU hdeg N hN0 hNt)
  have hρϖN : rhoF hM hU hdeg s hs he (ϖ ^ N) ∈ L.fixingSubgroup := by
    rw [map_pow, rhoF_stdVarpi, tau_one_pow]
    refine fixingSubgroup_antitone hLE ?_
    exact (le_iff_le (K := E) (H := Subgroup.zpowers (tau hM hU hdeg 1 N))).1 le_rfl
      (Subgroup.mem_zpowers _)
  have hle : L.fixingSubgroup.comap (rhoF hM hU hdeg s hs he) ≤ normGroup K L := by
    intro x hx
    rw [Subgroup.mem_comap] at hx
    -- normalise the valuation into `[1, N]`
    set a := v p (x : K)
    set r : ℤ := (a - 1) % N + 1
    have hN' : (0 : ℤ) < N := by exact_mod_cast hN0
    have hr1 : 1 ≤ r := by have := Int.emod_nonneg (a - 1) hN'.ne'; omega
    have hrN : r ≤ N := by have := Int.emod_lt_of_pos (a - 1) hN'; omega
    set q : ℤ := (a - 1) / N
    have hqr : a = N * q + r := by
      have h := Int.emod_def (a - 1) N
      show a = N * ((a - 1) / N) + ((a - 1) % N + 1)
      linarith
    set x' := x * (ϖ ^ N) ^ (-q)
    have hvx' : v p (x' : K) = r := by
      simp only [x', Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val]
      rw [v_mul x.ne_zero (zpow_ne_zero _ (pow_ne_zero _ (Units.ne_zero _))),
        v_zpow (pow_ne_zero _ (Units.ne_zero _)), v_pow (Units.ne_zero _), v_stdVarpi hM]
      have ha : a = v p (x : K) := rfl
      linarith
    have hx'L : rhoF hM hU hdeg s hs he x' ∈ L.fixingSubgroup := by
      simp only [x', map_mul, map_zpow]
      exact mul_mem hx (zpow_mem hρϖN _)
    -- `ρ_F x' = τ = (g, φ^k)`
    set k : ℕ := r.toNat
    have hk : 0 < k := by omega
    have hkN : k ≤ N := by omega
    have hkr : (k : ℤ) = r := Int.toNat_of_nonneg (by omega)
    set g := (MulEquiv.ofBijective _ (stdResM_bijective hM hU hdeg)).symm
      (psi hM hU hdeg s hs he (unitPart hM x'))
    have hτ : rhoF hM hU hdeg s hs he x' = tau hM hU hdeg g k := by
      rw [rhoF_apply, hvx', ← hkr, zpow_natCast]
      rfl
    obtain ⟨y, hy⟩ := exists_v_eq_one_tau hM hU hdeg g k hk (hNt k hk hkN)
    have hy0 : Algebra.norm K y ≠ 0 := by
      refine Algebra.norm_ne_zero_iff.2 fun h ↦ ?_
      rw [h, ZeroMemClass.coe_zero] at hy
      simp [v, wval] at hy
    have hN := rhoF_norm_tau hM hU hdeg g k hk (hNt k hk hkN) s hs he y hy hy0
    -- `L ⊆ Σ`
    have hLS : L ≤ fixedField (Subgroup.zpowers (tau hM hU hdeg g k)) := by
      rw [le_iff_le, Subgroup.zpowers_le, ← hτ]
      exact hx'L
    have hNy : Units.mk0 _ hy0 ∈ normGroup K L :=
      normGroup_le_of_le (p := p) hLS ⟨Units.mk0 y (fun h ↦ hy0 (Algebra.norm_eq_zero_iff.2 h)), Units.ext rfl⟩
    have hker : x' * (Units.mk0 _ hy0)⁻¹ ∈ normGroup K L := by
      apply normGroup_top_le (p := p) L
      apply mem_normGroup_of_rhoF_eq_one hM hU hdeg s hs he
      rw [map_mul, map_inv, hN, hτ, mul_inv_cancel]
    have hx' : x' ∈ normGroup K L := by
      have := mul_mem hker hNy
      rwa [inv_mul_cancel_right] at this
    have : x = x' * (ϖ ^ N) ^ q := by simp [x']
    rw [this]
    exact mul_mem hx' (zpow_mem hϖN _)
  -- indices
  have hidx1 : (L.fixingSubgroup.comap (rhoF hM hU hdeg s hs he)).index = Module.finrank K L := by
    rw [Subgroup.index_comap_of_surjective _ (rhoF_surjective hM hU hdeg s hs he)]
    have h1 := Subgroup.index_mul_card L.fixingSubgroup
    rw [IsGalois.card_fixingSubgroup_eq_finrank, IsGalois.card_aut_eq_finrank,
      ← Module.finrank_mul_finrank K L F] at h1
    exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1
  have hidx2 : (normGroup K L).index = Module.finrank K L :=
    index_normGroup_of_isCyclic (p := p)
  have h1 := Subgroup.relIndex_mul_index hle
  rw [hidx1, hidx2] at h1
  have : (L.fixingSubgroup.comap (rhoF hM hU hdeg s hs he)).relIndex (normGroup K L) = 1 :=
    Nat.eq_of_mul_eq_mul_right Module.finrank_pos (h1.trans (one_mul _).symm)
  exact le_antisymm hle (Subgroup.relIndex_eq_one.1 this)

end PadicField
