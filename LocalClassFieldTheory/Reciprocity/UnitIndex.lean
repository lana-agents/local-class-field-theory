/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.Standard

/-!
# Unit norms in totally ramified and standard extensions

* `PadicField.relIndex_unitNorms`: for a cyclic totally ramified `M/K`,
  `[𝒪ˣ_K : N(𝒪ˣ_M)] = [M : K]` (from the class field axiom).
* `PadicField.std_exists_norm_eq` (vanishing at an unramified level): in a standard extension
  `F = M U` with `[M : K] ∣ [U : K]`, every unit of `K` is the norm `N_{F/U}` of a unit of `F`.
-/

set_option linter.unusedSectionVars false

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]

section TotRam

variable {K M : Type*} [Field K] [Field M] [Algebra ℚ_[p] K] [Algebra ℚ_[p] M]
  [Algebra K M] [IsScalarTower ℚ_[p] K M] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] M]

/-- The norm group of a totally ramified extension contains a uniformiser. -/
theorem exists_uniformizer_mem_normGroup [FiniteDimensional K M] (hM : e p K M = Module.finrank K M) :
    ∃ ϖ : Kˣ, v p (ϖ : K) = 1 ∧ ϖ ∈ normGroup K M := by
  have hπ := uniformizer_spec (p := p) (K := M)
  set π : Mˣ := Units.mk0 _ hπ.ne_zero
  refine ⟨Units.map (Algebra.norm K : M →* K) π, ?_, π, rfl⟩
  have hf : f p K M = 1 := by
    have := e_mul_f (p := p) (K := K) (L := M)
    rw [hM] at this
    exact (Nat.mul_eq_left Module.finrank_pos.ne').1 this
  change v p (Algebra.norm K (uniformizer p M)) = 1
  rw [v_norm hπ.ne_zero, hf, hπ]; rfl

theorem unitGroup_sup_normGroup [FiniteDimensional K M] (hM : e p K M = Module.finrank K M) :
    unitGroup p K ⊔ normGroup K M = ⊤ := by
  obtain ⟨ϖ, hϖ, hmem⟩ := exists_uniformizer_mem_normGroup (p := p) hM
  refine eq_top_iff.2 fun x _ ↦ ?_
  have hx : x = (x * ϖ ^ (-v p (x : K))) * ϖ ^ (v p (x : K)) := by group
  rw [hx]
  refine Subgroup.mul_mem_sup ?_ (Subgroup.zpow_mem _ hmem _)
  rw [mem_unitGroup, Units.val_mul, nrm_mul, Units.val_zpow_eq_zpow_val, nrm_zpow,
    nrm_eq_nrm_uniformizer_zpow (π := (ϖ : K)) hϖ ϖ.ne_zero, hϖ, zpow_one,
    nrm_eq_nrm_uniformizer_zpow hϖ x.ne_zero, ← zpow_add₀ (nrm_pos_iff.2 ϖ.ne_zero).ne']
  simp

/-- `[𝒪ˣ_K : N(Mˣ) ∩ 𝒪ˣ_K] = [M : K]` for a cyclic totally ramified `M/K`. -/
theorem relIndex_unitNorms [FiniteDimensional K M] [IsGalois K M] [IsCyclic (M ≃ₐ[K] M)]
    (hM : e p K M = Module.finrank K M) :
    (normGroup K M ⊓ unitGroup p K).relIndex (unitGroup p K) = Module.finrank K M := by
  rw [Subgroup.inf_relIndex_right, ← Subgroup.relIndex_sup_right,
    unitGroup_sup_normGroup hM, Subgroup.relIndex_top_right,
    index_normGroup_of_isCyclic (p := p)]

end TotRam


theorem nrm_eq_one_of_norm {L L' : Type*} [Field L] [Field L'] [Algebra ℚ_[p] L]
    [Algebra ℚ_[p] L'] [Algebra L L'] [IsScalarTower ℚ_[p] L L'] [FiniteDimensional ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L'] {y : L'} (h : nrm p L (Algebra.norm L y) = 1) :
    nrm p L' y = 1 := by
  haveI := finiteDimensional_tower (p := p) L L'
  rw [nrm_norm] at h
  exact (pow_eq_one_iff_of_nonneg (nrm_nonneg y) Module.finrank_pos.ne').1 h

section Std

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

theorem std_isCyclic_U : IsCyclic (F ≃ₐ[U] F) :=
  isCyclic_of_surjective (MulEquiv.ofBijective _ (stdResM_bijective hM hU hdeg)).symm.toMonoidHom
    (MulEquiv.ofBijective _ (stdResM_bijective hM hU hdeg)).symm.surjective

/-- **Vanishing at an unramified level**: if `[M : K] ∣ [U : K]`, every unit of `K` is the norm
of a unit of `F` down to `U`. -/
theorem std_exists_norm_eq (he : Module.finrank K M ∣ Module.finrank K U) (u : Kˣ)
    (hu : nrm p K (u : K) = 1) :
    ∃ η : Fˣ, nrm p F (η : F) = 1 ∧ Algebra.norm U (η : F) = algebraMap K U u := by
  haveI := finiteDimensional_tower (p := p) K M
  haveI := finiteDimensional_tower (p := p) K U
  haveI := finiteDimensional_tower (p := p) U F
  haveI := finiteDimensional_tower (p := p) M F
  haveI : IsGalois U F := IsGalois.tower_top_of_isGalois K U F
  haveI := std_isCyclic_U hM hU hdeg
  let AK := unitGroup p K
  let BK := normGroup K M ⊓ unitGroup p K
  let AU := unitGroup p U
  let BU := normGroup U F ⊓ unitGroup p U
  have hBK : (BK.subgroupOf AK).index = Module.finrank K M := relIndex_unitNorms hM
  have hBU : (BU.subgroupOf AU).index = Module.finrank K M := by
    rw [← std_finrank_U hM hU hdeg]
    exact relIndex_unitNorms (std_e_U hM hU hdeg)
  -- the norm map on units
  let nmap : AU →* AK := {
    toFun := fun w ↦ ⟨Units.map (Algebra.norm K : U →* K) (w : Uˣ), by
      change nrm p K (Algebra.norm K ((w : Uˣ) : U)) = 1
      rw [nrm_norm, (mem_unitGroup.1 w.2), one_pow]⟩
    map_one' := by ext; simp
    map_mul' := fun a b ↦ by ext; simp }
  let n : AU →* AK ⧸ BK.subgroupOf AK := (QuotientGroup.mk' _).comp nmap
  have hnsurj : Function.Surjective n := by
    intro z
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ z
    obtain ⟨y, hy1, hy⟩ := exists_norm_eq_of_isUnramified hU (a : Kˣ) (mem_unitGroup.1 a.2)
    refine ⟨⟨y, hy1⟩, ?_⟩
    simp only [n, MonoidHom.comp_apply]
    congr 1
    ext
    exact hy
  have hle : BU.subgroupOf AU ≤ n.ker := by
    rintro ⟨w, hwU⟩ hw
    obtain ⟨⟨y, hy⟩, -⟩ := hw
    rw [MonoidHom.mem_ker]
    simp only [n, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨⟨Units.map (Algebra.norm M : F →* M) y, Units.ext ?_⟩, ?_⟩
    · change Algebra.norm K (Algebra.norm M (y : F)) = Algebra.norm K ((w : Uˣ) : U)
      have hy' : Algebra.norm U (y : F) = ((w : Uˣ) : U) := congrArg Units.val hy
      rw [Algebra.norm_norm, ← hy', Algebra.norm_norm]
    · exact (nmap ⟨w, hwU⟩).2
  have hker : n.ker = BU.subgroupOf AU := by
    have hidx : n.ker.index = Module.finrank K M := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hnsurj, Subgroup.card_top, ← hBK]
      rfl
    have h1 := Subgroup.relIndex_mul_index hle
    rw [hidx, hBU] at h1
    have : (BU.subgroupOf AU).relIndex n.ker = 1 :=
      Nat.eq_of_mul_eq_mul_right Module.finrank_pos (h1.trans (one_mul _).symm)
    exact le_antisymm (Subgroup.relIndex_eq_one.1 this) hle
  -- the image of `u`
  let uU : AU := ⟨Units.map (algebraMap K U : K →* U) u, by
    rw [mem_unitGroup]; change nrm p U (algebraMap K U u) = 1
    rw [nrm_algebraMap_tower]; exact hu⟩
  have hmem : uU ∈ n.ker := by
    rw [MonoidHom.mem_ker]
    have h1 : n uU = (QuotientGroup.mk' _ ⟨u, hu⟩ : AK ⧸ BK.subgroupOf AK) ^
        Module.finrank K U := by
      rw [← map_pow]
      simp only [n, MonoidHom.comp_apply]
      congr 1
      ext
      change Algebra.norm K (algebraMap K U u) = _
      rw [Algebra.norm_algebraMap]
      rfl
    rw [h1]
    obtain ⟨c, hc⟩ := he
    have hcard : Nat.card (AK ⧸ BK.subgroupOf AK) = Module.finrank K M := hBK
    rw [hc, pow_mul, ← hcard, pow_card_eq_one', one_pow]
  have hmem' : (uU : Uˣ) ∈ normGroup U F := by
    rw [hker] at hmem
    exact (Subgroup.mem_subgroupOf.1 hmem).1
  obtain ⟨η, hη⟩ := mem_normGroup.1 hmem'
  have hη' : Algebra.norm U (η : F) = algebraMap K U u := hη
  have hu' : nrm p U (algebraMap K U u) = 1 := by rw [nrm_algebraMap_tower]; exact hu
  exact ⟨η, nrm_eq_one_of_norm (L := U) (by rw [hη']; exact hu'), hη'⟩

end Std

end PadicField
