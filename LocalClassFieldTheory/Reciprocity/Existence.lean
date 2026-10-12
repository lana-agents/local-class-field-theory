/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.ArtinContinuous

/-!
# Towards the existence theorem: formal properties of norm groups

* `PadicField.exists_normGroup_eq_of_le`: subgroups of `Kˣ` containing a norm group
  `N_{L/K} Lˣ` (`L/K` finite abelian) are norm groups of subextensions of `L`;
* `PadicField.normGroup_sup`: `N_{L₁ L₂} = N_{L₁} ∩ N_{L₂}`;
* `PadicField.pow_mem_of_index_ne_zero`, `PadicField.isOpen_of_index_ne_zero`: subgroups of finite
  index contain all `n`-th powers (`n` the index) and hence a neighbourhood of `1`;
* `PadicField.existence_of_pow`: the existence theorem reduces to showing that every `(Kˣ)^n`
  contains a norm group.
-/

set_option linter.unusedSectionVars false

open IntermediateField
open scoped IsMulCommutative

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

include hp in
/-- **Upward closure of norm groups**: a subgroup containing `N_{L/K} Lˣ` is the norm group of
the fixed field of its image under the reciprocity map. -/
theorem exists_normGroup_eq_of_le (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] (N : Subgroup Kˣ) (hN : normGroup K L ≤ N) :
    ∃ L' : AbFin K Ω, L'.1 ≤ L ∧ normGroup K L'.1 = N := by
  set H := N.map (abRec p L)
  set L' := lift (fixedField H)
  let ε : fixedField H ≃ₐ[K] L' := liftAlgEquiv _
  haveI : FiniteDimensional K L' := LinearEquiv.finiteDimensional ε.toLinearEquiv
  haveI : IsAbelianGalois K L' := .of_algHom ε.symm.toAlgHom
  have hL'L : L' ≤ L := lift_le _
  refine ⟨⟨L', inferInstance, inferInstance⟩, hL'L, ?_⟩
  change normGroup K L' = N
  rw [← ker_abRec (p := p) L']
  ext x
  rw [MonoidHom.mem_ker, ← resHom_abRec_of_le L L' hL'L]
  have hfix : resHom hL'L (abRec p L x) = 1 ↔ abRec p L x ∈ H := by
    rw [← fixingSubgroup_fixedField H, IntermediateField.mem_fixingSubgroup_iff, resHom_eq_iff]
    constructor
    · intro h y hy
      have := h ⟨y, (mem_lift y).2 hy⟩
      rw [AlgEquiv.one_apply] at this
      exact Subtype.ext this
    · intro h y
      rw [AlgEquiv.one_apply]
      exact congrArg Subtype.val (h _ ((mem_lift (inclusion hL'L y)).1 y.2))
  rw [hfix]
  constructor
  · rintro ⟨n, hn, hnx⟩
    have hker : x * n⁻¹ ∈ normGroup K L := by
      rw [← ker_abRec (p := p) L, MonoidHom.mem_ker, map_mul, map_inv, hnx, mul_inv_cancel]
    have := mul_mem (hN hker) hn
    rwa [inv_mul_cancel_right] at this
  · intro hx
    exact ⟨x, hx, rfl⟩

include hp in
/-- `N_{L₁ L₂} = N_{L₁} ∩ N_{L₂}` for finite abelian `L₁, L₂`. -/
theorem normGroup_sup (L₁ L₂ : IntermediateField K Ω) [FiniteDimensional K L₁]
    [FiniteDimensional K L₂] [IsAbelianGalois K L₁] [IsAbelianGalois K L₂] :
    haveI := isAbelianGalois_sup L₁ L₂
    normGroup K (L₁ ⊔ L₂ : IntermediateField K Ω) = normGroup K L₁ ⊓ normGroup K L₂ := by
  haveI := isAbelianGalois_sup L₁ L₂
  ext x
  rw [Subgroup.mem_inf, ← ker_abRec (p := p), ← ker_abRec (p := p) L₁, ← ker_abRec (p := p) L₂,
    MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.mem_ker,
    ← resHom_abRec_of_le (L₁ ⊔ L₂ : IntermediateField K Ω) L₁ le_sup_left,
    ← resHom_abRec_of_le (L₁ ⊔ L₂ : IntermediateField K Ω) L₂ le_sup_right]
  constructor
  · intro h; rw [h, map_one, map_one]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact eq_one_of_resHom_eq_one rfl le_sup_left le_sup_right _ h1 h2

/-- A subgroup of finite index `n` contains all `n`-th powers. -/
theorem pow_mem_of_index_ne_zero (N : Subgroup Kˣ) (x : Kˣ) : x ^ N.index ∈ N := by
  haveI : N.Normal := ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩
  exact N.pow_index_mem x

include hp in
/-- Subgroups of finite index contain a neighbourhood `{u | ‖u - 1‖ < r}` of `1`. -/
theorem exists_nrm_sub_one_lt_mem (N : Subgroup Kˣ) (hN : N.index ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ u : Kˣ, nrm p K ((u : K) - 1) < r → u ∈ N := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  set n := N.index
  have hn : 0 < n := Nat.pos_of_ne_zero hN
  refine ⟨nrm p K ((n * (n * p) : ℕ) : K), nrm_pos_iff.2 (Nat.cast_ne_zero.2
    (Nat.mul_pos hn (Nat.mul_pos hn hp.out.pos)).ne'), fun u hu ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_pow_eq_of_nrm_sub_one_lt (p := p) n hn (u : K) hu
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [zero_pow hn.ne'] at hx; exact u.ne_zero hx.symm
  have : u = Units.mk0 x hx0 ^ n := Units.ext (by simp [hx])
  rw [this]
  exact pow_mem_of_index_ne_zero N _

include hp in
/-- **Reduction of the existence theorem**: if every subgroup `(Kˣ)^n` (`n ≥ 1`) contains the
norm group of a finite abelian extension, then every subgroup of finite index is a norm group. -/
theorem existence_of_pow
    (h : ∀ n : ℕ, 0 < n → ∃ L : AbFin K Ω, ∀ x ∈ normGroup K L.1, ∃ y : Kˣ, y ^ n = x)
    (N : Subgroup Kˣ) (hN : N.index ≠ 0) : ∃ L : AbFin K Ω, normGroup K L.1 = N := by
  obtain ⟨L, hL⟩ := h N.index (Nat.pos_of_ne_zero hN)
  obtain ⟨L', -, hL'⟩ := exists_normGroup_eq_of_le (p := p) L.1 N fun x hx ↦ by
    obtain ⟨y, rfl⟩ := hL x hx
    exact pow_mem_of_index_ne_zero N y
  exact ⟨L', hL'⟩

end PadicField
