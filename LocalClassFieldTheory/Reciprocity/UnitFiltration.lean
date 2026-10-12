/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.ArtinInertia

/-!
# The unit filtration and conductors

* `PadicField.unitFiltration p K n = U^(n)`: the units `x` with `‖x‖ = 1` and `‖x - 1‖ ≤ ‖π‖ⁿ`,
  i.e. `U^(0) = 𝒪ˣ` (`PadicField.unitFiltration_zero`) and `U^(n) = 1 + 𝔪ⁿ` for `n ≥ 1`; it is
  antitone with trivial intersection (`PadicField.iInf_unitFiltration`).
* `PadicField.exists_unitFiltration_le`: every finite-index subgroup of `Kˣ` contains some
  `U^(n)`; in particular (**existence of the conductor**) every norm group of a finite abelian
  `L ⊆ Ω` does (`PadicField.exists_unitFiltration_le_normGroup`), i.e. `artin(U^(n))` fixes `L`
  for `n` large (`PadicField.exists_unitFiltration_artin`).
-/

set_option linter.unusedSectionVars false

open IntermediateField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

theorem nrm_uniformizer_lt_one : nrm p K (uniformizer p K) < 1 :=
  (nrm_lt_one_iff_v_pos (uniformizer_spec (p := p) (K := K)).ne_zero).2
    ((uniformizer_spec (p := p) (K := K)).symm ▸ one_pos)

theorem nrm_uniformizer_pos : 0 < nrm p K (uniformizer p K) :=
  nrm_pos_iff.2 (uniformizer_spec (p := p) (K := K)).ne_zero

variable (p K) in
/-- The unit filtration `U^(n) = {x : ‖x‖ = 1, ‖x - 1‖ ≤ ‖π‖ⁿ}` (`U^(0) = 𝒪ˣ`,
`U^(n) = 1 + 𝔪ⁿ` for `n ≥ 1`). -/
noncomputable def unitFiltration (n : ℕ) : Subgroup Kˣ where
  carrier := {x | nrm p K (x : K) = 1 ∧ nrm p K ((x : K) - 1) ≤ nrm p K (uniformizer p K) ^ n}
  one_mem' := ⟨by rw [Units.val_one, nrm_one], by
    rw [Units.val_one, sub_self, nrm_eq_zero_iff.2 rfl]
    exact pow_nonneg (nrm_nonneg _) n⟩
  mul_mem' {a b} ha hb := by
    refine ⟨by rw [Units.val_mul, nrm_mul, ha.1, hb.1, one_mul], ?_⟩
    have h : ((a * b : Kˣ) : K) - 1 = (a : K) * ((b : K) - 1) + ((a : K) - 1) := by
      rw [Units.val_mul]; ring
    rw [h]
    refine (nrm_add_le_max _ _).trans (max_le ?_ ha.2)
    rw [nrm_mul, ha.1, one_mul]
    exact hb.2
  inv_mem' {a} ha := by
    have ha0 : (a : K) ≠ 0 := a.ne_zero
    refine ⟨by rw [Units.val_inv_eq_inv_val, nrm_inv, ha.1, inv_one], ?_⟩
    have h : ((a⁻¹ : Kˣ) : K) - 1 = -((a : K) - 1) / a := by
      rw [Units.val_inv_eq_inv_val]; field_simp; ring
    rw [h, nrm_div, nrm_neg, ha.1, div_one]
    exact ha.2

theorem mem_unitFiltration {n : ℕ} {x : Kˣ} :
    x ∈ unitFiltration p K n ↔
      nrm p K (x : K) = 1 ∧ nrm p K ((x : K) - 1) ≤ nrm p K (uniformizer p K) ^ n :=
  Iff.rfl

/-- `U^(0) = 𝒪ˣ`. -/
theorem unitFiltration_zero : unitFiltration p K 0 = unitGroup p K := by
  ext x
  rw [mem_unitFiltration, mem_unitGroup, pow_zero]
  refine ⟨And.left, fun h ↦ ⟨h, ?_⟩⟩
  rw [sub_eq_add_neg]
  refine (nrm_add_le_max _ _).trans (max_le h.le ?_)
  rw [nrm_neg, nrm_one]

theorem unitFiltration_le_unitGroup (n : ℕ) : unitFiltration p K n ≤ unitGroup p K :=
  fun _ hx ↦ hx.1

theorem unitFiltration_antitone : Antitone (unitFiltration p K) := by
  intro m n hmn x hx
  exact ⟨hx.1, hx.2.trans (pow_le_pow_of_le_one (nrm_nonneg _) nrm_uniformizer_lt_one.le hmn)⟩

/-- The unit filtration has trivial intersection. -/
theorem iInf_unitFiltration : ⨅ n, unitFiltration p K n = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_iInf] at hx
  rw [Subgroup.mem_bot]
  have h0 : nrm p K ((x : K) - 1) ≤ 0 :=
    ge_of_tendsto (tendsto_pow_atTop_nhds_zero_of_lt_one (nrm_nonneg _) nrm_uniformizer_lt_one)
      (Filter.Eventually.of_forall fun n ↦ (hx n).2)
  have h1 : (x : K) - 1 = 0 := nrm_eq_zero_iff.1 (le_antisymm h0 (nrm_nonneg _))
  exact Units.ext (sub_eq_zero.1 h1)

include hp in
/-- Every finite-index subgroup of `Kˣ` contains some `U^(n)`. -/
theorem exists_unitFiltration_le (N : Subgroup Kˣ) (hN : N.index ≠ 0) :
    ∃ n, unitFiltration p K n ≤ N := by
  obtain ⟨r, hr, hrN⟩ := exists_nrm_sub_one_lt_mem (p := p) N hN
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (nrm_uniformizer_lt_one (p := p) (K := K))
  exact ⟨n, fun x hx ↦ hrN x (hx.2.trans_lt hn)⟩

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

include hp in
/-- **Existence of the conductor**: the norm group of a finite abelian `L ⊆ Ω` contains some
`U^(n)`. -/
theorem exists_unitFiltration_le_normGroup (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] : ∃ n, unitFiltration p K n ≤ normGroup K L := by
  refine exists_unitFiltration_le (p := p) _ ?_
  rw [index_normGroup_eq_finrank (p := p)]
  exact Module.finrank_pos.ne'

include hp in
/-- For every finite abelian `L ⊆ Ω`, the Artin map is trivial on `L` on `U^(n)` for `n` large. -/
theorem exists_unitFiltration_artin (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] : ∃ n, ∀ u ∈ unitFiltration p K n, ∀ y : maxAbelian K Ω,
      (y : Ω) ∈ L → artin p K Ω u y = y := by
  obtain ⟨n, hn⟩ := exists_unitFiltration_le_normGroup (p := p) (Ω := Ω) L
  exact ⟨n, fun u hu ↦ (artin_apply_eq_self_iff (p := p) u L).2 (hn hu)⟩

end PadicField
