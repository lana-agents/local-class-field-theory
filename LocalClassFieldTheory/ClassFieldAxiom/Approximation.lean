/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.Complete

/-!
# Successive approximation in unit groups

Let `L` be a field finite over `ℚ_[p]` and `V : ℕ → Subgroup Lˣ` a decreasing filtration by
subgroups which shrink to `1` geometrically (`‖x - 1‖ ≤ r ^ (k + 1)` on `V k`) and each contain a
ball around `1`. If a group homomorphism `Φ : Lˣ →* Lˣ` preserves the filtration and, level by
level, every element of `V k ⊓ W` is a `Φ`-image modulo `V (k + 1)` (where `W ⊇ range Φ`), then
every element of `V 0 ⊓ W` is in `Φ (V 0)`. This is the completeness argument behind the
vanishing of Tate cohomology of the higher unit groups (Serre, *Local Fields*, V §2 / XII §2).
-/

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {L : Type*} [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

/-- Successive approximation for a homomorphism of unit groups. -/
theorem exists_eq_of_approx {V : ℕ → Subgroup Lˣ} {W : Subgroup Lˣ} {Φ : Lˣ →* Lˣ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < 1)
    (hanti : ∀ k, V (k + 1) ≤ V k)
    (hsmall : ∀ k, ∀ x ∈ V k, nrm p L ((x : L) - 1) ≤ r ^ (k + 1))
    (hball : ∀ k, ∃ m, ∀ x : Lˣ, nrm p L ((x : L) - 1) ≤ r ^ m → x ∈ V k)
    (hΦV : ∀ k, ∀ x ∈ V k, Φ x ∈ V k) (hΦW : ∀ x, Φ x ∈ W)
    (step : ∀ k, ∀ x ∈ V k, x ∈ W → ∃ y ∈ V k, x / Φ y ∈ V (k + 1)) :
    ∀ x ∈ V 0, x ∈ W → ∃ y ∈ V 0, Φ y = x := by
  classical
  intro x hx0 hxW
  have hmono : ∀ {j k}, j ≤ k → V k ≤ V j := by
    intro j k hjk
    induction k, hjk using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih => exact (hanti k).trans ih
  -- the correction terms
  let yf : ℕ → Lˣ → Lˣ := fun k z ↦
    if h : z ∈ V k ∧ z ∈ W then (step k z h.1 h.2).choose else 1
  have hyf : ∀ k z, z ∈ V k → z ∈ W → yf k z ∈ V k ∧ z / Φ (yf k z) ∈ V (k + 1) := by
    intro k z hz hzW
    simp only [yf, dif_pos (And.intro hz hzW)]
    exact (step k z hz hzW).choose_spec
  -- the remainders `xs k` and the corrections `ys k`
  let xs : ℕ → Lˣ := fun k ↦ Nat.rec x (fun k z ↦ z / Φ (yf k z)) k
  have hxs_succ : ∀ k, xs (k + 1) = xs k / Φ (yf k (xs k)) := fun k ↦ rfl
  have hxs : ∀ k, xs k ∈ V k ∧ xs k ∈ W := by
    intro k
    induction k with
    | zero => exact ⟨hx0, hxW⟩
    | succ k ih =>
      rw [hxs_succ]
      exact ⟨(hyf k _ ih.1 ih.2).2, W.div_mem ih.2 (hΦW _)⟩
  let ys : ℕ → Lˣ := fun k ↦ yf k (xs k)
  have hys : ∀ k, ys k ∈ V k := fun k ↦ (hyf k _ (hxs k).1 (hxs k).2).1
  -- partial products
  let P : ℕ → Lˣ := fun k ↦ ∏ i ∈ Finset.range k, ys i
  have hP0 : ∀ k, P k ∈ V 0 := fun k ↦
    Subgroup.prod_mem _ fun i _ ↦ hmono (Nat.zero_le i) (hys i)
  have hnrm1 : ∀ k, ∀ z ∈ V k, nrm p L (z : L) = 1 := by
    intro k z hz
    have h1 : nrm p L ((z : L) - 1) < 1 :=
      (hsmall k z hz).trans_lt (pow_lt_one₀ hr0 hr (Nat.succ_ne_zero k))
    have : (z : L) = 1 + ((z : L) - 1) := by ring
    rw [this, nrm_add_eq_left (by simpa using h1), nrm_one]
  have hxk : ∀ k, x = Φ (P k) * xs k := by
    intro k
    induction k with
    | zero => simp [P, xs]
    | succ k ih =>
      rw [ih]
      simp only [P, Finset.prod_range_succ, map_mul, hxs_succ, ys]
      rw [mul_assoc, mul_comm (Φ (yf _ _)), div_mul_cancel]
  have hstepP : ∀ k, nrm p L ((P (k + 1) : L) - P k) ≤ r ^ k := by
    intro k
    have : ((P (k + 1) : L) - P k) = (P k : L) * ((ys k : L) - 1) := by
      simp only [P, Finset.prod_range_succ, Units.val_mul]; ring
    rw [this, nrm_mul, hnrm1 0 _ (hP0 k), one_mul]
    exact (hsmall k _ (hys k)).trans (pow_le_pow_of_le_one hr0 hr.le (Nat.le_succ k))
  obtain ⟨Y, hY⟩ := exists_limit (x := fun k ↦ (P k : L)) hr0 hr hstepP
  -- `Y` is a unit
  have hY1 : nrm p L (Y - 1) < 1 := by
    have hP1 : (P 1 : L) = ys 0 := by simp [P]
    have : Y - 1 = (Y - P 1) + ((P 1 : L) - 1) := by ring
    rw [this]
    refine (nrm_add_le_max _ _).trans_lt (max_lt ((hY 1).trans_lt ?_) ?_)
    · simpa using hr
    · rw [hP1]; exact (hsmall 0 _ (hys 0)).trans_lt (by simpa using hr)
  have hYne : Y ≠ 0 := by
    rintro rfl
    simp at hY1
  set Yu : Lˣ := Units.mk0 Y hYne
  have hYP : ∀ k, nrm p L (((Yu / P k : Lˣ) : L) - 1) ≤ r ^ k := by
    intro k
    have hPk : (P k : L) ≠ 0 := (P k).ne_zero
    have : ((Yu / P k : Lˣ) : L) - 1 = (Y - P k) / P k := by
      simp only [Units.val_div_eq_div_val, Units.val_mk0, Yu]
      field_simp
    rw [this, nrm_div, hnrm1 0 _ (hP0 k), div_one]
    exact hY k
  have hYPV : ∀ j, ∃ k₀, ∀ k ≥ k₀, Yu / P k ∈ V j := by
    intro j
    obtain ⟨m, hm⟩ := hball j
    exact ⟨m, fun k hk ↦ hm _ ((hYP k).trans (pow_le_pow_of_le_one hr0 hr.le hk))⟩
  have hYV : Yu ∈ V 0 := by
    obtain ⟨k₀, hk₀⟩ := hYPV 0
    have : Yu = P k₀ * (Yu / P k₀) := (mul_div_cancel _ _).symm
    rw [this]
    exact mul_mem (hP0 k₀) (hk₀ k₀ le_rfl)
  refine ⟨Yu, hYV, ?_⟩
  -- `Φ Yu / x` is in every `V j`, hence equals `1`
  have hall : ∀ j, Φ Yu / x ∈ V j := by
    intro j
    obtain ⟨k₀, hk₀⟩ := hYPV j
    set k := max k₀ j
    have h1 : Φ Yu / x = Φ (Yu / P k) / xs k := by
      rw [hxk k, map_div, div_mul_eq_div_div]
    rw [h1]
    exact div_mem (hΦV j _ (hk₀ k (le_max_left _ _)))
      (hmono (le_max_right _ _) (hxs k).1)
  have hz : ((Φ Yu / x : Lˣ) : L) = 1 := by
    by_contra hne
    have hpos : 0 < nrm p L (((Φ Yu / x : Lˣ) : L) - 1) := nrm_pos_iff.2 (sub_ne_zero.2 hne)
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hpos hr
    have := hsmall j _ (hall j)
    have hle : r ^ (j + 1) ≤ r ^ j := pow_le_pow_of_le_one hr0 hr.le (Nat.le_succ j)
    linarith
  have : Φ Yu / x = 1 := Units.ext hz
  exact div_eq_one.1 this

end PadicField
