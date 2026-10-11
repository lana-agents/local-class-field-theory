/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.Uniformizer

/-!
# Completeness and Hensel's lemma

A field `K` finite over `ℚ_[p]` is complete for its absolute value (it is finite dimensional over
the complete field `ℚ_[p]`). We record this in the elementary form needed later
(`PadicField.exists_limit`: geometrically convergent sequences have limits), and deduce that
`𝒪 p K` is `𝔪`-adically complete, hence Henselian (`PadicField.Integers.henselianLocalRing`).
-/

open Polynomial IsLocalRing

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

theorem nrm_sub_le_of_le_geometric {x : ℕ → K} {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1)
    (hx : ∀ n, nrm p K (x (n + 1) - x n) ≤ r ^ n) {m n : ℕ} (hmn : n ≤ m) :
    nrm p K (x m - x n) ≤ r ^ n := by
  induction m, hmn using Nat.le_induction with
  | base => simpa using pow_nonneg hr0 n
  | succ m hnm ih =>
    have : x (m + 1) - x n = (x (m + 1) - x m) + (x m - x n) := by ring
    rw [this]
    exact (nrm_add_le_max _ _).trans
      (max_le ((hx m).trans (pow_le_pow_of_le_one hr0 hr hnm)) ih)

/-- Completeness of `K`: a sequence whose successive differences are bounded by a geometric
sequence with ratio `< 1` converges, with the same bounds for the distance to the limit. -/
theorem exists_limit {x : ℕ → K} {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hx : ∀ n, nrm p K (x (n + 1) - x n) ≤ r ^ n) :
    ∃ y : K, ∀ n, nrm p K (y - x n) ≤ r ^ n := by
  letI : NormedField K := spectralNorm.normedField ℚ_[p] K
  haveI : CompleteSpace K := spectralNorm.completeSpace ℚ_[p] K
  have hdist : ∀ n, dist (x n) (x (n + 1)) ≤ 1 * r ^ n := by
    intro n
    rw [one_mul, dist_comm]
    exact hx n
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric r 1 hr hdist)
  refine ⟨y, fun n ↦ ?_⟩
  have hlim : Filter.Tendsto (fun m ↦ nrm p K (x m - x n)) Filter.atTop
      (nhds (nrm p K (y - x n))) := by
    have := (hy.sub_const (x n)).norm
    exact this
  refine le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨n, fun m hm ↦ ?_⟩)
  exact nrm_sub_le_of_le_geometric hr0 hr.le hx hm

namespace Integers

theorem mem_maximalIdeal_pow_iff_nrm (x : 𝒪 p K) (n : ℕ) :
    x ∈ maximalIdeal (𝒪 p K) ^ n ↔ nrm p K (x : K) ≤ nrm p K (uniformizer p K) ^ n := by
  rw [mem_maximalIdeal_pow_iff]
  have hπ := uniformizer_spec (p := p) (K := K)
  by_cases hx : x = 0
  · simp [hx, pow_nonneg (nrm_nonneg _)]
  have hx' : (x : K) ≠ 0 := fun h ↦ hx (coe_eq_zero_iff.1 h)
  rw [← nrm_pow, nrm_le_iff_v_le hx' (pow_ne_zero _ hπ.ne_zero), v_pow hπ.ne_zero, hπ, mul_one]
  simp [hx]

theorem smul_top_eq (n : ℕ) :
    (maximalIdeal (𝒪 p K) ^ n • ⊤ : Submodule (𝒪 p K) (𝒪 p K)) =
      maximalIdeal (𝒪 p K) ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

instance isAdicComplete : IsAdicComplete (maximalIdeal (𝒪 p K)) (𝒪 p K) where
  haus' x hx := by
    by_contra h
    have hx' : (x : K) ≠ 0 := fun h' ↦ h (coe_eq_zero_iff.1 h')
    obtain ⟨n, hn⟩ := exists_nat_gt (v p (x : K))
    have := hx n
    rw [SModEq.sub_mem, sub_zero, smul_top_eq, mem_maximalIdeal_pow_iff] at this
    rcases this with h0 | h0
    · exact h h0
    · omega
  prec' f hf := by
    have hπ := uniformizer_spec (p := p) (K := K)
    set r := nrm p K (uniformizer p K)
    have hr0 : 0 ≤ r := nrm_nonneg _
    have hr1 : r < 1 := hπ.nrm_lt_one
    have hstep : ∀ n, nrm p K ((f (n + 1) : K) - f n) ≤ r ^ n := by
      intro n
      have := hf (Nat.le_succ n)
      rw [SModEq.sub_mem, smul_top_eq, ← neg_mem_iff, neg_sub, mem_maximalIdeal_pow_iff_nrm,
        coe_sub] at this
      exact this
    obtain ⟨y, hy⟩ := exists_limit (x := fun n ↦ (f n : K)) hr0 hr1 hstep
    have hy1 : nrm p K y ≤ 1 := by
      have : y = (y - f 0) + f 0 := by ring
      rw [this]
      exact (nrm_add_le_max _ _).trans (max_le ((hy 0).trans (by simp)) (nrm_coe_le_one _))
    refine ⟨mk y hy1, fun n ↦ ?_⟩
    rw [SModEq.sub_mem, smul_top_eq, ← neg_mem_iff, neg_sub, mem_maximalIdeal_pow_iff_nrm,
      coe_sub, coe_mk]
    exact hy n

/-- Hensel's lemma holds in `𝒪 p K`. -/
instance henselianLocalRing : HenselianLocalRing (𝒪 p K) where
  is_henselian f hf a₀ h₁ h₂ :=
    (IsAdicComplete.henselianRing (𝒪 p K) (maximalIdeal (𝒪 p K))).is_henselian f hf a₀ h₁
      (h₂.map _)

end Integers

end PadicField
