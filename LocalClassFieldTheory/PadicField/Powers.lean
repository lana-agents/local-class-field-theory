/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.Complete

/-!
# `n`-th powers near `1`

* `PadicField.exists_root_of_isAdicComplete`: Hensel's lemma (Newton's method) for arbitrary,
  not necessarily monic, polynomials over an `I`-adically complete ring (the proof of Mathlib's
  `IsAdicComplete.henselianRing` does not use monicity);
* `PadicField.exists_pow_eq_of_nrm_sub_one_lt`: every `u ∈ K` with `‖u - 1‖ < ‖n² p‖` is an
  `n`-th power.
-/

open Polynomial IsLocalRing
open scoped Ring

namespace PadicField

/-- **Hensel's lemma** over an `I`-adically complete ring, without monicity. -/
theorem exists_root_of_isAdicComplete {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  classical
  let f' := derivative f
  let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * (f'.eval b)⁻¹ʳ
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
    intro n
    simp only [c]
  have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => ?_
    rw [hc, sub_eq_add_neg, ← add_zero a₀]
    refine ih.add ?_
    rw [SModEq.zero, Ideal.neg_mem_iff]
    refine I.mul_mem_right _ ?_
    rw [← SModEq.zero] at h₁ ⊢
    exact (ih.eval f).trans h₁
  have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
    intro n
    haveI := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    convert! h₂ using 1
    exact SModEq.def.mp ((hc_mod n).eval _)
  have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using! h₁
    | succ n ih => ?_
    rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
      add_neg_cancel_comm]
    rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
      Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
    swap
    · intro i
      rw [zero_mul]
    refine Ideal.add_mem _ ?_ ?_
    · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
        taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
        mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
      exact Ideal.zero_mem _
    · refine Submodule.sum_mem _ ?_
      simp only [Finset.mem_Ico]
      rintro i ⟨h2i, _⟩
      have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
      refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
      rw [pow_mul']
      exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    clear hmn
    induction k with
    | zero => rw [add_zero]
    | succ k ih => ?_
    rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
    refine ih.add ?_
    symm
    rw [SModEq.zero, Ideal.neg_mem_iff]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
    rw [add_assoc]
    exact le_self_add
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · show f.IsRoot a
    suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hfcI _)
  · show a - a₀ ∈ I
    specialize ha (0 + 1)
    rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
    rw [← SModEq.sub_mem, ← add_zero a₀]
    refine ha.symm.trans (SModEq.rfl.add ?_)
    rw [SModEq.zero, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ h₁

/-- The binomial identity behind `exists_pow_eq_one_add`: with `c = n p` and
`a j = C(n, j+1) c^{j+1} / (n c)`, we have `n c * a j = C(n, j+1) c^{j+1}`. -/
theorem choose_mul_pow_dvd (n p j : ℕ) : n * (n * p) ∣ n.choose (j + 1) * (n * p) ^ (j + 1) := by
  rcases j with _ | j
  · simp [Nat.choose_one_right]
  · refine Dvd.dvd.mul_left ?_ _
    rw [pow_succ, pow_succ]
    exact ⟨(n * p) ^ j * p, by ring⟩

/-- In a commutative ring, `(1 + c y)^n - 1 = Σ_{j < n} C(n, j+1) (c y)^{j+1}`. -/
theorem one_add_pow_sub_one {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    (1 + x) ^ n - 1 = ∑ j ∈ Finset.range n, (n.choose (j + 1) : R) * x ^ (j + 1) := by
  rw [add_comm, add_pow, Finset.sum_range_succ', sub_eq_iff_eq_add]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by ring

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

/-- `1 + n (n p) w` is an `n`-th power in `𝒪 K` for `w ∈ 𝔪`. -/
theorem exists_pow_eq_one_add (n : ℕ) (hn : 0 < n) (w : 𝒪 p K)
    (hw : w ∈ maximalIdeal (𝒪 p K)) :
    ∃ y : 𝒪 p K, (1 + ((n * p : ℕ) : 𝒪 p K) * y) ^ n = 1 + ((n * (n * p) : ℕ) : 𝒪 p K) * w := by
  set a : ℕ → ℕ := fun j ↦ n.choose (j + 1) * (n * p) ^ (j + 1) / (n * (n * p))
  have ha : ∀ j, ((n * (n * p) : ℕ) : 𝒪 p K) * (a j : 𝒪 p K) =
      (n.choose (j + 1) : 𝒪 p K) * ((n * p : ℕ) : 𝒪 p K) ^ (j + 1) := by
    intro j
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (choose_mul_pow_dvd n p j)]
    push_cast; ring
  have ha0 : a 0 = 1 := by
    simp only [a, Nat.choose_one_right, zero_add, pow_one]
    exact Nat.div_self (Nat.mul_pos hn (Nat.mul_pos hn hp.out.pos))
  set g : (𝒪 p K)[X] := ∑ j ∈ Finset.range n, C (a j : 𝒪 p K) * X ^ (j + 1) - C w
  have hg0 : g.eval 0 ∈ maximalIdeal (𝒪 p K) := by
    simp only [g, eval_sub, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    simp [hw]
  have hg1 : (derivative g).eval 0 = 1 := by
    simp only [g, derivative_sub, derivative_C, sub_zero, derivative_sum, derivative_mul,
      derivative_C, zero_mul, zero_add, derivative_X_pow, eval_finsetSum, eval_mul, eval_C]
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hn)]
    · simp [ha0]
    · intro j _ hj
      simp [hj]
  obtain ⟨y, hy, -⟩ := exists_root_of_isAdicComplete (maximalIdeal (𝒪 p K)) g 0 hg0
    (by rw [hg1, map_one]; exact isUnit_one)
  refine ⟨y, ?_⟩
  have h := congrArg (fun z ↦ ((n * (n * p) : ℕ) : 𝒪 p K) * z) hy.eq_zero
  simp only [g, eval_sub, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, mul_zero,
    mul_sub, Finset.mul_sum] at h
  rw [← sub_eq_zero, ← sub_sub, one_add_pow_sub_one, ← h]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← mul_assoc, ha, mul_pow]
  ring

include hp in
/-- **`n`-th powers near `1`**: every `u ∈ K` with `‖u - 1‖ < ‖n² p‖` is an `n`-th power. -/
theorem exists_pow_eq_of_nrm_sub_one_lt (n : ℕ) (hn : 0 < n) (u : K)
    (hu : nrm p K (u - 1) < nrm p K ((n * (n * p) : ℕ) : K)) : ∃ x : K, x ^ n = u := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  set N : K := ((n * (n * p) : ℕ) : K)
  have hN : N ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hn (Nat.mul_pos hn hp.out.pos)).ne'
  have hw1 : nrm p K ((u - 1) / N) < 1 := by
    rw [nrm_div, div_lt_one (nrm_pos_iff.2 hN)]
    exact hu
  set w : 𝒪 p K := Integers.mk ((u - 1) / N) hw1.le
  have hw : w ∈ maximalIdeal (𝒪 p K) := Integers.mem_maximalIdeal_iff.2 hw1
  obtain ⟨y, hy⟩ := exists_pow_eq_one_add n hn w hw
  refine ⟨algebraMap (𝒪 p K) K (1 + ((n * p : ℕ) : 𝒪 p K) * y), ?_⟩
  rw [← map_pow, hy, map_add, map_one, map_mul, map_natCast]
  change 1 + N * ((u - 1) / N) = u
  field_simp
  ring

end PadicField
