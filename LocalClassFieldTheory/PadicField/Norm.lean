/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# The absolute value on an algebraic extension of `ℚ_[p]`

Every field `K` algebraic over `ℚ_[p]` carries a canonical absolute value extending `‖·‖_p`,
namely Mathlib's spectral norm `spectralNorm ℚ_[p] K`, which is multiplicative because `ℚ_[p]` is
complete. We package it as `PadicField.nrm p K : MulAlgebraNorm ℚ_[p] K`.

Since the spectral norm of `x` only depends on the minimal polynomial of `x` over `ℚ_[p]`, it is
automatically compatible with all `ℚ_[p]`-algebra maps (`PadicField.nrm_map`); in particular it is
compatible with towers of extensions and invariant under Galois automorphisms.

## Main results

* `PadicField.nrm_add_le_max`: the absolute value is nonarchimedean.
* `PadicField.nrm_map`: invariance under `ℚ_[p]`-algebra homomorphisms.
* `PadicField.nrm_le_one_of_isIntegral`: integral elements over the unit ball have norm `≤ 1`.
* `PadicField.exists_nrm_pow_eq`: `‖x‖ ^ N = p ^ (-m)` for some `m : ℤ`, where `N` only depends on
  `[K : ℚ_[p]]` (discreteness of the value group).
-/

open Polynomial

namespace PadicField

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [Algebra ℚ_[p] K]

/-- The canonical absolute value on a field algebraic over `ℚ_[p]`, extending `‖·‖_p`. -/
noncomputable def nrm [Algebra.IsAlgebraic ℚ_[p] K] : MulAlgebraNorm ℚ_[p] K :=
  spectralMulAlgNorm ℚ_[p] K

variable [Algebra.IsAlgebraic ℚ_[p] K]
variable {p K}

theorem nrm_apply (x : K) : nrm p K x = spectralNorm ℚ_[p] K x := rfl

@[simp]
theorem nrm_algebraMap (a : ℚ_[p]) : nrm p K (algebraMap ℚ_[p] K a) = ‖a‖ :=
  spectralNorm_extends a

theorem nrm_nonneg (x : K) : 0 ≤ nrm p K x := apply_nonneg _ x

@[simp]
theorem nrm_eq_zero_iff {x : K} : nrm p K x = 0 ↔ x = 0 := map_eq_zero_iff_eq_zero _

theorem nrm_pos_iff {x : K} : 0 < nrm p K x ↔ x ≠ 0 := by
  rw [(nrm_nonneg x).lt_iff_ne, ne_comm, Ne, nrm_eq_zero_iff]

@[simp]
theorem nrm_mul (x y : K) : nrm p K (x * y) = nrm p K x * nrm p K y := map_mul _ x y

@[simp]
theorem nrm_one : nrm p K 1 = 1 := map_one _

@[simp]
theorem nrm_pow (x : K) (n : ℕ) : nrm p K (x ^ n) = nrm p K x ^ n := map_pow _ x n

@[simp]
theorem nrm_inv (x : K) : nrm p K x⁻¹ = (nrm p K x)⁻¹ := by
  exact map_inv₀ _ x

@[simp]
theorem nrm_div (x y : K) : nrm p K (x / y) = nrm p K x / nrm p K y := by
  rw [div_eq_mul_inv, nrm_mul, nrm_inv, div_eq_mul_inv]

@[simp]
theorem nrm_zpow (x : K) (n : ℤ) : nrm p K (x ^ n) = nrm p K x ^ n := by
  rcases n with n | n
  · simp
  · simp [zpow_negSucc]

@[simp]
theorem nrm_neg (x : K) : nrm p K (-x) = nrm p K x := map_neg_eq_map _ x

theorem nrm_add_le_max (x y : K) : nrm p K (x + y) ≤ max (nrm p K x) (nrm p K y) :=
  isNonarchimedean_spectralNorm x y

theorem nrm_sub_le_max (x y : K) : nrm p K (x - y) ≤ max (nrm p K x) (nrm p K y) := by
  simpa [sub_eq_add_neg] using nrm_add_le_max x (-y)

theorem nrm_add_eq_left {x y : K} (h : nrm p K y < nrm p K x) : nrm p K (x + y) = nrm p K x := by
  refine le_antisymm ((nrm_add_le_max x y).trans (max_le le_rfl h.le)) ?_
  by_contra! H
  have : nrm p K x ≤ max (nrm p K (x + y)) (nrm p K y) := by
    simpa using nrm_sub_le_max (x + y) y
  exact (max_lt H h).not_ge this

theorem nrm_sum_le {ι : Type*} (s : Finset ι) (f : ι → K) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i ∈ s, nrm p K (f i) ≤ c) : nrm p K (∑ i ∈ s, f i) ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hc
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (nrm_add_le_max _ _).trans (max_le (h a (by simp)) (ih fun i hi ↦ h i (by simp [hi])))

/-- The absolute value only depends on the minimal polynomial over `ℚ_[p]`: it is invariant under
`ℚ_[p]`-algebra homomorphisms. -/
theorem nrm_map {L : Type*} [Field L] [Algebra ℚ_[p] L] [Algebra.IsAlgebraic ℚ_[p] L]
    (f : K →ₐ[ℚ_[p]] L) (x : K) : nrm p L (f x) = nrm p K x := by
  simp only [nrm_apply, spectralNorm, minpoly.algHom_eq f f.injective x]

/-- Compatibility of the absolute values in a tower. -/
theorem nrm_algebraMap_tower {L : Type*} [Field L] [Algebra ℚ_[p] L] [Algebra.IsAlgebraic ℚ_[p] L]
    [Algebra K L] [IsScalarTower ℚ_[p] K L] (x : K) :
    nrm p L (algebraMap K L x) = nrm p K x :=
  nrm_map (IsScalarTower.toAlgHom ℚ_[p] K L) x

/-- The absolute value is invariant under `ℚ_[p]`-algebra automorphisms. -/
theorem nrm_algEquiv (σ : K ≃ₐ[ℚ_[p]] K) (x : K) : nrm p K (σ x) = nrm p K x :=
  nrm_map σ.toAlgHom x

/-- `‖x‖ ≤ 1` iff all coefficients of the minimal polynomial of `x` over `ℚ_[p]` have norm `≤ 1`. -/
theorem nrm_le_one_iff_coeff (x : K) :
    nrm p K x ≤ 1 ↔ ∀ n, ‖(minpoly ℚ_[p] x).coeff n‖ ≤ 1 :=
  spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral x))

/-- An element satisfying a monic equation whose lower coefficients have norm `≤ 1` has norm
`≤ 1`. -/
theorem nrm_le_one_of_monic_root {x : K} (f : K[X]) (hf : f.Monic) (hroot : aeval x f = 0)
    (hcoeff : ∀ i, nrm p K (f.coeff i) ≤ 1) : nrm p K x ≤ 1 := by
  by_contra! hx
  have hdeg : 0 < f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h | h
    · rw [hf.natDegree_eq_zero.1 h] at hroot; simp at hroot
    · exact h
  -- `x ^ d = - ∑_{i < d} a_i x ^ i`, and the right side is too small.
  have key : x ^ f.natDegree = -∑ i ∈ Finset.range f.natDegree, f.coeff i * x ^ i := by
    rw [aeval_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, one_smul] at hroot
    simp only [smul_eq_mul] at hroot
    linear_combination hroot
  have hlt : nrm p K (∑ i ∈ Finset.range f.natDegree, f.coeff i * x ^ i) <
      nrm p K x ^ f.natDegree := by
    have hpos : 0 < nrm p K x ^ (f.natDegree - 1) := pow_pos (one_pos.trans hx) _
    refine lt_of_le_of_lt (nrm_sum_le _ _ hpos.le fun i hi ↦ ?_) ?_
    · rw [nrm_mul, nrm_pow]
      calc nrm p K (f.coeff i) * nrm p K x ^ i ≤ 1 * nrm p K x ^ i := by
            gcongr; exact hcoeff i
        _ ≤ nrm p K x ^ (f.natDegree - 1) := by
            rw [one_mul]
            exact pow_le_pow_right₀ hx.le (by simp at hi; omega)
    · exact pow_lt_pow_right₀ hx (by omega)
  rw [← nrm_pow, key, nrm_neg] at hlt
  exact hlt.false

/-- Discreteness of the value group: for nonzero `x`, `‖x‖ ^ d = p ^ (-m)` where `d` is the
degree of `x` over `ℚ_[p]`. -/
theorem exists_nrm_pow_natDegree_eq {x : K} (hx : x ≠ 0) :
    ∃ m : ℤ, nrm p K x ^ (minpoly ℚ_[p] x).natDegree = (p : ℝ) ^ (-m) := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hd : (minpoly ℚ_[p] x).natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have h0 : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
  refine ⟨((minpoly ℚ_[p] x).coeff 0).valuation, ?_⟩
  rw [nrm_apply, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ (by exact_mod_cast hd),
    Real.rpow_one, Padic.norm_eq_zpow_neg_valuation h0]

end PadicField
