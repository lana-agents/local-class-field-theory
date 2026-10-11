/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Teichmüller representatives

Let `R` be a Henselian local ring whose residue field `k` is finite with `Q` elements.
Every `a : k` has a unique lift `teichmuller R a` satisfying `x ^ Q = x`; this gives a
multiplicative section `k →* R` of the residue map.

## Main results

* `Teichmuller.eq_of_pow_card_eq_self`: two roots of `X ^ Q - X` with the same residue are equal.
* `Teichmuller.teichmuller`: the multiplicative section, with `residue_teichmuller` and
  `teichmuller_pow_card`.
-/

open Polynomial IsLocalRing

-- `HenselianLocalRing` extends `IsLocalRing`, but `ResidueField R` needs the latter first.
set_option linter.overlappingInstances false

namespace Teichmuller

variable (R : Type*) [CommRing R] [IsLocalRing R] [Finite (ResidueField R)]

/-- The cardinality of the residue field. -/
noncomputable abbrev Q : ℕ := Nat.card (ResidueField R)

variable {R}

theorem natCast_Q_mem_maximalIdeal : (Q R : R) ∈ maximalIdeal R := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change residue R (Q R : R) = 0
  rw [map_natCast]
  haveI := Fintype.ofFinite (ResidueField R)
  obtain ⟨p, hchar⟩ := CharP.exists (ResidueField R)
  haveI := hchar
  rw [Q, Nat.card_eq_fintype_card]
  exact FiniteField.cast_card_eq_zero (ResidueField R)

theorem pow_Q_residue (a : ResidueField R) : a ^ Q R = a := by
  haveI := Fintype.ofFinite (ResidueField R)
  rw [Q, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card a

theorem one_lt_Q : 1 < Q R := Finite.one_lt_card

/-- Two roots of `X ^ Q - X` that are congruent modulo the maximal ideal are equal. -/
theorem eq_of_pow_card_eq_self {x y : R} (hx : x ^ Q R = x) (hy : y ^ Q R = y)
    (hxy : residue R x = residue R y) : x = y := by
  set s := ∑ i ∈ Finset.range (Q R), x ^ i * y ^ (Q R - 1 - i)
  have hgeom : s * (x - y) = x ^ Q R - y ^ Q R := (Commute.all x y).geom_sum₂_mul (Q R)
  rw [hx, hy] at hgeom
  have hs : s ∈ maximalIdeal R := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residue R s = 0
    simp only [s, map_sum, map_mul, map_pow, hxy]
    rw [Finset.sum_congr rfl fun i hi ↦ by
      rw [← pow_add, Nat.add_sub_cancel' (by simp at hi; omega)]]
    have hQ0 : residue R (Q R : R) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 natCast_Q_mem_maximalIdeal
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← map_natCast (residue R), hQ0,
      zero_mul]
  have hunit : IsUnit (1 - s) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro h
    exact (maximalIdeal.isMaximal R).ne_top
      ((Ideal.eq_top_iff_one _).2 (by simpa using add_mem h hs))
  have : (1 - s) * (x - y) = 0 := by rw [sub_mul, one_mul, hgeom, sub_self]
  rw [← sub_eq_zero]
  exact (hunit.mul_right_eq_zero).1 this

variable [HenselianLocalRing R]

theorem exists_lift (a : ResidueField R) : ∃ x : R, x ^ Q R = x ∧ residue R x = a := by
  obtain ⟨a₀, rfl⟩ := residue_surjective a
  set F : R[X] := X ^ Q R - X
  have hQ := one_lt_Q (R := R)
  have hF : F.Monic := monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hQ)
  have h₁ : F.eval a₀ ∈ maximalIdeal R := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change residue R (F.eval a₀) = 0
    simp [F, pow_Q_residue]
  have h₂ : IsUnit (F.derivative.eval a₀) := by
    have : F.derivative.eval a₀ = (Q R : R) * a₀ ^ (Q R - 1) - 1 := by
      simp [F, derivative_X_pow]
    rw [this, ← IsLocalRing.notMem_maximalIdeal]
    intro h
    have h' := Ideal.mul_mem_right (a₀ ^ (Q R - 1)) _ natCast_Q_mem_maximalIdeal
    have := sub_mem h' h
    rw [sub_sub_cancel] at this
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
  obtain ⟨x, hroot, hx⟩ := HenselianLocalRing.is_henselian F hF a₀ h₁ h₂
  refine ⟨x, ?_, ?_⟩
  · have := hroot.eq_zero
    simp only [F, eval_sub, eval_pow, eval_X] at this
    exact sub_eq_zero.1 this
  · rw [← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hx

variable (R) in
/-- The Teichmüller lift of an element of the residue field. -/
noncomputable def lift (a : ResidueField R) : R := (exists_lift a).choose

theorem lift_pow_Q (a : ResidueField R) : lift R a ^ Q R = lift R a := (exists_lift a).choose_spec.1

@[simp]
theorem residue_lift (a : ResidueField R) : residue R (lift R a) = a :=
  (exists_lift a).choose_spec.2

theorem eq_lift {x : R} (hx : x ^ Q R = x) : x = lift R (residue R x) :=
  eq_of_pow_card_eq_self hx (lift_pow_Q _) (by simp)

variable (R) in
/-- The Teichmüller character `k →* R`. -/
noncomputable def teichmuller : ResidueField R →* R where
  toFun := lift R
  map_one' := (eq_lift (by simp)).symm.trans (by simp)
  map_mul' a b := by
    have h : (lift R a * lift R b) ^ Q R = lift R a * lift R b := by
      rw [mul_pow, lift_pow_Q, lift_pow_Q]
    rw [eq_lift h, map_mul, residue_lift, residue_lift]

@[simp]
theorem residue_teichmuller (a : ResidueField R) : residue R (teichmuller R a) = a :=
  residue_lift a

theorem teichmuller_pow_Q (a : ResidueField R) : teichmuller R a ^ Q R = teichmuller R a :=
  lift_pow_Q a

theorem teichmuller_injective : Function.Injective (teichmuller R) := fun a b h ↦ by
  rw [← residue_teichmuller a, h, residue_teichmuller]

theorem eq_teichmuller {x : R} (hx : x ^ Q R = x) : x = teichmuller R (residue R x) :=
  eq_lift hx

@[simp]
theorem teichmuller_zero : teichmuller R 0 = 0 := by
  have h := eq_teichmuller (R := R) (x := 0) (zero_pow (by have := one_lt_Q (R := R); omega))
  rw [map_zero] at h
  exact h.symm

end Teichmuller
