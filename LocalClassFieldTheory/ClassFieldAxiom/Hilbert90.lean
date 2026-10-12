/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Hilbert 90 for cyclic extensions, in arbitrary universes

Mathlib's `groupCohomology.exists_div_of_norm_eq_one` is stated for fields in `Type`. We deduce the
universe-polymorphic version from Noether's theorem
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units` by writing down the cocycle
`σ ^ i ↦ x · σ x ⋯ σ^(i-1) x` explicitly.
-/

namespace PadicField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The partial norms `x · σ x ⋯ σ ^ (i - 1) x`. -/
noncomputable def partialNorm (σ : L ≃ₐ[K] L) (x : Lˣ) (i : ℕ) : Lˣ :=
  ∏ j ∈ Finset.range i, Units.map ((σ ^ j : L ≃ₐ[K] L) : L →* L) x

omit [FiniteDimensional K L] in
theorem partialNorm_add (σ : L ≃ₐ[K] L) (x : Lˣ) (a b : ℕ) :
    partialNorm σ x (a + b) =
      partialNorm σ x a * Units.map ((σ ^ a : L ≃ₐ[K] L) : L →* L) (partialNorm σ x b) := by
  simp only [partialNorm, Finset.prod_range_add, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  ext
  simp [pow_add, AlgEquiv.mul_apply]

/-- Hilbert's Theorem 90 for cyclic extensions: if `σ` generates `Gal(L/K)` and the product of
the conjugates of `x` is `1`, then `x = σ y / y`. -/
theorem exists_div_of_prod_eq_one (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (x : Lˣ) (hx : partialNorm σ x (orderOf σ) = 1) :
    ∃ y : Lˣ, Units.map (σ : L →* L) y / y = x := by
  classical
  set n := orderOf σ
  have hn : 0 < n := orderOf_pos σ
  -- periodicity
  have hper : ∀ i, partialNorm σ x (i % n) = partialNorm σ x i := by
    intro i
    conv_rhs => rw [← Nat.mod_add_div i n]
    rw [partialNorm_add]
    suffices partialNorm σ x (n * (i / n)) = 1 by rw [this, map_one, mul_one]
    induction i / n with
    | zero => simp [partialNorm]
    | succ k ih =>
      rw [mul_add, mul_one, partialNorm_add, ih, one_mul, hx, map_one]
  have hpow : ∀ g : L ≃ₐ[K] L, ∃ k : ℕ, σ ^ k = g := fun g ↦
    (mem_powers_iff_mem_zpowers.2 (hσ g))
  let k : (L ≃ₐ[K] L) → ℕ := fun g ↦ (hpow g).choose
  have hk : ∀ g, σ ^ k g = g := fun g ↦ (hpow g).choose_spec
  have hwd : ∀ a b : ℕ, σ ^ a = σ ^ b → partialNorm σ x a = partialNorm σ x b := by
    intro a b hab
    rw [← hper a, ← hper b, pow_eq_pow_iff_modEq.1 hab]
  let f : (L ≃ₐ[K] L) → Lˣ := fun g ↦ partialNorm σ x (k g)
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    simp only [f, AlgEquiv.smul_units_def]
    have h1 : σ ^ k (g * h) = σ ^ (k g + k h) := by rw [hk, pow_add, hk, hk]
    rw [hwd _ _ h1, partialNorm_add, mul_comm]
    congr 2
    rw [hk]
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  refine ⟨β, ?_⟩
  have := hβ σ
  rw [AlgEquiv.smul_units_def] at this
  rw [this]
  simp only [f]
  have h1 : σ ^ k σ = σ ^ 1 := by rw [hk, pow_one]
  rw [hwd _ _ h1]
  simp only [partialNorm, Finset.range_one, Finset.prod_singleton, pow_zero]
  ext
  rfl

end PadicField
