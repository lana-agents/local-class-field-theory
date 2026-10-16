/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.EulerFinite

/-!
# Descent of the Euler characteristic formula along `ℓ`-extensions

Let `ℓ` be a prime and `X` a finite discrete `G_K`-module killed by `ℓ`, with a `G_K`-equivariant
automorphism `R` such that `R^ℓ = 1`. Put `D = R - 1`. Then `D^ℓ = R^ℓ - 1 = 0` (characteristic
`ℓ`), so `X` is filtered by `X_k = ker D^k` (`0 = X_0 ⊆ X_1 ⊆ … ⊆ X_ℓ = X`) and `D^k` embeds
`X_{k+1}/X_k` into `Y = X_1 = X^R`. If `#X = #Y^ℓ` all these embeddings are isomorphisms
(counting), and the multiplicativity of the Euler ratio (`PadicField.eulerRatio_shortExact`)
gives

* **`PadicField.eulerRatio_eq_pow_of_aut`** : `ρ(X) = ρ(X^R)^ℓ`.
-/

open groupCohomology Brauer ContH2 IntermediateField

set_option linter.unusedSectionVars false

universe v

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

section Binomial

variable {X : Type*} [CommGroup X]

/-- `D x = R x / x`. -/
def dOp (R : X →* X) : X →* X where
  toFun x := R x / x
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]; exact mul_div_mul_comm _ _ _ _

theorem dOp_apply (R : X →* X) (x : X) : dOp R x = R x / x := rfl

/-- **`D^ℓ = 0`**: if `X` is killed by the prime `ℓ` and `R^ℓ = 1`, then `(R - 1)^ℓ = 0`. -/
theorem dOp_iterate_eq_one {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hX : ∀ x : X, x ^ ℓ = 1) (R : X →* X)
    (hR : ∀ x, R^[ℓ] x = x) (x : X) : (dOp R)^[ℓ] x = 1 := by
  by_cases hs : Subsingleton X
  · exact Subsingleton.elim _ _
  rw [not_subsingleton_iff_nontrivial] at hs
  let R' : AddMonoid.End (Additive X) := MonoidHom.toAdditive R
  let E : AddMonoid.End (Additive X) := R' - 1
  haveI : CharP (AddMonoid.End (Additive X)) ℓ := by
    refine ⟨fun n => ⟨fun h => ?_, fun h => ?_⟩⟩
    · obtain ⟨y, hy⟩ := exists_ne (1 : X)
      have h1 := congrArg (fun f : AddMonoid.End (Additive X) => f (Additive.ofMul y)) h
      simp only [AddMonoid.End.natCast_apply] at h1
      have h2 : y ^ n = 1 := by
        rw [← toMul_ofMul y, ← toMul_nsmul, h1]
        rfl
      rw [← orderOf_eq_prime (hX y) hy]
      exact orderOf_dvd_of_pow_eq_one h2
    · obtain ⟨m, rfl⟩ := h
      ext a
      have : ℓ • a = 0 := by
        rw [← ofMul_toMul a, ← ofMul_pow, hX]
        rfl
      have h0 : ((ℓ * m : ℕ) : AddMonoid.End (Additive X)) a = 0 := by
        rw [AddMonoid.End.natCast_apply, mul_nsmul, this, nsmul_zero]
      rw [h0]
      rfl
  have hsR : Function.Semiconj Additive.ofMul R R' := fun _ => rfl
  have hsD : Function.Semiconj Additive.ofMul (dOp R) E := fun _ => rfl
  have hR'ℓ : R' ^ ℓ = 1 := by
    ext a
    rw [AddMonoid.End.coe_pow, ← ofMul_toMul a, ← hsR.iterate_right ℓ, hR]
    rfl
  have hEℓ : E ^ ℓ = 0 := by
    change (R' - 1) ^ ℓ = 0
    rw [sub_pow_char_of_commute ℓ (Commute.one_right R'), hR'ℓ, one_pow, sub_self]
  have := hsD.iterate_right ℓ x
  rw [← AddMonoid.End.coe_pow, hEℓ] at this
  exact Additive.ofMul.injective this

end Binomial

end PadicField
