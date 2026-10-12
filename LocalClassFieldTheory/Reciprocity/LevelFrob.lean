/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.Tools

/-!
# Frobenius components at a standard level

For a standard extension `F = M U`:

* `PadicField.stdResU_stdFrob`: the Frobenius of `F/M` restricts to the Frobenius of `U/K`;
* `PadicField.eq_tau_of_restrict`: an automorphism of `F/K` acting on `U` as `Frob_U ^ k` is the
  Frobenius lift `τ = (g, φ^k)` for its `Gal(F/U)`-component `g`.
-/

set_option linter.unusedSectionVars false

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]

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

/-- The Frobenius of `F/M` restricts to the Frobenius of `U/K`. -/
theorem stdResU_stdFrob : stdResU hU (stdFrob hM hU hdeg) = frob hU := by
  have hqM : q p M = q p K := by
    have hf : f p K M = 1 := by
      have h1 := e_mul_f (p := p) (K := K) (L := M)
      rw [hM] at h1
      haveI := finiteDimensional_tower (p := p) K M
      exact (Nat.mul_eq_left Module.finrank_pos.ne').1 h1
    rw [q_eq_pow_f (K := K) (L := M), hf, pow_one]
  rw [eq_frob_iff]
  intro x
  rw [← Integers.algebraMap_mem_maximalIdeal_iff (L := F)]
  have h := frob_spec (std_isUnramified_top hM hU hdeg) (algebraMap (𝒪 p U) (𝒪 p F) x)
  rw [hqM] at h
  convert h using 1
  apply Integers.ext
  simp only [map_sub, map_pow, Integers.coe_algebraMap,
    Integers.coe_smul]
  rw [stdResU_apply]
  rfl

/-- An automorphism acting on `U` as `Frob_U ^ k` is a Frobenius lift `(g, φ^k)`. -/
theorem eq_tau_of_restrict (τ : F ≃ₐ[K] F) (k : ℕ)
    (h : ∀ u : U, τ (algebraMap U F u) = algebraMap U F ((frob hU ^ k) u)) :
    τ = tau hM hU hdeg ((stdProd hM hU hdeg).symm τ).1 k := by
  set gh := (stdProd hM hU hdeg).symm τ with hgh
  have hτ : τ = stdProd hM hU hdeg gh := by rw [hgh, MulEquiv.apply_symm_apply]
  have h2 : gh.2 = stdFrob hM hU hdeg ^ k := by
    apply (stdResU_bijective hM hU hdeg).1
    rw [map_pow, stdResU_stdFrob]
    ext u
    apply (algebraMap U F).injective
    rw [stdResU_apply, ← h u, hτ, stdProd_apply, ← stdResU_apply hU gh.2 u, gh.1.commutes]
  rw [tau, ← h2]
  exact hτ

end PadicField
