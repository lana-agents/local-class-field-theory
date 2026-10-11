/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.Ramification

/-!
# The field norm and the absolute value

For an extension `L/K` of fields finite over `ℚ_[p]` we prove

* `PadicField.nrm_norm`: `‖N_{L/K} x‖ = ‖x‖ ^ [L : K]`;
* `PadicField.v_norm`: `v_K (N_{L/K} x) = f(L/K) * v_L (x)`;
* the norm maps `𝒪 p L` to `𝒪 p K` and units to units.
-/

open Polynomial

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L]

/-- `‖N_{L/K} x‖ = ‖x‖ ^ [L : K]`. -/
theorem nrm_norm (x : L) :
    nrm p K (Algebra.norm K x) = nrm p L x ^ Module.finrank K L := by
  haveI := finiteDimensional_tower (p := p) K L
  haveI := charZero p K
  set E := AlgebraicClosure L
  haveI : Algebra.IsAlgebraic ℚ_[p] E := Algebra.IsAlgebraic.trans ℚ_[p] L E
  have h := Algebra.norm_eq_prod_embeddings K E x
  have h1 : nrm p E (algebraMap K E (Algebra.norm K x)) = nrm p K (Algebra.norm K x) :=
    nrm_algebraMap_tower _
  rw [← h1, h, map_prod]
  have h2 : ∀ σ : L →ₐ[K] E, nrm p E (σ x) = nrm p L x := fun σ ↦ nrm_algHom_tower K L σ x
  simp only [h2, Finset.prod_const, Finset.card_univ]
  rw [AlgHom.card]

/-- `‖x‖ = ‖π‖ ^ v x`. -/
theorem nrm_eq_nrm_uniformizer_zpow {π : K} (hπ : IsUniformizer p K π) {x : K} (hx : x ≠ 0) :
    nrm p K x = nrm p K π ^ v p x := by
  obtain ⟨u, hu, hxu⟩ := eq_zpow_mul_unit hπ hx
  conv_lhs => rw [hxu]
  rw [nrm_mul, hu, mul_one, nrm_zpow]

/-- `v_K (N_{L/K} x) = f(L/K) * v_L (x)`. -/
theorem v_norm {x : L} (hx : x ≠ 0) : v p (Algebra.norm K x) = f p K L * v p x := by
  haveI := finiteDimensional_tower (p := p) K L
  have hN : Algebra.norm K x ≠ 0 := Algebra.norm_ne_zero_iff.2 hx
  set πK := uniformizer p K
  set πL := uniformizer p L
  have hπK := uniformizer_spec (p := p) (K := K)
  have hπL := uniformizer_spec (p := p) (K := L)
  -- `‖π_K‖ = ‖π_L‖ ^ e`
  have hKL : nrm p K πK = nrm p L πL ^ (e p K L : ℤ) := by
    rw [← nrm_algebraMap_tower (L := L), nrm_eq_nrm_uniformizer_zpow hπL
      ((map_ne_zero_iff _ (algebraMap K L).injective).2 hπK.ne_zero), v_algebraMap_uniformizer]
  have key : nrm p K (Algebra.norm K x) = nrm p K (πK ^ (f p K L * v p x)) := by
    rw [nrm_norm, nrm_zpow, hKL, nrm_eq_nrm_uniformizer_zpow hπL hx, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, ← e_mul_f (p := p) (K := K) (L := L)]
    congr 1
    push_cast; ring
  rw [nrm_eq_iff_v_eq hN (zpow_ne_zero _ hπK.ne_zero), v_zpow hπK.ne_zero, hπK] at key
  rw [key, mul_one]

/-- The norm of an integer is an integer. -/
theorem nrm_norm_le_one {x : L} (hx : nrm p L x ≤ 1) : nrm p K (Algebra.norm K x) ≤ 1 := by
  rw [nrm_norm]; exact pow_le_one₀ (nrm_nonneg x) hx

/-- The norm of a unit is a unit. -/
theorem nrm_norm_eq_one {x : L} (hx : nrm p L x = 1) : nrm p K (Algebra.norm K x) = 1 := by
  rw [nrm_norm, hx, one_pow]

end PadicField
