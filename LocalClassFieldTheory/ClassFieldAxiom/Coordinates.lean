/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.FieldNorm

/-!
# Coordinates with respect to a basis are bounded

For an extension `L/K` of fields finite over `ℚ_[p]` and any `K`-basis `b` of `L`, the coordinate
functionals are bounded: `‖b.repr x i‖ ≤ C * ‖x‖` (`PadicField.exists_repr_bound`). The proof writes
the coordinates as traces against the dual basis for the trace form, and uses
`‖Tr_{L/K} y‖ ≤ ‖y‖` (`PadicField.nrm_trace_le`).
-/

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L]

/-- The trace does not increase the absolute value. -/
theorem nrm_trace_le (x : L) : nrm p K (Algebra.trace K L x) ≤ nrm p L x := by
  haveI := finiteDimensional_tower (p := p) K L
  haveI := charZero p K
  set E := AlgebraicClosure L
  haveI : Algebra.IsAlgebraic ℚ_[p] E := Algebra.IsAlgebraic.trans ℚ_[p] L E
  have h := trace_eq_sum_embeddings (K := K) E (x := x)
  rw [← nrm_algebraMap_tower (L := E), h]
  exact nrm_sum_le _ _ (nrm_nonneg x) fun σ _ ↦ (nrm_algHom_tower K L σ x).le

/-- Coordinates with respect to a basis are bounded by the absolute value. -/
theorem exists_repr_bound {ι : Type*} [Finite ι] (b : Module.Basis ι K L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x i, nrm p K (b.repr x i) ≤ C * nrm p L x := by
  classical
  haveI := Fintype.ofFinite ι
  haveI := finiteDimensional_tower (p := p) K L
  haveI := charZero p K
  set B := Algebra.traceForm K L
  have hB : B.Nondegenerate := traceForm_nondegenerate K L
  set β := B.flip.dualBasis hB.flip b
  have hb : B.dualBasis hB β = b := LinearMap.BilinForm.dualBasis_dualBasis_flip hB b
  refine ⟨∑ i, nrm p L (β i), Finset.sum_nonneg fun i _ ↦ nrm_nonneg _, fun x i ↦ ?_⟩
  have hrepr : b.repr x i = Algebra.trace K L (x * β i) := by
    rw [← hb, LinearMap.BilinForm.dualBasis_repr_apply]
    rfl
  rw [hrepr]
  refine (nrm_trace_le (p := p) _).trans ?_
  rw [nrm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := fun i ↦ nrm p L (β i)) (fun i _ ↦ nrm_nonneg _)
      (Finset.mem_univ i)) (nrm_nonneg x)

end PadicField
