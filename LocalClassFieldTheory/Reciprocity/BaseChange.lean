/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.FrobLiftPow
import LocalClassFieldTheory.Reciprocity.Artin

/-!
# Unramified extensions under base change

Let `K' ⊆ Ω` be a finite extension of `K` with inertia degree `f' = f(K'/K)`; we use `K'` as a
new base field.

* `PadicField.unramifiedOfDegree_le_baseChange`: `K_{f' m} ⊆ K'_m`;
* `PadicField.resHom_frob_baseChange`: an automorphism acting on `K'_m` as the Frobenius of
  `K'` acts on `K_{f' m}` as `Frob_K ^ f'`.
-/

set_option linter.unusedSectionVars false

open IntermediateField Polynomial

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]
variable (K' : IntermediateField K Ω) [FiniteDimensional K K']

theorem q_baseChange : q p K' = q p K ^ f p K K' := q_eq_pow_f

/-- `K_{f' m} ⊆ K'_m`. -/
theorem unramifiedOfDegree_le_baseChange {m : ℕ} (hm : 0 < m) :
    unramifiedOfDegree p K Ω (f p K K' * m) ≤
      (unramifiedOfDegree p K' Ω m).restrictScalars K := by
  have hfm : 0 < f p K K' * m := Nat.mul_pos f_pos hm
  rw [unramifiedOfDegree_def p K Ω]
  refine adjoin_le_iff.2 fun x hx ↦ ?_
  rw [SetLike.mem_coe, mem_restrictScalars]
  rw [mem_rootSet_X_pow_sub_X (one_lt_q_pow hfm)] at hx
  refine mem_unramifiedOfDegree_of_pow_eq hm ?_
  rwa [q_baseChange, ← pow_mul]

/-- On roots of `X^(q^(f' m)) - X`, the Frobenius of `K'_m` acts as `x ↦ x ^ (q ^ f')`. -/
theorem frob_baseChange_apply {m : ℕ} (hm : 0 < m) (x : unramifiedOfDegree p K' Ω m)
    (hx : (x : Ω) ^ q p K ^ (f p K K' * m) = x) :
    (frobT p K' Ω m x : Ω) = (x : Ω) ^ q p K ^ f p K K' := by
  rw [frobT, frob_unramifiedOfDegree_apply hm x (by rwa [q_baseChange, ← pow_mul]),
    q_baseChange, IntermediateField.coe_pow]

/-- `Frob_K ^ k` acts on roots of `X^(q^n) - X` as `x ↦ x ^ (q ^ k)`. -/
theorem frobT_pow_apply_of_pow_eq {n : ℕ} (hn : 0 < n) (k : ℕ) (x : unramifiedOfDegree p K Ω n)
    (hx : (x : Ω) ^ q p K ^ n = x) :
    ((frobT p K Ω n ^ k) x : Ω) = (x : Ω) ^ q p K ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hy : (((frobT p K Ω n ^ k) x : unramifiedOfDegree p K Ω n) : Ω) ^ q p K ^ n =
        ((frobT p K Ω n ^ k) x : Ω) := by
      rw [ih, ← pow_mul, mul_comm, pow_mul, hx]
    rw [pow_succ', AlgEquiv.mul_apply, frobT, frob_unramifiedOfDegree_apply hn _ hy]
    rw [IntermediateField.coe_pow, ih, ← pow_mul, ← pow_succ]

/-- `K'_m = K' ⊔ K_{f' m}` (as extensions of `K`). -/
theorem restrictScalars_unramifiedOfDegree {m : ℕ} (hm : 0 < m) :
    (unramifiedOfDegree p K' Ω m).restrictScalars K =
      K' ⊔ unramifiedOfDegree p K Ω (f p K K' * m) := by
  have hfm : 0 < f p K K' * m := Nat.mul_pos f_pos hm
  rw [unramifiedOfDegree_def p K' Ω, restrictScalars_adjoin_eq_sup,
    unramifiedOfDegree_def p K Ω]
  congr 2
  ext x
  rw [mem_rootSet_X_pow_sub_X (one_lt_q_pow hm), mem_rootSet_X_pow_sub_X (one_lt_q_pow hfm),
    q_baseChange, ← pow_mul]

/-- An automorphism of `D ⊇ K'` over `K'`, viewed as an automorphism over `K`. -/
noncomputable def autRestrict {D : IntermediateField K Ω} (h : K' ≤ D)
    (τ : extendScalars h ≃ₐ[K'] extendScalars h) : D ≃ₐ[K] D :=
  τ.restrictScalars K

theorem autRestrict_apply {D : IntermediateField K Ω} (h : K' ≤ D)
    (τ : extendScalars h ≃ₐ[K'] extendScalars h) (x : D) :
    ((autRestrict K' h τ x : D) : Ω) = ((τ x : extendScalars h) : Ω) := rfl

/-- An automorphism acting on `K'_m` as the Frobenius of `K'` acts on `K_{f' m}` as
`Frob_K ^ f'`. -/
theorem resHom_frob_baseChange {D : IntermediateField K Ω} (h : K' ≤ D) {m : ℕ} (hm : 0 < m)
    (hmD : unramifiedOfDegree p K' Ω m ≤ extendScalars h)
    (hKD : unramifiedOfDegree p K Ω (f p K K' * m) ≤ D)
    (τ : extendScalars h ≃ₐ[K'] extendScalars h) (hτ : resHom hmD τ = frobT p K' Ω m) :
    resHom hKD (autRestrict K' h τ) = frobT p K Ω (f p K K' * m) ^ f p K K' := by
  have hfm : 0 < f p K K' * m := Nat.mul_pos f_pos hm
  rw [resHom_eq_iff]
  let φ₁ : unramifiedOfDegree p K Ω (f p K K' * m) →ₐ[K] Ω :=
    D.val.comp ((autRestrict K' h τ).toAlgHom.comp (inclusion hKD))
  let φ₂ : unramifiedOfDegree p K Ω (f p K K' * m) →ₐ[K] Ω :=
    (unramifiedOfDegree p K Ω (f p K K' * m)).val.comp
      (frobT p K Ω (f p K K' * m) ^ f p K K').toAlgHom
  have key : φ₁ = φ₂ := by
    refine algHom_ext_of_eq_adjoin K (unramifiedOfDegree_def p K Ω _) fun z hz ↦ ?_
    rw [mem_rootSet_X_pow_sub_X (one_lt_q_pow hfm)] at hz
    have hzK : z ∈ unramifiedOfDegree p K Ω (f p K K' * m) :=
      mem_unramifiedOfDegree_of_pow_eq hfm hz
    have hzK' : z ∈ unramifiedOfDegree p K' Ω m := unramifiedOfDegree_le_baseChange K' hm hzK
    simp only [φ₁, φ₂, AlgHom.comp_apply, coe_val, AlgEquiv.coe_toAlgHom]
    have h1 := resHom_apply hmD τ ⟨z, hzK'⟩
    rw [hτ, frob_baseChange_apply K' hm _ hz] at h1
    rw [frobT_pow_apply_of_pow_eq hfm _ ⟨z, hzK⟩ hz]
    exact h1.symm
  intro x
  exact DFunLike.congr_fun key x

end PadicField
