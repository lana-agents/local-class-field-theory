/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.FieldNorm

/-!
# Towers and intermediate fields

* Intermediate fields of an extension of fields finite over `ℚ_[p]` are again finite over `ℚ_[p]`
  (instances), so the whole theory applies to them.
* Multiplicativity of `e` and `f` in towers `K ⊆ E ⊆ L`.
* If every residue class of `L` is represented in `E`, then `f(L/E) = 1`.
-/

open IsLocalRing

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]

section IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] (E : IntermediateField K L)

instance intermediateField_isScalarTower_top : IsScalarTower ℚ_[p] E L :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply ℚ_[p] K L, IsScalarTower.algebraMap_apply ℚ_[p] K E]
    rfl

instance intermediateField_finiteDimensional [FiniteDimensional ℚ_[p] L] :
    FiniteDimensional ℚ_[p] E :=
  Module.Finite.of_injective ((IsScalarTower.toAlgHom ℚ_[p] E L).toLinearMap)
    (algebraMap E L).injective

end IntermediateField

section TowerTypes

variable {K E L : Type*} [Field K] [Field E] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] E]
  [Algebra ℚ_[p] L] [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower ℚ_[p] K E]
  [IsScalarTower ℚ_[p] E L] [IsScalarTower ℚ_[p] K L] [IsScalarTower K E L]

instance integers_isScalarTower [Algebra.IsAlgebraic ℚ_[p] K] [Algebra.IsAlgebraic ℚ_[p] E]
    [Algebra.IsAlgebraic ℚ_[p] L] : IsScalarTower (𝒪 p K) (𝒪 p E) (𝒪 p L) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ Integers.ext <| by
    simp only [Integers.coe_algebraMap]
    exact IsScalarTower.algebraMap_apply K E L _

variable [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] L]

theorem f_mul_f : f p K E * f p E L = f p K L := by
  haveI := finiteDimensional_tower (p := p) K E
  haveI := finiteDimensional_tower (p := p) E L
  exact Module.finrank_mul_finrank (𝓴 p K) (𝓴 p E) (𝓴 p L)

theorem e_mul_e : e p K E * e p E L = e p K L := by
  have h := v_algebraMap (p := p) (K := E) (L := L) (algebraMap K E (uniformizer p K))
  rw [← IsScalarTower.algebraMap_apply, v_algebraMap_uniformizer,
    v_algebraMap_uniformizer] at h
  exact_mod_cast (h.trans (mul_comm _ _)).symm

/-- If the residue map `𝓴 E → 𝓴 L` is surjective then `f(L/E) = 1`. -/
theorem f_eq_one_of_forall_exists
    (h : ∀ y : 𝒪 p L, ∃ x : 𝒪 p E, y - algebraMap (𝒪 p E) (𝒪 p L) x ∈ maximalIdeal (𝒪 p L)) :
    f p E L = 1 := by
  have hsurj : Function.Surjective (algebraMap (𝓴 p E) (𝓴 p L)) := by
    intro b
    obtain ⟨y, rfl⟩ := residue_surjective b
    obtain ⟨x, hx⟩ := h y
    refine ⟨residue _ x, ?_⟩
    rw [ResidueField.algebraMap_residue, eq_comm, ← sub_eq_zero, ← map_sub]
    exact (residue_eq_zero_iff _).2 hx
  have hbij : Function.Bijective (algebraMap (𝓴 p E) (𝓴 p L)) :=
    ⟨(algebraMap (𝓴 p E) (𝓴 p L)).injective, hsurj⟩
  have e := (AlgEquiv.ofBijective (Algebra.ofId (𝓴 p E) (𝓴 p L)) hbij).toLinearEquiv
  rw [f, ← e.finrank_eq, Module.finrank_self]

end TowerTypes

end PadicField
