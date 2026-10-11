/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.Unramified

/-!
# Galois groups, inertia and Frobenius

Let `L/K` be a finite Galois extension of fields finite over `ℚ_[p]`.

* `PadicField.residueGal : Gal(L/K) →* Gal(𝓴 L/𝓴 K)` is surjective
  (`PadicField.residueGal_surjective`), with kernel the inertia group
  `PadicField.inertia p K L` (`PadicField.ker_residueGal`).
* If `L/K` is unramified, `residueGal` is an isomorphism (`PadicField.residueGalEquiv`); the
  arithmetic Frobenius `PadicField.frob p K L` is the unique `σ` with `σ x ≡ x ^ q (mod 𝔪_L)`
  (`PadicField.frob_spec`, `PadicField.eq_frob_iff`), and it generates `Gal(L/K)`, which is
  therefore cyclic of order `[L : K]` (`PadicField.orderOf_frob`).
-/

open Polynomial IsLocalRing
open scoped Pointwise

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L]

namespace Integers

omit [FiniteDimensional ℚ_[p] K] in
theorem smul_maximalIdeal (σ : L ≃ₐ[K] L) :
    σ • maximalIdeal (𝒪 p L) = maximalIdeal (𝒪 p L) := by
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_maximalIdeal_iff, mem_maximalIdeal_iff,
    coe_smul, nrm_algEquiv_tower]

omit [FiniteDimensional ℚ_[p] K] in
theorem stabilizer_eq_top : MulAction.stabilizer (L ≃ₐ[K] L) (maximalIdeal (𝒪 p L)) = ⊤ :=
  eq_top_iff.2 fun σ _ ↦ smul_maximalIdeal σ

instance isInvariant [IsGalois K L] : Algebra.IsInvariant (𝒪 p K) (𝒪 p L) (L ≃ₐ[K] L) where
  isInvariant x hx := by
    haveI := finiteDimensional_tower (p := p) K L
    have hfix : (x : L) ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) := by
      rintro ⟨σ, -⟩
      exact congrArg (fun y : 𝒪 p L ↦ (y : L)) (hx σ)
    rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at hfix
    obtain ⟨a, ha⟩ := hfix
    have ha1 : nrm p K a ≤ 1 := by
      rw [← nrm_algebraMap_tower (L := L), ha]; exact nrm_coe_le_one x
    exact ⟨mk a ha1, ext ha⟩

end Integers

variable (p K L) in
/-- The inertia group of `L/K`. -/
noncomputable def inertia : Subgroup (L ≃ₐ[K] L) :=
  (maximalIdeal (𝒪 p L)).toAddSubgroup.inertia (L ≃ₐ[K] L)

omit [FiniteDimensional ℚ_[p] K] in
theorem mem_inertia_iff (σ : L ≃ₐ[K] L) :
    σ ∈ inertia p K L ↔ ∀ x : 𝒪 p L, σ • x - x ∈ maximalIdeal (𝒪 p L) := Iff.rfl

/-- The map from `Gal(L/K)` into the stabiliser of `𝔪_L`, which is everything. -/
noncomputable def toStabilizer : (L ≃ₐ[K] L) →* MulAction.stabilizer (L ≃ₐ[K] L) (maximalIdeal (𝒪 p L)) where
  toFun σ := ⟨σ, Integers.smul_maximalIdeal σ⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable (p K L) in
/-- The action of `Gal(L/K)` on the residue field. -/
noncomputable def residueGal : (L ≃ₐ[K] L) →* (𝓴 p L ≃ₐ[𝓴 p K] 𝓴 p L) :=
  (Ideal.Quotient.stabilizerHom (maximalIdeal (𝒪 p L)) (maximalIdeal (𝒪 p K))
    (L ≃ₐ[K] L)).comp toStabilizer

theorem residueGal_residue (σ : L ≃ₐ[K] L) (x : 𝒪 p L) :
    residueGal p K L σ (residue _ x) = residue _ (σ • x) := rfl

theorem residueGal_surjective [IsGalois K L] : Function.Surjective (residueGal p K L) := by
  haveI := finiteDimensional_tower (p := p) K L
  haveI : Finite (L ≃ₐ[K] L) := inferInstance
  intro τ
  obtain ⟨⟨σ, hσ⟩, h⟩ := Ideal.Quotient.stabilizerHom_surjective (L ≃ₐ[K] L)
    (maximalIdeal (𝒪 p K)) (maximalIdeal (𝒪 p L)) τ
  exact ⟨σ, h⟩

theorem ker_residueGal : (residueGal p K L).ker = inertia p K L := by
  ext σ
  rw [MonoidHom.mem_ker, mem_inertia_iff]
  constructor
  · intro hσ x
    have := congrArg (fun τ : 𝓴 p L ≃ₐ[𝓴 p K] 𝓴 p L ↦ τ (residue _ x)) hσ
    simp only [residueGal_residue, AlgEquiv.one_apply] at this
    rw [← residue_eq_zero_iff, map_sub, this, sub_self]
  · intro hσ
    ext y
    obtain ⟨x, rfl⟩ := residue_surjective y
    rw [residueGal_residue, AlgEquiv.one_apply, eq_comm, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff, ← neg_mem_iff, neg_sub]
    exact hσ x

theorem card_gal_residue : Nat.card (𝓴 p L ≃ₐ[𝓴 p K] 𝓴 p L) = f p K L := by
  classical
  haveI := Fintype.ofFinite (𝓴 p K)
  rw [← Nat.card_fin (f p K L)]
  exact (Nat.card_eq_of_bijective _
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (𝓴 p K) (𝓴 p L))).symm

section Unramified

variable (h : IsUnramified p K L)
include h

theorem residueGal_bijective : Function.Bijective (residueGal p K L) := by
  haveI := isGalois_of_isUnramified h
  haveI := finiteDimensional_tower (p := p) K L
  refine residueGal_surjective.bijective_of_nat_card_le ?_
  rw [card_gal_residue, h.f_eq, IsGalois.card_aut_eq_finrank]

/-- For unramified `L/K`, `Gal(L/K) ≃ Gal(𝓴 L/𝓴 K)`. -/
noncomputable def residueGalEquiv : (L ≃ₐ[K] L) ≃* (𝓴 p L ≃ₐ[𝓴 p K] 𝓴 p L) :=
  MulEquiv.ofBijective (residueGal p K L) (residueGal_bijective h)

theorem inertia_eq_bot : inertia p K L = ⊥ := by
  rw [← ker_residueGal, MonoidHom.ker_eq_bot_iff]
  exact (residueGal_bijective h).1

/-- The arithmetic Frobenius of an unramified extension. -/
noncomputable def frob : L ≃ₐ[K] L := by
  classical
  haveI := Fintype.ofFinite (𝓴 p K)
  exact (residueGalEquiv h).symm (FiniteField.frobeniusAlgEquivOfAlgebraic (𝓴 p K) (𝓴 p L))

theorem residueGal_frob (y : 𝓴 p L) : residueGal p K L (frob h) y = y ^ q p K := by
  classical
  haveI := Fintype.ofFinite (𝓴 p K)
  change residueGalEquiv h (frob h) y = _
  rw [frob, MulEquiv.apply_symm_apply, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, q]
  simp only [Fintype.card_eq_nat_card]

/-- The defining property of the arithmetic Frobenius: `σ x ≡ x ^ q (mod 𝔪_L)`. -/
theorem frob_spec (x : 𝒪 p L) : frob h • x - x ^ q p K ∈ maximalIdeal (𝒪 p L) := by
  rw [← residue_eq_zero_iff, map_sub, ← residueGal_residue, residueGal_frob, map_pow, sub_self]

/-- Uniqueness of the arithmetic Frobenius. -/
theorem eq_frob_iff (σ : L ≃ₐ[K] L) :
    σ = frob h ↔ ∀ x : 𝒪 p L, σ • x - x ^ q p K ∈ maximalIdeal (𝒪 p L) := by
  refine ⟨fun hσ ↦ hσ ▸ frob_spec h, fun hσ ↦ (residueGal_bijective h).1 ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := residue_surjective y
  rw [residueGal_frob, residueGal_residue, ← map_pow, ← sub_eq_zero, ← map_sub,
    residue_eq_zero_iff]
  exact hσ x

theorem orderOf_frob : orderOf (frob h) = Module.finrank K L := by
  classical
  haveI := Fintype.ofFinite (𝓴 p K)
  rw [← h.f_eq, f, ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (𝓴 p K) (𝓴 p L),
    frob, MulEquiv.orderOf_eq]
  congr
  exact Subsingleton.elim _ _

theorem zpowers_frob : Subgroup.zpowers (frob h) = ⊤ := by
  haveI := isGalois_of_isUnramified h
  haveI := finiteDimensional_tower (p := p) K L
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, orderOf_frob, IsGalois.card_aut_eq_finrank]

theorem isCyclic_gal : IsCyclic (L ≃ₐ[K] L) :=
  ⟨⟨frob h, fun σ ↦ by
    have : σ ∈ Subgroup.zpowers (frob h) := (zpowers_frob h).symm ▸ Subgroup.mem_top σ
    exact this⟩⟩

end Unramified

end PadicField
