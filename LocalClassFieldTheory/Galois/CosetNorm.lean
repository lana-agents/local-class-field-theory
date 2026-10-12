/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Norms as products over coset representatives

Let `F / K` be a finite Galois extension and `E` an intermediate field. The norm `N_{E/K}(y)` of
`y ∈ E` is the product of the conjugates `τ y` over all `K`-embeddings `τ : E → F`
(`IntermediateField.algebraMap_norm_eq_prod_algHom`). Since every such embedding is the
restriction of an automorphism of `F`, uniquely determined modulo `Gal(F/E)`, we get
`N_{E/K}(y) = ∏_{r ∈ R} r y` for any set `R` of left coset representatives of `Gal(F/E)` in
`Gal(F/K)`.

## Main results

* `IntermediateField.algebraMap_norm_eq_prod_algHom`: `N_{E/K}(y) = ∏_{τ : E → F} τ y`.
* `IntermediateField.bijOn_restrict_of_bijOn_mk`: a set of left coset representatives of
  `E.fixingSubgroup` maps bijectively onto `E →ₐ[K] F` by restriction.
* `IntermediateField.algebraMap_norm_eq_prod_of_bijOn`: `N_{E/K}(y) = ∏_{r ∈ R} r y`.
* `IntermediateField.algebraMap_norm_eq_prod_of_fixedField`: the same for `E = fixedField H`
  and `R` a set of representatives of `Gal(F/K) ⧸ H`.
* `Subgroup.bijOn_mk_of_injOn_of_card_eq`: an injective-mod-`H` finset of `H.index` elements is a
  set of representatives.
-/

open Polynomial

namespace Subgroup

/-- A finset of `H.index` elements which are pairwise distinct modulo `H` is a set of left coset
representatives. -/
theorem bijOn_mk_of_injOn_of_card_eq {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    {R : Finset G} (hinj : Set.InjOn (QuotientGroup.mk : G → G ⧸ H) R)
    (hcard : R.card = H.index) :
    Set.BijOn (QuotientGroup.mk : G → G ⧸ H) R Set.univ := by
  classical
  refine ⟨Set.mapsTo_univ _ _, hinj, ?_⟩
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have himg : R.image (QuotientGroup.mk : G → G ⧸ H) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, hcard, Subgroup.index, Nat.card_eq_fintype_card]
  intro x _
  have hx : x ∈ R.image (QuotientGroup.mk : G → G ⧸ H) := himg ▸ Finset.mem_univ x
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
  exact ⟨r, hr, rfl⟩

end Subgroup

namespace IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (E : IntermediateField K F)

/-- The restriction of an automorphism of `F` to an intermediate field `E`, as an embedding. -/
def restrictAlgHom (σ : F ≃ₐ[K] F) : E →ₐ[K] F := (σ : F →ₐ[K] F).comp E.val

@[simp]
theorem restrictAlgHom_apply (σ : F ≃ₐ[K] F) (y : E) : E.restrictAlgHom σ y = σ (y : F) := rfl

theorem restrictAlgHom_eq_iff (σ τ : F ≃ₐ[K] F) :
    E.restrictAlgHom σ = E.restrictAlgHom τ ↔
      (QuotientGroup.mk σ : (F ≃ₐ[K] F) ⧸ E.fixingSubgroup) = QuotientGroup.mk τ := by
  rw [QuotientGroup.eq, mem_fixingSubgroup_iff]
  constructor
  · intro h x hx
    have := DFunLike.congr_fun h ⟨x, hx⟩
    simp only [restrictAlgHom_apply] at this
    rw [AlgEquiv.mul_apply, ← this, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  · intro h
    ext y
    have := h y y.2
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at this
    simp only [restrictAlgHom_apply]
    exact this.symm

/-- Every `K`-embedding of `E` into a normal extension `F` is the restriction of an automorphism
of `F`. -/
theorem exists_restrictAlgHom_eq [Normal K F] (τ : E →ₐ[K] F) :
    ∃ σ : F ≃ₐ[K] F, E.restrictAlgHom σ = τ :=
  ⟨AlgEquiv.ofBijective (τ.liftNormal F) (Algebra.IsAlgebraic.algHom_bijective _), by
    ext y; exact τ.liftNormal_commutes F y⟩

/-- A set of left coset representatives of `Gal(F/E)` maps bijectively onto the `K`-embeddings
`E → F` by restriction. -/
theorem bijOn_restrict_of_bijOn_mk [Normal K F] {R : Set (F ≃ₐ[K] F)}
    (hR : Set.BijOn (QuotientGroup.mk : _ → (F ≃ₐ[K] F) ⧸ E.fixingSubgroup) R Set.univ) :
    Set.BijOn E.restrictAlgHom R Set.univ := by
  refine ⟨Set.mapsTo_univ _ _, fun r hr s hs h ↦ hR.injOn hr hs
    ((E.restrictAlgHom_eq_iff r s).1 h), fun τ _ ↦ ?_⟩
  obtain ⟨σ, rfl⟩ := E.exists_restrictAlgHom_eq τ
  obtain ⟨r, hr, hrσ⟩ := hR.surjOn (Set.mem_univ (QuotientGroup.mk σ))
  exact ⟨r, hr, (E.restrictAlgHom_eq_iff r σ).2 hrσ⟩

variable [FiniteDimensional K F] [IsGalois K F]

/-- For `F / K` finite Galois and `E` an intermediate field, the composition with an embedding of
`F` into an algebraically closed field is a bijection on `K`-embeddings of `E`. -/
theorem bijective_comp_algHom {A : Type*} [Field A] [Algebra K A] [IsAlgClosed A]
    (ι : F →ₐ[K] A) : Function.Bijective fun τ : E →ₐ[K] F ↦ ι.comp τ := by
  haveI : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E F
  have hinj : Function.Injective fun τ : E →ₐ[K] F ↦ ι.comp τ := fun τ₁ τ₂ h ↦ by
    ext y
    exact ι.injective (DFunLike.congr_fun h y)
  refine hinj.bijective_of_nat_card_le ?_
  have h1 : Field.finSepDegree K E = Nat.card (E →ₐ[K] F) :=
    Field.finSepDegree_eq_of_adjoin_splits K E F (adjoin_univ K E) fun s _ ↦
      ⟨Algebra.IsIntegral.isIntegral s, by
        rw [minpoly_eq]; exact Normal.splits inferInstance (s : F)⟩
  rw [← h1, Field.finSepDegree_eq_of_isAlgClosed K E A]

/-- For `F / K` finite Galois, the norm of `y ∈ E` is the product of its images under all
`K`-embeddings `E → F`. -/
theorem algebraMap_norm_eq_prod_algHom [Fintype (E →ₐ[K] F)] (y : E) :
    algebraMap K F (Algebra.norm K y) = ∏ τ : E →ₐ[K] F, τ y := by
  haveI : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E F
  let ι := IsScalarTower.toAlgHom K F (AlgebraicClosure F)
  apply (algebraMap F (AlgebraicClosure F)).injective
  rw [map_prod, ← IsScalarTower.algebraMap_apply, Algebra.norm_eq_prod_embeddings]
  exact (Fintype.prod_bijective _ (E.bijective_comp_algHom ι) _ _ fun τ ↦ rfl).symm

/-- **Norms as products over coset representatives.** If `R` is a set of left coset
representatives of `Gal(F/E)` in `Gal(F/K)`, then `N_{E/K}(y) = ∏_{r ∈ R} r y`. -/
theorem algebraMap_norm_eq_prod_of_bijOn {R : Finset (F ≃ₐ[K] F)}
    (hR : Set.BijOn (QuotientGroup.mk : _ → (F ≃ₐ[K] F) ⧸ E.fixingSubgroup) R Set.univ)
    (y : E) : algebraMap K F (Algebra.norm K y) = ∏ r ∈ R, r (y : F) := by
  classical
  haveI : Fintype (E →ₐ[K] F) := Fintype.ofFinite _
  have h := E.bijOn_restrict_of_bijOn_mk hR
  rw [E.algebraMap_norm_eq_prod_algHom y]
  symm
  refine Finset.prod_nbij E.restrictAlgHom (fun _ _ ↦ Finset.mem_univ _) h.injOn
    (by rw [Finset.coe_univ]; exact h.surjOn) fun r _ ↦ rfl

/-- **Norms as products over coset representatives**, for `E` the fixed field of a subgroup `H`:
if `R` maps bijectively onto `Gal(F/K) ⧸ H`, then `N_{E/K}(y) = ∏_{r ∈ R} r y`. (This applies
in particular when `Gal(F/K)` is abelian, where left and right cosets agree.) -/
theorem algebraMap_norm_eq_prod_of_fixedField (H : Subgroup (F ≃ₐ[K] F))
    {R : Finset (F ≃ₐ[K] F)}
    (hR : Set.BijOn (QuotientGroup.mk : _ → (F ≃ₐ[K] F) ⧸ H) R Set.univ)
    (y : fixedField H) : algebraMap K F (Algebra.norm K y) = ∏ r ∈ R, r (y : F) := by
  refine (fixedField H).algebraMap_norm_eq_prod_of_bijOn ?_ y
  rwa [fixingSubgroup_fixedField]

/-- Variant of `algebraMap_norm_eq_prod_of_fixedField` with the hypothesis that `R` has
`[Gal(F/K) : H]` elements, pairwise distinct modulo `H`. -/
theorem algebraMap_norm_eq_prod_of_injOn (H : Subgroup (F ≃ₐ[K] F)) {R : Finset (F ≃ₐ[K] F)}
    (hinj : Set.InjOn (QuotientGroup.mk : _ → (F ≃ₐ[K] F) ⧸ H) R) (hcard : R.card = H.index)
    (y : fixedField H) : algebraMap K F (Algebra.norm K y) = ∏ r ∈ R, r (y : F) :=
  algebraMap_norm_eq_prod_of_fixedField H (Subgroup.bijOn_mk_of_injOn_of_card_eq hinj hcard) y

end IntermediateField
