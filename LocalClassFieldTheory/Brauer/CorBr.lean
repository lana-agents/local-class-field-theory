/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.Corestriction
import LocalClassFieldTheory.Brauer.Invariant

/-!
# Corestriction of Brauer classes and `inv ∘ cor = inv`

For a finite `K' ⊆ Ω` over `K`, `Gal(Ω/K') ≅ Gal(Ω/K)_{K'}` is an open subgroup of index
`[K' : K]`, and the corestriction of `ContH2` gives `Brauer.corBr K' : Br(K') → Br(K)` with

* `Brauer.corBr_res : cor ∘ res = (·)^{[K':K]}`,
* `PadicField.invEquiv_corBr : inv_K ∘ cor = inv_{K'}` (restriction is surjective since
  `inv_{K'} ∘ res = [K':K] · inv_K` and `ℚ/ℤ` is divisible).
-/

open ContH2 IntermediateField groupCohomology

set_option linter.unusedSectionVars false

namespace Brauer

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (K' : IntermediateField K Ω)

theorem continuous_fixingSubgroupEquiv [Algebra.IsIntegral K Ω] [FiniteDimensional K K'] :
    Continuous (fixingSubgroupEquiv K') := by
  refine continuous_of_continuousAt_one (fixingSubgroupEquiv K').toMonoidHom ?_
  intro V hV
  rw [map_one] at hV
  obtain ⟨E', hE', hE'V⟩ := (krullTopology_mem_nhds_one_iff K' Ω V).1 hV
  haveI : FiniteDimensional K (E'.restrictScalars K) := by
    have : FiniteDimensional K E' := Module.Finite.trans K' E'
    exact this
  rw [Filter.mem_map]
  have hopen := (E'.restrictScalars K).fixingSubgroup_isOpen
  refine Filter.mem_of_superset
    ((continuous_subtype_val.isOpen_preimage _ hopen).mem_nhds
      (show (1 : Ω ≃ₐ[K] Ω) ∈ (E'.restrictScalars K).fixingSubgroup from Subgroup.one_mem _))
    fun k hk => hE'V ?_
  rw [Set.mem_preimage, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hk
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact hk x hx

theorem continuous_fixingSubgroupEquiv_symm [Algebra.IsIntegral K Ω] :
    Continuous (fixingSubgroupEquiv K').symm :=
  (continuous_resScalars K').subtype_mk _

/-- `Br(K') ≃ H²(Gal(Ω/K)_{K'}, Ωˣ)`. -/
noncomputable def brFixingEquiv [Algebra.IsIntegral K Ω] [FiniteDimensional K K'] :
    Br K' Ω ≃* ContH2 K'.fixingSubgroup Ωˣ :=
  ContH2.mapEquiv (fixingSubgroupEquiv K') (continuous_fixingSubgroupEquiv K')
    (continuous_fixingSubgroupEquiv_symm K') (fun _ _ => rfl)

variable [IsGalois K Ω] [FiniteDimensional K K']

theorem index_fixingSubgroup : K'.fixingSubgroup.index = Module.finrank K K' :=
  (IntermediateField.finrank_eq_fixingSubgroup_index K').symm

instance : K'.fixingSubgroup.FiniteIndex :=
  ⟨by rw [index_fixingSubgroup]; exact Module.finrank_pos.ne'⟩

noncomputable instance : Fintype ((Ω ≃ₐ[K] Ω) ⧸ K'.fixingSubgroup) :=
  have : Finite ((Ω ≃ₐ[K] Ω) ⧸ K'.fixingSubgroup) := Subgroup.finite_quotient_of_finiteIndex
  Fintype.ofFinite _

theorem card_quotient_fixingSubgroup :
    Fintype.card ((Ω ≃ₐ[K] Ω) ⧸ K'.fixingSubgroup) = Module.finrank K K' := by
  rw [← Nat.card_eq_fintype_card, ← Subgroup.index, index_fixingSubgroup]

/-- **Corestriction** `Br(K') → Br(K)`. -/
noncomputable def corBr : Br K' Ω →* Br K Ω :=
  (ContH2.cor K'.fixingSubgroup K'.fixingSubgroup_isOpen).comp
    (brFixingEquiv K').toMonoidHom

theorem brFixingEquiv_res (α : Br K Ω) :
    brFixingEquiv K' (res K' α) =
      ContH2.map K'.fixingSubgroup.subtype continuous_subtype_val (MonoidHom.id Ωˣ)
        (fun _ _ => rfl) α := by
  induction α using ContH2.induction_on with | h E => ?_
  rfl

/-- **`cor ∘ res = (·)^{[K' : K]}`**. -/
theorem corBr_res (α : Br K Ω) : corBr K' (res K' α) = α ^ Module.finrank K K' := by
  rw [corBr, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, brFixingEquiv_res, ContH2.cor_res,
    card_quotient_fixingSubgroup]

end Brauer

namespace PadicField

open Brauer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

theorem exists_nsmul_eq_QZ {N : ℕ} (hN : 0 < N) (x : QZ) : ∃ y : QZ, N • y = x := by
  obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨((q / N : ℚ) : QZ), ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (by exact_mod_cast hN.ne')]

variable (p) in
include hp in
/-- Restriction `Br(K) → Br(K')` is surjective. -/
theorem res_surjective (K' : IntermediateField K Ω) [FiniteDimensional K K'] :
    Function.Surjective (res (Ω := Ω) K') := by
  intro β
  obtain ⟨y, hy⟩ := exists_nsmul_eq_QZ (Module.finrank_pos (R := K) (M := K'))
    (Multiplicative.toAdd (invEquiv p K' Ω β))
  obtain ⟨α, hα⟩ := (invEquiv p K Ω).surjective (Multiplicative.ofAdd y)
  refine ⟨α, (invEquiv p K' Ω).injective ?_⟩
  rw [invEquiv_res, hα, ← ofAdd_nsmul, hy, ofAdd_toAdd]

/-- **`inv_K ∘ cor = inv_{K'}`**. -/
theorem invEquiv_corBr (K' : IntermediateField K Ω) [FiniteDimensional K K'] (β : Br K' Ω) :
    invEquiv p K Ω (corBr K' β) = invEquiv p K' Ω β := by
  obtain ⟨α, rfl⟩ := res_surjective p K' β
  rw [corBr_res, map_pow, invEquiv_res]

end PadicField
