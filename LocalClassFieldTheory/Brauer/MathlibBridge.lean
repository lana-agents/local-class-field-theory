/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.ContH2

/-!
# Comparison with Mathlib's group cohomology

For a discrete group `G` (all cochains are locally constant) acting on a commutative group `M`,
`ContH2 G M` is Mathlib's `groupCohomology.H2` of the representation
`Rep.ofMulDistribMulAction G M` (`ContH2.addEquivH2`, for `G M : Type`, the universe of
`Rep.ofMulDistribMulAction`).
-/

open groupCohomology CategoryTheory

namespace ContH2

variable {G M : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G] [CommGroup M]
  [MulDistribMulAction G M]

/-- The comparison map on cocycles. -/
noncomputable def toH2Cocycles :
    cocycles G M →* Multiplicative (H2 (Rep.ofMulDistribMulAction G M)) where
  toFun f := Multiplicative.ofAdd (H2π _ (cocyclesOfIsMulCocycle₂ (isMulCocycle₂ f)))
  map_one' := by
    rw [← ofAdd_zero, ← map_zero (H2π (Rep.ofMulDistribMulAction G M)).hom]
    congr 2
  map_mul' f f' := by
    rw [← ofAdd_add, ← map_add (H2π (Rep.ofMulDistribMulAction G M)).hom]
    congr 2

/-- `ContH2 G M → H²(G, M)` (Mathlib). -/
noncomputable def toH2 : ContH2 G M →* Multiplicative (H2 (Rep.ofMulDistribMulAction G M)) :=
  QuotientGroup.lift _ toH2Cocycles (by
    rintro f ⟨x, -, hxf⟩
    rw [MonoidHom.mem_ker, toH2Cocycles, MonoidHom.coe_mk, OneHom.coe_mk, ← ofAdd_zero,
      Multiplicative.ofAdd.apply_eq_iff_eq, H2π_eq_zero_iff]
    refine ⟨x, ?_⟩
    funext gh
    exact congrFun hxf gh)

theorem toH2_bijective : Function.Bijective (toH2 (G := G) (M := M)) := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro α hα
    induction α using induction_on with | h f => ?_
    rw [MonoidHom.mem_ker] at hα
    have h' : (H2π (Rep.ofMulDistribMulAction G M)) (cocyclesOfIsMulCocycle₂ (isMulCocycle₂ f)) =
        0 := congrArg Multiplicative.toAdd hα
    rw [H2π_eq_zero_iff] at h'
    obtain ⟨x, hx⟩ := isMulCoboundary₂_of_mem_coboundaries₂ _ h'
    rw [Subgroup.mem_bot, mk_eq_one_iff]
    exact ⟨x, IsLocallyConstant.of_discrete _, funext fun gh => hx gh.1 gh.2⟩
  · have key : ∀ z : H2 (Rep.ofMulDistribMulAction G M),
        ∃ a, toH2 a = Multiplicative.ofAdd z := by
      intro z
      induction z using H2_induction_on with | h x => ?_
      refine ⟨mk (mkCocycle _ (IsLocallyConstant.of_discrete _)
        (isMulCocycle₂_of_mem_cocycles₂ (G := G) (M := M) x.1 x.2)), ?_⟩
      rfl
    intro y
    exact key (Multiplicative.toAdd y)

/-- **`ContH2 G M` is Mathlib's `H²`** for discrete `G`. -/
noncomputable def addEquivH2 : Additive (ContH2 G M) ≃+ H2 (Rep.ofMulDistribMulAction G M) :=
  (MulEquiv.ofBijective _ toH2_bijective).toAdditive

theorem addEquivH2_mk (f : cocycles G M) :
    addEquivH2 (Additive.ofMul (mk f)) = H2π _ (cocyclesOfIsMulCocycle₂ (isMulCocycle₂ f)) := rfl

end ContH2
