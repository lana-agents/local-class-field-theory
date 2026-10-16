/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.ShapiroOpen
import LocalClassFieldTheory.Duality.Statements
import LocalClassFieldTheory.Brauer.CorBr

/-!
# Shapiro's lemma for `G_K` and the Euler characteristic of coinduced modules

Let `K'/K` be a finite extension inside `Ω`, `H = Gal(Ω/K') ≤ G_K = Gal(Ω/K)` (an open subgroup
of index `[K' : K]`) and `A` a finite discrete `G_K`-module. Shapiro's lemma
(`LocalClassFieldTheory.Duality.ShapiroOpen`) gives

`#Hⁱ(K, CoInd_H A) = #Hⁱ(K', A)` for `i = 0, 1, 2`

(**`PadicField.card_h0_coInd`**, **`PadicField.card_h1_coInd`**, **`PadicField.card_h2_coInd`**),
where `Gal(Ω/K')` acts on `A` through `Gal(Ω/K') ≅ H` (`IntermediateField.fixingSubgroupEquiv`).
Since `#CoInd_H A = #A^{[K':K]}` and `[K' : ℚ_p] = [K' : K] [K : ℚ_p]`, the two sides of the
Euler characteristic formula correspond:

* **`PadicField.eulerCharacteristicFor_coInd_iff`** : the local Euler characteristic formula holds
  for `CoInd_H A` over `K` iff it holds for `A` over `K'`.

Generic transport lemmas: `ContH2.CoInd.card_h0_eq`, `card_h1_eq`, `card_h2_eq` (abstract
Shapiro), `Brauer.card_h0_of_equiv`, `Brauer.card_h1_of_equiv`, `Brauer.card_h2_of_equiv`
(isomorphisms of topological groups compatible with the actions).
-/

open groupCohomology Brauer

set_option linter.unusedSectionVars false

namespace ContH2.CoInd

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CommGroup A]
  [MulDistribMulAction G A] (H : Subgroup G) [Finite (G ⧸ H)] (hH : IsOpen (H : Set G))

theorem card_h0_eq : Nat.card (H0 G (CoInd H A)) = Nat.card (H0 H A) :=
  Nat.card_congr (Equiv.ofBijective _ (shapiro0_bijective H))

include hH in
theorem card_h2_eq : Nat.card (ContH2 G (CoInd H A)) = Nat.card (ContH2 H A) :=
  Nat.card_congr (Equiv.ofBijective _ (shapiro2_bijective H hH))

variable [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalGroup A]

include hH in
theorem card_h1_eq : Nat.card (ContH1 G (CoInd H A)) = Nat.card (ContH1 H A) :=
  Nat.card_congr (Equiv.ofBijective _ (shapiro1_bijective H hH))

theorem card_coInd [Fintype (G ⧸ H)] [Finite A] :
    Nat.card (CoInd H A) = Nat.card A ^ Fintype.card (G ⧸ H) := by
  rw [show Nat.card (CoInd H A) = Nat.card (G ⧸ H → A) from rfl, Nat.card_fun,
    Nat.card_eq_fintype_card (α := G ⧸ H)]

end ContH2.CoInd

namespace Brauer

/-! ### Transport along isomorphisms of topological groups -/

section Transport

variable {G G' A : Type*} [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G']
  [CommGroup A] [MulDistribMulAction G A] [MulDistribMulAction G' A]
  (e : G' ≃* G) (h : ∀ (g : G') (m : A), e g • m = g • m)

include h in
theorem h0_eq_of_equiv : (H0 G' A : Set A) = H0 G A := by
  ext m
  constructor
  · intro hm g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [h]
    exact hm g'
  · intro hm g'
    rw [← h]
    exact hm (e g')

include h in
theorem card_h0_of_equiv : Nat.card (H0 G' A) = Nat.card (H0 G A) := by
  change Nat.card ((H0 G' A : Set A)) = Nat.card ((H0 G A : Set A))
  rw [h0_eq_of_equiv e h]

variable (he : Continuous e) (he' : Continuous e.symm)

include he he' h in
theorem card_h2_of_equiv : Nat.card (ContH2 G' A) = Nat.card (ContH2 G A) :=
  (Nat.card_congr (ContH2.mapEquiv e he he' h).toEquiv).symm

variable [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalGroup A]

include he he' h in
theorem card_h1_of_equiv : Nat.card (ContH1 G' A) = Nat.card (ContH1 G A) := by
  have h' : ∀ (g : G) (m : A), e.symm g • m = g • m := fun g m => by
    rw [← h, MulEquiv.apply_symm_apply]
  let φ : ContH1 G A →* ContH1 G' A :=
    ContH1.map (e : G' →* G) he (MonoidHom.id A) continuous_id fun g m => h g m
  let ψ : ContH1 G' A →* ContH1 G A :=
    ContH1.map (e.symm : G →* G') he' (MonoidHom.id A) continuous_id fun g m => h' g m
  have hl : ∀ x, ψ (φ x) = x := by
    intro x
    induction x using ContH1.induction_on with | h c => ?_
    simp only [φ, ψ, ContH1.map_mk]
    congr 1
    exact Subtype.ext (funext fun g => by simp)
  have hr : ∀ x, φ (ψ x) = x := by
    intro x
    induction x using ContH1.induction_on with | h c => ?_
    simp only [φ, ψ, ContH1.map_mk]
    congr 1
    exact Subtype.ext (funext fun g => by simp)
  exact Nat.card_congr ⟨ψ, φ, hr, hl⟩

end Transport

end Brauer

namespace PadicField

open ContH2

variable (p : ℕ) [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

section CoInd

variable (K' : IntermediateField K Ω) [FiniteDimensional K K']
variable {A : Type*} [CommGroup A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [IsTopologicalGroup A] [MulDistribMulAction (Ω ≃ₐ[K] Ω) A] [SmoothAction (Ω ≃ₐ[K] Ω) A]
  [MulDistribMulAction (Ω ≃ₐ[K'] Ω) A]

/-- `H = Gal(Ω/K')` is open of finite index in `G_K`. -/
instance : Finite ((Ω ≃ₐ[K] Ω) ⧸ K'.fixingSubgroup) := Finite.of_fintype _

variable {K'}

/-- `Gal(Ω/K')` acts on `A` through `Gal(Ω/K') ≅ H ≤ G_K`. -/
abbrev ResCompat (K' : IntermediateField K Ω) (A : Type*) [CommGroup A]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) A] [MulDistribMulAction (Ω ≃ₐ[K'] Ω) A] : Prop :=
  ∀ (σ : K'.fixingSubgroup) (a : A), IntermediateField.fixingSubgroupEquiv K' σ • a = σ • a

/-- Restriction `Gal(Ω/K') → Gal(Ω/K)`, an isomorphism onto `H = Gal(Ω/K)_{K'}`. -/
noncomputable def galRes (K' : IntermediateField K Ω) : (Ω ≃ₐ[K'] Ω) →* (Ω ≃ₐ[K] Ω) :=
  K'.fixingSubgroup.subtype.comp (IntermediateField.fixingSubgroupEquiv K').symm.toMonoidHom

theorem continuous_galRes (K' : IntermediateField K Ω) : Continuous (galRes K') :=
  continuous_subtype_val.comp (continuous_fixingSubgroupEquiv_symm K')

/-- The action of `Gal(Ω/K')` on a `G_K`-module by restriction. -/
@[reducible]
noncomputable def resAction (K' : IntermediateField K Ω) (B : Type*) [CommGroup B]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) B] : MulDistribMulAction (Ω ≃ₐ[K'] Ω) B :=
  MulDistribMulAction.compHom B (galRes K')

theorem resCompat_resAction (K' : IntermediateField K Ω) (B : Type*) [CommGroup B]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) B] :
    letI := resAction K' B
    ResCompat K' B := by
  intro σ a
  change galRes K' _ • a = (σ : Ω ≃ₐ[K] Ω) • a
  simp [galRes]

theorem smoothAction_resAction (K' : IntermediateField K Ω) (B : Type*) [CommGroup B]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) B] [SmoothAction (Ω ≃ₐ[K] Ω) B] :
    @SmoothAction (Ω ≃ₐ[K'] Ω) B _ (resAction K' B).toSMul :=
  @SmoothAction.mk (Ω ≃ₐ[K'] Ω) B _ (resAction K' B).toSMul fun b =>
    (SmoothAction.isLocallyConstant_smul (G := Ω ≃ₐ[K] Ω) b).comp_continuous (continuous_galRes K')

variable (hA : ResCompat K' A)

include hA in
theorem card_h0_coInd :
    Nat.card (H0 (Ω ≃ₐ[K] Ω) (CoInd K'.fixingSubgroup A)) = Nat.card (H0 (Ω ≃ₐ[K'] Ω) A) := by
  rw [CoInd.card_h0_eq, card_h0_of_equiv (IntermediateField.fixingSubgroupEquiv K') hA]

include hA in
theorem card_h1_coInd :
    Nat.card (ContH1 (Ω ≃ₐ[K] Ω) (CoInd K'.fixingSubgroup A)) =
      Nat.card (ContH1 (Ω ≃ₐ[K'] Ω) A) := by
  rw [CoInd.card_h1_eq _ K'.fixingSubgroup_isOpen,
    card_h1_of_equiv (IntermediateField.fixingSubgroupEquiv K') hA
      (continuous_fixingSubgroupEquiv K') (continuous_fixingSubgroupEquiv_symm K')]

include hA in
theorem card_h2_coInd :
    Nat.card (ContH2 (Ω ≃ₐ[K] Ω) (CoInd K'.fixingSubgroup A)) =
      Nat.card (ContH2 (Ω ≃ₐ[K'] Ω) A) := by
  rw [CoInd.card_h2_eq _ K'.fixingSubgroup_isOpen,
    card_h2_of_equiv (IntermediateField.fixingSubgroupEquiv K') hA
      (continuous_fixingSubgroupEquiv K') (continuous_fixingSubgroupEquiv_symm K')]

include hA in
/-- **The Euler characteristic formula and Shapiro's lemma**: the formula holds for the
coinduced module `CoInd_{G_{K'}} A` over `K` iff it holds for `A` over `K'`. -/
theorem eulerCharacteristicFor_coInd_iff :
    EulerCharacteristicFor p K Ω (CoInd K'.fixingSubgroup A) ↔
      EulerCharacteristicFor p K' Ω A := by
  have e1 := card_h1_coInd hA
  have e2 := card_h2_coInd hA
  have hc : padicValNat p (Nat.card (CoInd K'.fixingSubgroup A)) * Module.finrank ℚ_[p] K =
      padicValNat p (Nat.card A) * Module.finrank ℚ_[p] K' := by
    rw [CoInd.card_coInd, padicValNat.pow, card_quotient_fixingSubgroup,
      ← Module.finrank_mul_finrank ℚ_[p] K K']
    ring
  unfold EulerCharacteristicFor
  rw [card_h0_coInd hA, e1, e2, hc]
  constructor
  · rintro ⟨h1, h2, h⟩
    refine ⟨?_, ?_, h⟩
    · exact Nat.finite_of_card_ne_zero (by rw [← e1]; exact Nat.card_pos.ne')
    · exact Nat.finite_of_card_ne_zero (by rw [← e2]; exact Nat.card_pos.ne')
  · rintro ⟨h1, h2, h⟩
    refine ⟨?_, ?_, h⟩
    · exact Nat.finite_of_card_ne_zero (by rw [e1]; exact Nat.card_pos.ne')
    · exact Nat.finite_of_card_ne_zero (by rw [e2]; exact Nat.card_pos.ne')

end CoInd

end PadicField
