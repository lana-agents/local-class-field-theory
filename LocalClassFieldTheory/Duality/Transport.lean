/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.Statements

/-!
# Transport of cup product pairings along isomorphisms of modules

An equivariant isomorphism `τ : N ≃* N'` induces bijections `H^i(G, N) → H^i(G, N')`
(`Brauer.h0Map`, `Brauer.h1Map`, `Brauer.h2Map`). If two pairings `e : M × N → P` and
`e' : M × N' → P` satisfy `e'(m, τ n) = e(m, n)`, then the cup products correspond, and
perfectness in each degree is equivalent for `e` and `e'` (`Brauer.perfectDeg0_iff_of_equiv`,
`Brauer.perfectDeg1_iff_of_equiv`, `Brauer.perfectDeg2_iff_of_equiv`). This identifies the
abstract Cartier-dual formulation `PadicField.TateDualityFor` with concrete pairings.
-/

open ContH2 groupCohomology

set_option linter.unusedSectionVars false

namespace Brauer

/-- Precomposition with a bijective homomorphism is a bijection on `Hom(-, Z)`. -/
theorem bijective_precomp {A B Z : Type*} [Group A] [Group B] [CommGroup Z] (f : A →* B)
    (hf : Function.Bijective f) : Function.Bijective fun ψ : B →* Z => ψ.comp f := by
  set e := MulEquiv.ofBijective f hf
  refine ⟨fun ψ ψ' h => MonoidHom.ext fun b => ?_, fun φ => ⟨φ.comp e.symm.toMonoidHom, ?_⟩⟩
  · obtain ⟨a, rfl⟩ := hf.2 b
    exact DFunLike.congr_fun h a
  · refine MonoidHom.ext fun a => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    congr 1
    exact e.symm_apply_apply a

variable {G M N N' P : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [CommGroup N]
  [CommGroup N'] [CommGroup P] [MulDistribMulAction G M] [MulDistribMulAction G N]
  [MulDistribMulAction G N'] [MulDistribMulAction G P]

theorem symm_smul (τ : N ≃* N') (hτ : ∀ (g : G) (x : N), τ (g • x) = g • τ x) (g : G) (y : N') :
    τ.symm (g • y) = g • τ.symm y := by
  apply τ.injective
  rw [hτ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

/-! ### Degree zero -/

/-- `H⁰(G, N) → H⁰(G, N')` induced by `τ`. -/
def h0Map (τ : N ≃* N') (hτ : ∀ (g : G) (x : N), τ (g • x) = g • τ x) : H0 G N →* H0 G N' where
  toFun x := ⟨τ (x : N), fun g => by rw [← hτ, smul_H0 x g]⟩
  map_one' := Subtype.ext (map_one τ)
  map_mul' x y := Subtype.ext (map_mul τ (x : N) y)

theorem h0Map_bijective (τ : N ≃* N') (hτ : ∀ (g : G) (x : N), τ (g • x) = g • τ x) :
    Function.Bijective (h0Map τ hτ) := by
  refine ⟨fun x y h => Subtype.ext (τ.injective (congrArg Subtype.val h)), fun y => ?_⟩
  refine ⟨⟨τ.symm y, fun g => by rw [← symm_smul τ hτ, smul_H0 y g]⟩, Subtype.ext ?_⟩
  exact τ.apply_symm_apply y

/-! ### Degree two -/

/-- `H²(G, N) → H²(G, N')` induced by `τ`. -/
def h2Map (τ : N ≃* N') (hτ : ∀ (g : G) (x : N), τ (g • x) = g • τ x) :
    ContH2 G N →* ContH2 G N' :=
  ContH2.map (MonoidHom.id G) continuous_id τ.toMonoidHom hτ

theorem h2Map_bijective (τ : N ≃* N') (hτ : ∀ (g : G) (x : N), τ (g • x) = g • τ x) :
    Function.Bijective (h2Map τ hτ) := by
  have hl : ∀ β, h2Map τ.symm (symm_smul τ hτ) (h2Map τ hτ β) = β := by
    intro β
    induction β using induction_on with | h f => ?_
    simp only [h2Map, map_mk]
    congr 1
    exact cocycles_ext fun a b => by simp
  have hr : ∀ β, h2Map τ hτ (h2Map τ.symm (symm_smul τ hτ) β) = β := by
    intro β
    induction β using induction_on with | h f => ?_
    simp only [h2Map, map_mk]
    congr 1
    exact cocycles_ext fun a b => by simp
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

theorem cup02_h2Map (τ : N ≃* N') (hτ : ∀ (g : G) (x : N), τ (g • x) = g • τ x)
    (e : GPairing G M N P) (e' : GPairing G M N' P) (he : ∀ m x, e'.toHom m (τ x) = e.toHom m x)
    (m : H0 G M) (β : ContH2 G N) : cup02 e' m (h2Map τ hτ β) = cup02 e m β := by
  induction β using induction_on with | h f => ?_
  simp only [h2Map, map_mk, cup02_mk]
  congr 1
  exact cocycles_ext fun a b => by simp [he]

theorem cup20_h0Map (τ : N ≃* N') (hτ : ∀ (g : G) (x : N), τ (g • x) = g • τ x)
    (e : GPairing G M N P) (e' : GPairing G M N' P) (he : ∀ m x, e'.toHom m (τ x) = e.toHom m x)
    (β : ContH2 G M) (x : H0 G N) : cup20 e' β (h0Map τ hτ x) = cup20 e β x := by
  induction β using induction_on with | h f => ?_
  rw [cup20_apply, cup20_apply, cup02_mk, cup02_mk]
  congr 1
  exact cocycles_ext fun a b => by simp [h0Map, he]

/-- Perfectness in degree `0` is invariant under `τ`. -/
theorem perfectDeg0_iff_of_equiv {n : ℕ} (χ : ContH2 G P →* Multiplicative (ZMod n))
    (τ : N ≃* N') (hτ : ∀ (g : G) (x : N), τ (g • x) = g • τ x)
    (e : GPairing G M N P) (e' : GPairing G M N' P) (he : ∀ m x, e'.toHom m (τ x) = e.toHom m x) :
    PerfectDeg0 χ e' ↔ PerfectDeg0 χ e := by
  have h : (fun m : H0 G M => χ.comp (cup02 e m)) =
      (fun ψ => ψ.comp (h2Map τ hτ)) ∘ fun m : H0 G M => χ.comp (cup02 e' m) := by
    funext m
    exact MonoidHom.ext fun β => by simp [cup02_h2Map τ hτ e e' he]
  rw [PerfectDeg0, PerfectDeg0, h, Function.Bijective.of_comp_iff'
    (bijective_precomp _ (h2Map_bijective τ hτ))]

/-- Perfectness in degree `2` is invariant under `τ`. -/
theorem perfectDeg2_iff_of_equiv {n : ℕ} (χ : ContH2 G P →* Multiplicative (ZMod n))
    (τ : N ≃* N') (hτ : ∀ (g : G) (x : N), τ (g • x) = g • τ x)
    (e : GPairing G M N P) (e' : GPairing G M N' P) (he : ∀ m x, e'.toHom m (τ x) = e.toHom m x) :
    PerfectDeg2 χ e' ↔ PerfectDeg2 χ e := by
  have h : (fun β : ContH2 G M => χ.comp (cup20 e β)) =
      (fun ψ => ψ.comp (h0Map τ hτ)) ∘ fun β : ContH2 G M => χ.comp (cup20 e' β) := by
    funext β
    exact MonoidHom.ext fun x => by simp [cup20_h0Map τ hτ e e' he]
  rw [PerfectDeg2, PerfectDeg2, h, Function.Bijective.of_comp_iff'
    (bijective_precomp _ (h0Map_bijective τ hτ))]

/-! ### Degree one -/

section Deg1

variable [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalGroup M]
  [TopologicalSpace N] [DiscreteTopology N] [IsTopologicalGroup N] [SmoothAction G N]
  [TopologicalSpace N'] [DiscreteTopology N'] [IsTopologicalGroup N'] [SmoothAction G N']

/-- `H¹(G, N) → H¹(G, N')` induced by `τ`. -/
def h1Map (τ : N ≃* N') (hτ : ∀ (g : G) (x : N), τ (g • x) = g • τ x) :
    ContH1 G N →* ContH1 G N' :=
  ContH1.map (MonoidHom.id G) continuous_id τ.toMonoidHom continuous_of_discreteTopology
    (fun g x => hτ g x)

theorem h1Map_bijective (τ : N ≃* N') (hτ : ∀ (g : G) (x : N), τ (g • x) = g • τ x) :
    Function.Bijective (h1Map τ hτ) := by
  have hl : ∀ y, h1Map τ.symm (symm_smul τ hτ) (h1Map τ hτ y) = y := by
    intro y
    induction y using ContH1.induction_on with | h y => ?_
    simp only [h1Map, ContH1.map_mk]
    congr 1
    exact Subtype.ext (funext fun g => by simp)
  have hr : ∀ y, h1Map τ hτ (h1Map τ.symm (symm_smul τ hτ) y) = y := by
    intro y
    induction y using ContH1.induction_on with | h y => ?_
    simp only [h1Map, ContH1.map_mk]
    congr 1
    exact Subtype.ext (funext fun g => by simp)
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

theorem cup11_h1Map (τ : N ≃* N') (hτ : ∀ (g : G) (x : N), τ (g • x) = g • τ x)
    (e : GPairing G M N P) (e' : GPairing G M N' P) (he : ∀ m x, e'.toHom m (τ x) = e.toHom m x)
    (x : ContH1 G M) (y : ContH1 G N) : cup11 e' x (h1Map τ hτ y) = cup11 e x y := by
  induction x using ContH1.induction_on with | h x => ?_
  induction y using ContH1.induction_on with | h y => ?_
  simp only [h1Map, ContH1.map_mk, cup11_mk]
  congr 1
  refine cocycles_ext fun a b => ?_
  simp only [cup11Cocycle_apply, ContH1.cocyclesMap_apply, MonoidHom.id_apply,
    MulEquiv.coe_toMonoidHom]
  rw [← hτ, he]

/-- Perfectness in degree `1` is invariant under `τ`. -/
theorem perfectDeg1_iff_of_equiv {n : ℕ} (χ : ContH2 G P →* Multiplicative (ZMod n))
    (τ : N ≃* N') (hτ : ∀ (g : G) (x : N), τ (g • x) = g • τ x)
    (e : GPairing G M N P) (e' : GPairing G M N' P) (he : ∀ m x, e'.toHom m (τ x) = e.toHom m x) :
    PerfectDeg1 χ e' ↔ PerfectDeg1 χ e := by
  have h : (fun x : ContH1 G M => χ.comp (cup11 e x)) =
      (fun ψ => ψ.comp (h1Map τ hτ)) ∘ fun x : ContH1 G M => χ.comp (cup11 e' x) := by
    funext x
    exact MonoidHom.ext fun y => by simp [cup11_h1Map τ hτ e e' he]
  rw [PerfectDeg1, PerfectDeg1, h, Function.Bijective.of_comp_iff'
    (bijective_precomp _ (h1Map_bijective τ hτ))]

end Deg1

end Brauer
