/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.ArtinInertia
import LocalClassFieldTheory.Reciprocity.ArtinContinuous
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.FieldTheory.Galois.Profinite

/-!
# `Gal(K^ab/K)` is the profinite completion of `Kˣ`

Let `Ĝ = ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Kˣ)` be the profinite completion
of `Kˣ` (the limit of the finite quotients `Kˣ ⧸ H`, `H` of finite index). The Artin map
extends (universal property of the completion) to a continuous homomorphism
`Ĝ → Gal(K^ab/K)` (`PadicField.artinCompletionHom`), which is

* injective: if it kills `c`, then for every finite-index `H = N_{L/K} Lˣ` (existence theorem) the
  open set `{c' | c'_H = c_H, c' ↦ Gal(K^ab/L)}` contains some `x ∈ Kˣ` (density of `Kˣ` in
  `Ĝ`), and `artin x` fixing `L` means `x ∈ H`, so `c_H = 1`;
* surjective: its image is compact, hence closed, and contains the dense image of `artin`.

Hence (compact to Hausdorff) it is an isomorphism of topological groups
**`PadicField.artinCompletionEquiv : Ĝ ≃ₜ* Gal(K^ab/K)`** with
`artinCompletionEquiv (η x) = artin x` (`PadicField.artinCompletionEquiv_eta`).

The universal property of `ProfiniteGrp.ProfiniteCompletion` is stated for groups in a single
universe, so here `K` and `Ω` live in the same universe `u`.
-/

set_option linter.unusedSectionVars false

universe u

open IntermediateField CategoryTheory ProfiniteGrp

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type u} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

/-- The automorphisms of `K^ab` fixing a finite abelian `L` form an open set (they are the fixing
subgroup of `L` viewed inside `K^ab`). -/
theorem isOpen_setOf_fixes (L : AbFin K Ω) :
    IsOpen {g : maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω |
      ∀ y : maxAbelian K Ω, (y : Ω) ∈ L.1 → g y = y} := by
  haveI : FiniteDimensional K (restrict (le_maxAbelian L)) :=
    LinearEquiv.finiteDimensional (restrict_algEquiv (le_maxAbelian L)).toLinearEquiv
  have h := (restrict (le_maxAbelian L)).fixingSubgroup_isOpen
  convert h using 1
  ext g
  rw [Set.mem_setOf_eq, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h y hy ↦ h y ((mem_restrict _ y).1 hy), fun h y hy ↦ h y ((mem_restrict _ y).2 hy)⟩

variable (p K Ω) in
/-- `Gal(K^ab/K)` (Krull topology) as a profinite group. -/
noncomputable def galAb : ProfiniteGrp.{u} :=
  haveI := isGalois_maxAbelian (p := p) (K := K) (Ω := Ω)
  ProfiniteGrp.of (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω)

/-- The profinite completion of `Kˣ`. -/
local notation "Ĝ" K => ProfiniteCompletion.completion (GrpCat.of (Units K))

variable (p K Ω) in
/-- The extension of the Artin map to the profinite completion of `Kˣ` (as a morphism of
profinite groups). -/
noncomputable def artinLift : (Ĝ K) ⟶ galAb p K Ω :=
  ProfiniteCompletion.lift (GrpCat.ofHom (X := Kˣ) (Y := galAb p K Ω) (artin p K Ω))

variable (p K Ω) in
/-- The extension of the Artin map to the profinite completion of `Kˣ`. -/
noncomputable def artinCompletionHom :
    ContinuousMonoidHom (Ĝ K) (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) :=
  (artinLift p K Ω).hom

theorem artinCompletionHom_eta (x : Kˣ) :
    artinCompletionHom p K Ω (ProfiniteCompletion.etaFn _ x) = artin p K Ω x := by
  have := ConcreteCategory.congr_hom
    (ProfiniteCompletion.lift_eta (GrpCat.ofHom (X := Kˣ) (Y := galAb p K Ω) (artin p K Ω))) x
  exact this

include hp in
theorem artinCompletionHom_injective : Function.Injective (artinCompletionHom p K Ω) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  apply Subtype.ext
  funext H
  obtain ⟨L, hL⟩ := existence (p := p) (Ω := Ω) (H.toSubgroup : Subgroup Kˣ)
    Subgroup.FiniteIndex.index_ne_zero
  haveI : DiscreteTopology ((ProfiniteCompletion.diagram (GrpCat.of Kˣ)).obj H) := ⟨rfl⟩
  have hproj : Continuous fun c' : (Ĝ K) ↦ c'.1 H :=
    (continuous_apply H).comp continuous_subtype_val
  set V : Set (Ĝ K) := {c' | c'.1 H = c.1 H} ∩ artinCompletionHom p K Ω ⁻¹'
    {g | ∀ y : maxAbelian K Ω, (y : Ω) ∈ L.1 → g y = y} with hVdef
  have hV : IsOpen V := (hproj.isOpen_preimage {c.1 H} (isOpen_discrete _)).inter
    ((isOpen_setOf_fixes L).preimage (map_continuous _))
  have hcV : c ∈ V := ⟨rfl, fun y _ ↦ by rw [hc]; rfl⟩
  obtain ⟨x, hxV⟩ := (ProfiniteCompletion.denseRange (GrpCat.of Kˣ)).exists_mem_open hV ⟨c, hcV⟩
  obtain ⟨hx1, hx2⟩ := hxV
  rw [Set.mem_preimage, artinCompletionHom_eta, Set.mem_setOf_eq] at hx2
  have hxN : x ∈ normGroup K L.1 := (artin_apply_eq_self_iff (p := p) x L.1).1 hx2
  rw [hL] at hxN
  rw [Set.mem_setOf_eq] at hx1
  rw [← hx1]
  exact (QuotientGroup.eq_one_iff (N := H.toSubgroup) x).2 hxN

include hp in
theorem artinCompletionHom_surjective : Function.Surjective (artinCompletionHom p K Ω) := by
  haveI := isGalois_maxAbelian (p := p) (K := K) (Ω := Ω)
  have hcl : IsClosed (Set.range (artinCompletionHom p K Ω)) :=
    (isCompact_range (map_continuous _)).isClosed
  have hsub : Set.range (artin p K Ω) ⊆ Set.range (artinCompletionHom p K Ω) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, artinCompletionHom_eta x⟩
  intro σ
  have h := closure_mono hsub (denseRange_artin (p := p) (K := K) (Ω := Ω) σ)
  rwa [hcl.closure_eq] at h

variable (p K Ω) in
/-- **`Gal(K^ab/K)` is the profinite completion of `Kˣ`**: the Artin map extends to an
isomorphism of topological groups from the profinite completion of `Kˣ` onto `Gal(K^ab/K)`
(Krull topology). -/
noncomputable def artinCompletionEquiv :
    (Ĝ K) ≃ₜ* (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) :=
  haveI := isGalois_maxAbelian (p := p) (K := K) (Ω := Ω)
  let e := MulEquiv.ofBijective (artinCompletionHom p K Ω)
    ⟨artinCompletionHom_injective, artinCompletionHom_surjective⟩
  { e with
    continuous_toFun := map_continuous (artinCompletionHom p K Ω)
    continuous_invFun :=
      (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv)
        (map_continuous (artinCompletionHom p K Ω))).symm.continuous }

theorem artinCompletionEquiv_apply (c : Ĝ K) :
    artinCompletionEquiv p K Ω c = artinCompletionHom p K Ω c := rfl

/-- `artinCompletionEquiv` extends the Artin map. -/
theorem artinCompletionEquiv_eta (x : Kˣ) :
    artinCompletionEquiv p K Ω (ProfiniteCompletion.etaFn _ x) = artin p K Ω x :=
  artinCompletionHom_eta x

end PadicField
