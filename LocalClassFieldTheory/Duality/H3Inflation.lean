/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.EulerReduction

/-!
# `H³(K, Ωˣ) = 0` from the finite levels (inflation in degree three)

Every locally constant `3`-cocycle `z` of `Gal(Ω/K)` with values in `Ωˣ` is inflated from a
finite Galois level `L ⊆ Ω`: it is invariant under right translation by an open subgroup in each
variable (`exists_openSubgroup_triple_invariant`, compactness) and takes finitely many values. If
the descended cocycle of `Gal(L/K)` with values in `Lˣ` is a coboundary, so is `z`. Hence

* **`Brauer.h3UnitsVanishing_of_finite`** : if `H³(Gal(L/K), Lˣ) = 0` (cocycle form) for all finite
  Galois `L ⊆ Ω`, then `H3UnitsVanishing K Ω`;
* **`PadicField.localH3Vanishing_of_finiteLevel`**,
  **`PadicField.localEulerCharacteristic_of_finiteLevel`**: the vanishing of `H³` for finite
  discrete `G_K`-modules (`cd(G_K) ≤ 2`) and the reduction of the Euler characteristic formula to
  simple modules, assuming only the **finite-level** statement
  `PadicField.H3FiniteLevelVanishing K Ω`: `H³(Gal(L/K'), Lˣ) = 0` for all finite `K' ⊆ Ω` and
  finite Galois `L/K'` inside `Ω`.

`H³(Gal(L/K'), Lˣ) ≅ Ĥ¹(Gal(L/K'), ℤ) = 0` is Tate's theorem (cup product with the fundamental
class, Tate–Nakayama in degree three; Serre, *Local fields* IX.8, Cassels–Fröhlich IV.10); it is
**not** proved in this repository, which formalises Galois cohomology of `Lˣ` in degrees `≤ 2`.
-/

open ContH2 IntermediateField groupCohomology

open scoped Topology

set_option linter.unusedSectionVars false

/-- A locally constant function on `G × G × G` (`G` compact, open subgroups a basis at `1`) is
invariant under right translation by `U × U × U` for an open subgroup `U`. -/
theorem exists_openSubgroup_triple_invariant {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G]
    (hbasis : ∀ V ∈ 𝓝 (1 : G), ∃ U : Subgroup G, IsOpen (U : Set G) ∧ (U : Set G) ⊆ V)
    (z : G × G × G → X) (hz : IsLocallyConstant z) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ a b c : G, ∀ u ∈ U, ∀ u' ∈ U, ∀ u'' ∈ U,
      z (a * u, b * u', c * u'') = z (a, b, c) := by
  have hbasis2 : ∀ V ∈ 𝓝 (1 : G × G), ∃ U : Subgroup (G × G), IsOpen (U : Set (G × G)) ∧
      (U : Set (G × G)) ⊆ V := by
    intro V hV
    rw [Prod.one_eq_mk, mem_nhds_prod_iff] at hV
    obtain ⟨V₁, hV₁, V₂, hV₂, hV⟩ := hV
    obtain ⟨U₁, hU₁o, hU₁⟩ := hbasis V₁ hV₁
    obtain ⟨U₂, hU₂o, hU₂⟩ := hbasis V₂ hV₂
    refine ⟨U₁.prod U₂, ?_, fun x hx => hV (Set.mk_mem_prod (hU₁ hx.1) (hU₂ hx.2))⟩
    rw [Subgroup.coe_prod]
    exact hU₁o.prod hU₂o
  let F : (G × G) × (G × G) → X := fun qr => z (qr.1.1, qr.1.2, qr.2.1)
  have hF : IsLocallyConstant F := hz.comp_continuous (by fun_prop)
  obtain ⟨W, hWo, hW⟩ := exists_openSubgroup_prod_invariant hbasis2 F hF
  have hinl : Continuous (MonoidHom.inl G G) := continuous_id.prodMk continuous_const
  have hinr : Continuous (MonoidHom.inr G G) := continuous_const.prodMk continuous_id
  refine ⟨W.comap (MonoidHom.inl G G) ⊓ W.comap (MonoidHom.inr G G),
    (hinl.isOpen_preimage _ hWo).inter (hinr.isOpen_preimage _ hWo), ?_⟩
  intro a b c u hu u' hu' u'' hu''
  have hmem : ((u, u') : G × G) ∈ W := by
    have := W.mul_mem hu.1 hu'.2
    simpa using this
  have := hW (a, b) (c, 1) (u, u') hmem (u'', 1) hu''.1
  simpa [F] using this

namespace Brauer

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
theorem exists_fixingSubgroup_invariant₃ (z : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → Ωˣ)
    (hz : IsLocallyConstant z) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ a b c : Ω ≃ₐ[K] Ω, ∀ u ∈ E.fixingSubgroup, ∀ u' ∈ E.fixingSubgroup,
        ∀ u'' ∈ E.fixingSubgroup, z (a * u, b * u', c * u'') = z (a, b, c) := by
  obtain ⟨U, hUo, hU⟩ := exists_openSubgroup_triple_invariant (fun V hV => by
    obtain ⟨E, hE, hEV⟩ := (krullTopology_mem_nhds_one_iff K Ω V).1 hV
    exact ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, hEV⟩) z hz
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω U).1 (hUo.mem_nhds U.one_mem)
  exact ⟨E, hE, fun a b c u hu u' hu' u'' hu'' =>
    hU a b c u (hEU hu) u' (hEU hu') u'' (hEU hu'')⟩

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
/-- **Inflation in degree three**: `H³(K, Ωˣ) = 0` (cocycle form) if `H³(Gal(L/K), Lˣ) = 0` for
every finite Galois `L ⊆ Ω`. -/
theorem h3UnitsVanishing_of_finite
    (h : ∀ L : IntermediateField K Ω, FiniteDimensional K L → IsGalois K L →
      H3Trivial (L ≃ₐ[K] L) Lˣ) : H3UnitsVanishing K Ω := by
  intro z hzl hz
  classical
  obtain ⟨E, hE, hinv⟩ := exists_fixingSubgroup_invariant₃ z hzl
  have hfin : (Set.range fun q => (z q : Ω)).Finite :=
    (hzl.range_finite).image (fun u : Ωˣ => (u : Ω)) |>.subset (by
      rintro _ ⟨q, rfl⟩
      exact ⟨z q, ⟨q, rfl⟩, rfl⟩)
  set S := Set.range fun q => (z q : Ω)
  haveI : Finite S := hfin.to_subtype
  haveI : FiniteDimensional K (adjoin K S) :=
    finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral (R := K) x
  set F := E ⊔ adjoin K S
  set L := normalClosure K F Ω
  have hEL : E ≤ L := le_sup_left.trans (le_normalClosure F)
  have hmem : ∀ q, (z q : Ω) ∈ L := fun q =>
    le_normalClosure F (le_sup_right (a := E) (subset_adjoin K S ⟨q, rfl⟩))
  have hfixL : ∀ u ∈ L.fixingSubgroup, u ∈ E.fixingSubgroup :=
    fun u hu => fixingSubgroup_antitone hEL hu
  have hsurj := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := Ω)
  set π := AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L
  set lift := Function.surjInv hsurj
  have hres : ∀ τ, π (lift τ) = τ := Function.surjInv_eq hsurj
  have hdep1 : ∀ g g' : Ω ≃ₐ[K] Ω, π g = π g' → g⁻¹ * g' ∈ E.fixingSubgroup := by
    intro g g' hgg'
    apply hfixL
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, hgg',
      inv_mul_cancel]
  have hdep : ∀ a a' b b' c c' : Ω ≃ₐ[K] Ω, π a = π a' → π b = π b' → π c = π c' →
      z (a, b, c) = z (a', b', c') := by
    intro a a' b b' c c' ha hb hc
    have := hinv a b c _ (hdep1 a a' ha) _ (hdep1 b b' hb) _ (hdep1 c c' hc)
    simpa only [mul_inv_cancel_left] using this.symm
  -- the descended cocycle on `Gal(L/K)`
  let zL : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ := fun x =>
    Units.mk0 ⟨z (lift x.1, lift x.2.1, lift x.2.2), hmem _⟩ (by simp [Subtype.ext_iff])
  have hzLval : ∀ x, ((zL x : L) : Ω) = z (lift x.1, lift x.2.1, lift x.2.2) := fun _ => rfl
  have hsmul : ∀ (a : L ≃ₐ[K] L) (u : Lˣ), (((a • u : Lˣ) : L) : Ω) =
      ((lift a • Units.map (algebraMap L Ω : L →* Ω) u : Ωˣ) : Ω) := by
    intro a u
    have := units_map_restrictNormalHom_smul L (lift a) u
    rw [hres] at this
    exact congrArg Units.val this
  have hzL : IsMulCocycle₃ zL := by
    intro a b c d
    apply Units.ext
    apply Subtype.ext
    have hc := hz (lift a) (lift b) (lift c) (lift d)
    have e1 : z (lift a, lift (b * c), lift d) = z (lift a, lift b * lift c, lift d) :=
      hdep _ _ _ _ _ _ rfl (by rw [map_mul, hres, hres, hres]) rfl
    have e2 : z (lift (a * b), lift c, lift d) = z (lift a * lift b, lift c, lift d) :=
      hdep _ _ _ _ _ _ (by rw [map_mul, hres, hres, hres]) rfl rfl
    have e3 : z (lift a, lift b, lift (c * d)) = z (lift a, lift b, lift c * lift d) :=
      hdep _ _ _ _ _ _ rfl rfl (by rw [map_mul, hres, hres, hres])
    have hs : (((a • zL (b, c, d) : Lˣ) : L) : Ω) =
        ((lift a • z (lift b, lift c, lift d) : Ωˣ) : Ω) := by
      rw [hsmul]
      rfl
    simp only [Units.val_mul, MulMemClass.coe_mul, hs, hzLval, e1, e2, e3]
    exact congrArg Units.val hc
  obtain ⟨fL, -, hfL⟩ := h L inferInstance inferInstance zL (.of_discrete _) hzL
  let ι : Lˣ →* Ωˣ := Units.map (algebraMap L Ω : L →* Ω)
  have hι : ∀ (g : Ω ≃ₐ[K] Ω) (u : Lˣ), ι (π g • u) = g • ι u :=
    units_map_restrictNormalHom_smul L
  refine ⟨fun x => ι (fL (π x.1, π x.2)), ((IsLocallyConstant.of_discrete fL).comp_continuous
    (((InfiniteGalois.restrictNormalHom_continuous L).comp continuous_fst).prodMk
      ((InfiniteGalois.restrictNormalHom_continuous L).comp continuous_snd))).comp ι, ?_⟩
  funext ⟨a, b, c⟩
  have key := congrFun hfL (π a, π b, π c)
  have hz' : ι (zL (π a, π b, π c)) = z (a, b, c) := by
    apply Units.ext
    change ((zL (π a, π b, π c) : L) : Ω) = _
    rw [hzLval]
    exact congrArg Units.val (hdep _ _ _ _ _ _ (hres _) (hres _) (hres _))
  rw [← hz', ← key, dc2_apply, dc2_apply]
  simp only [map_mul, map_div, hι]

end Brauer

namespace PadicField

open Brauer

universe u

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

variable (K Ω) in
/-- **`H³(Gal(L/K'), Lˣ) = 0` for all finite Galois levels** (statement only): for every finite
`K' ⊆ Ω` over `K` and every finite Galois `L/K'` inside `Ω`, every `3`-cocycle of `Gal(L/K')`
with values in `Lˣ` is a coboundary. This is Tate's theorem (`H³(G, Lˣ) ≅ Ĥ¹(G, ℤ) = 0`), not
proved in this repository. -/
def H3FiniteLevelVanishing : Prop :=
  ∀ K' : IntermediateField K Ω, FiniteDimensional K K' →
    ∀ L : IntermediateField K' Ω, FiniteDimensional K' L → IsGalois K' L →
      H3Trivial (L ≃ₐ[K'] L) Lˣ

variable (p) in
include hp in
/-- **`cd(G_K) ≤ 2` in cocycle form, from the finite levels**: `H³(Gal(L/K'), Lˣ) = 0` for all
finite Galois levels implies `PadicField.LocalH3Vanishing K Ω`. -/
theorem localH3Vanishing_of_finiteLevel (h : H3FiniteLevelVanishing K Ω) :
    LocalH3Vanishing.{u} K Ω :=
  localH3Vanishing_of_h3UnitsVanishing p fun K' hK' => h3UnitsVanishing_of_finite (h K' hK')

variable (p) in
include hp in
/-- **The local Euler characteristic formula from the finite levels and the simple modules.** -/
theorem localEulerCharacteristic_of_finiteLevel (h : H3FiniteLevelVanishing K Ω)
    (hs : ∀ (A : Type u) [CommGroup A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
      [MulDistribMulAction (Ω ≃ₐ[K] Ω) A] [SmoothAction (Ω ≃ₐ[K] Ω) A],
      IsSimpleGModule (Ω ≃ₐ[K] Ω) A → EulerCharacteristicFor p K Ω A) :
    LocalEulerCharacteristic.{u} p K Ω :=
  localEulerCharacteristic_of_simple p (localH3Vanishing_of_finiteLevel p h) hs

end PadicField
