/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.TateH3
import LocalClassFieldTheory.Duality.H3Inflation
import LocalClassFieldTheory.Brauer.TateNakayamaDegrees

/-!
# Tate's theorem `H³(Gal(L/K), Lˣ) = 0` for local fields, and `cd(G_K) ≤ 2`

For a finite Galois extension `E/F` of finite extensions of `ℚ_p`:

* `PadicField.isCyclic_relBr`, `PadicField.card_relBr` : `Br(E/F) = H²(Gal(E/F), Eˣ)` is cyclic of
  order `[E : F]` (from `PadicField.fundClassPowEquiv` inside an algebraic closure of `E`);
* **`PadicField.h3Trivial_units`** : **`H³(Gal(E/F), Eˣ) = 0`** (cocycle form), by induction on
  `[E : F]` with `ContH2.h3Trivial_of_forall_prime` (Sylow reduction) and
  `ContH2.h3Trivial_of_index_prime` (normal subgroup of index `ℓ` in an `ℓ`-group), using
  Hilbert 90, `Br(E/F) ≅ ℤ/[E:F]` and `|H²(H, Eˣ)| ≤ |H|`; subgroups `S ≤ Gal(E/F)` are identified
  with `Gal(E/E^S)` (`IntermediateField.fixingSubgroupEquiv`).

Consequences, closing the inputs isolated in `LocalClassFieldTheory.Duality.H3Inflation`:

* **`PadicField.h3FiniteLevelVanishing`** : `PadicField.H3FiniteLevelVanishing K Ω`;
* **`PadicField.localH3Vanishing`** : `PadicField.LocalH3Vanishing K Ω`, i.e. `cd(G_K) ≤ 2` in
  cocycle form: every locally constant `3`-cocycle of `Gal(Ω/K)` with values in a finite discrete
  module is a coboundary;
* `PadicField.localEulerCharacteristic_of_simple'` : the local Euler characteristic formula for
  all finite modules follows from the formula for simple modules.
-/

open ContH2 Brauer groupCohomology

set_option linter.unusedSectionVars false

namespace ContH2

/-- **Transport of `H³ = 0` along an isomorphism of groups** compatible with the actions. -/
theorem h3Trivial_of_mulEquiv_group {G G' A : Type*} [Group G] [Group G'] [TopologicalSpace G]
    [DiscreteTopology G] [TopologicalSpace G'] [DiscreteTopology G'] [CommGroup A]
    [MulDistribMulAction G A] [MulDistribMulAction G' A] (e : G' ≃* G)
    (he : ∀ (g : G') (a : A), e g • a = g • a) (h : H3Trivial G A) : H3Trivial G' A := by
  intro z _ hz
  have he' : ∀ (g : G) (a : A), e.symm g • a = g • a := fun g a => by
    rw [← he, MulEquiv.apply_symm_apply]
  have hz' : IsMulCocycle₃ fun x : G × G × G => z (e.symm x.1, e.symm x.2.1, e.symm x.2.2) := by
    intro a b c d
    have := hz (e.symm a) (e.symm b) (e.symm c) (e.symm d)
    simpa only [map_mul, he'] using this
  obtain ⟨f, -, hf⟩ := h _ (.of_discrete _) hz'
  refine ⟨fun x => f (e x.1, e x.2), .of_discrete _, ?_⟩
  funext ⟨a, b, c⟩
  have := congrFun hf (e a, e b, e c)
  simp only [dc2_apply, MulEquiv.symm_apply_apply, he] at this
  simpa only [dc2_apply, map_mul] using this

end ContH2

namespace PadicField

universe u

variable {p : ℕ} [hp : Fact p.Prime]

section Abstract

variable {F E : Type*} [Field F] [Field E] [Algebra ℚ_[p] F] [Algebra ℚ_[p] E] [Algebra F E]
  [IsScalarTower ℚ_[p] F E] [FiniteDimensional ℚ_[p] F] [FiniteDimensional ℚ_[p] E]

/-- Transport of the relative Brauer group along an `F`-isomorphism `E ≃ₐ[F] E'`. -/
noncomputable def relBrCongr {E' : Type*} [Field E'] [Algebra F E'] [FiniteDimensional F E]
    [FiniteDimensional F E'] (ε : E ≃ₐ[F] E') : RelBr F E' ≃* RelBr F E where
  toFun := ContH2.map (AlgEquiv.autCongr ε).toMonoidHom continuous_of_discreteTopology
    (Units.map ε.symm.toRingEquiv.toRingHom.toMonoidHom) fun g m => by
      apply Units.ext
      simp [AlgEquiv.smul_units_def, AlgEquiv.autCongr_apply]
  invFun := ContH2.map (AlgEquiv.autCongr ε).symm.toMonoidHom continuous_of_discreteTopology
    (Units.map ε.toRingEquiv.toRingHom.toMonoidHom) fun g m => by
      apply Units.ext
      simp [AlgEquiv.smul_units_def, AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply]
  left_inv x := by
    induction x using induction_on with | h f => ?_
    simp only [map_mk]
    congr 1
    have h1 : ∀ a : E' ≃ₐ[F] E', ε.symm.trans ((ε.trans (a.trans ε.symm)).trans ε) = a :=
      fun a => by ext; simp
    exact cocycles_ext fun a b => by
      apply Units.ext
      simp [AlgEquiv.autCongr_apply, h1]
  right_inv x := by
    induction x using induction_on with | h f => ?_
    simp only [map_mk]
    congr 1
    have h1 : ∀ a : E ≃ₐ[F] E, ε.trans ((ε.symm.trans (a.trans ε)).trans ε.symm) = a :=
      fun a => by ext; simp
    exact cocycles_ext fun a b => by
      apply Units.ext
      simp [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply, h1]
  map_mul' := map_mul _

variable (p F E) in
include hp in
/-- **`Br(E/F)` is cyclic of order `[E : F]`** for a finite Galois extension of local fields. -/
theorem isCyclic_relBr_and_card [IsGalois F E] :
    IsCyclic (RelBr F E) ∧ Nat.card (RelBr F E) = Module.finrank F E := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ_[p] F E
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ_[p] F).injective
  let Ω := AlgebraicClosure E
  haveI : IsAlgClosure F Ω := IsAlgClosure.ofAlgebraic F E Ω
  haveI : IsGalois F Ω := inferInstance
  let ι := IsScalarTower.toAlgHom F E Ω
  let L : IntermediateField F Ω := ι.fieldRange
  let ε : E ≃ₐ[F] L := AlgEquiv.ofInjectiveField ι
  haveI : FiniteDimensional F L := LinearEquiv.finiteDimensional ε.toLinearEquiv
  haveI : IsGalois F L := IsGalois.of_algEquiv ε
  let e : Multiplicative (ZMod (Module.finrank F L)) ≃* RelBr F E :=
    (fundClassPowEquiv (p := p) (Ω := Ω) L).trans (relBrCongr ε)
  refine ⟨isCyclic_of_surjective e.toMonoidHom e.surjective, ?_⟩
  rw [← Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
    ← ε.toLinearEquiv.finrank_eq]

/-- `H³(S, Eˣ) = 0` for a subgroup `S ≤ Gal(E/F)` from `H³(Gal(E/E^S), Eˣ) = 0`. -/
theorem h3Trivial_subgroup_of_fixedField [FiniteDimensional F E] (S : Subgroup (E ≃ₐ[F] E))
    (h : H3Trivial (E ≃ₐ[IntermediateField.fixedField S] E) Eˣ) : H3Trivial S Eˣ := by
  let e : S ≃* (E ≃ₐ[IntermediateField.fixedField S] E) :=
    (MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField S).symm).trans
      (IntermediateField.fixingSubgroupEquiv _)
  exact h3Trivial_of_mulEquiv_group e (fun _ _ => Units.ext rfl) h

theorem card_aut_fixedField [FiniteDimensional F E] (S : Subgroup (E ≃ₐ[F] E)) :
    Nat.card (E ≃ₐ[IntermediateField.fixedField S] E) = Nat.card S := by
  rw [← Nat.card_congr (IntermediateField.fixingSubgroupEquiv _).toEquiv,
    IntermediateField.fixingSubgroup_fixedField]

end Abstract

section Main

variable {E : Type u} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]

variable (p) in
include hp in
theorem h3Trivial_units_aux (n : ℕ) :
    ∀ (F : Type u) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [Algebra F E]
      [IsScalarTower ℚ_[p] F E] [IsGalois F E], Nat.card (E ≃ₐ[F] E) = n →
      H3Trivial (E ≃ₐ[F] E) Eˣ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F _ _ _ _ _ _ hn
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ_[p] F E
  have hsub : ∀ S : Subgroup (E ≃ₐ[F] E), Nat.card S < n → H3Trivial S Eˣ := by
    intro S hS
    apply h3Trivial_subgroup_of_fixedField S
    haveI : FiniteDimensional ℚ_[p] (IntermediateField.fixedField S) :=
      Module.Finite.of_injective (IsScalarTower.toAlgHom ℚ_[p] (IntermediateField.fixedField S)
        E).toLinearMap (RingHom.injective _)
    exact ih _ (card_aut_fixedField S ▸ hS) (IntermediateField.fixedField S)
      (card_aut_fixedField S)
  by_cases htriv : Subsingleton (E ≃ₐ[F] E)
  · exact h3Trivial_of_subsingleton_group
  by_cases hpg : ∃ ℓ, ℓ.Prime ∧ IsPGroup ℓ (E ≃ₐ[F] E)
  · obtain ⟨ℓ, hℓ, hpg⟩ := hpg
    haveI := Fact.mk hℓ
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpg
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact htriv (Finite.card_le_one_iff_subsingleton.1 hk.le)
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime ℓ
      (hk ▸ pow_dvd_pow ℓ (Nat.sub_le k 1) : ℓ ^ (k - 1) ∣ Nat.card (E ≃ₐ[F] E))
    have hkk : ℓ ^ k = ℓ ^ (k - 1) * ℓ := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have hidx : H.index = ℓ := by
      have := H.card_mul_index
      rw [hH, hk, hkk] at this
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hℓ.pos _) this
    haveI : H.Normal := Subgroup.normal_of_index_eq_minFac_card (by
      rw [hidx, hk, Nat.pow_minFac hk0, hℓ.minFac_eq])
    have hHlt : Nat.card H < n := by
      rw [← hn, hk, hH, hkk]
      exact lt_mul_of_one_lt_right (pow_pos hℓ.pos _) hℓ.one_lt
    obtain ⟨hcyc, hcard⟩ := isCyclic_relBr_and_card p F E
    obtain ⟨hH0, hHle⟩ := card_contH2_le (p := p) H
    haveI : Finite (ContH2 H Eˣ) := Nat.finite_of_card_ne_zero hH0
    haveI : Finite (RelBr F E) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
    exact h3Trivial_of_index_prime H (hidx ▸ hℓ)
      (fun y hy => isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units y hy) hHle
      (by rw [hcard, IsGalois.card_aut_eq_finrank]) (hsub H hHlt)
  · apply h3Trivial_of_forall_prime
    intro ℓ hℓ
    haveI := Fact.mk hℓ
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow ℓ (E ≃ₐ[F] E)))
    refine ⟨P, P.not_dvd_index, hsub P ?_⟩
    rw [← hn]
    refine lt_of_le_of_ne (Subgroup.card_le_card_group _) fun heq => hpg ⟨ℓ, hℓ, ?_⟩
    have htop : (P : Subgroup (E ≃ₐ[F] E)) = ⊤ := (Subgroup.card_eq_iff_eq_top _).1 heq
    exact P.isPGroup'.of_equiv ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)

variable (p) in
include hp in
/-- **Tate's theorem `H³(Gal(E/F), Eˣ) = 0`** (cocycle form) for every finite Galois extension
`E/F` of finite extensions of `ℚ_p`. -/
theorem h3Trivial_units (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [Algebra F E] [IsScalarTower ℚ_[p] F E] [IsGalois F E] : H3Trivial (E ≃ₐ[F] E) Eˣ := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ_[p] F E
  -- pass to the copy `E^{Gal(E/F)}` of `F` inside `E` (in the universe of `E`)
  let S : Subgroup (E ≃ₐ[F] E) := ⊤
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.fixedField S) :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom ℚ_[p] (IntermediateField.fixedField S)
      E).toLinearMap (RingHom.injective _)
  have h := h3Trivial_subgroup_of_fixedField S
    (h3Trivial_units_aux p _ (IntermediateField.fixedField S) rfl)
  exact h3Trivial_of_mulEquiv_group Subgroup.topEquiv.symm (fun _ _ => rfl) h

end Main

section Omega

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

variable (p K Ω) in
include hp in
/-- **`H³(Gal(L/K'), Lˣ) = 0` for all finite Galois levels** inside `Ω`. -/
theorem h3FiniteLevelVanishing : H3FiniteLevelVanishing K Ω := by
  intro K' hK' L hL hLg
  haveI : FiniteDimensional ℚ_[p] K' := Module.Finite.trans K K'
  haveI : FiniteDimensional ℚ_[p] L := Module.Finite.trans K' L
  exact h3Trivial_units p K'

variable (p K Ω) in
include hp in
/-- **`H³(K, Ωˣ) = 0`** (cocycle form): Tate's theorem at the level of `Gal(Ω/K)`. -/
theorem h3UnitsVanishing : H3UnitsVanishing K Ω :=
  h3UnitsVanishing_of_finite fun _ _ _ => h3Trivial_units p K

universe v

variable (p K Ω) in
include hp in
/-- **`cd(G_K) ≤ 2`** in cocycle form: every locally constant `3`-cocycle of `Gal(Ω/K)` with
values in a finite discrete module is a coboundary. -/
theorem localH3Vanishing : LocalH3Vanishing.{v} K Ω :=
  localH3Vanishing_of_finiteLevel p (h3FiniteLevelVanishing p K Ω)

include hp in
/-- **`H²(K, B) → H²(K, C)` is surjective** for every short exact sequence `0 → A → B → C → 0` of
discrete modules with `A` finite. -/
theorem h2Hom_surjective {A B C : Type v} [CommGroup A] [CommGroup B] [CommGroup C]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] [MulDistribMulAction (Ω ≃ₐ[K] Ω) A]
    [SmoothAction (Ω ≃ₐ[K] Ω) A] [MulDistribMulAction (Ω ≃ₐ[K] Ω) B]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) C] [SmoothAction (Ω ≃ₐ[K] Ω) B]
    (S : GShortExact (Ω ≃ₐ[K] Ω) A B C) :
    Function.Surjective (h2Hom (G := Ω ≃ₐ[K] Ω) S.π S.map_smul_π) :=
  S.h2Hom_surjective_of_h3Trivial (localH3Vanishing p K Ω A)

include hp in
/-- **The Euler characteristic formula is closed under extensions** (unconditionally). -/
theorem eulerCharacteristicFor_of_shortExact' {A B C : Type v} [CommGroup A] [CommGroup B]
    [CommGroup C] [Finite A] [Finite B] [Finite C] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalGroup A] [TopologicalSpace B] [DiscreteTopology B] [IsTopologicalGroup B]
    [TopologicalSpace C] [DiscreteTopology C] [IsTopologicalGroup C]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) A] [SmoothAction (Ω ≃ₐ[K] Ω) A]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) B] [MulDistribMulAction (Ω ≃ₐ[K] Ω) C]
    [SmoothAction (Ω ≃ₐ[K] Ω) B] (S : GShortExact (Ω ≃ₐ[K] Ω) A B C)
    (hA : EulerCharacteristicFor p K Ω A) (hC : EulerCharacteristicFor p K Ω C) :
    EulerCharacteristicFor p K Ω B :=
  eulerCharacteristicFor_of_shortExact_of_localH3Vanishing (localH3Vanishing p K Ω) S hA hC

variable (p K Ω) in
include hp in
/-- **The local Euler characteristic formula reduces to simple modules** (unconditionally). -/
theorem localEulerCharacteristic_of_simple'
    (hs : ∀ (A : Type v) [CommGroup A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
      [MulDistribMulAction (Ω ≃ₐ[K] Ω) A] [SmoothAction (Ω ≃ₐ[K] Ω) A],
      IsSimpleGModule (Ω ≃ₐ[K] Ω) A → EulerCharacteristicFor p K Ω A) :
    LocalEulerCharacteristic.{v} p K Ω :=
  localEulerCharacteristic_of_simple p (localH3Vanishing p K Ω) hs

end Omega


end PadicField
