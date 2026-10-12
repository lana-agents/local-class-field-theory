/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.CyclicRec
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Local reciprocity for finite abelian extensions

Let `L ⊆ Ω` be a finite abelian extension of `K`. The cyclic subextensions `E ⊆ L` separate the
points of `Gal(L/K)` (characters of a finite abelian group), so restriction
`res : Gal(L/K) → ∏_E Gal(E/K)` is injective. The product `Φ = (cycRec E)_E` of the cyclic
reciprocity maps takes the Neukirch values `N_{Σ/K} π_Σ` (for Frobenius lifts `τ` in
`L ⊔ K_s`) to `res(τ|_L)`; these generate, so `res(Gal(L/K)) ≤ Φ(Kˣ)`. Comparing with the second
inequality `[Kˣ : N Lˣ] ≤ [L : K]` gives `Φ(Kˣ) = res(Gal(L/K))` and `ker Φ = N_{L/K} Lˣ`.

## Main definitions and results

* `PadicField.abRec L : Kˣ →* Gal(L/K)`: the reciprocity map, characterised by
  `abRec L x |_E = cycRec E x` for all cyclic `E ⊆ L` (`PadicField.resHom_abRec`);
* `PadicField.ker_abRec : (abRec L).ker = normGroup K L` and `PadicField.abRec_surjective`,
  i.e. **local reciprocity** `Kˣ / N_{L/K} Lˣ ≃ Gal(L/K)` (`PadicField.abRecEquiv`);
* `PadicField.resHom_abRec_of_le`: compatibility with restriction to abelian `L' ⊆ L`.
-/

set_option linter.unusedSectionVars false

open IntermediateField
open scoped IsMulCommutative

namespace PadicField

/-- In a finite abelian group, every `g ≠ 1` lies outside some subgroup with cyclic quotient. -/
theorem exists_isCyclic_quotient {G : Type*} [Group G] [IsMulCommutative G] [Finite G] {g : G}
    (hg : g ≠ 1) : ∃ H : Subgroup G, g ∉ H ∧ IsCyclic (G ⧸ H) := by
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hg
  refine ⟨φ.ker, fun h ↦ hφ h, ?_⟩
  exact isCyclic_of_injective_ringHom ((Units.coeHom ℂ).comp (QuotientGroup.kerLift φ))
    (Units.val_injective.comp (QuotientGroup.kerLift_injective φ))

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

section CycSub

variable (L : IntermediateField K Ω) [FiniteDimensional K L]

/-- The cyclic subextensions of `L`. -/
def CycSub : Type _ := {E : IntermediateField K Ω // E ≤ L ∧ IsGalois K E ∧ IsCyclic (E ≃ₐ[K] E)}

variable {L}

instance CycSub.finiteDimensional (E : CycSub L) : FiniteDimensional K E.1 :=
  FiniteDimensional.of_injective (inclusion E.2.1).toLinearMap (inclusion E.2.1).injective

instance CycSub.isGalois (E : CycSub L) : IsGalois K E.1 := E.2.2.1
instance CycSub.isCyclic (E : CycSub L) : IsCyclic (E.1 ≃ₐ[K] E.1) := E.2.2.2

omit [IsAlgClosed Ω] in
theorem finite_cycSub [IsGalois K L] : Finite (CycSub L) := by
  haveI : Finite (IntermediateField K L) :=
    Field.finite_intermediateField_of_exists_primitive_element K L
      (Field.exists_primitive_element K L)
  refine Finite.of_injective (fun E : CycSub L ↦ restrict E.2.1) fun E E' h ↦ ?_
  apply Subtype.ext
  have := congrArg lift h
  simpa only [lift_restrict] using this

variable (L) in
/-- Restriction to all cyclic subextensions. -/
noncomputable def resCyc : (L ≃ₐ[K] L) →* ∀ E : CycSub L, E.1 ≃ₐ[K] E.1 :=
  MonoidHom.pi fun E ↦ resHom E.2.1

theorem resCyc_apply (σ : L ≃ₐ[K] L) (E : CycSub L) : resCyc L σ E = resHom E.2.1 σ := rfl

/-- The cyclic subextensions separate `Gal(L/K)`. -/
theorem resCyc_injective [IsAbelianGalois K L] : Function.Injective (resCyc L) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  by_contra hne
  obtain ⟨H, hσH, hcyc⟩ := exists_isCyclic_quotient hne
  set E := lift (fixedField H)
  let εE : fixedField H ≃ₐ[K] E := liftAlgEquiv _
  haveI : IsGalois K E := IsGalois.of_algEquiv εE
  haveI : IsCyclic (E ≃ₐ[K] E) :=
    isCyclic_of_surjective ((AlgEquiv.autCongr εE).toMonoidHom.comp
      (IsGalois.normalAutEquivQuotient H).toMonoidHom)
      ((AlgEquiv.autCongr εE).surjective.comp (IsGalois.normalAutEquivQuotient H).surjective)
  have h1 : resHom (lift_le (fixedField H)) σ = 1 := congrFun hσ ⟨E, lift_le _, inferInstance,
    inferInstance⟩
  apply hσH
  rw [← fixingSubgroup_fixedField H, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h2 := resHom_apply (lift_le (fixedField H)) σ ⟨x, (mem_lift x).2 hx⟩
  rw [h1, AlgEquiv.one_apply] at h2
  exact Subtype.ext h2.symm

variable (p L) in
/-- The product of the cyclic reciprocity maps. -/
noncomputable def recCyc : Kˣ →* ∀ E : CycSub L, E.1 ≃ₐ[K] E.1 :=
  MonoidHom.pi fun E ↦ cycRec p E.1

theorem recCyc_apply (x : Kˣ) (E : CycSub L) : recCyc p L x E = cycRec p E.1 x := rfl

end CycSub

/-- The fixed field of a Frobenius lift `τ ∈ Gal(D/K)` (acting on the maximal unramified
subextension `K_s` of `D` as the Frobenius) has inertia degree one. -/
theorem f_fixedField_frobLift {D : IntermediateField K Ω} [FiniteDimensional K D] {s : ℕ}
    (hs : 0 < s) (hfD : f p K D = s) (hsD : unramifiedOfDegree p K Ω s ≤ D) (τ : D ≃ₐ[K] D)
    (hτ : resHom hsD τ = frobT p K Ω s) : f p K (fixedField (Subgroup.zpowers τ)) = 1 := by
  set Fx := fixedField (Subgroup.zpowers τ)
  haveI : FiniteDimensional K (lift Fx) :=
    LinearEquiv.finiteDimensional (liftAlgEquiv Fx).toLinearEquiv
  have hfM : f p K (lift Fx) = f p K Fx := (f_eq_of_algEquiv (liftAlgEquiv Fx)).symm
  obtain ⟨m, hmdef⟩ : ∃ m, m = f p K (lift Fx) := ⟨_, rfl⟩
  have hKm : unramifiedOfDegree p K Ω m ≤ lift Fx := unramifiedOfDegree_le_of_f_eq _ hmdef.symm
  have hm0 : 0 < m := hmdef ▸ f_pos
  have hms : m ∣ s := by
    have := f_dvd_f_of_le (p := p) (hKm.trans (lift_le Fx))
    rwa [(isUnramified_unramifiedOfDegree p K Ω m).f_eq, finrank_unramifiedOfDegree p K Ω hm0,
      hfD] at this
  have hKmKs : unramifiedOfDegree p K Ω m ≤ unramifiedOfDegree p K Ω s :=
    unramifiedOfDegree_le_of_dvd hs.ne' hms
  have h1 : frobT p K Ω m = 1 := by
    ext x
    rw [← frob_unramifiedOfDegree_inclusion hm0 hs hKmKs x]
    have h2 := resHom_apply hsD τ (inclusion hKmKs x)
    rw [hτ] at h2
    rw [show frob (isUnramified_unramifiedOfDegree p K Ω s) = frobT p K Ω s from rfl, h2]
    have := (mem_lift (inclusion hsD (inclusion hKmKs x))).1 (hKm x.2)
      ⟨τ, Subgroup.mem_zpowers τ⟩
    exact congrArg Subtype.val this
  have := orderOf_frob (isUnramified_unramifiedOfDegree p K Ω m)
  rw [show frob (isUnramified_unramifiedOfDegree p K Ω m) = frobT p K Ω m from rfl, h1,
    orderOf_one, finrank_unramifiedOfDegree p K Ω hm0] at this
  rw [← hfM, ← hmdef, ← this]

section Abelian

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Restrictions of elements of `Gal(L/K)` to the cyclic subextensions are values of the cyclic
reciprocity maps. -/
theorem resCyc_mem_range (σ : L ≃ₐ[K] L) : resCyc L σ ∈ (recCyc p L).range := by
  classical
  haveI := finite_cycSub (L := L)
  haveI := Fintype.ofFinite (CycSub L)
  set s₀ := ∏ E : CycSub L, cycDeg p E.1
  have hs₀ : 0 < s₀ := Finset.prod_pos fun E _ ↦ cycDeg_pos E.1
  haveI : IsGalois K (unramifiedOfDegree p K Ω s₀) :=
    isGalois_of_isUnramified (isUnramified_unramifiedOfDegree p K Ω s₀)
  obtain ⟨D, hDdef⟩ : ∃ D, D = L ⊔ unramifiedOfDegree p K Ω s₀ := ⟨_, rfl⟩
  haveI : FiniteDimensional K D := hDdef ▸ inferInstance
  haveI : IsGalois K D := hDdef ▸ inferInstance
  obtain ⟨s, hsdef⟩ : ∃ s, s = f p K D := ⟨_, rfl⟩
  have hs : 0 < s := hsdef ▸ f_pos
  have hKs : unramifiedOfDegree p K Ω s ≤ D := unramifiedOfDegree_le_of_f_eq D hsdef.symm
  have hLD : L ≤ D := hDdef ▸ le_sup_left
  have hs₀s : s₀ ∣ s := by
    have := f_dvd_f_of_le (p := p)
      (show unramifiedOfDegree p K Ω s₀ ≤ D from hDdef ▸ le_sup_right)
    rwa [(isUnramified_unramifiedOfDegree p K Ω s₀).f_eq, finrank_unramifiedOfDegree p K Ω hs₀,
      ← hsdef] at this
  have key : ∀ τ : D ≃ₐ[K] D, resHom hKs τ = frobT p K Ω s →
      resCyc L (resHom hLD τ) ∈ (recCyc p L).range := by
    intro τ hτ
    have hf := f_fixedField_frobLift hs hsdef.symm hKs τ hτ
    have hπ := uniformizer_spec (p := p) (K := fixedField (Subgroup.zpowers τ))
    have hπ0 : Algebra.norm K (uniformizer p (fixedField (Subgroup.zpowers τ))) ≠ 0 :=
      Algebra.norm_ne_zero_iff.2 hπ.ne_zero
    refine ⟨Units.mk0 _ hπ0, funext fun E ↦ ?_⟩
    rw [recCyc_apply, resCyc_apply, resHom_trans]
    exact cycRec_norm_frobLift E.1 hs
      ((Finset.dvd_prod_of_mem _ (Finset.mem_univ E)).trans hs₀s) D (E.2.1.trans hLD) hKs τ hτ hf
      _ hπ hπ0
  obtain ⟨φ, hφ⟩ := resHom_surjective hKs (frobT p K Ω s)
  obtain ⟨g, rfl⟩ := resHom_surjective hLD σ
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
    ((zpowers_frob (isUnramified_unramifiedOfDegree p K Ω s)).symm ▸ Subgroup.mem_top
      (resHom hKs g))
  obtain ⟨a, ha⟩ : ∃ a, a = g * φ ^ (-j) * φ := ⟨_, rfl⟩
  have h1 : resHom hKs a = frobT p K Ω s := by
    rw [ha, map_mul, map_mul, map_zpow, hφ, ← hj, zpow_neg, mul_inv_cancel, one_mul]
  have hg : g = a * φ⁻¹ * φ ^ j := by
    rw [ha, mul_inv_cancel_right, zpow_neg, inv_mul_cancel_right]
  set F := (resCyc L).comp (resHom hLD)
  have hF : ∀ τ, resHom hKs τ = frobT p K Ω s → F τ ∈ (recCyc p L).range := key
  change F g ∈ _
  rw [hg, map_mul, map_mul, map_inv, map_zpow]
  exact mul_mem (mul_mem (hF _ h1) (inv_mem (hF φ hφ))) (zpow_mem (hF φ hφ) j)

theorem normGroup_le_ker_recCyc : normGroup K L ≤ (recCyc p L).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  refine funext fun E ↦ ?_
  change cycRec p E.1 x = 1
  rw [cycRec_eq_one_iff]
  exact normGroup_le_of_algHom (inclusion E.2.1) hx

theorem card_range_resCyc : Nat.card (resCyc L).range = Module.finrank K L := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (resCyc_injective (L := L))).toEquiv,
    IsGalois.card_aut_eq_finrank]

/-- The image of the cyclic reciprocity maps is the image of the Galois group. -/
theorem range_recCyc_and_ker :
    (recCyc p L).range = (resCyc L).range ∧ (recCyc p L).ker = normGroup K L := by
  haveI := finite_cycSub (L := L)
  have hle : (resCyc L).range ≤ (recCyc p L).range := by
    rintro _ ⟨σ, rfl⟩; exact resCyc_mem_range L σ
  have hN := normGroup_le_ker_recCyc (p := p) L
  have h1 : Module.finrank K L ≤ (recCyc p L).ker.index := by
    rw [Subgroup.index_ker, ← card_range_resCyc L]
    exact Subgroup.card_le_of_le hle
  have h2 := index_normGroup_le (p := p) (K := K) (L := L)
  have h3 := Subgroup.relIndex_mul_index hN
  have h5 : (normGroup K L).relIndex (recCyc p L).ker = 1 := by
    have h6 : (recCyc p L).ker.index ∣ (normGroup K L).index := Subgroup.index_dvd_of_le hN
    have h7 : (recCyc p L).ker.index = (normGroup K L).index :=
      le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero (index_normGroup_ne_zero (p := p))) h6)
        (h2.trans h1)
    rw [h7] at h3
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (index_normGroup_ne_zero (p := p)))
      (h3.trans (one_mul _).symm)
  have hker : (recCyc p L).ker = normGroup K L :=
    le_antisymm (Subgroup.relIndex_eq_one.1 h5) hN
  refine ⟨(Subgroup.eq_of_le_of_card_ge hle ?_).symm, hker⟩
  rw [card_range_resCyc, ← Subgroup.index_ker, hker]
  exact h2

variable (p) in
/-- **The local reciprocity map** of a finite abelian `L ⊆ Ω`. -/
noncomputable def abRec : Kˣ →* (L ≃ₐ[K] L) :=
  (MonoidHom.ofInjective (resCyc_injective (L := L))).symm.toMonoidHom.comp
    ((recCyc p L).codRestrict (resCyc L).range fun x ↦
      (range_recCyc_and_ker (p := p) L).1 ▸ ⟨x, rfl⟩)

theorem resCyc_abRec (x : Kˣ) : resCyc L (abRec p L x) = recCyc p L x := by
  have := (MonoidHom.ofInjective (resCyc_injective (L := L))).apply_symm_apply
    ⟨recCyc p L x, (range_recCyc_and_ker (p := p) L).1 ▸ ⟨x, rfl⟩⟩
  exact congrArg Subtype.val this

/-- `abRec L` restricts to the cyclic reciprocity maps. -/
theorem resHom_abRec (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E] [IsCyclic (E ≃ₐ[K] E)]
    (hE : E ≤ L) (x : Kˣ) : resHom hE (abRec p L x) = cycRec p E x :=
  congrFun (resCyc_abRec L x) ⟨E, hE, inferInstance, inferInstance⟩

/-- Uniqueness: `abRec L x` is the only automorphism restricting to `cycRec E x` on every cyclic
`E ⊆ L`. -/
theorem eq_abRec_iff (x : Kˣ) (σ : L ≃ₐ[K] L) :
    σ = abRec p L x ↔ ∀ E : CycSub L, resHom E.2.1 σ = cycRec p E.1 x := by
  constructor
  · rintro rfl E; exact congrFun (resCyc_abRec L x) E
  · intro h
    refine resCyc_injective (L := L) ?_
    rw [resCyc_abRec]
    exact funext h

theorem ker_abRec : (abRec p L).ker = normGroup K L := by
  rw [← (range_recCyc_and_ker (p := p) L).2]
  ext x
  simp only [MonoidHom.mem_ker]
  rw [← (resCyc_injective (L := L)).eq_iff, map_one, resCyc_abRec]

theorem abRec_surjective : Function.Surjective (abRec p L) := by
  intro σ
  obtain ⟨x, hx⟩ : resCyc L σ ∈ (recCyc p L).range :=
    (range_recCyc_and_ker (p := p) L).1 ▸ ⟨σ, rfl⟩
  refine ⟨x, resCyc_injective (L := L) ?_⟩
  rw [resCyc_abRec, hx]

variable (p) in
/-- **Local reciprocity**: `Kˣ / N_{L/K} Lˣ ≃ Gal(L/K)` for finite abelian `L ⊆ Ω`. -/
noncomputable def abRecEquiv : Kˣ ⧸ normGroup K L ≃* (L ≃ₐ[K] L) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_abRec (p := p) L).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (abRec_surjective (p := p) L))

/-- Compatibility with restriction to abelian subextensions. -/
theorem resHom_abRec_of_le (L' : IntermediateField K Ω) [FiniteDimensional K L']
    [IsAbelianGalois K L'] (h : L' ≤ L) (x : Kˣ) :
    resHom h (abRec p L x) = abRec p L' x := by
  rw [eq_abRec_iff]
  intro E
  rw [resHom_trans]
  exact resHom_abRec (p := p) L E.1 (E.2.1.trans h) x

/-- For cyclic `L`, `abRec L = cycRec L`. -/
theorem abRec_eq_cycRec [IsCyclic (L ≃ₐ[K] L)] (x : Kˣ) : abRec p L x = cycRec p L x := by
  have := resHom_abRec (p := p) L L le_rfl x
  rw [← this]
  ext y
  rw [resHom_apply]
  rfl

end Abelian

end PadicField
