/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.LevelNeukirch

/-!
# Cyclic extensions inside standard levels

Every finite cyclic `L ⊆ Ω` is contained in `M ⊔ K_s` for a cyclic totally ramified Galois
`M ⊆ Ω` and some `s` with `[L : K] ∣ s` (`PadicField.exists_totRam_le_sup`): with `D = L ⊔ K_n`,
`n = [L : K]`, `s = f(D/K)` and a lift `φ̃ ∈ Gal(D/K)` of the Frobenius of `K_s`, `M` is the fixed
field of `φ̃`. Consequently `L` lies in the standard level `(M, [M : K] s s!)`
(`PadicField.StdLevel.ofCyclic`).
-/

set_option linter.unusedSectionVars false

open IntermediateField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

omit [IsAlgClosed Ω] in
theorem mul_comm_of_isCyclic {G : Type*} [Group G] [IsCyclic G] (a b : G) : a * b = b * a := by
  letI := IsCyclic.commGroup (α := G)
  exact mul_comm a b

omit [IsAlgClosed Ω] in
/-- The Galois group of a compositum of two cyclic extensions is commutative. -/
theorem mul_comm_of_sup {L U A : IntermediateField K Ω} [Normal K L] [Normal K U]
    [IsCyclic (L ≃ₐ[K] L)] [IsCyclic (U ≃ₐ[K] U)]
    (hA : A = L ⊔ U) (hLA : L ≤ A) (hUA : U ≤ A) (σ τ : A ≃ₐ[K] A) : σ * τ = τ * σ := by
  have h := eq_one_of_resHom_eq_one hA hLA hUA (σ * τ * (τ * σ)⁻¹)
    (by rw [map_mul, map_inv, map_mul, map_mul, mul_comm_of_isCyclic (resHom hLA σ),
      mul_inv_cancel])
    (by rw [map_mul, map_inv, map_mul, map_mul, mul_comm_of_isCyclic (resHom hUA σ),
      mul_inv_cancel])
  exact mul_inv_eq_one.1 h

/-- **Cyclic extensions lie in `M ⊔ K_s`** for a cyclic totally ramified `M`. -/
theorem exists_totRam_le_sup (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    ∃ (M : IntermediateField K Ω) (_ : FiniteDimensional K M) (_ : IsGalois K M)
      (_ : IsCyclic (M ≃ₐ[K] M)) (s : ℕ), e p K M = Module.finrank K M ∧ 0 < s ∧
      Module.finrank K L ∣ s ∧ L ≤ M ⊔ unramifiedOfDegree p K Ω s := by
  classical
  set n := Module.finrank K L
  have hn : 0 < n := Module.finrank_pos
  haveI : IsGalois K (unramifiedOfDegree p K Ω n) :=
    isGalois_of_isUnramified (isUnramified_unramifiedOfDegree p K Ω n)
  obtain ⟨D, hDdef⟩ : ∃ D, D = L ⊔ unramifiedOfDegree p K Ω n := ⟨_, rfl⟩
  haveI : FiniteDimensional K D := hDdef ▸ inferInstance
  haveI : IsGalois K D := hDdef ▸ inferInstance
  obtain ⟨s, hsdef⟩ : ∃ s, s = f p K D := ⟨_, rfl⟩
  have hs : 0 < s := hsdef ▸ f_pos
  have hKs : unramifiedOfDegree p K Ω s ≤ D := unramifiedOfDegree_le_of_f_eq D hsdef.symm
  have hLD : L ≤ D := hDdef ▸ le_sup_left
  have hns : n ∣ s := by
    have := f_dvd_f_of_le (p := p) (show unramifiedOfDegree p K Ω n ≤ D from hDdef ▸ le_sup_right)
    rwa [(isUnramified_unramifiedOfDegree p K Ω n).f_eq, finrank_unramifiedOfDegree p K Ω hn,
      ← hsdef] at this
  have hD : D = L ⊔ unramifiedOfDegree p K Ω s := by
    refine le_antisymm ?_ (sup_le hLD hKs)
    rw [hDdef]
    exact sup_le le_sup_left ((unramifiedOfDegree_le_of_dvd hs.ne' hns).trans le_sup_right)
  haveI : IsCyclic (unramifiedOfDegree p K Ω s ≃ₐ[K] unramifiedOfDegree p K Ω s) :=
    isCyclic_gal (isUnramified_unramifiedOfDegree p K Ω s)
  obtain ⟨φ, hφ⟩ := resHom_surjective hKs (frobT p K Ω s)
  have hcomm : ∀ a b : D ≃ₐ[K] D, a * b = b * a := mul_comm_of_sup hD hLD hKs
  haveI hHn : (Subgroup.zpowers φ).Normal :=
    ⟨fun x hx g ↦ by rwa [hcomm g x, mul_inv_cancel_right]⟩
  set MD := fixedField (Subgroup.zpowers φ)
  set M := lift MD
  let εM : MD ≃ₐ[K] M := liftAlgEquiv MD
  haveI : FiniteDimensional K M := LinearEquiv.finiteDimensional εM.toLinearEquiv
  haveI : IsGalois K M := IsGalois.of_algEquiv εM
  have hMD : M ≤ D := lift_le MD
  have hφM : ∀ y : D, (y : Ω) ∈ M → φ y = y := fun y hy ↦
    (mem_lift y).1 hy ⟨φ, Subgroup.mem_zpowers φ⟩
  -- `M / K` is totally ramified
  have hfM : f p K M = 1 := by
    obtain ⟨m, hmdef⟩ : ∃ m, m = f p K M := ⟨_, rfl⟩
    have hKm : unramifiedOfDegree p K Ω m ≤ M := unramifiedOfDegree_le_of_f_eq M hmdef.symm
    have hm0 : 0 < m := hmdef ▸ f_pos
    have hms : m ∣ s := by
      have := f_dvd_f_of_le (p := p) (hKm.trans hMD)
      rwa [(isUnramified_unramifiedOfDegree p K Ω m).f_eq, finrank_unramifiedOfDegree p K Ω hm0,
        ← hsdef] at this
    have hKmKs : unramifiedOfDegree p K Ω m ≤ unramifiedOfDegree p K Ω s :=
      unramifiedOfDegree_le_of_dvd hs.ne' hms
    have hfix : ∀ x : unramifiedOfDegree p K Ω m,
        (frobT p K Ω s (inclusion hKmKs x) : Ω) = x := by
      intro x
      have h1 := resHom_apply hKs φ (inclusion hKmKs x)
      rw [hφ] at h1
      rw [h1, hφM _ (hKm x.2)]
      rfl
    have h1 : frobT p K Ω m = 1 := by
      ext x
      rw [← frob_unramifiedOfDegree_inclusion hm0 hs hKmKs x, hfix x]
      rfl
    have := orderOf_frob (isUnramified_unramifiedOfDegree p K Ω m)
    rw [show frob (isUnramified_unramifiedOfDegree p K Ω m) = frobT p K Ω m from rfl, h1,
      orderOf_one, finrank_unramifiedOfDegree p K Ω hm0] at this
    rw [← hmdef, ← this]
  have heM : e p K M = Module.finrank K M := by
    have := e_mul_f (p := p) (K := K) (L := M)
    rwa [hfM, mul_one] at this
  -- degrees
  have hφs : φ ^ s = 1 := by
    refine eq_one_of_resHom_eq_one hD hLD hKs _ ?_ ?_
    · rw [map_pow]
      refine orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard _).trans ?_)
      rwa [IsGalois.card_aut_eq_finrank]
    · rw [map_pow, hφ, frobT_pow_eq_one hs]
  have hdegD : Module.finrank K D ≤ s * Module.finrank K M := by
    have h1 := Module.finrank_mul_finrank K MD D
    rw [finrank_fixedField_eq_card, Nat.card_zpowers] at h1
    have h2 : orderOf φ ≤ s := Nat.le_of_dvd hs (orderOf_dvd_of_pow_eq_one hφs)
    have h3 : Module.finrank K MD = Module.finrank K M := εM.toLinearEquiv.finrank_eq
    rw [← h1, h3, mul_comm]
    exact Nat.mul_le_mul_right _ h2
  have hE : M ⊔ unramifiedOfDegree p K Ω s = D := by
    apply eq_of_le_of_finrank_le (sup_le hMD hKs)
    have he := e_dvd_of_algHom (p := p)
      (inclusion (le_sup_left : M ≤ M ⊔ unramifiedOfDegree p K Ω s))
    have hf := f_dvd_of_algHom (p := p)
      (inclusion (le_sup_right : unramifiedOfDegree p K Ω s ≤ M ⊔ unramifiedOfDegree p K Ω s))
    rw [heM] at he
    rw [(isUnramified_unramifiedOfDegree p K Ω s).f_eq, finrank_unramifiedOfDegree p K Ω hs] at hf
    rw [← e_mul_f (p := p) (K := K) (L := (M ⊔ unramifiedOfDegree p K Ω s :
      IntermediateField K Ω))]
    calc Module.finrank K D ≤ s * Module.finrank K M := hdegD
      _ = Module.finrank K M * s := mul_comm _ _
      _ ≤ _ := Nat.mul_le_mul (Nat.le_of_dvd e_pos he) (Nat.le_of_dvd f_pos hf)
  -- `Gal(M/K)` is cyclic
  have hcyc : IsCyclic (M ≃ₐ[K] M) := by
    set Hs := (resHom hKs).ker
    haveI : IsCyclic Hs := by
      refine isCyclic_of_injective ((resHom hLD).comp Hs.subtype) ?_
      rw [injective_iff_map_eq_one]
      rintro ⟨h, hh⟩ h1
      exact Subtype.ext (eq_one_of_resHom_eq_one hD hLD hKs h h1 hh)
    have hψφ : resHom hMD φ = 1 := by
      ext x
      rw [resHom_apply, hφM _ (by exact x.2)]
      rfl
    refine isCyclic_of_surjective ((resHom hMD).comp Hs.subtype) ?_
    intro g
    obtain ⟨g', rfl⟩ := resHom_surjective hMD g
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
      ((zpowers_frob (isUnramified_unramifiedOfDegree p K Ω s)).symm ▸ Subgroup.mem_top
        (resHom hKs g'))
    refine ⟨⟨g' * φ ^ (-j), ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_zpow, hφ, ← hj]
      rw [zpow_neg]
      exact mul_inv_cancel _
    · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_zpow, hψφ, one_zpow,
        mul_one]
  exact ⟨M, inferInstance, inferInstance, hcyc, s, heM, hs, hns, hLD.trans hE.ge⟩

end PadicField
