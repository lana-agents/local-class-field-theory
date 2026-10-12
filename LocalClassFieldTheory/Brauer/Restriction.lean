/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.Unramified
import LocalClassFieldTheory.Reciprocity.BaseChange

/-!
# Restriction of Brauer classes and `inv_{K'} ∘ res = [K' : K] · inv_K`

For a finite extension `K' ⊆ Ω` of `K` we define the restriction map
`Brauer.res K' : Br(K) → Br(K')` (pull back along `Gal(Ω/K') ⊆ Gal(Ω/K)`).

On unramified classes we compute it explicitly: if `n = f' m` (`f' = f(K'/K)`), the restriction
of the carry cocycle of `a ∈ Kˣ` on `Gal(K_n/K)` (generator `Frob_K`) is the inflation of the carry
cocycle of `a` on `Gal(K'_m/K')` (generator `Frob_{K'}`), because `Frob_{K'}` acts on `K_n` as
`Frob_K ^ f'` (`PadicField.restrictNormalHom_resScalars`). Since `v_{K'} = e · v_K` and
`e f' = [K' : K]`:

`PadicField.invUr_res : inv_{K'}(res α) = [K' : K] · inv_K(α)` for `α ∈ Br(K^ur/K)`.

## Main results

* `Brauer.resScalars`, `Brauer.continuous_resScalars`, `Brauer.res`.
* `PadicField.res_infl_cupClass`, `PadicField.res_mem_brUr`, **`PadicField.invUr_res`**.
-/

open ContH2 Brauer IntermediateField

namespace Brauer

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (K' : IntermediateField K Ω)

/-- `Gal(Ω/K') ⊆ Gal(Ω/K)`. -/
def resScalars : (Ω ≃ₐ[K'] Ω) →* (Ω ≃ₐ[K] Ω) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem resScalars_apply (σ : Ω ≃ₐ[K'] Ω) (x : Ω) : resScalars K' σ x = σ x := rfl

theorem continuous_resScalars [Algebra.IsIntegral K Ω] : Continuous (resScalars K') := by
  refine continuous_of_continuousAt_one (resScalars K') ?_
  intro V hV
  rw [map_one] at hV
  obtain ⟨E, hE, hEV⟩ := (krullTopology_mem_nhds_one_iff K Ω V).1 hV
  let b := Module.finBasis K E
  let S : Set Ω := Set.range fun i => (b i : Ω)
  haveI : Finite S := Set.finite_range _ |>.to_subtype
  let E' : IntermediateField K' Ω := adjoin K' S
  haveI : FiniteDimensional K' E' := finiteDimensional_adjoin fun x _ =>
    (Algebra.IsIntegral.isIntegral (R := K) x).tower_top
  rw [Filter.mem_map]
  refine Filter.mem_of_superset ((E'.fixingSubgroup_isOpen).mem_nhds E'.fixingSubgroup.one_mem)
    fun τ hτ => hEV ?_
  have hS : ∀ i, τ (b i : Ω) = b i := fun i =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ _ (subset_adjoin K' S ⟨i, rfl⟩)
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  suffices h : ∀ y : E, resScalars K' τ (y : Ω) = y from fun x hx => h ⟨x, hx⟩
  intro y
  have key : (y : Ω) = ∑ i, b.repr y i • (b i : Ω) := by
    conv_lhs => rw [← b.sum_repr y]
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul]
  rw [key, map_sum]
  simp only [map_smul, resScalars_apply, hS]

/-- **Restriction** `Br(K) → Br(K')` for an intermediate field `K'`. -/
noncomputable def res [Algebra.IsIntegral K Ω] : Br K Ω →* Br K' Ω :=
  ContH2.map (resScalars K') (continuous_resScalars K') (MonoidHom.id Ωˣ) (fun _ _ => rfl)

theorem res_mk [Algebra.IsIntegral K Ω] (f : cocycles (Ω ≃ₐ[K] Ω) Ωˣ) :
    res K' (mk f) = mk (cocyclesMap (resScalars K') (continuous_resScalars K') (MonoidHom.id Ωˣ)
      (fun _ _ => rfl) f) := rfl

end Brauer

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]
variable (K' : IntermediateField K Ω) [FiniteDimensional K K']

/-- `Frob_{K'}` acts on `K_{f' m}` as `Frob_K ^ f'`, at the level of `Gal(Ω/K')`. -/
theorem restrictNormalHom_resScalars {m : ℕ} (hm : 0 < m) (σ : Ω ≃ₐ[K'] Ω) (i : ℕ)
    (hσ : AlgEquiv.restrictNormalHom (unramifiedOfDegree p K' Ω m) σ = frobT p K' Ω m ^ i) :
    AlgEquiv.restrictNormalHom (unramifiedOfDegree p K Ω (f p K K' * m)) (resScalars K' σ) =
      frobT p K Ω (f p K K' * m) ^ (f p K K' * i) := by
  have hfm : 0 < f p K K' * m := Nat.mul_pos f_pos hm
  let φ₁ : unramifiedOfDegree p K Ω (f p K K' * m) →ₐ[K] Ω :=
    (unramifiedOfDegree p K Ω (f p K K' * m)).val.comp
      (AlgEquiv.restrictNormalHom (unramifiedOfDegree p K Ω (f p K K' * m))
        (resScalars K' σ)).toAlgHom
  let φ₂ : unramifiedOfDegree p K Ω (f p K K' * m) →ₐ[K] Ω :=
    (unramifiedOfDegree p K Ω (f p K K' * m)).val.comp
      (frobT p K Ω (f p K K' * m) ^ (f p K K' * i)).toAlgHom
  have key : φ₁ = φ₂ := by
    refine algHom_ext_of_eq_adjoin K (unramifiedOfDegree_def p K Ω _) fun z hz ↦ ?_
    rw [mem_rootSet_X_pow_sub_X (one_lt_q_pow hfm)] at hz
    have hzK : z ∈ unramifiedOfDegree p K Ω (f p K K' * m) :=
      mem_unramifiedOfDegree_of_pow_eq hfm hz
    have hzK' : z ∈ unramifiedOfDegree p K' Ω m := unramifiedOfDegree_le_baseChange K' hm hzK
    simp only [φ₁, φ₂, AlgHom.comp_apply, coe_val, AlgEquiv.coe_toAlgHom]
    rw [AlgEquiv.restrictNormalHom_apply, frobT_pow_apply_of_pow_eq hfm _ ⟨z, hzK⟩ hz,
      resScalars_apply]
    have h1 := AlgEquiv.restrictNormalHom_apply (unramifiedOfDegree p K' Ω m) σ ⟨z, hzK'⟩
    rw [hσ, frobT_pow_apply_of_pow_eq hm _ ⟨z, hzK'⟩ (by
      rw [q_baseChange, ← pow_mul]; exact hz)] at h1
    rw [← h1, q_baseChange, ← pow_mul]
  ext x
  exact DFunLike.congr_fun key x

theorem restrictNormalHom_resScalars_idx {m : ℕ} (hm : 0 < m) (x : Ω ≃ₐ[K'] Ω) :
    AlgEquiv.restrictNormalHom (unramifiedOfDegree p K Ω (f p K K' * m)) (resScalars K' x) =
      frobT p K Ω (f p K K' * m) ^ (f p K K' * idx (frobT p K' Ω m) (mem_zpowers_frob _)
        (AlgEquiv.restrictNormalHom (unramifiedOfDegree p K' Ω m) x)) :=
  restrictNormalHom_resScalars K' hm x _ (pow_idx (frobT p K' Ω m) (mem_zpowers_frob _) _).symm

theorem res_infl_cup_apply {m : ℕ} (hm : 0 < m) (a : Kˣ) (σ τ : Ω ≃ₐ[K'] Ω) :
    Units.map (algebraMap (unramifiedOfDegree p K Ω (f p K K' * m)) Ω : _ →* Ω)
      (cupCocycle (frobT p K Ω (f p K K' * m)) (mem_zpowers_frob _) a
        (AlgEquiv.restrictNormalHom _ (resScalars K' σ),
          AlgEquiv.restrictNormalHom _ (resScalars K' τ))) =
    Units.map (algebraMap (unramifiedOfDegree p K' Ω m) Ω : _ →* Ω)
      (cupCocycle (frobT p K' Ω m) (mem_zpowers_frob _) (Units.map (algebraMap K K' : K →* K') a)
        (AlgEquiv.restrictNormalHom _ σ, AlgEquiv.restrictNormalHom _ τ)) := by
  have hfm : 0 < f p K K' * m := Nat.mul_pos f_pos hm
  have ho : orderOf (frobT p K Ω (f p K K' * m)) = f p K K' * orderOf (frobT p K' Ω m) := by
    rw [orderOf_frob, finrank_unramifiedOfDegree p K Ω hfm, orderOf_frob,
      finrank_unramifiedOfDegree p K' Ω hm]
  have ha : Units.map (algebraMap (unramifiedOfDegree p K Ω (f p K K' * m)) Ω : _ →* Ω)
      (fixedUnitsEquiv K (unramifiedOfDegree p K Ω (f p K K' * m)) a :
        (unramifiedOfDegree p K Ω (f p K K' * m))ˣ) =
      Units.map (algebraMap (unramifiedOfDegree p K' Ω m) Ω : _ →* Ω)
      (fixedUnitsEquiv K' (unramifiedOfDegree p K' Ω m) (Units.map (algebraMap K K' : K →* K') a) :
        (unramifiedOfDegree p K' Ω m)ˣ) := by
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe, coe_fixedUnitsEquiv]
    rfl
  rw [cupCocycle_apply, cupCocycle_apply]
  exact cupFun_comp (frobT p K Ω (f p K K' * m)) (mem_zpowers_frob _) (frobT p K' Ω m)
    (mem_zpowers_frob _) f_pos ho _ _ (restrictNormalHom_resScalars_idx K' hm) _ _ _ _ ha σ τ


theorem res_infl_cupClass [IsGalois K Ω] {m : ℕ} (hm : 0 < m) (a : Kˣ) :
    res K' (infl (unramifiedOfDegree p K Ω (f p K K' * m))
      (cupClass (frobT p K Ω (f p K K' * m)) (mem_zpowers_frob _) a)) =
    infl (unramifiedOfDegree p K' Ω m)
      (cupClass (frobT p K' Ω m) (mem_zpowers_frob _)
        (Units.map (algebraMap K K' : K →* K') a)) := by
  rw [cupClass, cupClass, infl_mk, infl_mk, res_mk]
  exact congrArg mk (cocycles_ext fun σ τ => res_infl_cup_apply K' hm a σ τ)

omit [IsAlgClosed Ω] in
include hp in
theorem vQZ_algebraMap {m : ℕ} (hm : 0 < m) (a : Kˣ) :
    vQZ p K' m (Units.map (algebraMap K K' : K →* K') a) =
      vQZ p K (f p K K' * m) a ^ Module.finrank K K' := by
  rw [vQZ_apply, vQZ_apply, ← ofAdd_nsmul, ← QuotientAddGroup.mk_nsmul, Units.coe_map,
    MonoidHom.coe_coe, v_algebraMap, ← e_mul_f (p := p) (K := K) (L := K')]
  congr 2
  have hf : (f p K K' : ℚ) ≠ 0 := by exact_mod_cast (f_pos (p := p) (K := K) (L := K')).ne'
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [nsmul_eq_mul]
  push_cast
  field_simp

/-- **`inv_{K'} ∘ res = [K' : K] · inv_K`** on unramified classes; in particular restriction maps
`Br(K^ur/K)` into `Br(K'^ur/K')`. -/
theorem res_mem_brUr_and_invUr [IsGalois K Ω] {α : Br K Ω} (hα : α ∈ brUr p K Ω) :
    ∃ h : res K' α ∈ brUr p K' Ω,
      invUr ⟨res K' α, h⟩ = invUr ⟨α, hα⟩ ^ Module.finrank K K' := by
  obtain ⟨N, hN, β, rfl⟩ := hα
  have h2N : 0 < 2 * N := by omega
  have hn : 0 < f p K K' * (2 * N) := Nat.mul_pos f_pos h2N
  have hle : unramifiedOfDegree p K Ω N ≤ unramifiedOfDegree p K Ω (f p K K' * (2 * N)) :=
    unramifiedOfDegree_le_of_dvd hn.ne' (dvd_mul_of_dvd_right (dvd_mul_left N 2) _)
  obtain ⟨a, ha⟩ := unrClass_surjective (isUnramified_unramifiedOfDegree p K Ω _) (inflRel hle β)
  have hn1 : 1 < Module.finrank K (unramifiedOfDegree p K Ω (f p K K' * (2 * N))) := by
    rw [finrank_unramifiedOfDegree p K Ω hn]
    have := f_pos (p := p) (K := K) (L := K')
    nlinarith
  have hm1 : 1 < Module.finrank K' (unramifiedOfDegree p K' Ω (2 * N)) := by
    rw [finrank_unramifiedOfDegree p K' Ω h2N]
    omega
  have hα : infl (unramifiedOfDegree p K Ω N) β =
      infl (unramifiedOfDegree p K Ω (f p K K' * (2 * N)))
        (cupClass (frobT p K Ω (f p K K' * (2 * N))) (mem_zpowers_frob _) a) := by
    rw [← infl_inflRel hle, ← ha, unrClass_eq_cupClass _ hn1]
  have hres := res_infl_cupClass (p := p) K' h2N a
  rw [← hα, ← unrClass_eq_cupClass _ hm1] at hres
  refine ⟨⟨2 * N, h2N, _, hres.symm⟩, ?_⟩
  have e1 : invUr (p := p) ⟨res K' (infl (unramifiedOfDegree p K Ω N) β), ⟨2 * N, h2N, _,
      hres.symm⟩⟩ = vQZ p K' (2 * N) (Units.map (algebraMap K K' : K →* K') a) := by
    exact (invUrFun_eq _ h2N _ hres.symm).trans (invN_unrClassN h2N _)
  have e2 : invUr (p := p) ⟨infl (unramifiedOfDegree p K Ω N) β, infl_mem_brUr hN β⟩ =
      vQZ p K (f p K K' * (2 * N)) a := by
    refine (invUrFun_eq _ hn (inflRel hle β) (infl_inflRel hle β)).trans ?_
    rw [← ha]
    exact invN_unrClassN hn a
  rw [e1, e2, vQZ_algebraMap K' h2N]

end PadicField
