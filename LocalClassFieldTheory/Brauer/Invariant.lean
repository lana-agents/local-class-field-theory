/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.Restriction
import LocalClassFieldTheory.Brauer.OrderBound

/-!
# The invariant map `inv : Br(K) ≃ ℚ/ℤ`

Main results (`K` finite over `ℚ_[p]`, `Ω/K` an algebraically closed Galois extension, i.e. an
algebraic closure):

* `Brauer.mem_range_infl_of_res_eq_one` : `ker(res : Br(K) → Br(L)) ⊆ infl(Br(L/K))` for finite
  Galois `L ⊆ Ω` (inflation–restriction at the level of `Gal(Ω/K)`).
* `PadicField.range_infl_eq` : for finite Galois `L ⊆ Ω` of degree `n`, the image of `Br(L/K)` in
  `Br(K)` equals the image of `Br(K_n/K)`: every class split by `L` is split by `K_n` and
  conversely (`inv_L ∘ res = n · inv_K` kills `Br(K_n/K)`, and `|Br(L/K)| ≤ n = |Br(K_n/K)|`).
* `PadicField.brUr_eq_top` : every Brauer class is split by an unramified extension.
* **`PadicField.invEquiv : Br(K) ≃* ℚ/ℤ`**, `PadicField.card_relBr_eq : |Br(L/K)| = [L : K]`,
  `PadicField.invEquiv_res` (`inv_{K'} ∘ res = [K' : K] · inv_K` for all classes), and the
  **fundamental class** `PadicField.fundClass L` with `inv (infl u_{L/K}) = 1/[L : K]`.
-/

open ContH2 IntermediateField groupCohomology

namespace Brauer

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω) [Normal K L]

/-- `ker(Gal(Ω/K) → Gal(L/K)) → Gal(Ω/L)`. -/
def kerToGal : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker →* (Ω ≃ₐ[L] Ω) where
  toFun k :=
    { (k : Ω ≃ₐ[K] Ω).toRingEquiv with
      commutes' := fun x => by
        have h1 := congrArg (fun σ : L ≃ₐ[K] L => ((σ x : L) : Ω)) (MonoidHom.mem_ker.1 k.2)
        simp only [AlgEquiv.restrictNormalHom_apply, AlgEquiv.one_apply] at h1
        exact h1 }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem kerToGal_apply (k : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker) (x : Ω) :
    kerToGal L k x = (k : Ω ≃ₐ[K] Ω) x := rfl

theorem continuous_kerToGal [Algebra.IsIntegral K Ω] [FiniteDimensional K L] :
    Continuous (kerToGal L) := by
  refine continuous_of_continuousAt_one (kerToGal L) ?_
  intro V hV
  rw [map_one] at hV
  obtain ⟨E', hE', hE'V⟩ := (krullTopology_mem_nhds_one_iff L Ω V).1 hV
  haveI : FiniteDimensional K (E'.restrictScalars K) := by
    have : FiniteDimensional K E' := Module.Finite.trans L E'
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

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
/-- **Inflation–restriction for `Br`**: a class of `Br(K)` whose restriction to `Br(L)` is trivial
comes from `Br(L/K)`. -/
theorem mem_range_infl_of_res_eq_one [IsGalois K Ω] [FiniteDimensional K L] [IsGalois K L]
    {α : Br K Ω} (h : res L α = 1) : α ∈ (infl (Ω := Ω) L).range := by
  induction α using ContH2.induction_on with | h f => ?_
  rw [res_mk, mk_eq_one_iff] at h
  obtain ⟨y, hy, hyf⟩ := h
  let x : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker → Ωˣ := fun k => y (kerToGal L k)
  have hx : IsLocallyConstant x := hy.comp_continuous (continuous_kerToGal L)
  have hfx : ∀ n n' : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker,
      f ((n : Ω ≃ₐ[K] Ω), (n' : Ω ≃ₐ[K] Ω)) = (n : Ω ≃ₐ[K] Ω) • x n' / x (n * n') * x n := by
    intro n n'
    have := congrFun hyf (kerToGal L n, kerToGal L n')
    rw [cocyclesMap_apply, MonoidHom.id_apply] at this
    exact this.symm.trans (by simp only [x, dx_apply, map_mul]; rfl)
  obtain ⟨β, hβ⟩ := exists_map_eq_of_res (AlgEquiv.restrictNormalHom L)
    (InfiniteGalois.restrictNormalHom_continuous L) (AlgEquiv.restrictNormalHom_surjective Ω)
    (Units.map (algebraMap L Ω : L →* Ω)) (Units.map_injective (algebraMap L Ω).injective)
    (units_map_restrictNormalHom_smul L) (mem_range_of_fixed L) isLocallyConstant_smul_units
    (isMulCoboundary₁_ker L) f x hx hfx
  exact ⟨β, hβ⟩

end Brauer

namespace PadicField

open Brauer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

include hp in
theorem vQZ_pow_self {n : ℕ} (hn : 0 < n) (a : Kˣ) : vQZ p K n a ^ n = 1 := by
  rw [vQZ_apply, ← ofAdd_nsmul, ← QuotientAddGroup.mk_nsmul, nsmul_eq_mul,
    mul_div_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℚ) ≠ 0)]
  rw [← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq, AddCircle.coe_eq_zero_iff]
  exact ⟨v p (a : K), by simp⟩

omit [IsGalois K Ω] in
theorem invN_pow_self {n : ℕ} (hn : 0 < n) (β : RelBr K (unramifiedOfDegree p K Ω n)) :
    invN n β ^ n = 1 := by
  obtain ⟨a, rfl⟩ := unrClass_surjective (isUnramified_unramifiedOfDegree p K Ω n) β
  rw [show invN n (unrClass (isUnramified_unramifiedOfDegree p K Ω n) a) =
    invN n (unrClassN (p := p) (Ω := Ω) n a) from rfl, invN_unrClassN hn, vQZ_pow_self hn]

theorem card_range_of_injective {G N : Type*} [Group G] [Group N] {f : G →* N}
    (hf : Function.Injective f) : Nat.card f.range = Nat.card G :=
  (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]

/-- Classes split by `K_n`, `n = [L : K]`, are split by `L`. -/
theorem infl_unramified_mem_range (β : RelBr K (unramifiedOfDegree p K Ω (Module.finrank K L))) :
    infl (unramifiedOfDegree p K Ω (Module.finrank K L)) β ∈ (infl (Ω := Ω) L).range := by
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  set α := infl (Ω := Ω) (unramifiedOfDegree p K Ω (Module.finrank K L)) β
  have hα : α ∈ brUr p K Ω := infl_mem_brUr hn β
  obtain ⟨h, hinv⟩ := res_mem_brUr_and_invUr (p := p) L hα
  apply mem_range_infl_of_res_eq_one L
  have h1 : invUr (p := p) ⟨res L α, h⟩ = 1 := by
    rw [hinv]
    change invUrFun ⟨α, hα⟩ ^ _ = 1
    rw [invUrFun_eq ⟨α, hα⟩ hn β rfl]
    exact invN_pow_self hn β
  have := invUr_injective (p := p) (K := L) (Ω := Ω) (h1.trans (map_one _).symm)
  exact congrArg Subtype.val this

/-- **The image of `Br(L/K)` in `Br(K)` is the image of `Br(K_n/K)`**, `n = [L : K]`. -/
theorem range_infl_eq :
    (infl (Ω := Ω) L).range =
      (infl (Ω := Ω) (unramifiedOfDegree p K Ω (Module.finrank K L))).range := by
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  have hle : (infl (Ω := Ω) (unramifiedOfDegree p K Ω (Module.finrank K L))).range ≤
      (infl (Ω := Ω) L).range := by
    rintro _ ⟨β, rfl⟩
    exact infl_unramified_mem_range L β
  obtain ⟨h0, hcard⟩ := card_relBr_le (p := p) (K := K) (L := L)
  haveI : Finite (RelBr K L) := Nat.finite_of_card_ne_zero h0
  haveI : Finite (infl (Ω := Ω) L).range := Set.finite_range _ |>.to_subtype
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_range_of_injective (infl_injective L),
    card_range_of_injective (infl_injective _), card_relBr_unramifiedOfDegree hn]
  exact hcard

variable (p) in
include hp in
/-- `|Br(L/K)| = [L : K]`. -/
theorem card_relBr_eq : Nat.card (RelBr K L) = Module.finrank K L := by
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  rw [← card_range_of_injective (infl_injective (Ω := Ω) L), range_infl_eq (p := p),
    card_range_of_injective (infl_injective _), card_relBr_unramifiedOfDegree hn]

variable (p K Ω) in
/-- **Every Brauer class is split by an unramified extension**: `Br(K) = Br(K^ur/K)`. -/
theorem brUr_eq_top : brUr p K Ω = ⊤ := by
  refine eq_top_iff.2 fun α _ => ?_
  obtain ⟨L, hL, hLG, β, rfl⟩ := exists_infl_eq α
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  obtain ⟨β', hβ'⟩ : infl (Ω := Ω) L β ∈
      (infl (Ω := Ω) (unramifiedOfDegree p K Ω (Module.finrank K L))).range := by
    rw [← range_infl_eq]
    exact ⟨β, rfl⟩
  exact ⟨_, hn, β', hβ'⟩

variable (p K Ω) in
/-- **The invariant map** `inv : Br(K) ≃* ℚ/ℤ`. -/
noncomputable def invEquiv : Br K Ω ≃* Multiplicative QZ :=
  Subgroup.topEquiv.symm.trans
    ((MulEquiv.subgroupCongr (brUr_eq_top p K Ω).symm).trans invUrEquiv)

theorem invEquiv_apply (α : Br K Ω) :
    invEquiv p K Ω α = invUr ⟨α, (brUr_eq_top p K Ω).symm ▸ Subgroup.mem_top α⟩ := rfl

/-- On unramified classes the invariant is `v(a)/n` (`a` the periodicity element of the
Frobenius). -/
theorem invEquiv_infl {n : ℕ} (hn : 0 < n) (β : RelBr K (unramifiedOfDegree p K Ω n)) :
    invEquiv p K Ω (infl _ β) = invN n β :=
  invUrFun_eq _ hn β rfl

/-- **`inv_{K'} ∘ res = [K' : K] · inv_K`** for every finite `K' ⊆ Ω`. -/
theorem invEquiv_res (K' : IntermediateField K Ω) [FiniteDimensional K K'] (α : Br K Ω) :
    invEquiv p K' Ω (res K' α) = invEquiv p K Ω α ^ Module.finrank K K' := by
  obtain ⟨h, e⟩ := res_mem_brUr_and_invUr (p := p) K'
    ((brUr_eq_top p K Ω).symm ▸ Subgroup.mem_top α)
  exact e

section Fundamental

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]

theorem exists_fundClass : ∃ u : RelBr K L, invEquiv p K Ω (infl L u) =
    Multiplicative.ofAdd (((1 / Module.finrank K L : ℚ) : ℚ) : QZ) := by
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  have hπ : IsUniformizer p K (uniformizer p K) := uniformizer_spec
  set π : Kˣ := Units.mk0 _ hπ.ne_zero
  obtain ⟨u, hu⟩ := infl_unramified_mem_range L (unrClassN (p := p) (Ω := Ω) _ π)
  refine ⟨u, ?_⟩
  rw [hu, invEquiv_infl hn, invN_unrClassN hn, vQZ_apply]
  simp only [π, Units.val_mk0]
  rw [show v p (uniformizer p K) = 1 from hπ]
  simp

/-- The **fundamental class** `u_{L/K} ∈ Br(L/K) = H²(Gal(L/K), Lˣ)`: the class with invariant
`1/[L : K]`. -/
noncomputable def fundClass : RelBr K L := (exists_fundClass (p := p) (Ω := Ω) L).choose

theorem invEquiv_infl_fundClass :
    invEquiv p K Ω (infl L (fundClass (p := p) L)) =
      Multiplicative.ofAdd (((1 / Module.finrank K L : ℚ) : ℚ) : QZ) :=
  (exists_fundClass (p := p) (Ω := Ω) L).choose_spec

theorem orderOf_fundClass : orderOf (fundClass (p := p) (Ω := Ω) L) = Module.finrank K L := by
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  rw [← orderOf_injective _ (infl_injective L),
    ← orderOf_injective (invEquiv p K Ω).toMonoidHom (invEquiv p K Ω).injective,
    MulEquiv.coe_toMonoidHom,
    invEquiv_infl_fundClass, orderOf_ofAdd_eq_addOrderOf]
  have := AddCircle.addOrderOf_coe_rat (p := (1 : ℚ)) (q := 1 / Module.finrank K L)
  rw [mul_one, Rat.cast_id] at this
  rw [this, one_div, Rat.inv_natCast_den, if_neg hn.ne']

/-- `Br(L/K)` is cyclic of order `[L : K]`, generated by the fundamental class. -/
theorem zpowers_fundClass : Subgroup.zpowers (fundClass (p := p) (Ω := Ω) L) = ⊤ := by
  have h0 := card_relBr_eq p (Ω := Ω) L
  haveI : Finite (RelBr K L) :=
    Nat.finite_of_card_ne_zero (h0 ▸ Module.finrank_pos.ne')
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, orderOf_fundClass, h0]

end Fundamental

end PadicField
