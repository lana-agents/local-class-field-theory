/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.ClassFieldAxiom.Axiom
import LocalClassFieldTheory.PadicField.Galois

/-!
# The second inequality and unramified norm groups

* `PadicField.index_normGroup_le`: for an abelian extension `L/K` of fields finite over `ℚ_[p]`,
  `[Kˣ : N_{L/K} Lˣ] ≤ [L : K]` (induction along a cyclic tower, using the class field axiom).
* `PadicField.normGroup_of_isUnramified`: for an unramified `L/K` of degree `n`, the norm group
  is `{x | n ∣ v x}`; in particular every unit of `K` is the norm of a unit of `L`
  (`PadicField.exists_norm_eq_of_isUnramified`).
-/

set_option linter.unusedSectionVars false

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]

/-- Index of the image of a subgroup under a homomorphism. -/
theorem index_map_le_mul {G G' : Type*} [Group G] [Group G'] (f : G →* G') (H : Subgroup G)
    (hH : H.index ≠ 0) : (H.map f).index ≤ f.range.index * H.index := by
  have hle : H.map f ≤ f.range := by
    rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩
  rw [← Subgroup.relIndex_mul_index hle, mul_comm]
  refine Nat.mul_le_mul_left _ ?_
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
    Subgroup.relIndex_top_right]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hH) (Subgroup.index_dvd_of_le le_sup_left)

/-- Norm groups in a tower. -/
theorem normGroup_tower {K E L : Type*} [Field K] [Field E] [Field L] [Algebra K E] [Algebra E L]
    [Algebra K L] [IsScalarTower K E L] [FiniteDimensional K E] [FiniteDimensional E L] :
    normGroup K L = (normGroup E L).map (Units.map (Algebra.norm K : E →* K)) := by
  ext x
  simp only [normGroup, Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map (Algebra.norm E : L →* E) y, ⟨y, rfl⟩, Units.ext ?_⟩
    simp [Algebra.norm_norm]
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, Units.ext (by simp [Algebra.norm_norm])⟩

/-- The image of a finite-index subgroup under a homomorphism with finite-index range has finite
index. -/
theorem index_map_ne_zero {G G' : Type*} [Group G] [Group G'] (f : G →* G') (H : Subgroup G)
    (hH : H.index ≠ 0) (hr : f.range.index ≠ 0) : (H.map f).index ≠ 0 := by
  have hle : H.map f ≤ f.range := by
    rintro _ ⟨x, -, rfl⟩; exact ⟨x, rfl⟩
  rw [← Subgroup.relIndex_mul_index hle]
  refine mul_ne_zero ?_ hr
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
    Subgroup.relIndex_top_right]
  exact fun h ↦ hH (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le le_sup_left))

/-- **The second inequality** (with finiteness): for an abelian extension `L/K`,
`0 < [Kˣ : N Lˣ] ≤ [L : K]`. -/
theorem index_normGroup_pos_le {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K]
    [Algebra ℚ_[p] L] [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
    [FiniteDimensional ℚ_[p] L] [IsAbelianGalois K L] :
    0 < (normGroup K L).index ∧ (normGroup K L).index ≤ Module.finrank K L := by
  haveI := finiteDimensional_tower (p := p) K L
  -- strong induction on the degree
  induction h : Module.finrank K L using Nat.strong_induction_on generalizing L with
  | _ n ih =>
  by_cases hbot : ∀ g : L ≃ₐ[K] L, g = 1
  · -- trivial Galois group: `L = K`
    have hn : Module.finrank K L = 1 := by
      rw [← IsGalois.card_aut_eq_finrank, Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b ↦ (hbot a).trans (hbot b).symm⟩, ⟨1⟩⟩
    rw [← h, hn]
    -- every element of `K` is a norm
    have h1 : (normGroup K L).index = 1 := by
      refine Subgroup.index_eq_one.2 (eq_top_iff.2 fun x _ ↦ ?_)
      have hrank := hn
      obtain ⟨y, hy⟩ : ∃ y : Lˣ, Algebra.norm K (y : L) = x := by
        refine ⟨Units.map (algebraMap K L : K →* L) x, ?_⟩
        simp [Algebra.norm_algebraMap, hrank]
      exact ⟨y, Units.ext hy⟩
    rw [h1]
    exact ⟨one_pos, le_rfl⟩
  · obtain ⟨g, hg⟩ := not_forall.1 hbot
    set H := Subgroup.zpowers g
    set E := IntermediateField.fixedField H
    have hHE : E.fixingSubgroup = H := IntermediateField.fixingSubgroup_fixedField H
    -- `L/E` is cyclic
    haveI : IsCyclic (L ≃ₐ[E] L) := by
      haveI : IsCyclic H := Subgroup.isCyclic_zpowers g
      rw [← hHE] at this
      exact isCyclic_of_surjective (IntermediateField.fixingSubgroupEquiv E).toMonoidHom
        (IntermediateField.fixingSubgroupEquiv E).surjective
    haveI : IsGalois E L := inferInstance
    have hEL : 1 < Module.finrank E L := by
      rw [← IsGalois.card_aut_eq_finrank]
      rw [← Nat.card_congr (IntermediateField.fixingSubgroupEquiv E).toEquiv, hHE]
      exact (Subgroup.one_lt_card_iff_ne_bot _).2 fun h' ↦ hg (by
        have : g ∈ H := Subgroup.mem_zpowers g
        rw [h'] at this; exact this)
    have hEK : Module.finrank K E < n := by
      rw [← h, ← Module.finrank_mul_finrank K E L]
      exact lt_mul_of_one_lt_right Module.finrank_pos hEL
    have ihE := ih _ hEK (L := E) inferInstance rfl
    have hcyc := index_normGroup_of_isCyclic (p := p) (K := E) (L := L)
    rw [normGroup_tower (E := E)]
    refine ⟨Nat.pos_of_ne_zero (index_map_ne_zero _ _ (by rw [hcyc]; exact Module.finrank_pos.ne')
      ihE.1.ne'), ?_⟩
    calc ((normGroup E L).map (Units.map (Algebra.norm K : E →* K))).index
        ≤ (Units.map (Algebra.norm K : E →* K)).range.index * (normGroup E L).index :=
          index_map_le_mul _ _ (by rw [hcyc]; exact Module.finrank_pos.ne')
      _ ≤ Module.finrank K E * Module.finrank E L := by
          rw [hcyc]
          exact Nat.mul_le_mul_right _ ihE.2
      _ = n := by rw [Module.finrank_mul_finrank K E L, h]

/-- **The second inequality**: for an abelian extension `L/K`, `[Kˣ : N Lˣ] ≤ [L : K]`. -/
theorem index_normGroup_le {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
    [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
    [FiniteDimensional ℚ_[p] L] [IsAbelianGalois K L] :
    (normGroup K L).index ≤ Module.finrank K L :=
  (index_normGroup_pos_le (p := p)).2

/-- Norm groups of abelian extensions have finite index. -/
theorem index_normGroup_ne_zero {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K]
    [Algebra ℚ_[p] L] [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
    [FiniteDimensional ℚ_[p] L] [IsAbelianGalois K L] : (normGroup K L).index ≠ 0 :=
  (index_normGroup_pos_le (p := p)).1.ne'

section Unramified

variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L]

variable (p K) in
/-- The subgroup `{x | n ∣ v x}` of `Kˣ`. -/
noncomputable def vDvd (n : ℕ) : Subgroup Kˣ where
  carrier := {x | (n : ℤ) ∣ v p (x : K)}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul] at *
    rw [v_mul a.ne_zero b.ne_zero]; exact dvd_add ha hb
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val] at *
    rw [v_inv a.ne_zero]; exact (dvd_neg).2 ha

theorem mem_vDvd {n : ℕ} {x : Kˣ} : x ∈ vDvd p K n ↔ (n : ℤ) ∣ v p (x : K) := Iff.rfl

theorem index_vDvd {n : ℕ} (hn : n ≠ 0) : (vDvd p K n).index = n := by
  haveI : NeZero n := ⟨hn⟩
  let φ : Kˣ →* Multiplicative (ZMod n) :=
    { toFun := fun x ↦ Multiplicative.ofAdd ((v p (x : K) : ℤ) : ZMod n)
      map_one' := by simp
      map_mul' := fun a b ↦ by
        simp only [Units.val_mul, v_mul a.ne_zero b.ne_zero, Int.cast_add, ofAdd_add] }
  have hker : φ.ker = vDvd p K n := by
    ext x
    rw [MonoidHom.mem_ker, mem_vDvd]
    change Multiplicative.ofAdd ((v p (x : K) : ℤ) : ZMod n) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hsurj : Function.Surjective φ := by
    intro z
    have hπ := uniformizer_spec (p := p) (K := K)
    refine ⟨Units.mk0 _ (zpow_ne_zero (Multiplicative.toAdd z).val hπ.ne_zero), ?_⟩
    change Multiplicative.ofAdd (((v p ((uniformizer p K) ^ ((Multiplicative.toAdd z).val : ℤ))
      : ℤ)) : ZMod n) = z
    rw [v_zpow hπ.ne_zero, hπ, mul_one]
    simp
  rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top,
    Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem normGroup_le_vDvd (h : IsUnramified p K L) :
    normGroup K L ≤ vDvd p K (Module.finrank K L) := by
  rintro _ ⟨y, rfl⟩
  rw [mem_vDvd]
  change (Module.finrank K L : ℤ) ∣ v p (Algebra.norm K (y : L))
  rw [v_norm y.ne_zero, h.f_eq]
  exact dvd_mul_right _ _

/-- The norm group of an unramified extension of degree `n` is `{x | n ∣ v x}`. -/
theorem normGroup_of_isUnramified (h : IsUnramified p K L) :
    normGroup K L = vDvd p K (Module.finrank K L) := by
  haveI := finiteDimensional_tower (p := p) K L
  haveI := isGalois_of_isUnramified h
  haveI := isCyclic_gal h
  have hn : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  have hle := normGroup_le_vDvd h
  have hidx := Subgroup.relIndex_mul_index hle
  rw [index_vDvd hn, index_normGroup_of_isCyclic (p := p)] at hidx
  have h1 : (normGroup K L).relIndex (vDvd p K (Module.finrank K L)) = 1 := by
    have := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn) (hidx.trans (one_mul _).symm)
    exact this
  exact le_antisymm hle (Subgroup.relIndex_eq_one.1 h1)

/-- In an unramified extension every unit is the norm of a unit. -/
theorem exists_norm_eq_of_isUnramified (h : IsUnramified p K L) (u : Kˣ)
    (hu : nrm p K (u : K) = 1) :
    ∃ y : Lˣ, nrm p L (y : L) = 1 ∧ Algebra.norm K (y : L) = u := by
  haveI := finiteDimensional_tower (p := p) K L
  haveI := isGalois_of_isUnramified h
  have hmem : u ∈ normGroup K L := by
    rw [normGroup_of_isUnramified h, mem_vDvd, (nrm_eq_one_iff_v_eq_zero u.ne_zero).1 hu]
    exact dvd_zero _
  obtain ⟨y, hy⟩ := mem_normGroup.1 hmem
  refine ⟨y, ?_, hy⟩
  rw [nrm_eq_one_iff_v_eq_zero y.ne_zero]
  have h1 := v_norm (K := K) (p := p) y.ne_zero
  rw [hy, (nrm_eq_one_iff_v_eq_zero u.ne_zero).1 hu, h.f_eq] at h1
  have hn : (Module.finrank K L : ℤ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  exact (mul_eq_zero.1 h1.symm).resolve_left hn

end Unramified

end PadicField
