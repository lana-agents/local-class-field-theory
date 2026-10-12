/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.ClassFieldAxiom.HerbrandUnits
import LocalClassFieldTheory.ClassFieldAxiom.Hilbert90

/-!
# The class field axiom for cyclic extensions

Let `L/K` be a cyclic extension of fields finite over `ℚ_[p]`. Then
`[Kˣ : N_{L/K} Lˣ] = [L : K]` (`PadicField.index_normGroup_of_isCyclic`).

Proof: the Herbrand quotient of `Lˣ` is `h(𝒪ˣ_L) · h(ℤ) = 1 · n` (valuation sequence
`1 → 𝒪ˣ_L → Lˣ → ℤ → 0`), `Ĥ⁻¹(Lˣ) = 1` by Hilbert 90, and `Ĥ⁰(Lˣ) = Kˣ / N Lˣ`.
(Serre, *Local Fields*, XIII §2 and V §2; Neukirch, ANT V.1.)
-/

open Herbrand

set_option linter.unusedSectionVars false

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L] [FiniteDimensional K L] [IsGalois K L]

variable (K L) in
/-- The norm group `N_{L/K} Lˣ ≤ Kˣ`. -/
noncomputable def normGroup : Subgroup Kˣ := (Units.map (Algebra.norm K : L →* K)).range

theorem mem_normGroup {a : Kˣ} : a ∈ normGroup K L ↔ ∃ y : Lˣ, Algebra.norm K (y : L) = a := by
  simp only [normGroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩; exact ⟨y, Units.ext hy⟩

omit [IsGalois K L] in
/-- An element fixed by a generator is fixed by the whole Galois group. -/
theorem apply_eq_of_generator (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {y : L}
    (h : σ y = y) (g : L ≃ₐ[K] L) : g y = y := by
  let S : Subgroup (L ≃ₐ[K] L) :=
    { carrier := {a | a y = y}
      one_mem' := rfl
      mul_mem' := fun {a c} ha hc ↦ by
        simp only [Set.mem_setOf_eq, AlgEquiv.mul_apply] at *; rw [hc, ha]
      inv_mem' := fun {a} ha ↦ by
        simp only [Set.mem_setOf_eq] at *
        rw [AlgEquiv.aut_inv]; exact (a.symm_apply_eq).2 ha.symm }
  exact (Subgroup.zpowers_le.2 (show σ ∈ S from h)) (hσ g)

section Cyclic

variable (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
include hp

variable (p L) in
/-- The valuation `Additive Lˣ →+ ℤ`. -/
noncomputable def valHom : Additive Lˣ →+ ℤ where
  toFun x := v p ((Additive.toMul x : Lˣ) : L)
  map_zero' := by simp
  map_add' x y := by
    simp only [toMul_add, Units.val_mul]
    exact v_mul (Additive.toMul x).ne_zero (Additive.toMul y).ne_zero

theorem valHom_σL (x : Additive Lˣ) : valHom p L (σL σ x) = valHom p L x := by
  simp only [valHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, σL, ofMonoidEnd_apply, toMul_ofMul]
  rw [← nrm_eq_iff_v_eq (Units.ne_zero _) (Units.ne_zero _)]
  exact nrm_algEquiv_tower (p := p) _ _ σ _

theorem valHom_surjective : Function.Surjective (valHom p L) := by
  intro m
  have hπ := uniformizer_spec (p := p) (K := L)
  refine ⟨Additive.ofMul (Units.mk0 _ (zpow_ne_zero m hπ.ne_zero)), ?_⟩
  simp only [valHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul, Units.val_mk0]
  rw [v_zpow hπ.ne_zero, hπ, mul_one]

theorem range_subtype_eq_ker_valHom :
    (unitGroup p L).toAddSubgroup.subtype.range = (valHom p L).ker := by
  ext x
  rw [AddSubgroup.range_subtype, AddMonoidHom.mem_ker]
  change nrm p L ((Additive.toMul x : Lˣ) : L) = 1 ↔ _
  exact nrm_eq_one_iff_v_eq_zero (Additive.toMul x).ne_zero

include hσ

/-- The Herbrand quotient of `Lˣ` is `[L : K]` (more precisely, the order of the generator). -/
theorem herbrand_σL :
    Finite (H0 (σL σ) (orderOf σ)) ∧ Finite (Hm1 (σL σ) (orderOf σ)) ∧
      herbrand (σL σ) (orderOf σ) = orderOf σ := by
  obtain ⟨h0, h1, hU⟩ := herbrand_σU (p := p) σ hσ
  have hn : 0 < orderOf σ := orderOf_pos σ
  haveI : Finite (H0 (1 : AddMonoid.End ℤ) (orderOf σ)) :=
    Nat.finite_of_card_ne_zero (by rw [card_H0_int]; exact hn.ne')
  haveI : Subsingleton (Hm1 (1 : AddMonoid.End ℤ) (orderOf σ)) := subsingleton_Hm1_int hn
  have hσn := σL_pow_orderOf (K := K) σ
  set AU := (unitGroup p L).toAddSubgroup
  refine ⟨finite_H0_of_ses hσn AU.subtype (valHom p L) Subtype.val_injective valHom_surjective
      range_subtype_eq_ker_valHom (σA := σU (p := p) σ) (σC := 1) (fun _ ↦ rfl)
      (fun x ↦ valHom_σL σ x),
    finite_Hm1_of_ses hσn AU.subtype (valHom p L) Subtype.val_injective valHom_surjective
      range_subtype_eq_ker_valHom (σA := σU (p := p) σ) (σC := 1) (fun _ ↦ rfl)
      (fun x ↦ valHom_σL σ x), ?_⟩
  rw [herbrand_eq_mul_of_ses hσn AU.subtype (valHom p L) Subtype.val_injective valHom_surjective
      range_subtype_eq_ker_valHom (σA := σU (p := p) σ) (σC := 1) (fun _ ↦ rfl)
      (fun x ↦ valHom_σL σ x), hU, herbrand_int hn, one_mul]

theorem normUnits_eq_partialNorm (u : Lˣ) :
    normUnits (K := K) u = partialNorm σ u (orderOf σ) := by
  rw [normUnits, MonoidHom.finsetProd_apply, prod_eq_prod_range σ hσ]
  rfl

/-- Hilbert 90: `Ĥ⁻¹(Lˣ)` is trivial. -/
theorem subsingleton_Hm1_σL : Subsingleton (Hm1 (σL σ) (orderOf σ)) := by
  rw [subsingleton_Hm1_iff]
  intro x hx
  rw [N_σL σ hσ] at hx
  have h1 : partialNorm σ (Additive.toMul x) (orderOf σ) = 1 := by
    rw [← normUnits_eq_partialNorm (p := p) σ hσ]
    exact Additive.ofMul.injective hx
  obtain ⟨y, hy⟩ := exists_div_of_prod_eq_one σ hσ _ h1
  refine ⟨Additive.ofMul y, ?_⟩
  apply Additive.toMul.injective
  simp only [σL, ofMonoidEnd_apply, toMul_sub, toMul_ofMul]
  exact hy

theorem card_H0_σL : Nat.card (H0 (σL σ) (orderOf σ)) = orderOf σ := by
  obtain ⟨-, -, h⟩ := herbrand_σL (p := p) σ hσ
  haveI := subsingleton_Hm1_σL (p := p) σ hσ
  rw [herbrand, Nat.card_of_subsingleton (0 : Hm1 (σL σ) (orderOf σ)), Nat.cast_one,
    div_one] at h
  exact_mod_cast h

/-- `Ĥ⁰(Lˣ) = Kˣ / N Lˣ`. -/
theorem card_H0_σL_eq_index : Nat.card (H0 (σL σ) (orderOf σ)) = (normGroup K L).index := by
  let φ : Additive Kˣ →+ Additive Lˣ := (Units.map (algebraMap K L : K →* L)).toAdditive
  have hker : (D (σL σ)).ker = φ.range := by
    ext x
    rw [mem_ker_D_iff, AddMonoidHom.mem_range]
    constructor
    · intro hx
      have hfix : σ ((Additive.toMul x : Lˣ) : L) = ((Additive.toMul x : Lˣ) : L) :=
        congrArg (fun z : Additive Lˣ ↦ ((Additive.toMul z : Lˣ) : L)) hx
      have hbot : ((Additive.toMul x : Lˣ) : L) ∈ (⊥ : IntermediateField K L) :=
        (IsGalois.mem_bot_iff_fixed _).2 (apply_eq_of_generator σ hσ hfix)
      obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 hbot
      have ha0 : a ≠ 0 := by
        rintro rfl; simp at ha; exact (Additive.toMul x).ne_zero ha.symm
      refine ⟨Additive.ofMul (Units.mk0 a ha0), ?_⟩
      apply Additive.toMul.injective
      ext
      simp [φ, ha]
    · rintro ⟨a, rfl⟩
      apply Additive.toMul.injective
      ext
      exact σ.commutes _
  have hcomap : (N (σL σ) (orderOf σ)).range.comap φ = (normGroup K L).toAddSubgroup := by
    ext a
    rw [AddSubgroup.mem_comap, AddMonoidHom.mem_range, Additive.mem_toAddSubgroup,
      mem_normGroup]
    constructor
    · rintro ⟨z, hz⟩
      rw [N_σL σ hσ] at hz
      refine ⟨Additive.toMul z, ?_⟩
      have := congrArg (fun w : Additive Lˣ ↦ ((Additive.toMul w : Lˣ) : L)) hz
      simp only [toMul_ofMul, coe_normUnits_eq_norm, φ] at this
      exact (algebraMap K L).injective (by simpa using this)
    · rintro ⟨y, hy⟩
      refine ⟨Additive.ofMul y, ?_⟩
      rw [N_σL σ hσ]
      apply Additive.toMul.injective
      ext
      simp [φ, coe_normUnits_eq_norm, hy]
  rw [TateQuot.card_eq_relIndex, hker, AddMonoidHom.range_eq_map φ,
    ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, hcomap,
    Subgroup.index_toAddSubgroup]

/-- **The class field axiom**: for a cyclic extension `L/K`, `[Kˣ : N_{L/K} Lˣ] = [L : K]`. -/
theorem index_normGroup_of_generator : (normGroup K L).index = Module.finrank K L := by
  rw [← card_H0_σL_eq_index (p := p) σ hσ, card_H0_σL (p := p) σ hσ,
    orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank]

end Cyclic

include hp in
/-- **The class field axiom**: for a cyclic extension `L/K` of fields finite over `ℚ_[p]`,
`[Kˣ : N_{L/K} Lˣ] = [L : K]`. -/
theorem index_normGroup_of_isCyclic [IsCyclic (L ≃ₐ[K] L)] :
    (normGroup K L).index = Module.finrank K L := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  exact index_normGroup_of_generator (p := p) σ hσ

end PadicField
