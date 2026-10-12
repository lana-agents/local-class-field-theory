/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.ClassFieldAxiom.Vanishing
import LocalClassFieldTheory.Herbrand.Exact
import LocalClassFieldTheory.Herbrand.Examples

/-!
# The Herbrand quotient of the units of a cyclic extension

Let `L/K` be a cyclic extension of fields finite over `ℚ_[p]`, `σ` a generator of `Gal(L/K)` and
`n` its order. We view `Additive Lˣ` as a module over the cyclic group via `σ`.

* `PadicField.herbrand_unitGroup`: the Herbrand quotient of the units of absolute value one is
  `1` (they contain the finite-index subgroup `V 0` with trivial Tate groups).
-/

open Polynomial Herbrand

set_option linter.unusedSectionVars false

namespace Herbrand

variable {M : Type*} [AddCommGroup M] {σ : AddMonoid.End M} {n : ℕ}
variable (A : AddSubgroup M) (hA : ∀ x ∈ A, σ x ∈ A)

theorem coe_N_restrict (y : A) : ((N (restrict σ A hA) n y : A) : M) = N σ n y :=
  map_N_apply A.subtype (fun _ ↦ rfl) y

theorem subsingleton_H0_restrict_iff :
    Subsingleton (H0 (restrict σ A hA) n) ↔ ∀ x ∈ A, σ x = x → ∃ y ∈ A, N σ n y = x := by
  rw [subsingleton_H0_iff]
  constructor
  · intro h x hx hfix
    obtain ⟨y, hy⟩ := h ⟨x, hx⟩ (Subtype.ext hfix)
    exact ⟨y, y.2, by rw [← coe_N_restrict A hA, hy]⟩
  · intro h x hfix
    obtain ⟨y, hy, hyx⟩ := h x x.2 (congrArg Subtype.val hfix)
    exact ⟨⟨y, hy⟩, Subtype.ext (by rw [coe_N_restrict A hA, hyx])⟩

theorem subsingleton_Hm1_restrict_iff :
    Subsingleton (Hm1 (restrict σ A hA) n) ↔
      ∀ x ∈ A, N σ n x = 0 → ∃ y ∈ A, σ y - y = x := by
  rw [subsingleton_Hm1_iff]
  constructor
  · intro h x hx hN
    obtain ⟨y, hy⟩ := h ⟨x, hx⟩ (Subtype.ext (by rw [coe_N_restrict A hA]; exact hN))
    exact ⟨y, y.2, congrArg Subtype.val hy⟩
  · intro h x hN
    obtain ⟨y, hy, hyx⟩ := h x x.2 (by rw [← coe_N_restrict A hA, hN]; rfl)
    exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩

end Herbrand

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L] [FiniteDimensional K L] [IsGalois K L]

variable (p L) in
/-- The units of absolute value one. -/
noncomputable def unitGroup : Subgroup Lˣ where
  carrier := {u | nrm p L (u : L) = 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by simp_all
  inv_mem' {a} ha := by simp_all [Units.val_inv_eq_inv_val]

theorem mem_unitGroup {u : Lˣ} : u ∈ unitGroup p L ↔ nrm p L (u : L) = 1 := Iff.rfl

/-- `σ` acting on `Lˣ`, as a monoid endomorphism. -/
abbrev galEnd (σ : L ≃ₐ[K] L) : Monoid.End Lˣ := galUnits σ

theorem galEnd_pow_apply (σ : L ≃ₐ[K] L) (i : ℕ) (u : Lˣ) :
    (galEnd σ ^ i) u = galUnits (σ ^ i) u := by
  rw [Monoid.End.coe_pow]
  induction i generalizing u with
  | zero => ext; simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih]
    ext
    simp only [coe_galUnits, pow_succ, AlgEquiv.mul_apply]
    rfl

/-- `σ` acting on `Additive Lˣ`. -/
abbrev σL (σ : L ≃ₐ[K] L) : AddMonoid.End (Additive Lˣ) := ofMonoidEnd (galEnd σ)

theorem σL_pow (σ : L ≃ₐ[K] L) (i : ℕ) (x : Additive Lˣ) :
    (σL σ ^ i) x = Additive.ofMul (galUnits (σ ^ i) x.toMul) := by
  rw [σL, ofMonoidEnd_pow, ofMonoidEnd_apply, galEnd_pow_apply]

theorem σL_pow_orderOf (σ : L ≃ₐ[K] L) : σL σ ^ orderOf σ = 1 := by
  ext x
  rw [σL_pow, pow_orderOf_eq_one]
  rfl

theorem N_σL (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (x : Additive Lˣ) :
    N (σL σ) (orderOf σ) x = Additive.ofMul (normUnits (K := K) x.toMul) := by
  rw [N_apply]
  simp_rw [σL_pow]
  apply Additive.toMul.injective
  rw [toMul_sum]
  simp only [toMul_ofMul]
  rw [normUnits, MonoidHom.finsetProd_apply, prod_eq_prod_range σ hσ]

theorem galUnits_mem_unitGroup (σ : L ≃ₐ[K] L) {u : Lˣ} (hu : u ∈ unitGroup p L) :
    galUnits σ u ∈ unitGroup p L := by
  rw [mem_unitGroup, coe_galUnits, nrm_algEquiv_tower]; exact hu

end PadicField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L] [FiniteDimensional K L] [IsGalois K L]

theorem finite_quotient_of_ker_le {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Finite H]
    (f : G →+ H) (A : AddSubgroup G) (h : f.ker ≤ A) : Finite (G ⧸ A) := by
  haveI : Finite (G ⧸ f.ker) := Finite.of_injective _ (QuotientAddGroup.kerLift_injective f)
  exact Finite.of_surjective (QuotientAddGroup.map f.ker A (AddMonoidHom.id G) h)
    (fun q ↦ QuotientAddGroup.induction_on q fun g ↦ ⟨g, rfl⟩)

/-- `‖π_K‖ = ‖π_L‖ ^ e`. -/
theorem ρ_eq_pow_e : ρ p K = nrm p L (uniformizer p L) ^ e p K L := by
  have hπK := uniformizer_spec (p := p) (K := K)
  rw [ρ, ← nrm_algebraMap_tower (L := L), nrm_eq_nrm_uniformizer_zpow uniformizer_spec
    ((map_ne_zero_iff _ (algebraMap K L).injective).2 hπK.ne_zero), v_algebraMap_uniformizer,
    zpow_natCast]

/-- Units of absolute value one, as units of `𝒪 p L`. -/
noncomputable def toIntegersUnits : unitGroup p L →* (𝒪 p L)ˣ where
  toFun u :=
    { val := Integers.mk (u : Lˣ) (le_of_eq u.2)
      inv := Integers.mk ((u : Lˣ)⁻¹ : Lˣ) (le_of_eq (inv_mem u.2))
      val_inv := Integers.ext (by simp)
      inv_val := Integers.ext (by simp) }
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

theorem finite_quotient_unitGroup (M : ℕ) (A : AddSubgroup (unitGroup p L).toAddSubgroup)
    (hA : ∀ u : (unitGroup p L).toAddSubgroup,
      nrm p L ((Additive.toMul (u : Additive Lˣ) : Lˣ) - 1 : L) ≤
        nrm p L (uniformizer p L) ^ M → u ∈ A) :
    Finite ((unitGroup p L).toAddSubgroup ⧸ A) := by
  set I := IsLocalRing.maximalIdeal (𝒪 p L) ^ M
  haveI : Finite (𝒪 p L ⧸ IsLocalRing.maximalIdeal (𝒪 p L)) :=
    inferInstanceAs (Finite (𝓴 p L))
  haveI : Finite (𝒪 p L ⧸ I) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) M
  let φ : (unitGroup p L).toAddSubgroup →+ Additive (𝒪 p L ⧸ I)ˣ :=
    { toFun := fun u ↦ Additive.ofMul (Units.map (Ideal.Quotient.mk I).toMonoidHom
        (toIntegersUnits ⟨Additive.toMul (u : Additive Lˣ), u.2⟩))
      map_zero' := by simp; rfl
      map_add' := fun u v ↦ by
        rw [← ofMul_mul, ← map_mul, ← map_mul]; rfl }
  refine finite_quotient_of_ker_le φ A fun u hu ↦ hA u ?_
  have h1 := congrArg (fun z : Additive (𝒪 p L ⧸ I)ˣ ↦ ((Additive.toMul z : (𝒪 p L ⧸ I)ˣ) :
    𝒪 p L ⧸ I)) (AddMonoidHom.mem_ker.1 hu)
  simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul, Units.coe_map,
    MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, toMul_zero, Units.val_one] at h1
  rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at h1
  have := (Integers.mem_maximalIdeal_pow_iff_nrm _ M).1 h1
  simpa [toIntegersUnits] using this


section Cyclic

variable (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)

theorem σL_mem_AU : ∀ x ∈ (unitGroup p L).toAddSubgroup, σL σ x ∈ (unitGroup p L).toAddSubgroup :=
  fun _ hx ↦ galUnits_mem_unitGroup σ hx

/-- `σ` acting on the additive group of units of absolute value one. -/
noncomputable abbrev σU : AddMonoid.End (unitGroup p L).toAddSubgroup :=
  restrict (σL σ) (unitGroup p L).toAddSubgroup (σL_mem_AU σ)

include hσ

/-- The units of absolute value one have trivial Herbrand quotient, with finite Tate groups. -/
theorem herbrand_σU :
    Finite (H0 (σU (p := p) σ) (orderOf σ)) ∧ Finite (Hm1 (σU (p := p) σ) (orderOf σ)) ∧
      herbrand (σU (p := p) σ) (orderOf σ) = 1 := by
  obtain ⟨b, hb, hb1⟩ := exists_integral_normalBasis (p := p) (K := K) (L := L)
  obtain ⟨N, hN⟩ := exists_lat_ball (p := p) b
  set V := filt b hb hb1 N hN 0
  have hVU : ∀ u ∈ V, u ∈ unitGroup p L := fun u hu ↦ nrm_eq_one_of_mem_filt b hb hb1 N hN hu
  set AU := (unitGroup p L).toAddSubgroup
  let A : AddSubgroup AU := V.toAddSubgroup.addSubgroupOf AU
  have hmemA : ∀ x : AU, x ∈ A ↔ Additive.toMul (x : Additive Lˣ) ∈ V := fun x ↦ Iff.rfl
  have hA : ∀ x ∈ A, σU σ x ∈ A := fun x hx ↦ by
    rw [hmemA] at hx ⊢
    exact galUnits_mem_filt b hb hb1 N hN hx σ
  have hσn : σU (p := p) σ ^ orderOf σ = 1 := restrict_pow_eq_one _ (σL_pow_orderOf σ)
  -- finite index
  haveI hfin : Finite (AU ⧸ A) := by
    refine finite_quotient_unitGroup (e p K L * (2 * N + 1 + N)) A fun u hu ↦ ?_
    rw [hmemA]
    refine mem_filt_of_nrm_le b hb hb1 N hN 0 _ (hu.trans (le_of_eq ?_))
    rw [ρ_eq_pow_e (L := L), ← pow_mul, zero_add]
  -- trivial Tate groups of `V 0`
  have hH0 : Subsingleton (H0 (restrict (σU (p := p) σ) A hA) (orderOf σ)) := by
    rw [subsingleton_H0_restrict_iff]
    intro x hx hfix
    have hfix' : galUnits σ (Additive.toMul (x : Additive Lˣ)) =
        Additive.toMul (x : Additive Lˣ) := by
      exact congrArg (fun z : AU ↦ Additive.toMul (z : Additive Lˣ)) hfix
    obtain ⟨y, hyV, hyx⟩ := exists_normUnits_eq b hb hb1 N hN σ hσ _ hx hfix'
    refine ⟨⟨Additive.ofMul y, hVU y hyV⟩, hyV, Subtype.ext ?_⟩
    rw [coe_N_restrict, N_σL σ hσ]
    simp [hyx]
  have hHm1 : Subsingleton (Hm1 (restrict (σU (p := p) σ) A hA) (orderOf σ)) := by
    rw [subsingleton_Hm1_restrict_iff]
    intro x hx hNx
    have hN1 : normUnits (K := K) (Additive.toMul (x : Additive Lˣ)) = 1 := by
      have := congrArg (fun z : AU ↦ Additive.toMul (z : Additive Lˣ)) hNx
      simp only [coe_N_restrict, N_σL σ hσ, toMul_ofMul] at this
      simpa using this
    obtain ⟨y, hyV, hyx⟩ := exists_galUnits_div_eq b hb hb1 N hN σ hσ _ hx hN1
    refine ⟨⟨Additive.ofMul y, hVU y hyV⟩, hyV, Subtype.ext ?_⟩
    apply Additive.toMul.injective
    change galUnits σ y / y = _
    rw [hyx]
    rfl
  haveI := hH0
  haveI := hHm1
  have hfH0 := finite_H0_of_finite_quotient hσn A hA
  have hfHm1 := finite_Hm1_of_finite_quotient hσn A hA
  refine ⟨hfH0, hfHm1, ?_⟩
  rw [herbrand_eq_of_finite_quotient hσn A hA, herbrand,
    Nat.card_of_subsingleton (0 : H0 (restrict (σU (p := p) σ) A hA) (orderOf σ)),
    Nat.card_of_subsingleton (0 : Hm1 (restrict (σU (p := p) σ) A hA) (orderOf σ))]
  norm_num

end Cyclic

end PadicField
