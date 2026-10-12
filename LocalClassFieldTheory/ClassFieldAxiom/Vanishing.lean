/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.ClassFieldAxiom.Units

/-!
# Vanishing of `Ĥ⁰` and `Ĥ⁻¹` on the unit filtration

For a cyclic extension `L/K` with generator `σ` of `Gal(L/K)` and the filtration
`filt b hb hb1 N hN` of `Lˣ` (see `ClassFieldAxiom/Units.lean`):

* `PadicField.exists_normUnits_eq`: every `σ`-invariant element of `V 0` is the norm of an
  element of `V 0`;
* `PadicField.exists_galUnits_div_eq`: every element of `V 0` of norm one is `σ y / y` for some
  `y ∈ V 0`.
-/

open Polynomial

set_option linter.unusedSectionVars false

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L] [FiniteDimensional K L] [IsGalois K L]

section Enumeration

variable {G : Type*} [Group G] (σ : G) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
include hσ

theorem bijective_pow_fin [Finite G] :
    Function.Bijective fun i : Fin (orderOf σ) ↦ σ ^ (i : ℕ) := by
  classical
  haveI := Fintype.ofFinite G
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun i j hij ↦ ?_, ?_⟩
  · exact Fin.ext (pow_injOn_Iio_orderOf (Set.mem_Iio.2 i.2) (Set.mem_Iio.2 j.2) hij)
  · rw [Fintype.card_fin, orderOf_eq_card_of_forall_mem_zpowers hσ, Nat.card_eq_fintype_card]

theorem sum_eq_sum_range [Fintype G] {M : Type*} [AddCommMonoid M] (F : G → M) :
    ∑ g, F g = ∑ i ∈ Finset.range (orderOf σ), F (σ ^ i) := by
  rw [← Fintype.sum_bijective _ (bijective_pow_fin σ hσ) (fun i ↦ F (σ ^ (i : ℕ))) F
    (fun _ ↦ rfl), Fin.sum_univ_eq_sum_range (fun i ↦ F (σ ^ i))]

theorem prod_eq_prod_range [Fintype G] {M : Type*} [CommMonoid M] (F : G → M) :
    ∏ g, F g = ∏ i ∈ Finset.range (orderOf σ), F (σ ^ i) := by
  rw [← Fintype.prod_bijective _ (bijective_pow_fin σ hσ) (fun i ↦ F (σ ^ (i : ℕ))) F
    (fun _ ↦ rfl), Fin.prod_univ_eq_prod_range (fun i ↦ F (σ ^ i))]

end Enumeration

theorem normUnits_galUnits (g : L ≃ₐ[K] L) (x : Lˣ) :
    normUnits (K := K) (galUnits g x) = normUnits (K := K) x := by
  ext
  rw [coe_normUnits (K := K), coe_normUnits (K := K)]
  exact Fintype.prod_equiv (Equiv.mulRight g) _ _ fun h ↦ by simp [AlgEquiv.mul_apply]

theorem galUnits_normUnits (g : L ≃ₐ[K] L) (x : Lˣ) :
    galUnits g (normUnits (K := K) x) = normUnits (K := K) x := by
  ext
  rw [coe_galUnits, coe_normUnits (K := K), map_prod]
  exact Fintype.prod_equiv (Equiv.mulLeft g) _ _ fun h ↦ by simp [AlgEquiv.mul_apply]

section Steps

variable (b : Module.Basis (L ≃ₐ[K] L) K L) (hb : ∀ g, b g = g (b 1))
  (hb1 : nrm p L (b 1) ≤ 1) (N : ℕ)
  (hN : ∀ k : ℕ, ∀ x : L, nrm p L x ≤ ρ p K ^ (k + N) → x ∈ lat p b k)

include hb hb1 hN

theorem galois_smul_basis (g : L ≃ₐ[K] L) (a : K) (h : L ≃ₐ[K] L) :
    g (a • b h) = a • b (g * h) := by
  rw [map_smul, hb h, hb (g * h), AlgEquiv.mul_apply]

theorem nrm_normUnits_eq_one {k : ℕ} {y : Lˣ} (hy : y ∈ filt b hb hb1 N hN k) :
    nrm p L (normUnits (K := K) y : L) = 1 :=
  nrm_eq_one_of_mem_filt b hb hb1 N hN (normUnits_mem_filt b hb hb1 N hN hy)

/-- The approximation step for `Ĥ⁰`. -/
theorem step_H0 (k : ℕ) (x : Lˣ) (hx : x ∈ filt b hb hb1 N hN k)
    (hfix : ∀ g : L ≃ₐ[K] L, galUnits g x = x) :
    ∃ y ∈ filt b hb hb1 N hN k, x / normUnits (K := K) y ∈ filt b hb hb1 N hN (k + 1) := by
  set j := k + (2 * N + 1)
  set t : L := (x : L) - 1
  have ht : t ∈ lat p b j := hx
  have htfix : ∀ g : L ≃ₐ[K] L, g t = t := fun g ↦ by
    have := congrArg Units.val (hfix g)
    simp only [coe_galUnits] at this
    simp [t, this]
  set a : K := b.repr t 1
  have hconst : ∀ g, b.repr t g = a := fun g ↦ by
    have := repr_apply_galois b hb g g t
    rw [htfix g, inv_mul_cancel] at this
    exact this
  set z : L := a • b 1
  have hz : z ∈ lat p b j := smul_basis_mem_lat b (ht 1) 1
  have hzn : nrm p L z ≤ ρ p K ^ j := nrm_le_ρ_pow_of_mem b hb hb1 N hN hz
  have hz1 : nrm p L z < 1 := hzn.trans_lt (pow_lt_one₀ ρ_nonneg ρ_lt_one (by omega))
  have hy0 : (1 + z) ≠ 0 := by
    intro h
    have : z = -1 := by linear_combination h
    rw [this, nrm_neg, nrm_one] at hz1
    exact lt_irrefl _ hz1
  set y : Lˣ := Units.mk0 (1 + z) hy0
  have hyV : y ∈ filt b hb hb1 N hN k := by
    rw [mem_filt]; simpa [y] using hz
  refine ⟨y, hyV, ?_⟩
  -- the norm of `y`
  have hgz : ∀ g : L ≃ₐ[K] L, g z = a • b g := fun g ↦ by
    rw [galois_smul_basis b hb hb1 N hN g a 1, mul_one]
  have hsum : ∑ g : L ≃ₐ[K] L, g z = t := by
    simp_rw [hgz]
    conv_rhs => rw [← b.sum_repr t]
    simp [hconst]
  have hNy : (normUnits (K := K) y : L) = ∏ g : L ≃ₐ[K] L, (1 + g z) := by
    rw [coe_normUnits (K := K)]; simp [y]
  have hE := nrm_prod_one_add_sub_le (p := p) Finset.univ (fun g : L ≃ₐ[K] L ↦ g z)
    (pow_nonneg ρ_nonneg j) (pow_le_one₀ ρ_nonneg ρ_lt_one.le)
    (fun g _ ↦ by rw [nrm_algEquiv_tower]; exact hzn)
  rw [hsum, ← hNy] at hE
  refine mem_filt_of_nrm_le b hb hb1 N hN _ _ ?_
  have hNy1 := nrm_normUnits_eq_one b hb hb1 N hN hyV
  have hcalc : ((x / normUnits (K := K) y : Lˣ) : L) - 1 =
      -(((normUnits (K := K) y : L)) - 1 - t) / (normUnits (K := K) y : L) := by
    have h0 : (normUnits (K := K) y : L) ≠ 0 := (normUnits (K := K) y).ne_zero
    simp only [Units.val_div_eq_div_val, t]
    field_simp
    ring
  rw [hcalc, nrm_div, nrm_neg, hNy1, div_one]
  refine hE.trans ?_
  rw [← pow_mul]
  exact ρ_pow_le (by omega)

/-- The approximation step for `Ĥ⁻¹`. -/
theorem step_Hm1 (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (k : ℕ) (x : Lˣ)
    (hx : x ∈ filt b hb hb1 N hN k) (hnorm : normUnits (K := K) x = 1) :
    ∃ y ∈ filt b hb hb1 N hN k,
      x / (galUnits σ y / y) ∈ filt b hb hb1 N hN (k + 1) := by
  set j := k + (2 * N + 1)
  set t : L := (x : L) - 1
  have ht : t ∈ lat p b j := hx
  have htn : nrm p L t ≤ ρ p K ^ j := nrm_le_ρ_pow_of_mem b hb hb1 N hN ht
  obtain ⟨m, hm⟩ : ∃ m, orderOf σ = m + 1 :=
    Nat.exists_eq_add_one_of_ne_zero (orderOf_pos σ).ne'
  set c : ℕ → K := fun i ↦ b.repr t (σ ^ i)
  set s : K := ∑ i ∈ Finset.range (m + 1), c i
  set d : ℕ → K := fun i ↦ -∑ l ∈ Finset.range i, c (l + 1)
  set w : L := ∑ i ∈ Finset.range (m + 1), d i • b (σ ^ i)
  have hc : ∀ i, nrm p K (c i) ≤ ρ p K ^ j := fun i ↦ ht _
  have hd : ∀ i, nrm p K (d i) ≤ ρ p K ^ j := fun i ↦ by
    simp only [d, nrm_neg]
    exact nrm_sum_le _ _ (pow_nonneg ρ_nonneg _) fun l _ ↦ hc _
  have hw : w ∈ lat p b j :=
    AddSubgroup.sum_mem _ fun i _ ↦ smul_basis_mem_lat b (hd i) _
  have hwn : nrm p L w ≤ ρ p K ^ j := nrm_le_ρ_pow_of_mem b hb hb1 N hN hw
  -- expansion of `t` in the basis `σ ^ i (b 1)`
  have ht_exp : t = ∑ i ∈ Finset.range (m + 1), c i • b (σ ^ i) := by
    conv_lhs => rw [← b.sum_repr t]
    rw [sum_eq_sum_range σ hσ, hm]
  have hσpow : σ ^ (m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one σ
  -- `σ w - w = t - s • b 1`
  have key : σ w - w = t - s • b 1 := by
    have e1 : σ w = ∑ i ∈ Finset.range m, d i • b (σ ^ (i + 1)) + d m • b 1 := by
      simp only [w, map_sum, galois_smul_basis b hb hb1 N hN, ← pow_succ']
      rw [Finset.sum_range_succ, hσpow]
    have e2 : w = ∑ i ∈ Finset.range m, d (i + 1) • b (σ ^ (i + 1)) := by
      simp only [w]
      rw [Finset.sum_range_succ']
      simp [d]
    have e3 : t = c 0 • b 1 + ∑ i ∈ Finset.range m, c (i + 1) • b (σ ^ (i + 1)) := by
      rw [ht_exp, Finset.sum_range_succ', add_comm, pow_zero]
    have e4 : ∀ i, d (i + 1) = d i - c (i + 1) := fun i ↦ by
      simp only [d, Finset.sum_range_succ]; ring
    have e5 : d m = c 0 - s := by
      simp only [d, s, Finset.sum_range_succ']; ring
    rw [e1, e2, e3, e5]
    simp_rw [e4, sub_smul, Finset.sum_sub_distrib]
    abel
  -- the sum of the conjugates of `t` is very small
  have hprod : ∏ g : L ≃ₐ[K] L, (1 + g t) = 1 := by
    have := congrArg Units.val hnorm
    rw [coe_normUnits (K := K), Units.val_one] at this
    refine Eq.trans (Finset.prod_congr rfl fun g _ ↦ ?_) this
    simp [t]
  have hE := nrm_prod_one_add_sub_le (p := p) Finset.univ (fun g : L ≃ₐ[K] L ↦ g t)
    (pow_nonneg ρ_nonneg j) (pow_le_one₀ ρ_nonneg ρ_lt_one.le)
    (fun g _ ↦ by rw [nrm_algEquiv_tower]; exact htn)
  rw [hprod, sub_self, zero_sub, nrm_neg, ← pow_mul] at hE
  have hlat : ∑ g : L ≃ₐ[K] L, g t ∈ lat p b (j * 2 - N) :=
    hN _ _ (hE.trans (le_of_eq (by congr 1; omega)))
  have hs_eq : b.repr (∑ g : L ≃ₐ[K] L, g t) 1 = s := by
    rw [map_sum, Finsupp.finsetSum_apply]
    simp_rw [repr_apply_galois b hb, mul_one]
    rw [Fintype.sum_equiv (Equiv.inv _) _ (fun g ↦ b.repr t g) (fun g ↦ by simp),
      sum_eq_sum_range σ hσ, hm]
  have hs : nrm p K s ≤ ρ p K ^ (j * 2 - N) := hs_eq ▸ hlat 1
  -- the correction `y = 1 + w`
  have hw1 : nrm p L w < 1 := hwn.trans_lt (pow_lt_one₀ ρ_nonneg ρ_lt_one (by omega))
  have hy0 : (1 + w) ≠ 0 := by
    intro h
    have : w = -1 := by linear_combination h
    rw [this, nrm_neg, nrm_one] at hw1
    exact lt_irrefl _ hw1
  set y : Lˣ := Units.mk0 (1 + w) hy0
  have hyV : y ∈ filt b hb hb1 N hN k := by rw [mem_filt]; simpa [y] using hw
  refine ⟨y, hyV, mem_filt_of_nrm_le b hb hb1 N hN _ _ ?_⟩
  have hσyV := galUnits_mem_filt b hb hb1 N hN hyV σ
  have hσy1 := nrm_eq_one_of_mem_filt b hb hb1 N hN hσyV
  have hσy : (galUnits σ y : L) = 1 + σ w := by simp [y]
  have hnum : (1 + t) * (1 + w) - (1 + σ w) = s • b 1 + t * w := by
    linear_combination (-1 : L) * key
  have hcalc : ((x / (galUnits σ y / y) : Lˣ) : L) - 1 =
      (s • b 1 + t * w) / (galUnits σ y : L) := by
    have h0 : (galUnits σ y : L) ≠ 0 := (galUnits σ y).ne_zero
    have hy0' : (y : L) ≠ 0 := y.ne_zero
    have hval : ((x / (galUnits σ y / y) : Lˣ) : L) = (x : L) * (y : L) / (galUnits σ y : L) := by
      simp only [Units.val_div_eq_div_val]
      field_simp
    have hxL : (x : L) = 1 + t := by simp [t]
    have hy' : (y : L) = 1 + w := rfl
    rw [hval, div_sub_one h0, hxL, hy', hσy, hnum]
  rw [hcalc, nrm_div, hσy1, div_one]
  refine (nrm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [Algebra.smul_def, nrm_mul, nrm_algebraMap_tower]
    calc nrm p K s * nrm p L (b 1) ≤ ρ p K ^ (j * 2 - N) * 1 :=
          mul_le_mul hs hb1 (nrm_nonneg _) (pow_nonneg ρ_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact ρ_pow_le (by omega)
  · rw [nrm_mul]
    calc nrm p L t * nrm p L w ≤ ρ p K ^ j * ρ p K ^ j :=
          mul_le_mul htn hwn (nrm_nonneg _) (pow_nonneg ρ_nonneg _)
      _ = ρ p K ^ (j + j) := (pow_add _ _ _).symm
      _ ≤ _ := ρ_pow_le (by omega)

/-- `Ĥ⁰` vanishes on `V 0`: invariant elements are norms. -/
theorem exists_normUnits_eq (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (x : Lˣ)
    (hx : x ∈ filt b hb hb1 N hN 0) (hfix : galUnits σ x = x) :
    ∃ y ∈ filt b hb hb1 N hN 0, normUnits (K := K) y = x := by
  let W : Subgroup Lˣ :=
    { carrier := {z | ∀ g : L ≃ₐ[K] L, galUnits g z = z}
      one_mem' := fun g ↦ map_one _
      mul_mem' := fun ha hb' g ↦ by rw [map_mul, ha g, hb' g]
      inv_mem' := fun ha g ↦ by rw [map_inv, ha g] }
  have hxW : x ∈ W := by
    intro g
    let S : Subgroup (L ≃ₐ[K] L) :=
      { carrier := {a | a (x : L) = x}
        one_mem' := rfl
        mul_mem' := fun {a c} ha hc ↦ by
          simp only [Set.mem_setOf_eq, AlgEquiv.mul_apply] at *; rw [hc, ha]
        inv_mem' := fun {a} ha ↦ by
          simp only [Set.mem_setOf_eq] at *
          rw [AlgEquiv.aut_inv]; exact (a.symm_apply_eq).2 ha.symm }
    have hσS : σ ∈ S := congrArg Units.val hfix
    have hgS : g ∈ S := (Subgroup.zpowers_le.2 hσS) (hσ g)
    exact Units.ext hgS
  exact exists_eq_of_approx (V := filt b hb hb1 N hN) (W := W) (Φ := normUnits (K := K))
    ρ_nonneg ρ_lt_one (filt_succ_le b hb hb1 N hN)
    (fun k u hu ↦ nrm_sub_one_le_of_mem_filt b hb hb1 N hN hu)
    (fun k ↦ ⟨k + (2 * N + 1) + N, fun u hu ↦ mem_filt_of_nrm_le b hb hb1 N hN k u hu⟩)
    (fun k u hu ↦ normUnits_mem_filt b hb hb1 N hN hu)
    (fun u g ↦ galUnits_normUnits g u)
    (fun k u hu huW ↦ step_H0 b hb hb1 N hN k u hu huW) x hx hxW

/-- `Ĥ⁻¹` vanishes on `V 0`: elements of norm one are of the form `σ y / y`. -/
theorem exists_galUnits_div_eq (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (x : Lˣ)
    (hx : x ∈ filt b hb hb1 N hN 0) (hnorm : normUnits (K := K) x = 1) :
    ∃ y ∈ filt b hb hb1 N hN 0, galUnits σ y / y = x := by
  let Φ : Lˣ →* Lˣ := galUnits σ / MonoidHom.id Lˣ
  have hΦ : ∀ y, Φ y = galUnits σ y / y := fun _ ↦ rfl
  obtain ⟨y, hy, hyx⟩ := exists_eq_of_approx (V := filt b hb hb1 N hN)
    (W := (normUnits (K := K)).ker) (Φ := Φ)
    ρ_nonneg ρ_lt_one (filt_succ_le b hb hb1 N hN)
    (fun k u hu ↦ nrm_sub_one_le_of_mem_filt b hb hb1 N hN hu)
    (fun k ↦ ⟨k + (2 * N + 1) + N, fun u hu ↦ mem_filt_of_nrm_le b hb hb1 N hN k u hu⟩)
    (fun k u hu ↦ by rw [hΦ]; exact div_mem (galUnits_mem_filt b hb hb1 N hN hu σ) hu)
    (fun u ↦ by rw [MonoidHom.mem_ker, hΦ, _root_.map_div, normUnits_galUnits, div_self'])
    (fun k u hu huW ↦ by
      simp_rw [hΦ]
      exact step_Hm1 b hb hb1 N hN σ hσ k u hu (MonoidHom.mem_ker.1 huW))
    x hx (MonoidHom.mem_ker.2 hnorm)
  exact ⟨y, hy, hyx⟩

end Steps

end PadicField
