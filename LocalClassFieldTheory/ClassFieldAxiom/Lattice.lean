/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.ClassFieldAxiom.Coordinates
import LocalClassFieldTheory.ClassFieldAxiom.Approximation

/-!
# A normal-basis lattice and the filtration `1 + 𝔅ₖ` of the unit group

Let `L/K` be a finite Galois extension of fields finite over `ℚ_[p]`, and `b` a normal basis
(`b g = g (b 1)`) with `‖b 1‖ ≤ 1`. For `k : ℕ` let `𝔅 k` be the set of `x : L` whose coordinates
have absolute value `≤ ρ ^ k`, where `ρ = ‖π_K‖`. This is a `Gal(L/K)`-stable lattice, contained
in the ball of radius `ρ ^ k` and containing the ball of radius `ρ ^ (k + N)` for a fixed `N`.

Here we set up `𝔅` and the basic estimates; see `ClassFieldAxiom/Units.lean` for the unit
filtration.
-/

open Polynomial

-- The section variables are shared by many small lemmas; not all of them use every instance.
set_option linter.unusedSectionVars false

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L] [FiniteDimensional K L] [IsGalois K L]

variable (p K) in
/-- `ρ = ‖π_K‖`. -/
noncomputable def ρ : ℝ := nrm p K (uniformizer p K)

theorem ρ_nonneg : 0 ≤ ρ p K := nrm_nonneg _

theorem ρ_lt_one : ρ p K < 1 := uniformizer_spec.nrm_lt_one

theorem ρ_pos : 0 < ρ p K := nrm_pos_iff.2 uniformizer_spec.ne_zero

/-- Products of `1 + z_i` with small `z_i`: `‖∏ (1 + z_i) - 1 - ∑ z_i‖ ≤ r ^ 2`. -/
theorem nrm_prod_one_add_sub_le {ι : Type*} (s : Finset ι) (z : ι → L) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hz : ∀ i ∈ s, nrm p L (z i) ≤ r) :
    nrm p L (∏ i ∈ s, (1 + z i) - 1 - ∑ i ∈ s, z i) ≤ r ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pow_nonneg hr0 2
  | insert a s ha ih =>
    have ih := ih fun i hi ↦ hz i (by simp [hi])
    have hza := hz a (by simp)
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    set P := ∏ i ∈ s, (1 + z i)
    set S := ∑ i ∈ s, z i
    have hS : nrm p L S ≤ r := nrm_sum_le _ _ hr0 fun i hi ↦ hz i (by simp [hi])
    have : (1 + z a) * P - 1 - (z a + S) = (P - 1 - S) + z a * S + z a * (P - 1 - S) := by ring
    rw [this]
    have hr2 : r ^ 2 ≤ r := by nlinarith
    refine (nrm_add_le_max _ _).trans (max_le ((nrm_add_le_max _ _).trans (max_le ih ?_)) ?_)
    · rw [nrm_mul, sq]; exact mul_le_mul hza hS (nrm_nonneg _) hr0
    · rw [nrm_mul]
      calc nrm p L (z a) * nrm p L (P - 1 - S) ≤ 1 * r ^ 2 :=
            mul_le_mul (hza.trans hr1) ih (nrm_nonneg _) zero_le_one
        _ = r ^ 2 := one_mul _

section Basis

variable (b : Module.Basis (L ≃ₐ[K] L) K L)

/-- Coordinates with respect to a normal basis are permuted by the Galois action. -/
theorem repr_apply_galois (hb : ∀ g, b g = g (b 1)) (g h : L ≃ₐ[K] L) (x : L) :
    b.repr (g x) h = b.repr x (g⁻¹ * h) := by
  classical
  let f₁ : L →ₗ[K] K := (Finsupp.lapply h).comp (b.repr.toLinearMap.comp g.toLinearMap)
  let f₂ : L →ₗ[K] K := (Finsupp.lapply (g⁻¹ * h)).comp b.repr.toLinearMap
  have : f₁ = f₂ := by
    refine b.ext fun k ↦ ?_
    simp only [f₁, f₂, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      LinearEquiv.coe_coe, Finsupp.lapply_apply, Module.Basis.repr_self]
    have hgk : g (b k) = b (g * k) := by rw [hb k, hb (g * k), AlgEquiv.mul_apply]
    rw [hgk, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.single_apply]
    congr 1
    apply propext
    constructor
    · rintro rfl; group
    · rintro rfl; group
  exact congrArg (fun f : L →ₗ[K] K ↦ f x) this

variable (p) in
/-- The lattice `𝔅 k`: elements whose coordinates have absolute value `≤ ρ ^ k`. -/
noncomputable def lat (k : ℕ) : AddSubgroup L where
  carrier := {x | ∀ g, nrm p K (b.repr x g) ≤ ρ p K ^ k}
  zero_mem' g := by
    rw [map_zero, Finsupp.zero_apply, map_zero]; exact pow_nonneg ρ_nonneg k
  add_mem' {x y} hx hy g := by
    rw [map_add, Finsupp.add_apply]
    exact (nrm_add_le_max _ _).trans (max_le (hx g) (hy g))
  neg_mem' {x} hx g := by
    rw [map_neg, Finsupp.neg_apply, nrm_neg]; exact hx g

theorem mem_lat {b : Module.Basis (L ≃ₐ[K] L) K L} {k : ℕ} {x : L} :
    x ∈ lat p b k ↔ ∀ g, nrm p K (b.repr x g) ≤ ρ p K ^ k := Iff.rfl

theorem lat_antitone {j k : ℕ} (hjk : j ≤ k) : lat p b k ≤ lat p b j := fun _ hx g ↦
  (hx g).trans (pow_le_pow_of_le_one ρ_nonneg ρ_lt_one.le hjk)

theorem galois_mem_lat (hb : ∀ g, b g = g (b 1)) {k : ℕ} {x : L} (hx : x ∈ lat p b k)
    (g : L ≃ₐ[K] L) : g x ∈ lat p b k := fun h ↦ by
  rw [repr_apply_galois b hb]; exact hx _

theorem smul_basis_mem_lat {k : ℕ} {a : K} (ha : nrm p K a ≤ ρ p K ^ k) (g : L ≃ₐ[K] L) :
    a • b g ∈ lat p b k := fun h ↦ by
  classical
  rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  split_ifs
  · simpa using ha
  · simpa using pow_nonneg ρ_nonneg k

/-- Elements of `𝔅 k` have absolute value `≤ ρ ^ k`. -/
theorem nrm_le_of_mem_lat (hb : ∀ g, b g = g (b 1)) (hb1 : nrm p L (b 1) ≤ 1) {k : ℕ} {x : L}
    (hx : x ∈ lat p b k) : nrm p L x ≤ ρ p K ^ k := by
  rw [← b.sum_repr x]
  refine nrm_sum_le _ _ (pow_nonneg ρ_nonneg k) fun g _ ↦ ?_
  rw [Algebra.smul_def, nrm_mul, nrm_algebraMap_tower, hb g, nrm_algEquiv_tower]
  calc nrm p K (b.repr x g) * nrm p L (b 1) ≤ ρ p K ^ k * 1 :=
        mul_le_mul (hx g) hb1 (nrm_nonneg _) (pow_nonneg ρ_nonneg k)
    _ = _ := mul_one _

/-- The lattice contains a ball: there is `N` with `‖x‖ ≤ ρ ^ (k + N) → x ∈ 𝔅 k`. -/
theorem exists_lat_ball : ∃ N : ℕ, ∀ k : ℕ, ∀ x : L,
    nrm p L x ≤ ρ p K ^ (k + N) → x ∈ lat p b k := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_repr_bound (p := p) b
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (C + 1) by positivity)
    (ρ_lt_one (p := p) (K := K))
  refine ⟨N, fun k x hx g ↦ (hC x g).trans ?_⟩
  have hN' : C * ρ p K ^ N ≤ 1 := by
    have h1 : ρ p K ^ N * (C + 1) < 1 := by
      rwa [lt_div_iff₀ (by positivity)] at hN
    nlinarith [pow_nonneg (ρ_nonneg (p := p) (K := K)) N]
  calc C * nrm p L x ≤ C * ρ p K ^ (k + N) := mul_le_mul_of_nonneg_left hx hC0
    _ = (C * ρ p K ^ N) * ρ p K ^ k := by rw [pow_add]; ring
    _ ≤ 1 * ρ p K ^ k := mul_le_mul_of_nonneg_right hN' (pow_nonneg ρ_nonneg k)
    _ = ρ p K ^ k := one_mul _

end Basis

/-- There is a normal basis with `‖b 1‖ ≤ 1`. -/
theorem exists_integral_normalBasis :
    ∃ b : Module.Basis (L ≃ₐ[K] L) K L, (∀ g, b g = g (b 1)) ∧ nrm p L (b 1) ≤ 1 := by
  set b₀ := IsGalois.normalBasis K L
  have hb₀ : ∀ g, b₀ g = g (b₀ 1) := fun g ↦ IsGalois.normalBasis_apply g
  set α := b₀ 1
  have hα : α ≠ 0 := b₀.ne_zero 1
  have hpos : 0 < nrm p L α := nrm_pos_iff.2 hα
  have hp1 : ‖(p : ℚ_[p])‖ < 1 := by rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ one_lt_p_real
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / nrm p L α by positivity) hp1
  set c : K := algebraMap ℚ_[p] K ((p : ℚ_[p]) ^ M)
  have hc : c ≠ 0 := by
    simp only [c, ne_eq, map_eq_zero_iff _ (algebraMap ℚ_[p] K).injective]
    exact pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  refine ⟨b₀.isUnitSMul (w := fun _ ↦ c) fun _ ↦ hc.isUnit, fun g ↦ ?_, ?_⟩
  · simp only [Module.Basis.isUnitSMul_apply, hb₀ g, map_smul]
    rfl
  · rw [Module.Basis.isUnitSMul_apply, Algebra.smul_def, nrm_mul, nrm_algebraMap_tower,
      nrm_algebraMap, norm_pow]
    rw [lt_div_iff₀ hpos] at hM
    exact hM.le

end PadicField
