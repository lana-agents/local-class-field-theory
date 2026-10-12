/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.MaxUnramified

/-!
# The absolute inertia group and the unramified quotient

Let `K` be a field finite over `ℚ_[p]` and `Ω` an algebraic closure of `K` (an algebraically
closed, algebraic extension). We assume `[Algebra.IsAlgebraic ℚ_[p] Ω]`, so that the canonical
absolute value `nrm p Ω` is defined on `Ω`; this is equivalent to `Algebra.IsAlgebraic K Ω`
(`PadicField.isAlgebraic_of_tower`, `PadicField.isAlgebraic_tower_top`). The hypothesis is phrased
over `ℚ_[p]` because an instance deriving it from `Algebra.IsAlgebraic K Ω` could not find `K`.

## Main definitions

* `PadicField.absInertia p K Ω`: the inertia subgroup `I_K` of `Gal(Ω/K)`, consisting of the
  automorphisms acting trivially on residues: `‖σ x - x‖ < 1` whenever `‖x‖ ≤ 1`.
* `PadicField.unramifiedQuotientEquiv`: `Gal(Ω/K) ⧸ I_K ≃* Gal(K^ur/K)`, induced by restriction.
* `PadicField.arithFrob p K Ω`: the arithmetic Frobenius in `Gal(Ω/K) ⧸ I_K`.

## Main results

* `PadicField.absInertia_eq`: `I_K = Gal(Ω/K^ur)`.
* `PadicField.absInertia_normal`: `I_K` is normal.
* `PadicField.arithFrob_spec`, `PadicField.mk_eq_arithFrob_iff`: a lift `σ` of `arithFrob`
  is characterised by `‖σ x - x ^ q‖ < 1` for all `‖x‖ ≤ 1`.

## Implementation notes

The key approximation lemma is `PadicField.exists_teichmuller_approx`: every `x ∈ Ω` with
`‖x‖ ≤ 1` is congruent modulo the maximal ideal to a root `ω` of `X ^ (q ^ n) - X` for some
`n > 0` (the Teichmüller representative of the residue of `x` in `K(x)`), hence to an element of
`K_n ⊆ K^ur`. Conversely, roots of `X ^ (q ^ n) - X` are determined by their residues
(`PadicField.eq_of_pow_eq_self_of_natCast_mem`), so inertia fixes them.
-/

open Polynomial IsLocalRing IntermediateField

namespace PadicField

section LocalRing

/-- In a local ring, two roots of `X ^ N - X` congruent modulo the maximal ideal are equal,
provided `N` lies in the maximal ideal. -/
theorem eq_of_pow_eq_self_of_natCast_mem {R : Type*} [CommRing R] [IsLocalRing R] {N : ℕ}
    (hN : (N : R) ∈ maximalIdeal R) {x y : R} (hx : x ^ N = x) (hy : y ^ N = y)
    (hxy : x - y ∈ maximalIdeal R) : x = y := by
  have hres : residue R x = residue R y := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hxy
  set s := ∑ i ∈ Finset.range N, x ^ i * y ^ (N - 1 - i)
  have hgeom : s * (x - y) = x ^ N - y ^ N := (Commute.all x y).geom_sum₂_mul N
  rw [hx, hy] at hgeom
  have hs : s ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff]
    simp only [s, map_sum, map_mul, map_pow, hres]
    rw [Finset.sum_congr rfl fun i hi ↦ by
      rw [← pow_add, Nat.add_sub_cancel' (by simp at hi; omega)]]
    have hN0 : residue R (N : R) = 0 := (residue_eq_zero_iff _).2 hN
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← map_natCast (residue R), hN0,
      zero_mul]
  have hunit : IsUnit (1 - s) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro h
    exact (maximalIdeal.isMaximal R).ne_top
      ((Ideal.eq_top_iff_one _).2 (by simpa using add_mem h hs))
  have : (1 - s) * (x - y) = 0 := by rw [sub_mul, one_mul, hgeom, sub_self]
  rw [← sub_eq_zero]
  exact (hunit.mul_right_eq_zero).1 this

end LocalRing

variable {p : ℕ} [hp : Fact p.Prime]

section Basic

variable {L : Type*} [Field L] [Algebra ℚ_[p] L] [Algebra.IsAlgebraic ℚ_[p] L]

/-- An element which is a root of `X ^ N - X` with `N ≥ 2` has norm `≤ 1`. -/
theorem nrm_le_one_of_pow_eq_self {N : ℕ} (hN : 1 < N) {x : L} (hx : x ^ N = x) :
    nrm p L x ≤ 1 := by
  have h1 := congrArg (nrm p L) hx
  rw [nrm_pow] at h1
  by_contra! hlt
  have := lt_self_pow₀ hlt hN
  linarith

/-- `‖a ^ n - b ^ n‖ ≤ ‖a - b‖` for `‖a‖, ‖b‖ ≤ 1`. -/
theorem nrm_pow_sub_pow_le {a b : L} (ha : nrm p L a ≤ 1) (hb : nrm p L b ≤ 1) (n : ℕ) :
    nrm p L (a ^ n - b ^ n) ≤ nrm p L (a - b) := by
  rw [← (Commute.all a b).geom_sum₂_mul n, nrm_mul]
  refine mul_le_of_le_one_left (nrm_nonneg _) (nrm_sum_le _ _ zero_le_one fun i _ ↦ ?_)
  rw [nrm_mul, nrm_pow, nrm_pow]
  exact mul_le_one₀ (pow_le_one₀ (nrm_nonneg _) ha) (pow_nonneg (nrm_nonneg _) _)
    (pow_le_one₀ (nrm_nonneg _) hb)

end Basic

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]

variable (p K Ω) in
/-- An algebraic extension of a field finite over `ℚ_[p]` is algebraic over `ℚ_[p]`. -/
theorem isAlgebraic_of_tower [Algebra.IsAlgebraic K Ω] : Algebra.IsAlgebraic ℚ_[p] Ω :=
  Algebra.IsAlgebraic.trans ℚ_[p] K Ω

variable (p K Ω) in
omit [FiniteDimensional ℚ_[p] K] in
/-- An extension algebraic over `ℚ_[p]` is algebraic over `K`. -/
theorem isAlgebraic_tower_top [Algebra.IsAlgebraic ℚ_[p] Ω] : Algebra.IsAlgebraic K Ω :=
  Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) K

variable [Algebra.IsAlgebraic ℚ_[p] Ω]

/-- The residue cardinality `q` of `K` has norm `< 1` in `Ω`. -/
theorem nrm_natCast_q_lt_one : nrm p Ω (q p K : Ω) < 1 := by
  have h := Teichmuller.natCast_Q_mem_maximalIdeal (R := 𝒪 p K)
  rw [Integers.mem_maximalIdeal_iff, Integers.coe_eq_algebraMap, map_natCast] at h
  rw [← map_natCast (algebraMap K Ω), nrm_algebraMap_tower]
  exact h

theorem nrm_natCast_q_pow_lt_one {n : ℕ} (hn : 0 < n) : nrm p Ω ((q p K ^ n : ℕ) : Ω) < 1 := by
  rw [Nat.cast_pow, nrm_pow]
  exact pow_lt_one₀ (nrm_nonneg _) nrm_natCast_q_lt_one hn.ne'

variable (p K Ω) in
/-- The (absolute) inertia group `I_K ≤ Gal(Ω/K)`: automorphisms acting trivially on the residues
of integral elements. -/
noncomputable def absInertia : Subgroup (Ω ≃ₐ[K] Ω) where
  carrier := {σ | ∀ x : Ω, nrm p Ω x ≤ 1 → nrm p Ω (σ x - x) < 1}
  one_mem' x _ := by simp
  mul_mem' {σ τ} hσ hτ x hx := by
    have hτx : nrm p Ω (τ x) ≤ 1 := by rwa [nrm_algEquiv_tower]
    have : σ (τ x) - x = (σ (τ x) - τ x) + (τ x - x) := by ring
    rw [AlgEquiv.mul_apply, this]
    exact (nrm_add_le_max _ _).trans_lt (max_lt (hσ _ hτx) (hτ x hx))
  inv_mem' {σ} hσ x hx := by
    have hy : nrm p Ω (σ⁻¹ x) ≤ 1 := by rwa [nrm_algEquiv_tower]
    have : σ⁻¹ x - x = -(σ (σ⁻¹ x) - σ⁻¹ x) := by
      rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]; ring
    rw [this, nrm_neg]
    exact hσ _ hy

omit [FiniteDimensional ℚ_[p] K] in
theorem mem_absInertia_iff (σ : Ω ≃ₐ[K] Ω) :
    σ ∈ absInertia p K Ω ↔ ∀ x : Ω, nrm p Ω x ≤ 1 → nrm p Ω (σ x - x) < 1 := Iff.rfl

/-- The inertia group is normal. -/
instance absInertia_normal : (absInertia p K Ω).Normal where
  conj_mem σ hσ τ x hx := by
    have hy : nrm p Ω (τ⁻¹ x) ≤ 1 := by rwa [nrm_algEquiv_tower]
    have : (τ * σ * τ⁻¹) x - x = τ (σ (τ⁻¹ x) - τ⁻¹ x) := by
      rw [map_sub, AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
        AlgEquiv.apply_symm_apply]
    rw [this, nrm_algEquiv_tower]
    exact hσ _ hy

/-- Inertia fixes every root of `X ^ (q ^ n) - X`. -/
theorem absInertia_apply_eq_of_pow_eq {σ : Ω ≃ₐ[K] Ω} (hσ : σ ∈ absInertia p K Ω) {n : ℕ}
    (hn : 0 < n) {x : Ω} (hx : x ^ q p K ^ n = x) : σ x = x := by
  have hN : 1 < q p K ^ n := one_lt_q_pow hn
  have hx1 : nrm p Ω x ≤ 1 := nrm_le_one_of_pow_eq_self hN hx
  have hy1 : nrm p Ω (σ x) ≤ 1 := by rwa [nrm_algEquiv_tower]
  have h := eq_of_pow_eq_self_of_natCast_mem (R := 𝒪 p Ω) (N := q p K ^ n)
    (x := Integers.mk (σ x) hy1) (y := Integers.mk x hx1) ?_ ?_ ?_ ?_
  · exact congrArg (fun z : 𝒪 p Ω ↦ (z : Ω)) h
  · rw [Integers.mem_maximalIdeal_iff, Integers.coe_eq_algebraMap, map_natCast]
    exact nrm_natCast_q_pow_lt_one hn
  · ext; simp only [Integers.coe_pow, Integers.coe_mk, ← map_pow, hx]
  · ext; simp only [Integers.coe_pow, Integers.coe_mk, hx]
  · rw [Integers.mem_maximalIdeal_iff, Integers.coe_sub, Integers.coe_mk, Integers.coe_mk]
    exact hσ x hx1

/-- **Teichmüller approximation.** Every `x ∈ Ω` with `‖x‖ ≤ 1` is congruent modulo the maximal
ideal to a root of `X ^ (q ^ n) - X` for some `n > 0`. -/
theorem exists_teichmuller_approx {x : Ω} (hx : nrm p Ω x ≤ 1) :
    ∃ n, 0 < n ∧ ∃ ω : Ω, ω ^ q p K ^ n = ω ∧ nrm p Ω (x - ω) < 1 := by
  haveI := isAlgebraic_tower_top p K Ω
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  set L := K⟮x⟯
  haveI : FiniteDimensional K L := adjoin.finiteDimensional hint
  set x' : L := AdjoinSimple.gen K x
  have hx' : nrm p L x' ≤ 1 := by
    rw [← nrm_algebraMap_tower (L := Ω), AdjoinSimple.algebraMap_gen]; exact hx
  set X := Integers.mk x' hx'
  set ω := Teichmuller.teichmuller (𝒪 p L) (residue _ X)
  refine ⟨f p K L, f_pos, ((ω : 𝒪 p L) : L), ?_, ?_⟩
  · have h := Teichmuller.teichmuller_pow_Q (residue _ X)
    have h' : ((ω : 𝒪 p L) : L) ^ q p L = (ω : L) := by
      rw [← Integers.coe_pow]; exact congrArg _ h
    rw [← q_eq_pow_f (K := K), ← IntermediateField.coe_pow, h']
  · have h : X - ω ∈ maximalIdeal (𝒪 p L) := by
      rw [← residue_eq_zero_iff, map_sub, Teichmuller.residue_teichmuller, sub_self]
    rw [Integers.mem_maximalIdeal_iff, Integers.coe_sub, Integers.coe_mk,
      ← nrm_algebraMap_tower (L := Ω), map_sub, AdjoinSimple.algebraMap_gen] at h
    exact h

/-- Every `x ∈ Ω` with `‖x‖ ≤ 1` is congruent modulo the maximal ideal to an element of
`K^ur` of norm `≤ 1`. -/
theorem exists_maxUnramified_approx {x : Ω} (hx : nrm p Ω x ≤ 1) :
    ∃ y ∈ maxUnramified p K Ω, nrm p Ω y ≤ 1 ∧ nrm p Ω (x - y) < 1 := by
  obtain ⟨n, hn, ω, hω, hxω⟩ := exists_teichmuller_approx (K := K) hx
  exact ⟨ω, unramifiedOfDegree_le_maxUnramified p K Ω n
    (mem_unramifiedOfDegree_of_pow_eq hn hω), nrm_le_one_of_pow_eq_self (one_lt_q_pow hn) hω,
    hxω⟩

/-- **Inertia is the Galois group over `K^ur`.** -/
theorem absInertia_eq : absInertia p K Ω = (maxUnramified p K Ω).fixingSubgroup := by
  refine le_antisymm ?_ fun σ hσ x hx ↦ ?_
  · rw [← IntermediateField.le_iff_le]
    refine iSup_le fun n ↦ ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [unramifiedOfDegree_zero]; exact bot_le
    rw [unramifiedOfDegree_def]
    refine adjoin_le_iff.2 fun x hx ↦ ?_
    rw [mem_rootSet_X_pow_sub_X (one_lt_q_pow hn)] at hx
    exact (mem_fixedField_iff _ _).2 fun σ hσ ↦ absInertia_apply_eq_of_pow_eq hσ hn hx
  · obtain ⟨y, hy, -, hxy⟩ := exists_maxUnramified_approx (K := K) hx
    have hσy : σ y = y := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ y hy
    have : σ x - x = σ (x - y) - (x - y) := by rw [map_sub, hσy]; ring
    rw [this]
    refine (nrm_sub_le_max _ _).trans_lt (max_lt ?_ hxy)
    rwa [nrm_algEquiv_tower]

variable [IsAlgClosed Ω]

variable (p K Ω) in
omit [FiniteDimensional ℚ_[p] K] in
include p in
/-- An algebraically closed field algebraic over `ℚ_[p]` is normal over `K`. -/
theorem normal_of_isAlgClosed : Normal K Ω :=
  haveI := isAlgebraic_tower_top p K Ω
  normal_iff.2 fun x ↦ ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩

theorem ker_restrictNormalHom_maxUnramified :
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (maxUnramified p K Ω)).ker =
      absInertia p K Ω := by
  rw [restrictNormalHom_ker, absInertia_eq]

variable (p K Ω) in
/-- The unramified quotient: `Gal(Ω/K) ⧸ I_K ≃* Gal(K^ur/K)`, induced by restriction. -/
noncomputable def unramifiedQuotientEquiv :
    (Ω ≃ₐ[K] Ω) ⧸ absInertia p K Ω ≃*
      (maxUnramified p K Ω ≃ₐ[K] maxUnramified p K Ω) :=
  haveI := normal_of_isAlgClosed p K Ω
  QuotientGroup.liftEquiv _ (AlgEquiv.restrictNormalHom_surjective Ω)
    ker_restrictNormalHom_maxUnramified.symm

theorem unramifiedQuotientEquiv_mk (σ : Ω ≃ₐ[K] Ω) (x : maxUnramified p K Ω) :
    (unramifiedQuotientEquiv p K Ω (QuotientGroup.mk σ) x : Ω) = σ x :=
  AlgEquiv.restrictNormalHom_apply _ σ x

variable (p K Ω) in
/-- The arithmetic Frobenius modulo inertia: the element of `Gal(Ω/K) ⧸ I_K` corresponding to
`frobUr`. -/
noncomputable def arithFrob : (Ω ≃ₐ[K] Ω) ⧸ absInertia p K Ω :=
  (unramifiedQuotientEquiv p K Ω).symm (frobUr p K Ω)

theorem unramifiedQuotientEquiv_arithFrob :
    unramifiedQuotientEquiv p K Ω (arithFrob p K Ω) = frobUr p K Ω :=
  MulEquiv.apply_symm_apply _ _

/-- A lift of the arithmetic Frobenius acts as `x ↦ x ^ q` on the roots of
`X ^ (q ^ n) - X`. -/
theorem arithFrob_apply_of_pow_eq {σ : Ω ≃ₐ[K] Ω} (hσ : QuotientGroup.mk σ = arithFrob p K Ω)
    {n : ℕ} (hn : 0 < n) {y : Ω} (hy : y ^ q p K ^ n = y) : σ y = y ^ q p K := by
  have hyn := mem_unramifiedOfDegree_of_pow_eq (p := p) (K := K) (Ω := Ω) hn hy
  have h := unramifiedQuotientEquiv_mk σ ⟨y, unramifiedOfDegree_le_maxUnramified p K Ω n hyn⟩
  rw [hσ, unramifiedQuotientEquiv_arithFrob, frobUr_apply hn hyn,
    frob_unramifiedOfDegree_apply hn _ hy] at h
  rw [← h]
  rfl

/-- **Arithmetic Frobenius modulo inertia.** Every lift `σ` of `arithFrob` satisfies
`‖σ x - x ^ q‖ < 1` for all `x ∈ Ω` with `‖x‖ ≤ 1`. -/
theorem arithFrob_spec {σ : Ω ≃ₐ[K] Ω} (hσ : QuotientGroup.mk σ = arithFrob p K Ω) {x : Ω}
    (hx : nrm p Ω x ≤ 1) : nrm p Ω (σ x - x ^ q p K) < 1 := by
  obtain ⟨n, hn, ω, hω, hxω⟩ := exists_teichmuller_approx (K := K) hx
  have hω1 : nrm p Ω ω ≤ 1 := nrm_le_one_of_pow_eq_self (one_lt_q_pow hn) hω
  have hσω := arithFrob_apply_of_pow_eq hσ hn hω
  have : σ x - x ^ q p K = σ (x - ω) - (x ^ q p K - ω ^ q p K) := by
    rw [map_sub, hσω]; ring
  rw [this]
  refine (nrm_sub_le_max _ _).trans_lt (max_lt ?_ ?_)
  · rwa [nrm_algEquiv_tower]
  · exact (nrm_pow_sub_pow_le hx hω1 _).trans_lt hxω

/-- **Uniqueness of the arithmetic Frobenius modulo inertia.** -/
theorem mk_eq_arithFrob_iff (σ : Ω ≃ₐ[K] Ω) :
    QuotientGroup.mk σ = arithFrob p K Ω ↔
      ∀ x : Ω, nrm p Ω x ≤ 1 → nrm p Ω (σ x - x ^ q p K) < 1 := by
  refine ⟨fun hσ x hx ↦ arithFrob_spec hσ hx, fun h ↦ ?_⟩
  obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (arithFrob p K Ω)
  rw [← hτ, eq_comm, QuotientGroup.eq]
  intro x hx
  have hτx := arithFrob_spec hτ hx
  have : (τ⁻¹ * σ) x - x = τ⁻¹ ((σ x - x ^ q p K) - (τ x - x ^ q p K)) := by
    rw [AlgEquiv.mul_apply, map_sub, map_sub, map_sub, AlgEquiv.aut_inv,
      AlgEquiv.symm_apply_apply]
    ring
  rw [this, nrm_algEquiv_tower]
  exact (nrm_sub_le_max _ _).trans_lt (max_lt (h x hx) hτx)

end PadicField
