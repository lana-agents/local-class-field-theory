/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.Integers

/-!
# Normalised valuation, uniformisers, and `𝒪 p K` is a discrete valuation ring

The values `wval p x` of nonzero elements form a nonzero subgroup of `ℤ`; we let `valGen p K` be its
positive generator, and define the normalised valuation `v p x = wval p x / valGen p K`.
A uniformiser is an element `π` with `v p π = 1`.

## Main results

* `PadicField.v_mul`, `PadicField.v_inv`, ...: `v` is a homomorphism on `Kˣ`.
* `PadicField.exists_uniformizer`: uniformisers exist.
* `PadicField.eq_zpow_mul_unit`: `x = π ^ v x * u` with `‖u‖ = 1`.
* `PadicField.Integers.isDiscreteValuationRing`: `𝒪 p K` is a DVR.
-/

open Polynomial

namespace PadicField

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

theorem exists_wval_pos : ∃ k : ℕ, 0 < k ∧ ∃ x : K, x ≠ 0 ∧ wval p x = k :=
  ⟨expo p K, expo_pos p K, p, natCast_p_ne_zero, wval_natCast_p⟩

open scoped Classical in
/-- The positive generator of the value group `wval p (Kˣ) ⊆ ℤ`. -/
noncomputable def valGen : ℕ := Nat.find (exists_wval_pos p K)

theorem valGen_pos : 0 < valGen p K := by
  classical
  exact (Nat.find_spec (exists_wval_pos p K)).1

open scoped Classical in
theorem valGen_le {k : ℕ} (hk : 0 < k) {x : K} (hx : x ≠ 0) (hw : wval p x = k) :
    valGen p K ≤ k :=
  Nat.find_min' (exists_wval_pos p K) ⟨hk, x, hx, hw⟩

variable {p K}

theorem exists_wval_eq_valGen : ∃ x : K, x ≠ 0 ∧ wval p x = valGen p K := by
  classical
  exact (Nat.find_spec (exists_wval_pos p K)).2

theorem valGen_dvd_wval {x : K} (hx : x ≠ 0) : (valGen p K : ℤ) ∣ wval p x := by
  classical
  obtain ⟨π, hπ0, hπ⟩ := exists_wval_eq_valGen (p := p) (K := K)
  have hg : (0 : ℤ) < valGen p K := by exact_mod_cast valGen_pos p K
  set q := wval p x / valGen p K
  set r := wval p x % valGen p K
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hg.ne'
  have hrg : r < valGen p K := Int.emod_lt_of_pos _ hg
  have hy : x / π ^ q ≠ 0 := div_ne_zero hx (zpow_ne_zero _ hπ0)
  have hwy : wval p (x / π ^ q) = r := by
    rw [wval_div hx (zpow_ne_zero _ hπ0), wval_zpow hπ0, hπ]
    have := Int.emod_def (wval p x) (valGen p K)
    linear_combination -this
  rcases hr0.lt_or_eq with hr | hr
  · exfalso
    have := valGen_le p K (k := r.toNat) (by omega) hy (by rw [hwy]; omega)
    omega
  · exact Int.dvd_of_emod_eq_zero hr.symm

variable (p) in
/-- The normalised valuation, with `v p π = 1` for a uniformiser `π` (and `v p 0 = 0`). -/
noncomputable def v (x : K) : ℤ := wval p x / valGen p K

theorem wval_eq_v_mul {x : K} (hx : x ≠ 0) : wval p x = v p x * valGen p K := by
  rw [v, Int.ediv_mul_cancel (valGen_dvd_wval hx)]

theorem v_eq_iff {x : K} (hx : x ≠ 0) (n : ℤ) : v p x = n ↔ wval p x = n * valGen p K := by
  have hg : (valGen p K : ℤ) ≠ 0 := by exact_mod_cast (valGen_pos p K).ne'
  rw [wval_eq_v_mul hx]
  exact ⟨fun h ↦ by rw [h], fun h ↦ mul_right_cancel₀ hg h⟩

theorem v_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : v p (x * y) = v p x + v p y := by
  rw [v_eq_iff (mul_ne_zero hx hy), wval_mul hx hy, wval_eq_v_mul hx, wval_eq_v_mul hy]; ring

@[simp]
theorem v_one : v p (1 : K) = 0 := by simp [v]

theorem v_inv {x : K} (hx : x ≠ 0) : v p x⁻¹ = -v p x := by
  rw [v_eq_iff (inv_ne_zero hx), wval_inv hx, wval_eq_v_mul hx]; ring

theorem v_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : v p (x / y) = v p x - v p y := by
  rw [div_eq_mul_inv, v_mul hx (inv_ne_zero hy), v_inv hy, sub_eq_add_neg]

theorem v_pow {x : K} (hx : x ≠ 0) (n : ℕ) : v p (x ^ n) = n * v p x := by
  rw [v_eq_iff (pow_ne_zero _ hx), wval_pow hx, wval_eq_v_mul hx]; ring

theorem v_zpow {x : K} (hx : x ≠ 0) (n : ℤ) : v p (x ^ n) = n * v p x := by
  rw [v_eq_iff (zpow_ne_zero _ hx), wval_zpow hx, wval_eq_v_mul hx]; ring

theorem nrm_le_one_iff_v_nonneg {x : K} (hx : x ≠ 0) : nrm p K x ≤ 1 ↔ 0 ≤ v p x := by
  have hg : (0 : ℤ) < valGen p K := by exact_mod_cast valGen_pos p K
  rw [nrm_le_one_iff_wval_nonneg hx, wval_eq_v_mul hx]
  exact ⟨fun h ↦ nonneg_of_mul_nonneg_left h hg, fun h ↦ mul_nonneg h hg.le⟩

theorem nrm_lt_one_iff_v_pos {x : K} (hx : x ≠ 0) : nrm p K x < 1 ↔ 0 < v p x := by
  have hg : (0 : ℤ) < valGen p K := by exact_mod_cast valGen_pos p K
  rw [nrm_lt_one_iff_wval_pos hx, wval_eq_v_mul hx]
  exact ⟨fun h ↦ pos_of_mul_pos_left h hg.le, fun h ↦ mul_pos h hg⟩

theorem nrm_eq_one_iff_v_eq_zero {x : K} (hx : x ≠ 0) : nrm p K x = 1 ↔ v p x = 0 := by
  rw [nrm_eq_one_iff_wval_eq_zero hx, wval_eq_v_mul hx]
  have hg : (valGen p K : ℤ) ≠ 0 := by exact_mod_cast (valGen_pos p K).ne'
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · exact h
    · exact absurd h hg
  · intro h; rw [h, zero_mul]

theorem nrm_le_iff_v_le {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    nrm p K x ≤ nrm p K y ↔ v p y ≤ v p x := by
  have hg : (0 : ℤ) < valGen p K := by exact_mod_cast valGen_pos p K
  rw [nrm_le_iff_wval_le hx hy, wval_eq_v_mul hx, wval_eq_v_mul hy]
  exact mul_le_mul_iff_left₀ hg

theorem nrm_lt_iff_v_lt {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    nrm p K x < nrm p K y ↔ v p y < v p x := by
  rw [← not_le, nrm_le_iff_v_le hy hx, not_le]

/-- The absolute value is determined by the valuation. -/
theorem nrm_eq_iff_v_eq {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    nrm p K x = nrm p K y ↔ v p x = v p y := by
  rw [le_antisymm_iff, le_antisymm_iff, nrm_le_iff_v_le hx hy, nrm_le_iff_v_le hy hx, and_comm]

variable (p K) in
/-- A uniformiser of `K`: an element of normalised valuation one. -/
def IsUniformizer (π : K) : Prop := v p π = 1

theorem IsUniformizer.ne_zero {π : K} (h : IsUniformizer p K π) : π ≠ 0 := by
  rintro rfl; simp [IsUniformizer, v, wval] at h

variable (p K) in
theorem exists_uniformizer : ∃ π : K, IsUniformizer p K π := by
  obtain ⟨π, hπ0, hπ⟩ := exists_wval_eq_valGen (p := p) (K := K)
  exact ⟨π, (v_eq_iff hπ0 1).2 (by rw [hπ]; ring)⟩

variable (p K) in
/-- A chosen uniformiser of `K`. -/
noncomputable def uniformizer : K := (exists_uniformizer p K).choose

theorem uniformizer_spec : IsUniformizer p K (uniformizer p K) :=
  (exists_uniformizer p K).choose_spec

theorem IsUniformizer.nrm_lt_one {π : K} (h : IsUniformizer p K π) : nrm p K π < 1 := by
  rw [nrm_lt_one_iff_v_pos h.ne_zero, h]; exact one_pos

/-- Every nonzero element is a power of a uniformiser times a unit. -/
theorem eq_zpow_mul_unit {π : K} (hπ : IsUniformizer p K π) {x : K} (hx : x ≠ 0) :
    ∃ u : K, nrm p K u = 1 ∧ x = π ^ v p x * u := by
  refine ⟨x / π ^ v p x, ?_, ?_⟩
  · have h0 : π ^ v p x ≠ 0 := zpow_ne_zero _ hπ.ne_zero
    rw [nrm_eq_one_iff_v_eq_zero (div_ne_zero hx h0), v_div hx h0, v_zpow hπ.ne_zero, hπ]
    ring
  · rw [mul_div_cancel₀ _ (zpow_ne_zero _ hπ.ne_zero)]

theorem v_natCast_p : v p (p : K) = expo p K / valGen p K := by
  rw [v, wval_natCast_p]

namespace Integers

variable (p K)

/-- A uniformiser, as an element of `𝒪 p K`. -/
noncomputable def ϖ : 𝒪 p K :=
  mk (uniformizer p K) uniformizer_spec.nrm_lt_one.le

variable {p K}

@[simp]
theorem coe_ϖ : ((ϖ p K : 𝒪 p K) : K) = uniformizer p K := rfl

theorem irreducible_ϖ : Irreducible (ϖ p K) := by
  have hπ := uniformizer_spec (p := p) (K := K)
  refine ⟨fun h ↦ ?_, fun a b hab ↦ ?_⟩
  · rw [isUnit_iff_nrm_eq_one, coe_ϖ] at h
    exact hπ.nrm_lt_one.ne h
  · have ha : (a : K) ≠ 0 := by
      rintro h; rw [coe_eq_zero_iff] at h; subst h
      have := congrArg (fun x : 𝒪 p K ↦ (x : K)) hab
      simp only [coe_ϖ, coe_zero, zero_mul] at this
      exact hπ.ne_zero this
    have hb : (b : K) ≠ 0 := by
      rintro h; rw [coe_eq_zero_iff] at h; subst h
      have := congrArg (fun x : 𝒪 p K ↦ (x : K)) hab
      simp only [coe_ϖ, coe_zero, mul_zero] at this
      exact hπ.ne_zero this
    have hv : v p (a : K) + v p (b : K) = 1 := by
      rw [← v_mul ha hb, ← coe_mul, ← hab, coe_ϖ]; exact hπ
    have hva := (nrm_le_one_iff_v_nonneg ha).1 (nrm_coe_le_one a)
    have hvb := (nrm_le_one_iff_v_nonneg hb).1 (nrm_coe_le_one b)
    rcases (show v p (a : K) = 0 ∨ v p (b : K) = 0 by omega) with h | h
    · left; rw [isUnit_iff_nrm_eq_one, nrm_eq_one_iff_v_eq_zero ha]; exact h
    · right; rw [isUnit_iff_nrm_eq_one, nrm_eq_one_iff_v_eq_zero hb]; exact h

theorem associated_ϖ_pow {x : 𝒪 p K} (hx : x ≠ 0) :
    Associated (ϖ p K ^ (v p (x : K)).toNat) x := by
  have hx' : (x : K) ≠ 0 := fun h ↦ hx (coe_eq_zero_iff.1 h)
  have hπ := uniformizer_spec (p := p) (K := K)
  obtain ⟨u, hu, hxu⟩ := eq_zpow_mul_unit hπ hx'
  have hv := (nrm_le_one_iff_v_nonneg hx').1 (nrm_coe_le_one x)
  have hunit : IsUnit (mk u hu.le : 𝒪 p K) := by rw [isUnit_iff_nrm_eq_one]; exact hu
  refine ⟨hunit.unit, ext ?_⟩
  simp only [IsUnit.unit_spec, coe_mul, coe_pow, coe_ϖ, coe_mk]
  rw [← zpow_natCast, Int.toNat_of_nonneg hv]
  exact hxu.symm

instance isDiscreteValuationRing : IsDiscreteValuationRing (𝒪 p K) :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨ϖ p K, irreducible_ϖ, fun hx ↦ ⟨_, associated_ϖ_pow hx⟩⟩

end Integers

end PadicField
