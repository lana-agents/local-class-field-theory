/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.Norm

/-!
# Valuation and ring of integers of a finite extension of `ℚ_[p]`

For a field `K` finite over `ℚ_[p]` we define

* `PadicField.valuation p K : Valuation K ℝ≥0`, the valuation given by the canonical absolute value;
* `PadicField.integers p K : ValuationSubring K`, the closed unit ball, and its type synonym
  `PadicField.Integers p K` (notation `𝒪 p K`), which is a discrete valuation ring;
* `PadicField.v p x : ℤ`, the normalised valuation (`v π = 1` for a uniformiser `π`).

The value group is discrete because `‖x‖ ^ [K : ℚ_[p]]! ∈ p ^ ℤ`
(`PadicField.nrm_pow_expo`).
-/

open Polynomial NNReal

namespace PadicField

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [Algebra ℚ_[p] K]

section Discrete

variable [FiniteDimensional ℚ_[p] K]

/-- A common multiple of the degrees of all elements of `K` over `ℚ_[p]`, namely `[K : ℚ_[p]]!`.
-/
noncomputable def expo : ℕ := (Module.finrank ℚ_[p] K).factorial

omit [FiniteDimensional ℚ_[p] K] in
theorem expo_pos : 0 < expo p K := Nat.factorial_pos _

variable {p K}

theorem exists_nrm_pow_expo_eq {x : K} (hx : x ≠ 0) :
    ∃ m : ℤ, nrm p K x ^ expo p K = (p : ℝ) ^ (-m) := by
  obtain ⟨m, hm⟩ := exists_nrm_pow_natDegree_eq (p := p) hx
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  obtain ⟨c, hc⟩ : (minpoly ℚ_[p] x).natDegree ∣ expo p K :=
    Nat.dvd_factorial (minpoly.natDegree_pos hint) (minpoly.natDegree_le x)
  refine ⟨m * c, ?_⟩
  rw [hc, pow_mul, hm, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

open scoped Classical in
variable (p) in
/-- The (unnormalised) additive valuation: `‖x‖ ^ expo = p ^ (- wval x)`. -/
noncomputable def wval (x : K) : ℤ :=
  if hx : x = 0 then 0 else (exists_nrm_pow_expo_eq (p := p) hx).choose

theorem nrm_pow_expo {x : K} (hx : x ≠ 0) :
    nrm p K x ^ expo p K = (p : ℝ) ^ (-wval p x) := by
  rw [wval, dif_neg hx]
  exact (exists_nrm_pow_expo_eq (p := p) hx).choose_spec

theorem one_lt_p_real : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

theorem zpow_p_injective : Function.Injective fun m : ℤ ↦ (p : ℝ) ^ m :=
  zpow_right_injective₀ (by exact_mod_cast hp.out.pos) one_lt_p_real.ne'

theorem wval_eq_iff {x : K} (hx : x ≠ 0) (m : ℤ) :
    wval p x = m ↔ nrm p K x ^ expo p K = (p : ℝ) ^ (-m) := by
  rw [nrm_pow_expo hx]
  constructor
  · rintro rfl; rfl
  · intro h; simpa using zpow_p_injective h

theorem wval_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : wval p (x * y) = wval p x + wval p y := by
  rw [wval_eq_iff (mul_ne_zero hx hy), nrm_mul, mul_pow, nrm_pow_expo hx, nrm_pow_expo hy,
    ← zpow_add₀ (by exact_mod_cast hp.out.ne_zero), neg_add]

@[simp]
theorem wval_one : wval p (1 : K) = 0 := by
  rw [wval_eq_iff one_ne_zero]; simp

theorem wval_inv {x : K} (hx : x ≠ 0) : wval p x⁻¹ = -wval p x := by
  have := wval_mul (p := p) hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, wval_one] at this
  linarith

theorem wval_pow {x : K} (hx : x ≠ 0) (n : ℕ) : wval p (x ^ n) = n * wval p x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, wval_mul (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem wval_zpow {x : K} (hx : x ≠ 0) (n : ℤ) : wval p (x ^ n) = n * wval p x := by
  rcases n with n | n
  · simpa using wval_pow hx n
  · rw [zpow_negSucc, wval_inv (pow_ne_zero _ hx), wval_pow hx, Int.negSucc_eq]; push_cast; ring

theorem wval_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : wval p (x / y) = wval p x - wval p y := by
  rw [div_eq_mul_inv, wval_mul hx (inv_ne_zero hy), wval_inv hy, sub_eq_add_neg]

theorem nrm_le_one_iff_wval_nonneg {x : K} (hx : x ≠ 0) : nrm p K x ≤ 1 ↔ 0 ≤ wval p x := by
  rw [← pow_le_one_iff_of_nonneg (nrm_nonneg x) (expo_pos p K).ne', nrm_pow_expo hx,
    zpow_le_one_iff_right₀ one_lt_p_real]
  omega

theorem nrm_lt_one_iff_wval_pos {x : K} (hx : x ≠ 0) : nrm p K x < 1 ↔ 0 < wval p x := by
  rw [← pow_lt_one_iff_of_nonneg (nrm_nonneg x) (expo_pos p K).ne', nrm_pow_expo hx,
    zpow_lt_one_iff_right₀ one_lt_p_real]
  omega

theorem nrm_eq_one_iff_wval_eq_zero {x : K} (hx : x ≠ 0) : nrm p K x = 1 ↔ wval p x = 0 := by
  rw [wval_eq_iff hx]; simp [pow_eq_one_iff_of_nonneg (nrm_nonneg x) (expo_pos p K).ne']

theorem nrm_le_iff_wval_le {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    nrm p K x ≤ nrm p K y ↔ wval p y ≤ wval p x := by
  have hy' : 0 < nrm p K y := nrm_pos_iff.2 hy
  rw [← div_le_one hy', ← nrm_div, nrm_le_one_iff_wval_nonneg (div_ne_zero hx hy), wval_div hx hy]
  omega

theorem nrm_lt_iff_wval_lt {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    nrm p K x < nrm p K y ↔ wval p y < wval p x := by
  rw [← not_le, nrm_le_iff_wval_le hy hx, not_le]

@[simp]
theorem wval_natCast_p : wval p (p : K) = expo p K := by
  have hp0 : (p : K) ≠ 0 := by
    have : (p : K) = algebraMap ℚ_[p] K p := by simp
    rw [this, map_ne_zero_iff _ (algebraMap ℚ_[p] K).injective]
    exact_mod_cast hp.out.ne_zero
  rw [wval_eq_iff hp0]
  have : (p : K) = algebraMap ℚ_[p] K p := by simp
  rw [this, nrm_algebraMap, Padic.norm_p, inv_pow, ← zpow_natCast, zpow_neg]

theorem natCast_p_ne_zero : (p : K) ≠ 0 := by
  intro h
  have := wval_natCast_p (p := p) (K := K)
  rw [h, wval, dif_pos rfl] at this
  exact (expo_pos p K).ne' (by exact_mod_cast this.symm)

end Discrete

section Valuation

variable [Algebra.IsAlgebraic ℚ_[p] K]

/-- The valuation `K → ℝ≥0` given by the canonical absolute value. -/
noncomputable def valuation : Valuation K ℝ≥0 where
  toFun x := ⟨nrm p K x, nrm_nonneg x⟩
  map_zero' := by simp only [map_zero]; rfl
  map_one' := by simp only [map_one]; rfl
  map_mul' x y := by simp only [map_mul]; rfl
  map_add_le_max' x y := by
    change nrm p K (x + y) ≤ max (nrm p K x) (nrm p K y)
    exact nrm_add_le_max x y

variable {p K} in
@[simp]
theorem coe_valuation (x : K) : (valuation p K x : ℝ) = nrm p K x := rfl

/-- The ring of integers, as a valuation subring: the closed unit ball. -/
noncomputable def integers : ValuationSubring K := (valuation p K).valuationSubring

variable {p K} in
theorem mem_integers {x : K} : x ∈ integers p K ↔ nrm p K x ≤ 1 := by
  rw [integers, Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe]; rfl

/-- The ring of integers of `K`, as a type. -/
def Integers : Type _ := integers p K

@[inherit_doc] scoped notation "𝒪" => PadicField.Integers

namespace Integers

noncomputable instance : CommRing (𝒪 p K) := inferInstanceAs (CommRing (integers p K))
instance : IsDomain (𝒪 p K) := inferInstanceAs (IsDomain (integers p K))
noncomputable instance {L : Type*} [Ring L] [Algebra K L] : Algebra (𝒪 p K) L :=
  inferInstanceAs (Algebra (integers p K) L)
instance {L : Type*} [Ring L] [Algebra K L] : IsScalarTower (𝒪 p K) K L :=
  inferInstanceAs (IsScalarTower (integers p K) K L)

instance : IsFractionRing (𝒪 p K) K := inferInstanceAs (IsFractionRing (integers p K) K)
instance : ValuationRing (𝒪 p K) := inferInstanceAs (ValuationRing (integers p K))
instance : IsLocalRing (𝒪 p K) := inferInstanceAs (IsLocalRing (integers p K))
instance : IsIntegrallyClosed (𝒪 p K) :=
  inferInstanceAs (IsIntegrallyClosed (integers p K))

variable {p K}

/-- The underlying element of `K`. -/
noncomputable abbrev val (x : 𝒪 p K) : K := algebraMap (𝒪 p K) K x

noncomputable instance : CoeHead (𝒪 p K) K := ⟨val⟩

theorem coe_eq_algebraMap (x : 𝒪 p K) : (x : K) = algebraMap (𝒪 p K) K x := rfl

@[ext]
theorem ext {x y : 𝒪 p K} (h : (x : K) = y) : x = y := Subtype.ext h

theorem coe_injective : Function.Injective (algebraMap (𝒪 p K) K) := fun _ _ h ↦ ext h

theorem nrm_coe_le_one (x : 𝒪 p K) : nrm p K (x : K) ≤ 1 := mem_integers.1 (Subtype.prop x)

/-- Build an element of `𝒪 p K` from an element of norm `≤ 1`. -/
noncomputable def mk (x : K) (hx : nrm p K x ≤ 1) : 𝒪 p K := ⟨x, mem_integers.2 hx⟩

@[simp]
theorem coe_mk (x : K) (hx : nrm p K x ≤ 1) : ((mk x hx : 𝒪 p K) : K) = x := rfl

@[simp] theorem coe_zero : ((0 : 𝒪 p K) : K) = 0 := rfl
@[simp] theorem coe_one : ((1 : 𝒪 p K) : K) = 1 := rfl
@[simp] theorem coe_add (x y : 𝒪 p K) : ((x + y : 𝒪 p K) : K) = x + y := rfl
@[simp] theorem coe_mul (x y : 𝒪 p K) : ((x * y : 𝒪 p K) : K) = x * y := rfl
@[simp] theorem coe_neg (x : 𝒪 p K) : ((-x : 𝒪 p K) : K) = -x := rfl
@[simp] theorem coe_sub (x y : 𝒪 p K) : ((x - y : 𝒪 p K) : K) = x - y := rfl
@[simp] theorem coe_pow (x : 𝒪 p K) (n : ℕ) : ((x ^ n : 𝒪 p K) : K) = (x : K) ^ n := rfl

@[simp]
theorem coe_eq_zero_iff {x : 𝒪 p K} : (x : K) = 0 ↔ x = 0 :=
  ⟨fun h ↦ ext h, fun h ↦ h ▸ rfl⟩

theorem isUnit_iff_nrm_eq_one {x : 𝒪 p K} : IsUnit x ↔ nrm p K (x : K) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    set a : K := ((u : 𝒪 p K) : K)
    set b : K := (((u⁻¹ : Units (𝒪 p K)) : 𝒪 p K) : K)
    have h1 : nrm p K a ≤ 1 := nrm_coe_le_one _
    have h2 : nrm p K b ≤ 1 := nrm_coe_le_one _
    have h3 : nrm p K a * nrm p K b = 1 := by
      rw [← nrm_mul]
      simp only [a, b, ← coe_mul, Units.mul_inv, coe_one, nrm_one]
    nlinarith [nrm_nonneg (p := p) a, nrm_nonneg (p := p) b]
  · intro h
    have hx : (x : K) ≠ 0 := by intro h0; rw [h0] at h; simp at h
    refine IsUnit.of_mul_eq_one (mk (x : K)⁻¹ (by rw [nrm_inv, h, inv_one])) ?_
    ext; simp [hx]

theorem mem_maximalIdeal_iff {x : 𝒪 p K} :
    x ∈ IsLocalRing.maximalIdeal (𝒪 p K) ↔ nrm p K (x : K) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_nrm_eq_one]
  exact ⟨fun h ↦ lt_of_le_of_ne (nrm_coe_le_one x) h, fun h ↦ h.ne⟩

end Integers

end Valuation

end PadicField
