/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.KummerH2
import LocalClassFieldTheory.Brauer.Duality
import LocalClassFieldTheory.Brauer.Restriction

/-!
# Functoriality of the cyclotomic rigidity isomorphism `H²(K, μ_n) ≃ ℤ/n`

* `PadicField.h2MuEquiv_muIncl`: for `n ∣ m`, the inclusion `μ_n ⊆ μ_m` corresponds to
  `ℤ/n → ℤ/m`, `k ↦ (m/n) k`;
* `PadicField.h2MuEquiv_muPow`: for `n ∣ m`, the power map `μ_m → μ_n`, `ζ ↦ ζ^{m/n}`, corresponds
  to the reduction `ℤ/m → ℤ/n`;
* `PadicField.h2MuEquiv_resMu`: restriction to a finite extension `K' ⊆ Ω` corresponds to
  multiplication by `[K' : K]`.

In particular the isomorphisms `H²(K, μ_n) ≃ ℤ/n` form a compatible system, giving
`H²(K, Ẑ(1)) ≃ Ẑ` in the limit.
-/

open ContH2 groupCohomology KummerTheory

set_option linter.unusedSectionVars false

namespace Brauer

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- The inclusion `μ_n ⊆ μ_m` for `n ∣ m`. -/
def muIncl {n m : ℕ} (h : n ∣ m) : Mu n Ω →* Mu m Ω where
  toFun ζ := Mu.mk (Mu.val ζ) (by
    obtain ⟨k, rfl⟩ := h
    rw [pow_mul, Mu.val_pow_n, one_pow])
  map_one' := Mu.ext (by simp)
  map_mul' _ _ := Mu.ext (by simp)

@[simp]
theorem val_muIncl {n m : ℕ} (h : n ∣ m) (ζ : Mu n Ω) : Mu.val (muIncl h ζ) = Mu.val ζ := rfl

/-- The power map `μ_m → μ_n`, `ζ ↦ ζ^{m/n}`, for `n ∣ m`. -/
def muPow {n m : ℕ} (h : n ∣ m) : Mu m Ω →* Mu n Ω where
  toFun ζ := Mu.mk (Mu.val ζ ^ (m / n)) (by
    rw [← pow_mul, Nat.div_mul_cancel h, Mu.val_pow_n])
  map_one' := Mu.ext (by simp)
  map_mul' _ _ := Mu.ext (by simp [mul_pow])

@[simp]
theorem val_muPow {n m : ℕ} (h : n ∣ m) (ζ : Mu m Ω) :
    Mu.val (muPow h ζ) = Mu.val ζ ^ (m / n) := rfl

/-- `H²(K, μ_n) → H²(K, μ_m)` induced by `μ_n ⊆ μ_m`. -/
def h2MuIncl {n m : ℕ} (h : n ∣ m) : H2Mu K Ω n →* H2Mu K Ω m :=
  ContH2.map (MonoidHom.id _) continuous_id (muIncl h) (fun _ _ => rfl)

/-- `H²(K, μ_m) → H²(K, μ_n)` induced by `ζ ↦ ζ^{m/n}`. -/
def h2MuPow {n m : ℕ} (h : n ∣ m) : H2Mu K Ω m →* H2Mu K Ω n :=
  ContH2.map (MonoidHom.id _) continuous_id (muPow h) (fun g ζ => Mu.ext (by
    simp only [val_muPow, Mu.val_smul, MonoidHom.id_apply, smul_pow']))

theorem toBr_h2MuIncl {n m : ℕ} (h : n ∣ m) (β : H2Mu K Ω n) :
    toBr m (h2MuIncl h β) = toBr n β := by
  induction β using ContH2.induction_on with | h f => ?_
  rfl

theorem toBr_h2MuPow {n m : ℕ} (h : n ∣ m) (β : H2Mu K Ω m) :
    toBr n (h2MuPow h β) = toBr m β ^ (m / n) := by
  induction β using ContH2.induction_on with | h f => ?_
  rw [h2MuPow, map_mk, toBr_mk, ← map_pow, ← map_pow, toBr_mk]
  refine congrArg mk (cocycles_ext fun g g' => ?_)
  simp only [cocyclesMap_apply, MonoidHom.id_apply, val_muPow, SubgroupClass.coe_pow,
    Pi.pow_apply, map_pow]

theorem zmodToQZ_zmodEmbed {n m : ℕ} [NeZero n] [NeZero m] (h : n ∣ m) (k : ZMod n) :
    zmodToQZ m (zmodEmbed n m h k) = zmodToQZ n k := by
  rw [zmodEmbed_apply_val]
  obtain ⟨c, rfl⟩ := h
  rw [Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero (NeZero.ne n))]
  conv_rhs => rw [← ZMod.natCast_zmod_val k]
  rw [← Int.cast_natCast (R := ZMod (n * c)), ← Int.cast_natCast (R := ZMod n), zmodToQZ_intCast,
    zmodToQZ_intCast]
  congr 1
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hm : (c : ℚ) ≠ 0 := by
    have := NeZero.ne (n * c)
    exact_mod_cast right_ne_zero_of_mul this
  push_cast
  field_simp

theorem zmodToQZ_castHom {n m : ℕ} [NeZero n] [NeZero m] (h : n ∣ m) (k : ZMod m) :
    zmodToQZ n (ZMod.castHom h (ZMod n) k) = (m / n) • zmodToQZ m k := by
  conv_lhs => rw [← ZMod.natCast_zmod_val k]
  conv_rhs => rw [← ZMod.natCast_zmod_val k]
  rw [map_natCast, ← Int.cast_natCast (R := ZMod m), ← Int.cast_natCast (R := ZMod n),
    zmodToQZ_intCast, zmodToQZ_intCast, ← QuotientAddGroup.mk_nsmul]
  congr 1
  obtain ⟨c, rfl⟩ := h
  rw [Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero (NeZero.ne n))]
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hm : (c : ℚ) ≠ 0 := by
    have := NeZero.ne (n * c)
    exact_mod_cast right_ne_zero_of_mul this
  rw [nsmul_eq_mul]
  push_cast
  field_simp

variable [Algebra.IsIntegral K Ω] in
/-- Restriction `H²(K, μ_n) → H²(K', μ_n)`. -/
noncomputable def resMu (K' : IntermediateField K Ω) (n : ℕ) : H2Mu K Ω n →* H2Mu K' Ω n :=
  ContH2.map (resScalars K') (continuous_resScalars K') (MonoidHom.id _) (fun _ _ => rfl)

variable [Algebra.IsIntegral K Ω] in
theorem toBr_resMu (K' : IntermediateField K Ω) (n : ℕ) (β : H2Mu K Ω n) :
    toBr n (resMu K' n β) = res K' (toBr n β) := by
  induction β using ContH2.induction_on with | h f => ?_
  rfl

end Brauer

namespace PadicField

open Brauer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

/-- The inclusion `μ_n ⊆ μ_m` corresponds to `ℤ/n → ℤ/m`, `k ↦ (m/n) k`. -/
theorem h2MuEquiv_h2MuIncl {n m : ℕ} [NeZero n] [NeZero m] (h : n ∣ m) (β : H2Mu K Ω n) :
    Multiplicative.toAdd (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne m)) (h2MuIncl h β)) =
      zmodEmbed n m h (Multiplicative.toAdd
        (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n)) β)) := by
  apply zmodToQZ_injective (Nat.pos_of_ne_zero (NeZero.ne m))
  apply Multiplicative.ofAdd.injective
  rw [zmodToQZ_zmodEmbed, ← invEquiv_toBr_h2MuEquiv, ← invEquiv_toBr_h2MuEquiv, toBr_h2MuIncl]

/-- The power map `μ_m → μ_n` corresponds to the reduction `ℤ/m → ℤ/n`. -/
theorem h2MuEquiv_h2MuPow {n m : ℕ} [NeZero n] [NeZero m] (h : n ∣ m) (β : H2Mu K Ω m) :
    Multiplicative.toAdd (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n)) (h2MuPow h β)) =
      ZMod.castHom h (ZMod n) (Multiplicative.toAdd
        (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne m)) β)) := by
  apply zmodToQZ_injective (Nat.pos_of_ne_zero (NeZero.ne n))
  apply Multiplicative.ofAdd.injective
  rw [zmodToQZ_castHom, ← invEquiv_toBr_h2MuEquiv, toBr_h2MuPow, map_pow,
    invEquiv_toBr_h2MuEquiv, ofAdd_nsmul]

/-- Restriction to `K' ⊆ Ω` corresponds to multiplication by `[K' : K]`. -/
theorem h2MuEquiv_resMu (K' : IntermediateField K Ω) [FiniteDimensional K K'] {n : ℕ}
    [NeZero n] (β : H2Mu K Ω n) :
    Multiplicative.toAdd (h2MuEquiv p K' Ω (Nat.pos_of_ne_zero (NeZero.ne n)) (resMu K' n β)) =
      Module.finrank K K' • Multiplicative.toAdd
        (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n)) β) := by
  apply zmodToQZ_injective (Nat.pos_of_ne_zero (NeZero.ne n))
  apply Multiplicative.ofAdd.injective
  rw [map_nsmul, ofAdd_nsmul, ← invEquiv_toBr_h2MuEquiv, ← invEquiv_toBr_h2MuEquiv,
    toBr_resMu, invEquiv_res]

end PadicField


