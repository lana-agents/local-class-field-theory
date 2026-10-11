/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Herbrand.Basic

/-!
# Herbrand quotients of basic examples

* The trivial action on `ℤ`: `Ĥ⁰ ≅ ℤ/n` and `Ĥ⁻¹ = 0`, so `h(ℤ) = n`
  (`Herbrand.card_H0_int`, `Herbrand.subsingleton_Hm1_int`, `Herbrand.herbrand_int`).
* Induced modules `ZMod n → A` with the cyclic shift `(σ f) i = f (i + 1)`: both Tate groups
  vanish (`Herbrand.subsingleton_H0_induced`, `Herbrand.subsingleton_Hm1_induced`), hence
  `h = 1` (`Herbrand.herbrand_induced`). Combine with `Herbrand.subsingleton_H0_congr` etc. to
  transport this to modules equivariantly isomorphic to an induced module.
-/

open Finset

namespace Herbrand

theorem TateQuot.card_eq_relIndex {M : Type*} [AddCommGroup M] (P Q : M →+ M) :
    Nat.card (TateQuot P Q) = (AddMonoidHom.range Q).relIndex (AddMonoidHom.ker P) :=
  rfl

/-! ### The trivial action -/

section Trivial

variable {M : Type*} [AddCommGroup M] {n : ℕ}

@[simp]
theorem D_one_apply (x : M) : D (1 : AddMonoid.End M) x = 0 := by
  rw [D_apply, sub_eq_zero]
  rfl

theorem N_one_apply (x : M) : N (1 : AddMonoid.End M) n x = n • x := by
  rw [N_apply]
  simp only [one_pow, sum_const, card_range]
  rfl

theorem ker_D_one : AddMonoidHom.ker (D (1 : AddMonoid.End M)) = ⊤ := by
  ext x
  simp

/-- For the trivial action on `ℤ`, `|Ĥ⁰| = n`. -/
theorem card_H0_int : Nat.card (H0 (1 : AddMonoid.End ℤ) n) = n := by
  have hN : AddMonoidHom.range (N (1 : AddMonoid.End ℤ) n) = AddSubgroup.zmultiples (n : ℤ) := by
    ext x
    simp only [AddMonoidHom.mem_range, N_one_apply, AddSubgroup.mem_zmultiples_iff, smul_eq_mul,
      nsmul_eq_mul]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [← hy, mul_comm]⟩, fun ⟨y, hy⟩ => ⟨y, by rw [← hy, mul_comm]⟩⟩
  rw [TateQuot.card_eq_relIndex, ker_D_one, AddSubgroup.relIndex_top_right, hN,
    Int.index_zmultiples, Int.natAbs_natCast]

/-- For the trivial action on `ℤ` (and `n > 0`), `Ĥ⁻¹ = 0`. -/
theorem subsingleton_Hm1_int (hn : 0 < n) : Subsingleton (Hm1 (1 : AddMonoid.End ℤ) n) := by
  rw [subsingleton_Hm1_iff]
  intro x hx
  rw [N_one_apply, nsmul_eq_mul, mul_eq_zero, Nat.cast_eq_zero] at hx
  refine ⟨0, ?_⟩
  rw [map_zero, sub_zero, hx.resolve_left hn.ne']

/-- The Herbrand quotient of `ℤ` with the trivial action is `n`. -/
theorem herbrand_int (hn : 0 < n) : herbrand (1 : AddMonoid.End ℤ) n = n := by
  have := subsingleton_Hm1_int hn
  rw [herbrand, card_H0_int, Nat.card_of_subsingleton (0 : Hm1 (1 : AddMonoid.End ℤ) n),
    Nat.cast_one, div_one]

end Trivial

/-! ### Induced modules -/

section Induced

variable (A : Type*) [AddCommGroup A] (n : ℕ)

/-- The cyclic shift `(σ f) i = f (i + 1)` on the induced module `ZMod n → A`. -/
def shift : AddMonoid.End (ZMod n → A) where
  toFun f i := f (i + 1)
  map_zero' := rfl
  map_add' _ _ := rfl

variable {A n}

@[simp]
theorem shift_apply (f : ZMod n → A) (i : ZMod n) : shift A n f i = f (i + 1) := rfl

theorem shift_pow_apply (k : ℕ) (f : ZMod n → A) (i : ZMod n) :
    (shift A n ^ k) f i = f (i + k) := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    change (shift A n ^ k) (shift A n f) i = _
    rw [ih, shift_apply]
    congr 1
    push_cast
    ring

theorem shift_pow_eq_one : shift A n ^ n = 1 := by
  ext f i
  rw [shift_pow_apply, ZMod.natCast_self, add_zero]
  rfl

theorem sum_range_add_natCast [NeZero n] (g : ZMod n → A) (i : ZMod n) :
    ∑ k ∈ range n, g (i + k) = ∑ j, g j := by
  refine Finset.sum_nbij' (fun k => i + k) (fun j => (j - i).val) (by simp)
    (fun j _ => by simpa using ZMod.val_lt (j - i)) (fun k hk => ?_) (fun j _ => by simp)
    (fun _ _ => rfl)
  rw [mem_range] at hk
  simp [ZMod.val_natCast, Nat.mod_eq_of_lt hk]

theorem N_shift_apply [NeZero n] (f : ZMod n → A) (i : ZMod n) :
    N (shift A n) n f i = ∑ j, f j := by
  rw [N_apply, Finset.sum_apply]
  simp only [shift_pow_apply]
  exact sum_range_add_natCast f i

/-- `Ĥ⁰` of an induced module vanishes. -/
theorem subsingleton_H0_induced [NeZero n] : Subsingleton (H0 (shift A n) n) := by
  rw [subsingleton_H0_iff]
  intro f hf
  have hconst : ∀ k : ℕ, f k = f 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [← ih, ← congrFun hf k, shift_apply, Nat.cast_succ]
  refine ⟨Pi.single 0 (f 0), funext fun i => ?_⟩
  rw [N_shift_apply, Finset.sum_pi_single', if_pos (mem_univ _), ← hconst i.val,
    ZMod.natCast_zmod_val]

/-- `Ĥ⁻¹` of an induced module vanishes. -/
theorem subsingleton_Hm1_induced [NeZero n] : Subsingleton (Hm1 (shift A n) n) := by
  rw [subsingleton_Hm1_iff]
  intro f hf
  have htot : ∑ k ∈ range n, f k = 0 := by
    have := congrFun hf 0
    rw [N_apply, Finset.sum_apply] at this
    simpa [shift_pow_apply] using this
  refine ⟨fun i => ∑ k ∈ range i.val, f k, funext fun i => ?_⟩
  have hi : i + 1 = ((i.val + 1 : ℕ) : ZMod n) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  simp only [shift_apply, Pi.sub_apply]
  rw [hi, ZMod.val_natCast]
  rcases (Nat.succ_le_of_lt (ZMod.val_lt i)).lt_or_eq with h | h
  · rw [Nat.mod_eq_of_lt h, sum_range_succ, ZMod.natCast_zmod_val, add_sub_cancel_left]
  · have h' : i.val + 1 = n := h
    rw [show range n = range (i.val + 1) from congrArg range h'.symm, sum_range_succ,
      ZMod.natCast_zmod_val] at htot
    rw [h', Nat.mod_self, sum_range_zero, zero_sub]
    exact neg_eq_of_add_eq_zero_right htot

/-- The Herbrand quotient of an induced module is `1`. -/
theorem herbrand_induced [NeZero n] : herbrand (shift A n) n = 1 := by
  have := subsingleton_H0_induced (A := A) (n := n)
  have := subsingleton_Hm1_induced (A := A) (n := n)
  rw [herbrand, Nat.card_of_subsingleton (0 : H0 (shift A n) n),
    Nat.card_of_subsingleton (0 : Hm1 (shift A n) n), Nat.cast_one, div_one]

end Induced

end Herbrand
