/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.KummerCompat
import LocalClassFieldTheory.Galois.ZHat

/-!
# `H²(K, Ẑ(1)) ≃ Ẑ`

We define `H²(K, Ẑ(1))` as the inverse limit `lim_n H²(Gal(Ω/K), μ_n)` along the maps induced by
`μ_m → μ_n`, `ζ ↦ ζ^{m/n}` (`Brauer.H2ZHatOne`; the same convention as
`KummerTheory.H1Limit`, which `continuous-kummer-theory` identifies with `H¹(K, Ẑ(1))`), and
`Ẑ = lim_n ℤ/n` (`Brauer.ZHat`, the limit along the reductions `ℤ/m → ℤ/n`). Both limits are
indexed by `ℕ+` ordered by divisibility: for `K` of characteristic zero this is the index type
`KummerIndex K` of `continuous-kummer-theory` (every `n > 0` is invertible in `K`), and using
`ℕ+` makes the indexing independent of the base field, so that restriction is a map between limits
over the same index set.

* `PadicField.h2ZHatOneEquiv : H²(K, Ẑ(1)) ≃* Ẑ`, the inverse limit of the cyclotomic rigidity
  isomorphisms `PadicField.h2MuEquiv`, compatible by `PadicField.h2MuEquiv_h2MuPow`;
* `PadicField.h2ZHatOneEquiv_res`: under these isomorphisms, restriction to a finite `K' ⊆ Ω`
  is multiplication by `[K' : K]`.

`Brauer.ZHat` and `Brauer.intToZHat` are defined in `LocalClassFieldTheory.Galois.ZHat`.

The limit definition of `H²(K, Ẑ(1))` is the usual one (continuous cochain cohomology of the
profinite module `Ẑ(1)` agrees with it since the `H¹(K, μ_n)` are finite, so `lim¹` vanishes);
the comparison with continuous cochains is not formalised here.
-/

open ContH2 KummerTheory

namespace Brauer

variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]

/-- `H²(K, Ẑ(1)) = lim_n H²(Gal(Ω/K), μ_n)`, along `ζ ↦ ζ^{m/n}`. -/
def H2ZHatOne : Subgroup (∀ n : ℕ+, H2Mu K Ω n) where
  carrier := {x | ∀ n m : ℕ+, ∀ h : (n : ℕ) ∣ m, h2MuPow h (x m) = x n}
  mul_mem' hx hy n m h := by simp [hx n m h, hy n m h]
  one_mem' n m h := by simp
  inv_mem' hx n m h := by simp [hx n m h]

variable {K Ω}

/-- The projection `H²(K, Ẑ(1)) → H²(K, μ_n)`. -/
def H2ZHatOne.proj (n : ℕ+) : H2ZHatOne K Ω →* H2Mu K Ω n :=
  (Pi.evalMonoidHom _ n).comp (H2ZHatOne K Ω).subtype

theorem h2MuPow_proj {n m : ℕ+} (h : (n : ℕ) ∣ m) (x : H2ZHatOne K Ω) :
    h2MuPow h (H2ZHatOne.proj m x) = H2ZHatOne.proj n x := x.2 n m h

variable [Algebra.IsIntegral K Ω]

theorem resMu_h2MuPow (K' : IntermediateField K Ω) {n m : ℕ} (h : n ∣ m) (β : H2Mu K Ω m) :
    resMu K' n (h2MuPow h β) = h2MuPow h (resMu K' m β) := by
  induction β using ContH2.induction_on with | h f => ?_
  rfl

/-- Restriction `H²(K, Ẑ(1)) → H²(K', Ẑ(1))` for `K' ⊆ Ω`. -/
noncomputable def resZHatOne (K' : IntermediateField K Ω) :
    H2ZHatOne K Ω →* H2ZHatOne K' Ω :=
  (MonoidHom.pi fun n : ℕ+ => (resMu K' n).comp (H2ZHatOne.proj n)).codRestrict _
    fun x n m h => by
      simp only [MonoidHom.pi_apply, MonoidHom.coe_comp, Function.comp_apply]
      rw [← resMu_h2MuPow, h2MuPow_proj]

theorem proj_resZHatOne (K' : IntermediateField K Ω) (n : ℕ+) (x : H2ZHatOne K Ω) :
    H2ZHatOne.proj n (resZHatOne K' x) = resMu K' n (H2ZHatOne.proj n x) := rfl

end Brauer

namespace PadicField

open Brauer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

/-- The level-`n` cyclotomic rigidity isomorphism, additively. -/
noncomputable abbrev h2MuZMod (n : ℕ+) (β : H2Mu K Ω n) : ZMod n :=
  Multiplicative.toAdd (h2MuEquiv p K Ω n.pos β)

theorem h2MuZMod_h2MuPow {n m : ℕ+} (h : (n : ℕ) ∣ m) (β : H2Mu K Ω m) :
    h2MuZMod (p := p) n (h2MuPow h β) = ZMod.castHom h (ZMod n) (h2MuZMod (p := p) m β) :=
  h2MuEquiv_h2MuPow h β

variable (p K Ω) in
/-- The map `H²(K, Ẑ(1)) → Ẑ`. -/
noncomputable def h2ZHatOneHom : H2ZHatOne K Ω →* Multiplicative ZHat where
  toFun x := Multiplicative.ofAdd ⟨fun n => h2MuZMod (p := p) n (H2ZHatOne.proj n x),
    fun n m h => by rw [← h2MuZMod_h2MuPow, h2MuPow_proj]⟩
  map_one' := by
    rw [← ofAdd_zero]
    congr 1
    exact Subtype.ext (funext fun n => by simp)
  map_mul' x y := by
    rw [← ofAdd_add]
    congr 1
    exact Subtype.ext (funext fun n => by simp only [h2MuZMod, map_mul, toAdd_mul]; rfl)

theorem h2ZHatOneHom_apply (x : H2ZHatOne K Ω) (n : ℕ+) :
    ((Multiplicative.toAdd (h2ZHatOneHom p K Ω x) : ZHat) : ∀ n : ℕ+, ZMod n) n =
      h2MuZMod (p := p) n (H2ZHatOne.proj n x) := rfl

theorem h2ZHatOneHom_bijective : Function.Bijective (h2ZHatOneHom p K Ω) := by
  constructor
  · intro x y hxy
    refine Subtype.ext (funext fun n => (h2MuEquiv p K Ω n.pos).injective ?_)
    have := congrArg (fun z : Multiplicative ZHat =>
      ((Multiplicative.toAdd z : ZHat) : ∀ n : ℕ+, ZMod n) n) hxy
    exact congrArg Multiplicative.ofAdd this
  · intro z
    refine ⟨⟨fun n => (h2MuEquiv p K Ω n.pos).symm
      (Multiplicative.ofAdd (((Multiplicative.toAdd z : ZHat) : ∀ n : ℕ+, ZMod n) n)),
      fun n m h => ?_⟩, ?_⟩
    · apply (h2MuEquiv p K Ω n.pos).injective
      have e := h2MuZMod_h2MuPow (p := p) (K := K) (Ω := Ω) h ((h2MuEquiv p K Ω m.pos).symm
        (Multiplicative.ofAdd (((Multiplicative.toAdd z : ZHat) : ∀ n : ℕ+, ZMod n) m)))
      simp only [h2MuZMod, MulEquiv.apply_symm_apply, toAdd_ofAdd] at e
      rw [MulEquiv.apply_symm_apply, ← (Multiplicative.toAdd z).2 n m h, ← e, ofAdd_toAdd]
    · apply Multiplicative.toAdd.injective
      refine Subtype.ext (funext fun n => ?_)
      rw [h2ZHatOneHom_apply]
      simp [H2ZHatOne.proj, h2MuZMod]

variable (p K Ω) in
/-- **`H²(K, Ẑ(1)) ≃ Ẑ`**: the inverse limit of the cyclotomic rigidity isomorphisms
`H²(K, μ_n) ≃ ℤ/n`. -/
noncomputable def h2ZHatOneEquiv : H2ZHatOne K Ω ≃* Multiplicative ZHat :=
  MulEquiv.ofBijective _ (h2ZHatOneHom_bijective (p := p))

theorem h2ZHatOneEquiv_apply (x : H2ZHatOne K Ω) (n : ℕ+) :
    ((Multiplicative.toAdd (h2ZHatOneEquiv p K Ω x) : ZHat) : ∀ n : ℕ+, ZMod n) n =
      Multiplicative.toAdd (h2MuEquiv p K Ω n.pos (H2ZHatOne.proj n x)) := rfl

/-- Restriction to a finite `K' ⊆ Ω` is multiplication by `[K' : K]` on `Ẑ`. -/
theorem h2ZHatOneEquiv_res (K' : IntermediateField K Ω) [FiniteDimensional K K']
    (x : H2ZHatOne K Ω) :
    Multiplicative.toAdd (h2ZHatOneEquiv p K' Ω (resZHatOne K' x)) =
      Module.finrank K K' • Multiplicative.toAdd (h2ZHatOneEquiv p K Ω x) := by
  refine Subtype.ext (funext fun n => ?_)
  rw [h2ZHatOneEquiv_apply, proj_resZHatOne]
  exact h2MuEquiv_resMu (p := p) K' (n := (n : ℕ)) _

end PadicField
