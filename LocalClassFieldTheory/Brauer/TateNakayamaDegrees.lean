/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.TateNakayama

/-!
# Tate–Nakayama for local fields in degrees `0` and `-2`

For a finite Galois extension `L ⊆ Ω` of `K` with group `G = Gal(L/K)` of order `d = [L : K]`,
cup product with the fundamental class `u_{L/K}` is an isomorphism
`Ĥ^i(G, ℤ) ≅ Ĥ^{i+2}(G, Lˣ)` (Tate–Nakayama). We record the two degrees available with the
cohomology formalised here:

* **degree `0`** (any finite Galois `L/K`): `Ĥ⁰(G, ℤ) = ℤ/d → H²(G, Lˣ) = Br(L/K)`,
  `k ↦ k ∪ u_{L/K} = u_{L/K}^k`, is an isomorphism (`PadicField.fundClassPowEquiv`), and
  `inv(infl(u^k)) = k/d` (`PadicField.invEquiv_infl_fundClassPowEquiv`);
* **degree `-2`** (finite abelian `L/K`): `G = Ĥ⁻²(G, ℤ) → Ĥ⁰(G, Lˣ) = Kˣ/N_{L/K}Lˣ`,
  `g ↦ [∏_τ u(τ, g)]` (the cocycle formula for `g ∪ u_{L/K}`), is a bijection
  (`PadicField.bijective_relNak_fundClass`), the inverse of the reciprocity map.

Degree `-1` is Hilbert 90 (`Ĥ⁻¹(G, ℤ) = 0`, `H¹(G, Lˣ) = 1`, Mathlib's
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`). Not formalised: the
identification `Ĥ⁻²(G, ℤ) ≅ G^ab` and degree `-2` for non-abelian `L/K` (which needs
`N_{L/K}Lˣ = N_{L^{ab}/K}(L^{ab})ˣ`), and degrees `≥ 1` (no `H³`).
-/

open ContH2 Brauer

set_option linter.unusedSectionVars false

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

section Degree0

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]

instance : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩

/-- `k ↦ u_{L/K}^k`, the cup product `Ĥ⁰(G, ℤ) = ℤ/[L:K] → H²(G, Lˣ)` with the fundamental
class. -/
noncomputable def fundClassPowHom :
    Multiplicative (ZMod (Module.finrank K L)) →* RelBr K L where
  toFun k := fundClass (p := p) (Ω := Ω) L ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    have h := pow_mod_orderOf (fundClass (p := p) (Ω := Ω) L)
      ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val)
    rw [orderOf_fundClass] at h
    rw [toAdd_mul, ZMod.val_add, h, pow_add]

theorem fundClassPowHom_apply (k : Multiplicative (ZMod (Module.finrank K L))) :
    fundClassPowHom (p := p) (Ω := Ω) L k =
      fundClass (p := p) (Ω := Ω) L ^ (Multiplicative.toAdd k).val := rfl

theorem fundClassPowHom_bijective : Function.Bijective (fundClassPowHom (p := p) (Ω := Ω) L) := by
  have hinj : Function.Injective (fundClassPowHom (p := p) (Ω := Ω) L) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    rw [fundClassPowHom_apply, ← pow_zero (fundClass (p := p) (Ω := Ω) L), pow_eq_pow_iff_modEq,
      orderOf_fundClass, Nat.ModEq, Nat.zero_mod, Nat.mod_eq_of_lt (ZMod.val_lt _)] at hk
    rw [← ofAdd_toAdd k, (ZMod.val_eq_zero _).1 hk, ofAdd_zero]
  haveI : Finite (RelBr K L) :=
    Nat.finite_of_card_ne_zero (by rw [card_relBr_eq p (Ω := Ω) L]; exact Module.finrank_pos.ne')
  refine hinj.bijective_of_nat_card_le ?_
  rw [card_relBr_eq p (Ω := Ω) L, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- **Tate–Nakayama in degree `0`**: cup product with `u_{L/K}` is an isomorphism
`ℤ/[L : K] = Ĥ⁰(Gal(L/K), ℤ) ≃ H²(Gal(L/K), Lˣ) = Br(L/K)`, `k ↦ u_{L/K}^k`. -/
noncomputable def fundClassPowEquiv :
    Multiplicative (ZMod (Module.finrank K L)) ≃* RelBr K L :=
  MulEquiv.ofBijective _ (fundClassPowHom_bijective (p := p) (Ω := Ω) L)

theorem fundClassPowEquiv_apply (k : Multiplicative (ZMod (Module.finrank K L))) :
    fundClassPowEquiv (p := p) (Ω := Ω) L k =
      fundClass (p := p) (Ω := Ω) L ^ (Multiplicative.toAdd k).val := rfl

/-- The invariant of `u_{L/K}^k` is `k/[L : K]`. -/
theorem invEquiv_infl_fundClassPowEquiv (k : Multiplicative (ZMod (Module.finrank K L))) :
    invEquiv p K Ω (infl L (fundClassPowEquiv (p := p) (Ω := Ω) L k)) =
      Multiplicative.ofAdd (zmodToQZ (Module.finrank K L) (Multiplicative.toAdd k)) := by
  rw [fundClassPowEquiv_apply, map_pow, map_pow, invEquiv_infl_fundClass, ← ofAdd_nsmul]
  congr 1
  conv_rhs => rw [← ZMod.natCast_zmod_val (Multiplicative.toAdd k)]
  have hc : (((Multiplicative.toAdd k).val : ℕ) : ZMod (Module.finrank K L)) =
      ((((Multiplicative.toAdd k).val : ℕ) : ℤ) : ZMod (Module.finrank K L)) :=
    (Int.cast_natCast _).symm
  rw [hc, zmodToQZ_intCast, ← QuotientAddGroup.mk_nsmul]
  congr 1
  push_cast
  ring

end Degree0

section DegreeMinus2

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]

/-- **Tate–Nakayama in degree `-2`** for finite abelian `L/K`: `g ↦ [∏_τ u_{L/K}(τ, g)]`, the cup
product `Gal(L/K) = Ĥ⁻²(Gal(L/K), ℤ) → Ĥ⁰(Gal(L/K), Lˣ) = Kˣ/N_{L/K}Lˣ` with the fundamental
class, is a bijection (the inverse of the reciprocity isomorphism). -/
theorem bijective_relNak_fundClass :
    Function.Bijective fun g : L ≃ₐ[K] L => relNak g (fundClass (p := p) (Ω := Ω) L) := by
  have h : (fun g : L ≃ₐ[K] L => relNak g (fundClass (p := p) (Ω := Ω) L)) =
      (abRecEquiv p L).symm := by
    funext g
    exact relNak_fundClass L g
  rw [h]
  exact (abRecEquiv p L).symm.bijective

end DegreeMinus2

end PadicField
