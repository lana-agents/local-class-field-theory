/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Concrete Tate groups and Herbrand quotients for cyclic actions

Let `M` be an additive commutative group and `σ : AddMonoid.End M` an endomorphism with
`σ ^ n = 1` (think of a generator of a cyclic group of order `n` acting on `M`). We put
`D σ = σ - 1` and `N σ n = ∑ i ∈ range n, σ ^ i`, and define the (concrete) Tate groups

* `Herbrand.H0 σ n = ker D ⧸ im N` (`Ĥ⁰`),
* `Herbrand.Hm1 σ n = ker N ⧸ im D` (`Ĥ⁻¹`),

and the Herbrand quotient `Herbrand.herbrand σ n = |Ĥ⁰| / |Ĥ⁻¹| : ℚ` (only meaningful when both
groups are finite; theorems carry finiteness hypotheses).

Both groups are instances of a generic construction `Herbrand.TateQuot P Q = ker P ⧸ im Q` for two
endomorphisms `P`, `Q` (the image is intersected with `ker P`, so that no hypothesis is needed to
form the quotient). When `P ∘ Q = 0 = Q ∘ P` this is the homology of the 2-periodic complex
`⋯ → M →Q M →P M →Q ⋯`, and most results are proved in that generality.

## Main definitions

* `Herbrand.TateQuot P Q`, with functoriality `Herbrand.TateQuot.map` and
  `Herbrand.TateQuot.mapEquiv`.
* `Herbrand.D`, `Herbrand.N`, `Herbrand.H0`, `Herbrand.Hm1`, `Herbrand.herbrand`.
* `Herbrand.ofMonoidEnd`, `Herbrand.unitsEnd`: the endomorphism of `Additive G` induced by an
  endomorphism of a commutative group `G`, resp. of `Additive Rˣ` induced by a ring
  endomorphism of `R`. For instance, for a field automorphism `τ` of `L` of order `n`, use
  `Herbrand.H0 (Herbrand.unitsEnd (τ : L →+* L)) n` (`Ĥ⁰` of `Lˣ`), together with
  `Herbrand.unitsEnd_pow_eq_one`.

## Main results

* `Herbrand.mem_ker_D_iff`, `Herbrand.D_N_apply`, `Herbrand.N_D_apply`: basic identities.
* `Herbrand.subsingleton_H0_iff`, `Herbrand.subsingleton_Hm1_iff`: triviality criteria.
* `Herbrand.card_H0_eq_card_Hm1_of_finite`, `Herbrand.herbrand_eq_one_of_finite`: the Herbrand
  quotient of a finite module is `1`.
* `Herbrand.H0.mapEquiv`, `Herbrand.Hm1.mapEquiv`, `Herbrand.herbrand_congr`: transport along
  equivariant isomorphisms.
-/

open Finset

namespace Herbrand

section Generic

variable {M M' : Type*} [AddCommGroup M] [AddCommGroup M']

/-- The generic "Tate quotient" `ker P ⧸ im Q` (more precisely `ker P ⧸ (im Q ∩ ker P)`) attached
to two endomorphisms `P`, `Q` of `M`. -/
abbrev TateQuot (P Q : M →+ M) : Type _ :=
  AddMonoidHom.ker P ⧸ (AddMonoidHom.range Q).addSubgroupOf (AddMonoidHom.ker P)

namespace TateQuot

variable {P Q : M →+ M} {P' Q' : M' →+ M'}

theorem mk_eq_zero_iff (x : AddMonoidHom.ker P) :
    (x : TateQuot P Q) = 0 ↔ ∃ y, Q y = x := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]

theorem mk_eq_mk_iff (x y : AddMonoidHom.ker P) :
    (x : TateQuot P Q) = y ↔ ∃ z, Q z = (x : M) - y := by
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, mk_eq_zero_iff]
  rfl

theorem subsingleton_iff :
    Subsingleton (TateQuot P Q) ↔ ∀ x, P x = 0 → ∃ y, Q y = x := by
  constructor
  · intro h x hx
    exact (mk_eq_zero_iff (Q := Q) ⟨x, hx⟩).1 (Subsingleton.elim _ _)
  · intro h
    refine ⟨fun a b => ?_⟩
    induction a using QuotientAddGroup.induction_on with | H a => ?_
    induction b using QuotientAddGroup.induction_on with | H b => ?_
    rw [mk_eq_mk_iff]
    exact h _ (by rw [map_sub, a.2, b.2, sub_zero])

/-- `|ker P ⧸ im Q| * |im Q| = |ker P|` when `im Q ⊆ ker P` (as an identity of `Nat.card`s, so
with the convention that infinite cardinals are `0`). -/
theorem card_mul_card_range (hPQ : ∀ y, P (Q y) = 0) :
    Nat.card (TateQuot P Q) * Nat.card (AddMonoidHom.range Q) =
      Nat.card (AddMonoidHom.ker P) := by
  have hle : AddMonoidHom.range Q ≤ AddMonoidHom.ker P := by
    rintro _ ⟨y, rfl⟩
    exact hPQ y
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    ((AddMonoidHom.range Q).addSubgroupOf (AddMonoidHom.ker P)),
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hle).toEquiv]

theorem _root_.Herbrand.card_ker_mul_card_range (P : M →+ M) :
    Nat.card (AddMonoidHom.ker P) * Nat.card (AddMonoidHom.range P) = Nat.card M := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (AddMonoidHom.ker P), mul_comm,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange P).toEquiv]

/-- For a finite group, the two Tate quotients of a pair `P`, `Q` with `P ∘ Q = 0 = Q ∘ P` have
the same order. -/
theorem card_eq_of_finite [Finite M] (hPQ : ∀ y, P (Q y) = 0) (hQP : ∀ y, Q (P y) = 0) :
    Nat.card (TateQuot P Q) = Nat.card (TateQuot Q P) := by
  have h1 := card_mul_card_range hPQ
  have h2 := card_mul_card_range hQP
  have h3 := card_ker_mul_card_range P
  have h4 := card_ker_mul_card_range Q
  have hP : 0 < Nat.card (AddMonoidHom.range P) := Nat.card_pos
  have hQ : 0 < Nat.card (AddMonoidHom.range Q) := Nat.card_pos
  have key : Nat.card (TateQuot P Q) * (Nat.card (AddMonoidHom.range Q) *
      Nat.card (AddMonoidHom.range P)) = Nat.card (TateQuot Q P) *
      (Nat.card (AddMonoidHom.range Q) * Nat.card (AddMonoidHom.range P)) := by
    calc _ = Nat.card M := by rw [← h3, ← h1]; ring
      _ = _ := by rw [← h4, ← h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hQ hP) key

/-- Functoriality of `TateQuot` along a homomorphism intertwining the endomorphisms. -/
noncomputable def map (f : M →+ M') (hP : ∀ x, f (P x) = P' (f x))
    (hQ : ∀ x, f (Q x) = Q' (f x)) : TateQuot P Q →+ TateQuot P' Q' :=
  QuotientAddGroup.map _ _
    ((f.comp (AddMonoidHom.ker P).subtype).codRestrict (AddMonoidHom.ker P') fun x => by
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, AddSubgroup.coe_subtype,
        Function.comp_apply, ← hP]
      rw [x.2.out, map_zero])
    (by
      rintro x hx
      rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range] at hx
      obtain ⟨y, hy⟩ := hx
      rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
      exact ⟨f y, by simp [← hQ, hy]⟩)

@[simp]
theorem map_mk (f : M →+ M') (hP : ∀ x, f (P x) = P' (f x)) (hQ : ∀ x, f (Q x) = Q' (f x))
    (x : AddMonoidHom.ker P) :
    map f hP hQ (x : TateQuot P Q) =
      ((⟨f x, by rw [AddMonoidHom.mem_ker, ← hP, x.2.out, map_zero]⟩ :
        AddMonoidHom.ker P') : TateQuot P' Q') :=
  rfl

/-- Transport of `TateQuot` along an isomorphism intertwining the endomorphisms. -/
noncomputable def mapEquiv (e : M ≃+ M') (hP : ∀ x, e (P x) = P' (e x))
    (hQ : ∀ x, e (Q x) = Q' (e x)) : TateQuot P Q ≃+ TateQuot P' Q' :=
  have hP' : ∀ x, e.symm (P' x) = P (e.symm x) := fun x => by
    rw [e.symm_apply_eq, hP, e.apply_symm_apply]
  have hQ' : ∀ x, e.symm (Q' x) = Q (e.symm x) := fun x => by
    rw [e.symm_apply_eq, hQ, e.apply_symm_apply]
  { map (e : M →+ M') hP hQ with
    invFun := map (e.symm : M' →+ M) hP' hQ'
    left_inv := fun x => by
      induction x using QuotientAddGroup.induction_on with | H x => ?_
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_mk]
      congr 2
      exact e.symm_apply_apply _
    right_inv := fun x => by
      induction x using QuotientAddGroup.induction_on with | H x => ?_
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, map_mk]
      congr 2
      exact e.apply_symm_apply _ }

end TateQuot

end Generic

section Cyclic

variable {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
variable (σ : AddMonoid.End M) (n : ℕ)

/-- `D = σ - 1`. -/
def D : M →+ M := (σ - 1 : AddMonoid.End M)

/-- The norm `N = ∑_{i < n} σ ^ i`. -/
def N : M →+ M := ∑ i ∈ range n, ((σ ^ i : AddMonoid.End M) : M →+ M)

/-- The Tate group `Ĥ⁰ = ker (σ - 1) ⧸ im N`. -/
abbrev H0 : Type _ := TateQuot (D σ) (N σ n)

/-- The Tate group `Ĥ⁻¹ = ker N ⧸ im (σ - 1)`. -/
abbrev Hm1 : Type _ := TateQuot (N σ n) (D σ)

/-- The Herbrand quotient `|Ĥ⁰| / |Ĥ⁻¹|` (meaningful only when both groups are finite). -/
noncomputable def herbrand : ℚ := Nat.card (H0 σ n) / Nat.card (Hm1 σ n)

variable {σ n}

@[simp]
theorem D_apply (x : M) : D σ x = σ x - x := rfl

theorem N_apply (x : M) : N σ n x = ∑ i ∈ range n, (σ ^ i) x := by
  simp only [N, AddMonoidHom.finsetSum_apply]
  rfl

theorem mem_ker_D_iff {x : M} : x ∈ AddMonoidHom.ker (D σ) ↔ σ x = x := by
  rw [AddMonoidHom.mem_ker, D_apply, sub_eq_zero]

theorem mem_ker_N_iff {x : M} : x ∈ AddMonoidHom.ker (N σ n) ↔ N σ n x = 0 :=
  AddMonoidHom.mem_ker

theorem D_N_apply_eq (x : M) : D σ (N σ n x) = (σ ^ n) x - x := by
  change ((σ - 1) * ∑ i ∈ range n, σ ^ i : AddMonoid.End M) x = _
  rw [mul_geom_sum]
  rfl

theorem N_D_apply_eq (x : M) : N σ n (D σ x) = (σ ^ n) x - x := by
  change ((∑ i ∈ range n, σ ^ i) * (σ - 1) : AddMonoid.End M) x = _
  rw [geom_sum_mul]
  rfl

theorem D_N_apply (hσ : σ ^ n = 1) (x : M) : D σ (N σ n x) = 0 := by
  rw [D_N_apply_eq, hσ, sub_eq_zero]
  rfl

theorem N_D_apply (hσ : σ ^ n = 1) (x : M) : N σ n (D σ x) = 0 := by
  rw [N_D_apply_eq, hσ, sub_eq_zero]
  rfl

theorem N_apply_apply (x : M) : N σ n (σ x) = σ (N σ n x) := by
  change ((∑ i ∈ range n, σ ^ i) * σ : AddMonoid.End M) x =
    (σ * ∑ i ∈ range n, σ ^ i : AddMonoid.End M) x
  rw [Finset.sum_mul, Finset.mul_sum]
  simp only [← pow_succ, ← pow_succ']

theorem subsingleton_H0_iff :
    Subsingleton (H0 σ n) ↔ ∀ x, σ x = x → ∃ y, N σ n y = x := by
  rw [TateQuot.subsingleton_iff]
  simp only [D_apply, sub_eq_zero]

theorem subsingleton_Hm1_iff :
    Subsingleton (Hm1 σ n) ↔ ∀ x, N σ n x = 0 → ∃ y, σ y - y = x := by
  rw [TateQuot.subsingleton_iff]
  simp only [D_apply]

theorem H0.mk_eq_zero_iff (x : AddMonoidHom.ker (D σ)) :
    (x : H0 σ n) = 0 ↔ ∃ y, N σ n y = x :=
  TateQuot.mk_eq_zero_iff x

theorem Hm1.mk_eq_zero_iff (x : AddMonoidHom.ker (N σ n)) :
    (x : Hm1 σ n) = 0 ↔ ∃ y, σ y - y = x :=
  TateQuot.mk_eq_zero_iff x

/-- For a finite module, `|Ĥ⁰| = |Ĥ⁻¹|`. -/
theorem card_H0_eq_card_Hm1_of_finite [Finite M] (hσ : σ ^ n = 1) :
    Nat.card (H0 σ n) = Nat.card (Hm1 σ n) :=
  TateQuot.card_eq_of_finite (D_N_apply hσ) (N_D_apply hσ)

/-- The Herbrand quotient of a finite module is `1`. -/
theorem herbrand_eq_one_of_finite [Finite M] (hσ : σ ^ n = 1) : herbrand σ n = 1 := by
  rw [herbrand, card_H0_eq_card_Hm1_of_finite hσ]
  exact div_self (Nat.cast_ne_zero.2 Nat.card_pos.ne')

/-! ### Equivariant maps -/

section Equivariant

variable {σ' : AddMonoid.End M'}

theorem map_pow_apply (f : M →+ M') (hf : ∀ x, f (σ x) = σ' (f x)) (k : ℕ) (x : M) :
    f ((σ ^ k) x) = (σ' ^ k) (f x) := by
  simp only [AddMonoid.End.coe_pow]
  exact (Function.Semiconj.iterate_right (f := f) hf k x)

theorem map_D_apply (f : M →+ M') (hf : ∀ x, f (σ x) = σ' (f x)) (x : M) :
    f (D σ x) = D σ' (f x) := by
  rw [D_apply, D_apply, map_sub, hf]

theorem map_N_apply (f : M →+ M') (hf : ∀ x, f (σ x) = σ' (f x)) (x : M) :
    f (N σ n x) = N σ' n (f x) := by
  simp only [N_apply, map_sum, map_pow_apply f hf]

theorem pow_eq_one_of_injective (f : M →+ M') (hinj : Function.Injective f)
    (hf : ∀ x, f (σ x) = σ' (f x)) (hσ' : σ' ^ n = 1) : σ ^ n = 1 := by
  ext x
  apply hinj
  rw [map_pow_apply f hf, hσ']
  rfl

theorem pow_eq_one_of_surjective (f : M →+ M') (hsurj : Function.Surjective f)
    (hf : ∀ x, f (σ x) = σ' (f x)) (hσ : σ ^ n = 1) : σ' ^ n = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := hsurj y
  rw [← map_pow_apply f hf, hσ]
  rfl

/-- The map `Ĥ⁰(M) → Ĥ⁰(M')` induced by an equivariant homomorphism. -/
noncomputable def H0.map (f : M →+ M') (hf : ∀ x, f (σ x) = σ' (f x)) :
    H0 σ n →+ H0 σ' n :=
  TateQuot.map f (map_D_apply f hf) (map_N_apply f hf)

/-- The map `Ĥ⁻¹(M) → Ĥ⁻¹(M')` induced by an equivariant homomorphism. -/
noncomputable def Hm1.map (f : M →+ M') (hf : ∀ x, f (σ x) = σ' (f x)) :
    Hm1 σ n →+ Hm1 σ' n :=
  TateQuot.map f (map_N_apply f hf) (map_D_apply f hf)

/-- Transport of `Ĥ⁰` along an equivariant isomorphism. -/
noncomputable def H0.mapEquiv (e : M ≃+ M') (he : ∀ x, e (σ x) = σ' (e x)) :
    H0 σ n ≃+ H0 σ' n :=
  TateQuot.mapEquiv e (map_D_apply (e : M →+ M') he) (map_N_apply (e : M →+ M') he)

/-- Transport of `Ĥ⁻¹` along an equivariant isomorphism. -/
noncomputable def Hm1.mapEquiv (e : M ≃+ M') (he : ∀ x, e (σ x) = σ' (e x)) :
    Hm1 σ n ≃+ Hm1 σ' n :=
  TateQuot.mapEquiv e (map_N_apply (e : M →+ M') he) (map_D_apply (e : M →+ M') he)

theorem card_H0_congr (e : M ≃+ M') (he : ∀ x, e (σ x) = σ' (e x)) :
    Nat.card (H0 σ n) = Nat.card (H0 σ' n) :=
  Nat.card_congr (H0.mapEquiv e he).toEquiv

theorem card_Hm1_congr (e : M ≃+ M') (he : ∀ x, e (σ x) = σ' (e x)) :
    Nat.card (Hm1 σ n) = Nat.card (Hm1 σ' n) :=
  Nat.card_congr (Hm1.mapEquiv e he).toEquiv

theorem subsingleton_H0_congr (e : M ≃+ M') (he : ∀ x, e (σ x) = σ' (e x)) :
    Subsingleton (H0 σ n) ↔ Subsingleton (H0 σ' n) :=
  (H0.mapEquiv e he).toEquiv.subsingleton_congr

theorem subsingleton_Hm1_congr (e : M ≃+ M') (he : ∀ x, e (σ x) = σ' (e x)) :
    Subsingleton (Hm1 σ n) ↔ Subsingleton (Hm1 σ' n) :=
  (Hm1.mapEquiv e he).toEquiv.subsingleton_congr

theorem herbrand_congr (e : M ≃+ M') (he : ∀ x, e (σ x) = σ' (e x)) :
    herbrand σ n = herbrand σ' n := by
  rw [herbrand, herbrand, card_H0_congr e he, card_Hm1_congr e he]

end Equivariant

/-! ### Subgroups and quotients -/

section Restrict

variable (σ) (A : AddSubgroup M) (hA : ∀ x ∈ A, σ x ∈ A)

/-- The restriction of `σ` to a `σ`-stable subgroup `A`. -/
def restrict : AddMonoid.End A :=
  ((σ : M →+ M).comp A.subtype).codRestrict A fun x => hA x x.2

/-- The endomorphism of `M ⧸ A` induced by `σ`, for a `σ`-stable subgroup `A`. -/
def quotientEnd : AddMonoid.End (M ⧸ A) :=
  QuotientAddGroup.map A A (σ : M →+ M) fun x hx => hA x hx

variable {σ A}

@[simp]
theorem coe_restrict_apply (x : A) : (restrict σ A hA x : M) = σ x := rfl

@[simp]
theorem quotientEnd_mk (x : M) : quotientEnd σ A hA (x : M ⧸ A) = (σ x : M ⧸ A) := rfl

theorem restrict_pow_eq_one (hσ : σ ^ n = 1) : restrict σ A hA ^ n = 1 :=
  pow_eq_one_of_injective A.subtype Subtype.val_injective (fun _ => rfl) hσ

theorem quotientEnd_pow_eq_one (hσ : σ ^ n = 1) : quotientEnd σ A hA ^ n = 1 :=
  pow_eq_one_of_surjective (QuotientAddGroup.mk' A) (QuotientAddGroup.mk'_surjective A)
    (fun _ => rfl) hσ

end Restrict

end Cyclic

/-! ### Multiplicative groups -/

section Multiplicative

variable {G : Type*} [CommGroup G]

/-- The endomorphism of `Additive G` induced by an endomorphism of the commutative group `G`. -/
def ofMonoidEnd (f : Monoid.End G) : AddMonoid.End (Additive G) := MonoidHom.toAdditive f

@[simp]
theorem ofMonoidEnd_apply (f : Monoid.End G) (x : Additive G) :
    ofMonoidEnd f x = Additive.ofMul (f x.toMul) := rfl

theorem ofMonoidEnd_pow (f : Monoid.End G) (k : ℕ) : ofMonoidEnd f ^ k = ofMonoidEnd (f ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, ih]; rfl

theorem ofMonoidEnd_pow_eq_one {f : Monoid.End G} {n : ℕ} (h : f ^ n = 1) :
    ofMonoidEnd f ^ n = 1 := by
  rw [ofMonoidEnd_pow, h]
  rfl

variable {R : Type*} [CommMonoid R]

/-- The endomorphism of `Additive Rˣ` induced by a monoid endomorphism of `R` (e.g. a ring
endomorphism, via `RingHom.toMonoidHom`). -/
def unitsEnd (f : R →* R) : AddMonoid.End (Additive Rˣ) := ofMonoidEnd (Units.map f)

@[simp]
theorem coe_toMul_unitsEnd_apply (f : R →* R) (x : Additive Rˣ) :
    ((unitsEnd f x).toMul : R) = f (x.toMul : R) := rfl

theorem unitsEnd_pow_eq_one {f : R →* R} {n : ℕ} (h : ∀ x, f^[n] x = x) :
    unitsEnd f ^ n = 1 := by
  apply ofMonoidEnd_pow_eq_one
  ext x
  rw [Monoid.End.coe_pow]
  have : (fun u : Rˣ => (u : R)) ∘ (Units.map f)^[n] = f^[n] ∘ fun u : Rˣ => (u : R) :=
    Function.Semiconj.iterate_right (f := fun u : Rˣ => (u : R)) (fun _ => rfl) n |>.comp_eq
  exact (congrFun this x).trans (h x)

end Multiplicative

end Herbrand
