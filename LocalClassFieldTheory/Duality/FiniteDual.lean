/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.GroupTheory.FiniteAbelian.Duality
import ContinuousKummerTheory.Kummer.Basic

/-!
# Duality of finite abelian groups killed by `n`

Let `A` be a finite commutative group killed by `n` and `Ω` a field with enough `n`-th roots of
unity. With `μ_n = KummerTheory.Mu n Ω` and `Z = Multiplicative (ZMod n)`:

* `Brauer.card_hom_mu`, `Brauer.card_hom_zmod` : `#Hom(A, μ_n) = #Hom(A, Z) = #A`;
* `Brauer.exists_hom_mu_ne_one` : homomorphisms to `μ_n` separate the points of `A` (for `Z`
  this is `Brauer.exists_hom_zmod_ne_one`, in `LocalClassFieldTheory.Brauer.Duality`);
* `Brauer.exists_extend_mu`, `Brauer.exists_extend_zmod` : homomorphisms from a subgroup extend;
* **`Brauer.surjective_of_transpose_injective`** : if `Φ : X → Hom(Y, Z)` is a homomorphism of
  finite groups whose transpose `y ↦ (x ↦ Φ x y)` is injective, then `Φ` is surjective;
* **`Brauer.exists_factor_zmod`** : dualising an exact sequence `A → B → C` of groups killed by
  `n` gives an exact sequence `Hom(C, Z) → Hom(B, Z) → Hom(A, Z)`.

These are the facts about `Hom(-, ℚ/ℤ)` on finite groups used in the proof of local duality
(`LocalClassFieldTheory.Duality.General`). They are deduced from Mathlib's
`CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`,
`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity` and `MonoidHom.restrict_surjective`.
-/

open KummerTheory

namespace Brauer

section Mu

variable {Ω : Type*} [Field Ω] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity Ω n]
variable {A : Type*} [CommGroup A] [Finite A]

/-- For `A` killed by `n`, homomorphisms `A → μ_n` are homomorphisms `A → Ωˣ`. -/
def homMuEquiv (hA : ∀ a : A, a ^ n = 1) : (A →* Mu n Ω) ≃ (A →* Ωˣ) where
  toFun φ := Mu.val.comp φ
  invFun ψ :=
    { toFun := fun a => Mu.mk (ψ a) (by rw [← map_pow, hA, map_one])
      map_one' := Mu.ext (by simp)
      map_mul' := fun a b => Mu.ext (by simp) }
  left_inv φ := MonoidHom.ext fun a => Mu.ext rfl
  right_inv ψ := MonoidHom.ext fun a => rfl

omit [Finite A] in
theorem hasEnoughRootsOfUnity_exponent (hA : ∀ a : A, a ^ n = 1) :
    HasEnoughRootsOfUnity Ω (Monoid.exponent A) :=
  HasEnoughRootsOfUnity.of_dvd Ω (Monoid.exponent_dvd_of_forall_pow_eq_one hA)

/-- `#Hom(A, μ_n) = #A` for `A` killed by `n`. -/
theorem card_hom_mu (hA : ∀ a : A, a ^ n = 1) : Nat.card (A →* Mu n Ω) = Nat.card A := by
  haveI := hasEnoughRootsOfUnity_exponent (Ω := Ω) hA
  rw [Nat.card_congr (homMuEquiv hA)]
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity A Ω

/-- Homomorphisms `A → μ_n` separate points. -/
theorem exists_hom_mu_ne_one (hA : ∀ a : A, a ^ n = 1) {a : A} (ha : a ≠ 1) :
    ∃ φ : A →* Mu n Ω, φ a ≠ 1 := by
  haveI := hasEnoughRootsOfUnity_exponent (Ω := Ω) hA
  obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity A Ω ha
  refine ⟨(homMuEquiv hA).symm ψ, fun h => hψ ?_⟩
  have := congrArg Mu.val h
  simpa [homMuEquiv] using this

/-- Homomorphisms from a subgroup to `μ_n` extend. -/
theorem exists_extend_mu (hA : ∀ a : A, a ^ n = 1) (H : Subgroup A) (ψ : H →* Mu n Ω) :
    ∃ φ : A →* Mu n Ω, ∀ h : H, φ h = ψ h := by
  haveI := hasEnoughRootsOfUnity_exponent (Ω := Ω) hA
  have hH : ∀ h : H, h ^ n = 1 := fun h => Subtype.ext (by simpa using hA h)
  obtain ⟨φ, hφ⟩ := MonoidHom.restrict_surjective (M := Ω) H (homMuEquiv hH ψ)
  refine ⟨(homMuEquiv hA).symm φ, fun h => Mu.ext ?_⟩
  have := DFunLike.congr_fun hφ h
  simpa [homMuEquiv] using this

end Mu

section ZMod

variable {n : ℕ} [NeZero n]

instance : IsCyclic (Multiplicative (ZMod n)) := inferInstance

theorem card_multiplicative_zmod : Nat.card (Multiplicative (ZMod n)) = n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

variable (Ω : Type*) [Field Ω] [HasEnoughRootsOfUnity Ω n]

/-- A (non-canonical) isomorphism `ℤ/n ≃ μ_n(Ω)`. -/
noncomputable def zmodMuEquiv : Multiplicative (ZMod n) ≃* Mu n Ω :=
  haveI : IsCyclic (Mu n Ω) := inferInstanceAs (IsCyclic (rootsOfUnity n Ω))
  mulEquivOfCyclicCardEq (by
    rw [card_multiplicative_zmod]
    exact (HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω n).symm)

variable {Ω}
variable {A : Type*} [CommGroup A] [Finite A]

/-- Composition with an isomorphism `Z ≃ μ_n`. -/
def homZModMuEquiv (e : Multiplicative (ZMod n) ≃* Mu n Ω) :
    (A →* Multiplicative (ZMod n)) ≃ (A →* Mu n Ω) where
  toFun φ := e.toMonoidHom.comp φ
  invFun ψ := e.symm.toMonoidHom.comp ψ
  left_inv φ := MonoidHom.ext fun a => by simp
  right_inv ψ := MonoidHom.ext fun a => by simp

end ZMod

section ZModFacts

variable {n : ℕ} [NeZero n]
variable {A : Type*} [CommGroup A] [Finite A]

/-- The field `ℂ` has enough roots of unity; we use it as an auxiliary field. -/
theorem card_hom_zmod (hA : ∀ a : A, a ^ n = 1) :
    Nat.card (A →* Multiplicative (ZMod n)) = Nat.card A := by
  rw [Nat.card_congr (homZModMuEquiv (A := A) (zmodMuEquiv (n := n) ℂ)), card_hom_mu hA]

theorem exists_extend_zmod (hA : ∀ a : A, a ^ n = 1) (H : Subgroup A)
    (ψ : H →* Multiplicative (ZMod n)) :
    ∃ φ : A →* Multiplicative (ZMod n), ∀ h : H, φ h = ψ h := by
  obtain ⟨φ, hφ⟩ := exists_extend_mu (Ω := ℂ) hA H (homZModMuEquiv (zmodMuEquiv ℂ) ψ)
  refine ⟨(homZModMuEquiv (zmodMuEquiv (n := n) ℂ)).symm φ, fun h => ?_⟩
  have := congrArg (zmodMuEquiv (n := n) ℂ).symm (hφ h)
  simpa [homZModMuEquiv] using this

theorem pow_eq_one_zmod (z : Multiplicative (ZMod n)) : z ^ n = 1 := by
  have := pow_card_eq_one' (x := z)
  rwa [card_multiplicative_zmod] at this

theorem hom_pow_eq_one {Y : Type*} [Group Y] (φ : Y →* Multiplicative (ZMod n)) : φ ^ n = 1 :=
  MonoidHom.ext fun y => by rw [MonoidHom.pow_apply, pow_eq_one_zmod]; rfl

/-- **Transposition.** If `Φ : X → Hom(Y, ℤ/n)` is a homomorphism of finite groups whose
transpose is injective (`y ↦ (x ↦ Φ x y)` has trivial kernel), and `Y` is killed by `n`, then `Φ`
is surjective. -/
theorem surjective_of_transpose_injective {X Y : Type*} [CommGroup X] [CommGroup Y] [Finite X]
    [Finite Y] (hY : ∀ y : Y, y ^ n = 1) (Φ : X →* (Y →* Multiplicative (ZMod n)))
    (h : ∀ y : Y, (∀ x : X, Φ x y = 1) → y = 1) : Function.Surjective Φ := by
  set W := X ⧸ Φ.ker
  have hW : ∀ w : W, w ^ n = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow,
      hom_pow_eq_one]
  -- the transpose, as a map `Y → Hom(W, Z)`
  let ψ : Y → (W →* Multiplicative (ZMod n)) := fun y =>
    QuotientGroup.lift Φ.ker (Φ.flip y) (fun x hx => by
      rw [MonoidHom.mem_ker, MonoidHom.flip_apply, MonoidHom.mem_ker.1 hx]
      rfl)
  have hψ : Function.Injective ψ := by
    intro y y' hyy'
    have : ∀ x : X, Φ x (y / y') = 1 := fun x => by
      have := DFunLike.congr_fun hyy' (QuotientGroup.mk x)
      have e : ∀ z : Y, ψ z (QuotientGroup.mk x) = Φ x z := fun z => rfl
      rw [e, e] at this
      rw [map_div, this, div_self']
    exact div_eq_one.1 (h _ this)
  have h1 : Nat.card Y ≤ Nat.card W := by
    calc Nat.card Y ≤ Nat.card (W →* Multiplicative (ZMod n)) := by
          haveI : Finite (W →* Multiplicative (ZMod n)) :=
            Nat.finite_of_card_ne_zero (by rw [card_hom_zmod hW]; exact Nat.card_pos.ne')
          exact Nat.card_le_card_of_injective ψ hψ
      _ = Nat.card W := card_hom_zmod hW
  have h2 : Nat.card W = Nat.card Φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv
  haveI : Finite (Y →* Multiplicative (ZMod n)) :=
    Nat.finite_of_card_ne_zero (by rw [card_hom_zmod hY]; exact Nat.card_pos.ne')
  have h3 : Φ.range = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    rw [card_hom_zmod hY, ← h2]
    exact h1
  exact MonoidHom.range_eq_top.1 h3

/-- **Dualising an exact sequence.** If `A → B → C` is exact at `B` (`ker g = range f`), `C` is
finite and killed by `n`, and `ξ : B → ℤ/n` vanishes on the image of `A`, then `ξ` factors through
`g`. -/
theorem exists_factor_zmod {B C : Type*} [CommGroup B] [CommGroup C] [Finite C]
    (hC : ∀ c : C, c ^ n = 1) {A' : Type*} [Group A'] (f : A' →* B) (g : B →* C)
    (hfg : g.ker = f.range) (ξ : B →* Multiplicative (ZMod n)) (hξ : ∀ a, ξ (f a) = 1) :
    ∃ η : C →* Multiplicative (ZMod n), η.comp g = ξ := by
  have hker : g.ker ≤ ξ.ker := by
    rw [hfg]
    rintro _ ⟨a, rfl⟩
    exact hξ a
  -- `ξ` on `range g ≃ B / ker g`
  let η₀ : g.range →* Multiplicative (ZMod n) :=
    (QuotientGroup.lift g.ker ξ hker).comp
      (QuotientGroup.quotientKerEquivRange g).symm.toMonoidHom
  obtain ⟨η, hη⟩ := exists_extend_zmod hC g.range η₀
  refine ⟨η, MonoidHom.ext fun b => ?_⟩
  have := hη ⟨g b, b, rfl⟩
  rw [MonoidHom.comp_apply, this]
  simp only [η₀, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
  have e : (QuotientGroup.quotientKerEquivRange g).symm ⟨g b, b, rfl⟩ = (b : B ⧸ g.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [e, QuotientGroup.lift_mk]

end ZModFacts

end Brauer
