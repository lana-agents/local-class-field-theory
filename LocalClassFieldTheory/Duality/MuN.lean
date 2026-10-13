/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.Statements
import LocalClassFieldTheory.PadicField.PowIndexPadic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Local duality and the Euler characteristic for `μ_n` and `ℤ/n`

Let `K` be a finite extension of `ℚ_p`, `Ω` an algebraic closure, `G_K = Gal(Ω/K)` and `n ≥ 1`.
We consider `ℤ/n` with trivial action (`Brauer.TrivZMod n`), `μ_n = Mu n Ω` and the pairing
`(k, ζ) ↦ ζ^k` (`Brauer.powPairing`), and its swap `(ζ, k) ↦ ζ^k`.

## Local duality (`Brauer.PerfectDeg0/1/2`, cup products into `H²(K, μ_n) ≃ ℤ/n`)

* `PadicField.perfectDeg0_trivZMod`: `H⁰(K, ℤ/n) × H²(K, μ_n) → ℤ/n` is perfect;
* `PadicField.perfectDeg1_trivZMod`: `H¹(K, ℤ/n) × H¹(K, μ_n) → ℤ/n` is perfect;
* `PadicField.perfectDeg1_mu`: `H¹(K, μ_n) × H¹(K, ℤ/n) → ℤ/n` is perfect;
* `PadicField.perfectDeg2_mu`: `H²(K, μ_n) × H⁰(K, ℤ/n) → ℤ/n` is perfect.

The degree-one statements combine the non-degeneracy of the Artin pairing
(`PadicField.eq_one_of_forall_pairingH1_eq_zero`, `..._eq_zero'`, via the existence theorem) with
the graded commutativity `x ∪ y = (y ∪ x)⁻¹` (`Brauer.cup11_swap`) and a counting argument:
`#Hom(A, ℤ/n) ≤ #A` for finite `A` (`Brauer.card_hom_zmod_le`, from Pontryagin duality for
finite abelian groups in Mathlib). The identification `H¹(K, ℤ/n) ≃ Hom_cont(G_K, ℤ/n)` is
`Brauer.h1TrivEquiv`.

## The Euler characteristic of `μ_n`

* `PadicField.card_h0_mu`: `#H⁰(K, μ_n) = #μ_n(K)`;
* `PadicField.card_h1_mu`: `#H¹(K, μ_n) = [Kˣ : (Kˣ)ⁿ] = n · #μ_n(K) · p^{v_p(n) [K:ℚ_p]}`
  (Kummer theory and `PadicField.index_range_pow`);
* `PadicField.card_h1_trivZMod`: `#H¹(K, ℤ/n) = [Kˣ : (Kˣ)ⁿ]` as well;
* **`PadicField.eulerCharacteristicFor_mu`**: `#H⁰ · #H² / #H¹ = |n|_K` for `M = μ_n`
  (`#μ_n(Ω) = n`), i.e. `PadicField.EulerCharacteristicFor p K Ω (Mu n Ω)`.
-/

open ContH2 groupCohomology KummerTheory

set_option linter.unusedSectionVars false

namespace Brauer

/-! ### `ℤ/n` with trivial action -/

/-- `ℤ/n` (multiplicatively) with the trivial action of every monoid. -/
def TrivZMod (n : ℕ) : Type := Multiplicative (ZMod n)

namespace TrivZMod

variable {n : ℕ}

instance : CommGroup (TrivZMod n) := inferInstanceAs (CommGroup (Multiplicative (ZMod n)))

instance : TopologicalSpace (TrivZMod n) := ⊥

instance : DiscreteTopology (TrivZMod n) := ⟨rfl⟩

instance [NeZero n] : Finite (TrivZMod n) := inferInstanceAs (Finite (Multiplicative (ZMod n)))

/-- The identification with `Multiplicative (ZMod n)`. -/
def equiv : TrivZMod n ≃* Multiplicative (ZMod n) := MulEquiv.refl _

instance {G : Type*} [Monoid G] : MulDistribMulAction G (TrivZMod n) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

@[simp]
theorem smul_eq {G : Type*} [Monoid G] (g : G) (x : TrivZMod n) : g • x = x := rfl

instance {G : Type*} [Monoid G] [TopologicalSpace G] : SmoothAction G (TrivZMod n) :=
  ⟨fun x => IsLocallyConstant.const x⟩

theorem h0_eq_top {G : Type*} [Group G] : H0 G (TrivZMod n) = ⊤ :=
  eq_top_iff.2 fun _ _ _ => rfl

theorem card [NeZero n] : Nat.card (TrivZMod n) = n := by
  rw [Nat.card_congr (equiv (n := n)).toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

end TrivZMod

/-! ### `Hom(A, ℤ/n)` has at most `#A` elements -/

/-- `#Hom(A, ℤ/n) ≤ #A` for a finite commutative group `A`. -/
theorem card_hom_zmod_le (A : Type*) [CommGroup A] [Finite A] (n : ℕ) [NeZero n] :
    Nat.card (A →* Multiplicative (ZMod n)) ≤ Nat.card A := by
  classical
  haveI := Fintype.ofFinite A
  let f : (A →* Multiplicative (ZMod n)) → AddChar (Additive A) ℂ := fun ψ =>
    ZMod.stdAddChar.compAddMonoidHom (MonoidHom.toAdditive ψ)
  have hf : Function.Injective f := by
    intro ψ ψ' h
    refine MonoidHom.ext fun a => ?_
    have := DFunLike.congr_fun h (Additive.ofMul a)
    simp only [f, AddChar.compAddMonoidHom_apply] at this
    exact Multiplicative.toAdd.injective (ZMod.injective_stdAddChar this)
  calc Nat.card (A →* Multiplicative (ZMod n)) ≤ Nat.card (AddChar (Additive A) ℂ) :=
        Nat.card_le_card_of_injective f hf
    _ = Nat.card A := by
        rw [Nat.card_eq_fintype_card, AddChar.card_eq, ← Nat.card_eq_fintype_card]
        rfl

/-! ### `H¹(G, ℤ/n)` and characters -/

section Galois

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsIntegral K Ω]
variable (n : ℕ) [NeZero n]

/-- `(k, ζ) ↦ ζ^k`, the pairing `ℤ/n × μ_n → μ_n`. -/
def powPairing : GPairing (Ω ≃ₐ[K] Ω) (TrivZMod n) (Mu n Ω) (Mu n Ω) where
  toHom :=
    { toFun := fun k => powMonoidHom (Multiplicative.toAdd (TrivZMod.equiv k)).val
      map_one' := MonoidHom.ext fun ζ => by
        simp [TrivZMod.equiv]
      map_mul' := fun a b => MonoidHom.ext fun ζ => by
        simp only [map_mul, toAdd_mul, ZMod.val_add, powMonoidHom_apply, mu_pow_mod, pow_add,
          MonoidHom.mul_apply] }
  map_smul' g k ζ := by
    simp [smul_pow']

theorem powPairing_apply (k : TrivZMod n) (ζ : Mu n Ω) :
    (powPairing (K := K) n).toHom k ζ = ζ ^ (Multiplicative.toAdd (TrivZMod.equiv k)).val :=
  rfl

/-- The character `g ↦ x(g)` of a 1-cocycle with values in the trivial module `ℤ/n`. -/
def charOfCocycle (x : ContH1.cocycles (Ω ≃ₐ[K] Ω) (TrivZMod n)) : LocChar K Ω n :=
  ⟨{ toFun := fun g => TrivZMod.equiv (x g)
     map_one' := by rw [ContH1.map_one_eq x]; rfl
     map_mul' := fun g h => by
       rw [ContH1.isMulCocycle₁ x g h, TrivZMod.smul_eq, map_mul, mul_comm] },
    show IsLocallyConstant fun g => TrivZMod.equiv (x g) from
      ((IsLocallyConstant.iff_continuous _).2 (ContH1.continuous x)).comp _⟩

/-- The 1-cocycle of a locally constant character. -/
def cocycleOfChar (χ : LocChar K Ω n) : ContH1.cocycles (Ω ≃ₐ[K] Ω) (TrivZMod n) :=
  ContH1.mkCocycle (fun g => TrivZMod.equiv.symm (χ.1 g))
    ((IsLocallyConstant.iff_continuous _).1 (χ.2.comp _))
    (fun g h => by
      change TrivZMod.equiv.symm (χ.1 (g * h)) =
        TrivZMod.equiv.symm (χ.1 h) * TrivZMod.equiv.symm (χ.1 g)
      rw [map_mul, map_mul, mul_comm])

/-- **`H¹(G_K, ℤ/n) ≃ Hom_cont(G_K, ℤ/n)`**. -/
noncomputable def h1TrivEquiv : ContH1 (Ω ≃ₐ[K] Ω) (TrivZMod n) ≃* LocChar K Ω n where
  toFun := QuotientGroup.lift (ContH1.coboundaries _ _)
    { toFun := charOfCocycle n
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    (by
      rintro x ⟨m, hm⟩
      rw [MonoidHom.mem_ker]
      refine Subtype.ext (MonoidHom.ext fun g => ?_)
      change TrivZMod.equiv (x g) = 1
      rw [← hm g, TrivZMod.smul_eq, div_self', map_one])
  invFun χ := ContH1.mk (cocycleOfChar n χ)
  left_inv x := by
    induction x using ContH1.induction_on with | h x => ?_
    rfl
  right_inv χ := rfl
  map_mul' := map_mul _

theorem h1TrivEquiv_symm_apply (χ : LocChar K Ω n) :
    (h1TrivEquiv n).symm χ = ContH1.mk (cocycleOfChar n χ) := rfl

/-- On characters, the cup product with `μ_n`-classes is `Brauer.cupH1`. -/
theorem cup11_powPairing (χ : LocChar K Ω n) (ζ : ContH1 (Ω ≃ₐ[K] Ω) (Mu n Ω)) :
    cup11 (powPairing n) ((h1TrivEquiv n).symm χ) ζ = cupH1 n χ ζ := by
  induction ζ using ContH1.induction_on with | h ζ => ?_
  rw [h1TrivEquiv_symm_apply, cup11_mk, cupH1_mk]
  rfl

/-! ### Degree zero cup products are powers -/

theorem map_powMonoidHom_eq_pow {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M]
    [MulDistribMulAction G M] (j : ℕ) (h : ∀ (g : G) (m : M), (powMonoidHom j : M →* M)
      ((MonoidHom.id G) g • m) = g • (powMonoidHom j : M →* M) m) (β : ContH2 G M) :
    ContH2.map (MonoidHom.id G) continuous_id (powMonoidHom j) h β = β ^ j := by
  induction β using induction_on with | h f => ?_
  rw [map_mk, ← map_pow]
  congr 1

theorem cup02_powPairing (k : H0 (Ω ≃ₐ[K] Ω) (TrivZMod n)) (β : H2Mu K Ω n) :
    cup02 (powPairing n) k β = β ^ (Multiplicative.toAdd (TrivZMod.equiv (k : TrivZMod n))).val :=
  map_powMonoidHom_eq_pow _ _ β

theorem cup20_swap_powPairing (β : H2Mu K Ω n) (k : H0 (Ω ≃ₐ[K] Ω) (TrivZMod n)) :
    cup20 (powPairing n).swap β k =
      β ^ (Multiplicative.toAdd (TrivZMod.equiv (k : TrivZMod n))).val :=
  cup02_powPairing n k β

end Galois

/-! ### `Hom(ℤ/n, ℤ/n) = ℤ/n` -/

section HomZMod

variable {n : ℕ} [NeZero n]

theorem ofAdd_pow_val (x : Multiplicative (ZMod n)) (k : ZMod n) :
    x ^ k.val = Multiplicative.ofAdd (k * Multiplicative.toAdd x) := by
  rw [← ofAdd_toAdd x, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, toAdd_ofAdd]

/-- `k ↦ (a ↦ J(a)^k)` is a bijection `ℤ/n → Hom(A, ℤ/n)` for `J : A ≃ ℤ/n`. -/
theorem bijective_pow_comp {A : Type*} [CommGroup A] (J : A ≃* Multiplicative (ZMod n)) :
    Function.Bijective fun k : ZMod n =>
      (powMonoidHom k.val : Multiplicative (ZMod n) →* Multiplicative (ZMod n)).comp
        J.toMonoidHom := by
  refine ⟨fun k k' h => ?_, fun ψ => ?_⟩
  · have := DFunLike.congr_fun h (J.symm (Multiplicative.ofAdd 1))
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      powMonoidHom_apply, ofAdd_pow_val, toAdd_ofAdd, mul_one] at this
    exact Multiplicative.ofAdd.injective this
  · refine ⟨Multiplicative.toAdd (ψ (J.symm (Multiplicative.ofAdd 1))), MonoidHom.ext fun a => ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, powMonoidHom_apply,
      ofAdd_pow_val]
    have ha : a = J.symm (Multiplicative.ofAdd 1) ^ (Multiplicative.toAdd (J a)).val := by
      apply J.injective
      rw [map_pow, MulEquiv.apply_symm_apply, ofAdd_pow_val, toAdd_ofAdd, mul_one, ofAdd_toAdd]
    conv_rhs => rw [ha, map_pow, ofAdd_pow_val]
    rw [mul_comm]

/-- `a ↦ (k ↦ J(a)^k)` is a bijection `A → Hom(ℤ/n, ℤ/n)` for `J : A ≃ ℤ/n` (with `ℤ/n` realised
as a subgroup `H = ⊤` of `TrivZMod n`). -/
theorem bijective_pow_eval {A : Type*} [CommGroup A] (J : A ≃* Multiplicative (ZMod n))
    (H : Subgroup (TrivZMod n)) (hH : H = ⊤) (F : A → (H →* Multiplicative (ZMod n)))
    (hF : ∀ a k, F a k = J a ^ (Multiplicative.toAdd (TrivZMod.equiv (k : TrivZMod n))).val) :
    Function.Bijective F := by
  have h1 : (TrivZMod.equiv.symm (Multiplicative.ofAdd 1) : TrivZMod n) ∈ H := hH ▸ trivial
  set one : H := ⟨_, h1⟩
  refine ⟨fun a a' h => ?_, fun ψ => ?_⟩
  · have := DFunLike.congr_fun h one
    rw [hF, hF] at this
    simp only [one, MulEquiv.apply_symm_apply, toAdd_ofAdd, ofAdd_pow_val, one_mul,
      ofAdd_toAdd] at this
    exact J.injective this
  · refine ⟨J.symm (ψ one), MonoidHom.ext fun k => ?_⟩
    rw [hF, MulEquiv.apply_symm_apply]
    have hk : k = one ^ (Multiplicative.toAdd (TrivZMod.equiv (k : TrivZMod n))).val := by
      apply Subtype.ext
      apply TrivZMod.equiv.injective
      simp only [one, SubgroupClass.coe_pow, map_pow, MulEquiv.apply_symm_apply, ofAdd_pow_val,
        toAdd_ofAdd, mul_one, ofAdd_toAdd]
    conv_rhs => rw [hk, map_pow]

end HomZMod

end Brauer

namespace PadicField

open Brauer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
variable (n : ℕ) [NeZero n]

/-! ### Degrees `0` and `2` -/

/-- **`H⁰(K, ℤ/n) × H²(K, μ_n) → ℤ/n` is perfect.** -/
theorem perfectDeg0_trivZMod : PerfectDeg0 (invMu p K Ω n) (powPairing (K := K) (Ω := Ω) n) := by
  set J := h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n))
  set e : H0 (Ω ≃ₐ[K] Ω) (TrivZMod n) ≃ ZMod n :=
    ((Equiv.subtypeUnivEquiv fun x => (TrivZMod.h0_eq_top (n := n) (G := Ω ≃ₐ[K] Ω)).symm ▸
      Subgroup.mem_top x).trans TrivZMod.equiv.toEquiv).trans Multiplicative.toAdd
  have h : (fun m : H0 (Ω ≃ₐ[K] Ω) (TrivZMod n) => (invMu p K Ω n).comp (cup02 (powPairing n) m)) =
      (fun k : ZMod n => (powMonoidHom k.val).comp J.toMonoidHom) ∘ e := by
    funext m
    refine MonoidHom.ext fun β => ?_
    simp only [Function.comp_apply, MonoidHom.comp_apply, cup02_powPairing, map_pow,
      powMonoidHom_apply, MulEquiv.coe_toMonoidHom]
    rfl
  rw [PerfectDeg0, h]
  exact (bijective_pow_comp J).comp e.bijective

/-- **`H²(K, μ_n) × H⁰(K, ℤ/n) → ℤ/n` is perfect.** -/
theorem perfectDeg2_mu :
    PerfectDeg2 (invMu p K Ω n) (powPairing (K := K) (Ω := Ω) n).swap :=
  bijective_pow_eval (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n))) _
    TrivZMod.h0_eq_top _ fun β k => by
      rw [MonoidHom.comp_apply, cup20_swap_powPairing, map_pow]
      rfl

/-! ### Degree one -/

include hp in
theorem finite_h1_mu : Finite (ContH1 (Ω ≃ₐ[K] Ω) (Mu n Ω)) := by
  haveI := hasKummerRoots (K := K) (Ω := Ω) n
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  haveI := (KummerTheory.finiteKummerQuotients_of_isDiscreteValuationRing (𝒪 p K) K).finiteIndex
    n (NeZero.ne n)
  exact Finite.of_equiv _ (kummerEquiv n K Ω).toEquiv

include hp in
/-- `#H¹(K, μ_n) = [Kˣ : (Kˣ)ⁿ]`. -/
theorem card_h1_mu :
    Nat.card (ContH1 (Ω ≃ₐ[K] Ω) (Mu n Ω)) = (powMonoidHom n : Kˣ →* Kˣ).range.index := by
  haveI := hasKummerRoots (K := K) (Ω := Ω) n
  rw [← Nat.card_congr (kummerEquiv n K Ω).toEquiv]
  rfl

/-- The map `H¹(K, ℤ/n) → Hom(H¹(K, μ_n), ℤ/n)`, `x ↦ (y ↦ inv(x ∪ y))`, is injective. -/
theorem injective_deg1_trivZMod :
    Function.Injective fun x : ContH1 (Ω ≃ₐ[K] Ω) (TrivZMod n) =>
      (invMu p K Ω n).comp (cup11 (powPairing n) x) := by
  have key : Function.Injective
      ((MonoidHom.compHom (invMu p K Ω n)).comp (cup11 (powPairing (K := K) (Ω := Ω) n))) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    obtain ⟨χ, rfl⟩ := (h1TrivEquiv (K := K) (Ω := Ω) n).symm.surjective z
    have hχ : χ = 1 := eq_one_of_forall_pairingH1_eq_zero (p := p) n χ fun ζ => by
      have := DFunLike.congr_fun hz ζ
      change invMu p K Ω n (cup11 (powPairing n) ((h1TrivEquiv n).symm χ) ζ) = 1 at this
      rw [cup11_powPairing] at this
      rw [pairingH1]
      exact (congrArg Multiplicative.toAdd this).trans rfl
    rw [hχ, map_one]
  exact key

/-- The map `H¹(K, μ_n) → Hom(H¹(K, ℤ/n), ℤ/n)`, `y ↦ (x ↦ inv(y ∪ x))`, is injective. -/
theorem injective_deg1_mu :
    Function.Injective fun y : ContH1 (Ω ≃ₐ[K] Ω) (Mu n Ω) =>
      (invMu p K Ω n).comp (cup11 (powPairing (K := K) n).swap y) := by
  have key : Function.Injective
      ((MonoidHom.compHom (invMu p K Ω n)).comp
        (cup11 (powPairing (K := K) (Ω := Ω) n).swap)) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    refine eq_one_of_forall_pairingH1_eq_zero' (p := p) n z fun χ => ?_
    have := DFunLike.congr_fun hz ((h1TrivEquiv (K := K) (Ω := Ω) n).symm χ)
    change invMu p K Ω n (cup11 (powPairing n).swap z ((h1TrivEquiv n).symm χ)) = 1 at this
    rw [cup11_swap, GPairing.swap_swap, cup11_powPairing, map_inv, inv_eq_one] at this
    rw [pairingH1]
    exact (congrArg Multiplicative.toAdd this).trans rfl
  exact key

include hp in
theorem finite_h1_trivZMod : Finite (ContH1 (Ω ≃ₐ[K] Ω) (TrivZMod n)) := by
  haveI := finite_h1_mu (p := p) (K := K) (Ω := Ω) n
  haveI : Finite (ContH1 (Ω ≃ₐ[K] Ω) (Mu n Ω) →* Multiplicative (ZMod n)) :=
    Finite.of_injective _ DFunLike.coe_injective
  exact Finite.of_injective _ (injective_deg1_trivZMod (p := p) n)

include hp in
/-- `#H¹(K, ℤ/n) = #H¹(K, μ_n)`, and both equal `#Hom(H¹(K, μ_n), ℤ/n)`. -/
theorem card_h1_trivZMod_eq :
    Nat.card (ContH1 (Ω ≃ₐ[K] Ω) (TrivZMod n)) = Nat.card (ContH1 (Ω ≃ₐ[K] Ω) (Mu n Ω)) ∧
      Nat.card (ContH1 (Ω ≃ₐ[K] Ω) (Mu n Ω) →* Multiplicative (ZMod n)) =
        Nat.card (ContH1 (Ω ≃ₐ[K] Ω) (Mu n Ω)) ∧
      Nat.card (ContH1 (Ω ≃ₐ[K] Ω) (TrivZMod n) →* Multiplicative (ZMod n)) =
        Nat.card (ContH1 (Ω ≃ₐ[K] Ω) (TrivZMod n)) := by
  haveI := finite_h1_mu (p := p) (K := K) (Ω := Ω) n
  haveI := finite_h1_trivZMod (p := p) (K := K) (Ω := Ω) n
  haveI : Finite (ContH1 (Ω ≃ₐ[K] Ω) (Mu n Ω) →* Multiplicative (ZMod n)) :=
    Finite.of_injective _ DFunLike.coe_injective
  haveI : Finite (ContH1 (Ω ≃ₐ[K] Ω) (TrivZMod n) →* Multiplicative (ZMod n)) :=
    Finite.of_injective _ DFunLike.coe_injective
  have h1 := Nat.card_le_card_of_injective _ (injective_deg1_trivZMod (p := p) (K := K) (Ω := Ω) n)
  have h2 := Nat.card_le_card_of_injective _ (injective_deg1_mu (p := p) (K := K) (Ω := Ω) n)
  have h3 := card_hom_zmod_le (ContH1 (Ω ≃ₐ[K] Ω) (Mu n Ω)) n
  have h4 := card_hom_zmod_le (ContH1 (Ω ≃ₐ[K] Ω) (TrivZMod n)) n
  refine ⟨by omega, by omega, by omega⟩

/-- **`H¹(K, ℤ/n) × H¹(K, μ_n) → ℤ/n` is perfect.** -/
theorem perfectDeg1_trivZMod : PerfectDeg1 (invMu p K Ω n) (powPairing (K := K) (Ω := Ω) n) := by
  haveI := finite_h1_mu (p := p) (K := K) (Ω := Ω) n
  haveI : Finite (ContH1 (Ω ≃ₐ[K] Ω) (Mu n Ω) →* Multiplicative (ZMod n)) :=
    Finite.of_injective _ DFunLike.coe_injective
  obtain ⟨h1, h2, -⟩ := card_h1_trivZMod_eq (p := p) (K := K) (Ω := Ω) n
  exact (injective_deg1_trivZMod (p := p) n).bijective_of_nat_card_le (by omega)

/-- **`H¹(K, μ_n) × H¹(K, ℤ/n) → ℤ/n` is perfect.** -/
theorem perfectDeg1_mu : PerfectDeg1 (invMu p K Ω n) (powPairing (K := K) (Ω := Ω) n).swap := by
  haveI := finite_h1_trivZMod (p := p) (K := K) (Ω := Ω) n
  haveI : Finite (ContH1 (Ω ≃ₐ[K] Ω) (TrivZMod n) →* Multiplicative (ZMod n)) :=
    Finite.of_injective _ DFunLike.coe_injective
  obtain ⟨h1, -, h3⟩ := card_h1_trivZMod_eq (p := p) (K := K) (Ω := Ω) n
  exact (injective_deg1_mu (p := p) n).bijective_of_nat_card_le (by omega)

/-! ### Cardinalities and the Euler characteristic of `μ_n` -/

/-- `#H¹(K, μ_n) = n · #μ_n(K) · p^{v_p(n) [K : ℚ_p]}`. -/
theorem card_h1_mu_eq :
    Nat.card (ContH1 (Ω ≃ₐ[K] Ω) (Mu n Ω)) =
      n * Nat.card (rootsOfUnity n K) * p ^ (padicValNat p n * Module.finrank ℚ_[p] K) := by
  rw [card_h1_mu (p := p), index_range_pow (p := p)]

/-- `#H¹(K, ℤ/n) = n · #μ_n(K) · p^{v_p(n) [K : ℚ_p]}`. -/
theorem card_h1_trivZMod :
    Nat.card (ContH1 (Ω ≃ₐ[K] Ω) (TrivZMod n)) =
      n * Nat.card (rootsOfUnity n K) * p ^ (padicValNat p n * Module.finrank ℚ_[p] K) := by
  rw [(card_h1_trivZMod_eq (p := p) n).1, card_h1_mu_eq (p := p)]

include hp in
theorem card_h2_mu : Nat.card (H2Mu K Ω n) = n := by
  rw [Nat.card_congr (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n))).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- `H⁰(K, μ_n) = μ_n(K)`. -/
theorem card_h0_mu : Nat.card (H0 (Ω ≃ₐ[K] Ω) (Mu n Ω)) = Nat.card (rootsOfUnity n K) := by
  let f : rootsOfUnity n K → H0 (Ω ≃ₐ[K] Ω) (Mu n Ω) := fun ζ =>
    ⟨Mu.mk (Units.map (algebraMap K Ω : K →* Ω) ζ) (by
        rw [← map_pow, (mem_rootsOfUnity n _).1 ζ.2, map_one]),
      fun σ => Mu.ext (Units.ext (by
        rw [Mu.val_smul_coe, Mu.val_mk, Units.coe_map, MonoidHom.coe_coe, AlgEquiv.commutes]))⟩
  have hf : Function.Bijective f := by
    refine ⟨fun ζ ζ' h => ?_, fun μ => ?_⟩
    · have h' := congrArg (fun x : H0 (Ω ≃ₐ[K] Ω) (Mu n Ω) => ((Mu.val (x : Mu n Ω) : Ωˣ) : Ω)) h
      simp only [f, Mu.val_mk, Units.coe_map, MonoidHom.coe_coe] at h'
      exact Subtype.ext (Units.ext ((algebraMap K Ω).injective h'))
    · have hfix : ((Mu.val (μ : Mu n Ω) : Ωˣ) : Ω) ∈ (⊥ : IntermediateField K Ω) := by
        rw [InfiniteGalois.mem_bot_iff_fixed]
        intro σ
        rw [← Mu.val_smul_coe, smul_H0 μ σ]
      obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 hfix
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [map_zero] at ha
        exact (Mu.val (μ : Mu n Ω)).ne_zero ha.symm
      have han : (Units.mk0 a ha0) ^ n = 1 := by
        apply Units.ext
        apply (algebraMap K Ω).injective
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, ha, Units.val_one, map_one,
          ← Units.val_pow_eq_pow_val, Mu.val_pow_n, Units.val_one]
      refine ⟨⟨Units.mk0 a ha0, (mem_rootsOfUnity n _).2 han⟩, Subtype.ext (Mu.ext
        (Units.ext ?_))⟩
      simp only [f, Mu.val_mk, Units.coe_map, MonoidHom.coe_coe, Units.val_mk0, ha]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

include hp in
theorem card_mu : Nat.card (Mu n Ω) = n := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ_[p] Ω).injective
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 (NeZero.ne n)⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω n

/-- **The local Euler characteristic formula for `μ_n`**: `#H⁰(K, μ_n) · #H²(K, μ_n) / #H¹(K, μ_n)
= |n|_K = p^{-v_p(n) [K : ℚ_p]}`. -/
theorem eulerCharacteristicFor_mu : EulerCharacteristicFor p K Ω (Mu n Ω) := by
  refine ⟨finite_h1_mu (p := p) n, ?_, ?_⟩
  · exact Finite.of_equiv _ (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n))).symm.toEquiv
  · rw [card_h1_mu_eq (p := p), card_h0_mu, card_h2_mu (p := p), card_mu (p := p)]
    ring

end PadicField
