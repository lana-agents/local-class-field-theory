/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.MuN
import LocalClassFieldTheory.Duality.Transport

/-!
# Local Tate duality for `ℤ/n` and `μ_n` in the Cartier dual formulation

We identify the Cartier duals `Hom(ℤ/n, μ_n) ≃ μ_n` (`Brauer.dualTrivEquiv`, `φ ↦ φ(1)`) and
`ℤ/n ≃ Hom(μ_n, μ_n)` (`PadicField.dualMuEquiv`, `k ↦ (ζ ↦ ζ^k)`), so that the evaluation
pairings become `(k, ζ) ↦ ζ^k` and `(ζ, k) ↦ ζ^k`, and deduce from
`LocalClassFieldTheory.Duality.MuN` the abstract statements of `PadicField.TateDualityFor`:

* `PadicField.perfectDeg0_eval_trivZMod`, `PadicField.perfectDeg1_eval_trivZMod`: local duality for
  `M = ℤ/n` in degrees `0` and `1` (unconditionally);
* `PadicField.perfectDeg1_eval_mu`, `PadicField.perfectDeg2_eval_mu`: local duality for `M = μ_n`
  in degrees `1` and `2` (unconditionally).

If moreover `μ_n ⊆ K` (`#μ_n(K) = n`), then `ℤ/n ≃ μ_n` as Galois modules
(`PadicField.trivZModMuEquiv`), `H²(K, ℤ/n) ≃ ℤ/n`, and we obtain the remaining degrees:

* **`PadicField.tateDualityFor_trivZMod`**: `TateDualityFor p K Ω (TrivZMod n) n`;
* **`PadicField.tateDualityFor_mu`**: `TateDualityFor p K Ω (Mu n Ω) n`;
* **`PadicField.eulerCharacteristicFor_trivZMod`**: the Euler characteristic formula for `ℤ/n`.

Without `μ_n ⊆ K` the missing statements (`H²(K, ℤ/n)` dual to `μ_n(K)`) are instances of the
general `PadicField.LocalTateDuality`, proved in `LocalClassFieldTheory.Duality.General`.
-/

open ContH2 groupCohomology KummerTheory

set_option linter.unusedSectionVars false

namespace Brauer

variable {Ω : Type*} [Field Ω] (n : ℕ) [NeZero n]

/-- `k ↦ ζ^k`, a homomorphism `ℤ/n → μ_n`. -/
def powHomZMod (ζ : Mu n Ω) : TrivZMod n →* Mu n Ω where
  toFun k := ζ ^ (Multiplicative.toAdd (TrivZMod.equiv k)).val
  map_one' := by simp [TrivZMod.equiv]
  map_mul' a b := by
    simp only [map_mul, toAdd_mul, ZMod.val_add, mu_pow_mod, pow_add]

theorem powHomZMod_apply (ζ : Mu n Ω) (k : TrivZMod n) :
    powHomZMod n ζ k = ζ ^ (Multiplicative.toAdd (TrivZMod.equiv k)).val := rfl

/-- The generator `1 ∈ ℤ/n`. -/
def oneZMod : TrivZMod n := TrivZMod.equiv.symm (Multiplicative.ofAdd 1)

theorem oneZMod_pow (k : TrivZMod n) :
    oneZMod n ^ (Multiplicative.toAdd (TrivZMod.equiv k)).val = k := by
  apply TrivZMod.equiv.injective
  rw [map_pow, oneZMod, MulEquiv.apply_symm_apply, ofAdd_pow_val, toAdd_ofAdd, mul_one,
    ofAdd_toAdd]

theorem hom_eq_powHomZMod (φ : TrivZMod n →* Mu n Ω) (k : TrivZMod n) :
    φ k = powHomZMod n (φ (oneZMod n)) k := by
  rw [powHomZMod_apply, ← map_pow, oneZMod_pow]

theorem powHomZMod_one (ζ : Mu n Ω) : powHomZMod n ζ (oneZMod n) = ζ := by
  rw [powHomZMod_apply, oneZMod, MulEquiv.apply_symm_apply, toAdd_ofAdd,
    ZMod.val_one_eq_one_mod, mu_pow_mod, pow_one]

/-- `a ↦ (h ↦ J(a)^{j(h)})` is a bijection `A → Hom(H, ℤ/n)` for `J : A ≃ ℤ/n`, `j : H ≃ ℤ/n`. -/
theorem bijective_pow_eval' {A H : Type*} [CommGroup A] [Group H]
    (J : A ≃* Multiplicative (ZMod n)) (j : H ≃* Multiplicative (ZMod n))
    (F : A → (H →* Multiplicative (ZMod n)))
    (hF : ∀ a h, F a h = J a ^ (Multiplicative.toAdd (j h)).val) : Function.Bijective F := by
  set one : H := j.symm (Multiplicative.ofAdd 1)
  have hone : ∀ h : H, h = one ^ (Multiplicative.toAdd (j h)).val := by
    intro h
    apply j.injective
    rw [map_pow, MulEquiv.apply_symm_apply, ofAdd_pow_val, toAdd_ofAdd, mul_one, ofAdd_toAdd]
  refine ⟨fun a a' h => ?_, fun ψ => ?_⟩
  · have := DFunLike.congr_fun h one
    rw [hF, hF] at this
    simp only [one, MulEquiv.apply_symm_apply, toAdd_ofAdd, ofAdd_pow_val, one_mul,
      ofAdd_toAdd] at this
    exact J.injective this
  · refine ⟨J.symm (ψ one), MonoidHom.ext fun h => ?_⟩
    rw [hF, MulEquiv.apply_symm_apply]
    conv_rhs => rw [hone h, map_pow]

variable {G : Type*} [Group G] [MulDistribMulAction G (Mu n Ω)]

/-- **`μ_n ≃ Hom(ℤ/n, μ_n)`**, `ζ ↦ (k ↦ ζ^k)`. -/
def dualTrivEquiv : Mu n Ω ≃* CartierDual n Ω (TrivZMod n) where
  toFun ζ := CartierDual.toHom.symm (powHomZMod n ζ)
  invFun φ := CartierDual.toHom φ (oneZMod n)
  left_inv ζ := powHomZMod_one n ζ
  right_inv φ := by
    apply CartierDual.toHom.injective
    refine MonoidHom.ext fun k => ?_
    change powHomZMod n (CartierDual.toHom φ (oneZMod n)) k = CartierDual.toHom φ k
    exact (hom_eq_powHomZMod n _ k).symm
  map_mul' ζ ζ' := by
    apply CartierDual.toHom.injective
    refine MonoidHom.ext fun k => ?_
    change (ζ * ζ') ^ _ = ζ ^ _ * ζ' ^ _
    rw [mul_pow]

theorem dualTrivEquiv_smul (g : G) (ζ : Mu n Ω) :
    dualTrivEquiv n (g • ζ) = g • dualTrivEquiv n ζ := by
  apply CartierDual.toHom.injective
  refine MonoidHom.ext fun k => ?_
  rw [CartierDual.smul_apply, TrivZMod.smul_eq]
  change (g • ζ) ^ _ = g • ζ ^ _
  rw [smul_pow']

end Brauer

namespace PadicField

open Brauer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
variable (n : ℕ) [NeZero n]

/-! ### `M = ℤ/n` -/

theorem perfectDeg_eval_trivZMod_iff :
    (PerfectDeg0 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := TrivZMod n)
      (G := Ω ≃ₐ[K] Ω)) ↔ PerfectDeg0 (invMu p K Ω n) (powPairing (K := K) (Ω := Ω) n)) ∧
    (PerfectDeg1 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := TrivZMod n)
      (G := Ω ≃ₐ[K] Ω)) ↔ PerfectDeg1 (invMu p K Ω n) (powPairing (K := K) (Ω := Ω) n)) ∧
    (PerfectDeg2 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := TrivZMod n)
      (G := Ω ≃ₐ[K] Ω)) ↔ PerfectDeg2 (invMu p K Ω n) (powPairing (K := K) (Ω := Ω) n)) := by
  have hτ : ∀ (g : Ω ≃ₐ[K] Ω) (ζ : Mu n Ω), dualTrivEquiv n (g • ζ) = g • dualTrivEquiv n ζ :=
    dualTrivEquiv_smul n
  have he : ∀ (k : TrivZMod n) (ζ : Mu n Ω),
      (CartierDual.evalPairing (G := Ω ≃ₐ[K] Ω)).toHom k (dualTrivEquiv n ζ) =
        (powPairing (K := K) n).toHom k ζ := fun _ _ => rfl
  exact ⟨perfectDeg0_iff_of_equiv _ _ hτ _ _ he, perfectDeg1_iff_of_equiv _ _ hτ _ _ he,
    perfectDeg2_iff_of_equiv _ _ hτ _ _ he⟩

/-- **Local duality for `ℤ/n` in degree `0`**: `H⁰(K, ℤ/n) × H²(K, Hom(ℤ/n, μ_n)) → ℤ/n` is
perfect. -/
theorem perfectDeg0_eval_trivZMod :
    PerfectDeg0 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := TrivZMod n)
      (G := Ω ≃ₐ[K] Ω)) :=
  (perfectDeg_eval_trivZMod_iff n).1.2 (perfectDeg0_trivZMod n)

/-- **Local duality for `ℤ/n` in degree `1`**: `H¹(K, ℤ/n) × H¹(K, Hom(ℤ/n, μ_n)) → ℤ/n` is
perfect. -/
theorem perfectDeg1_eval_trivZMod :
    PerfectDeg1 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := TrivZMod n)
      (G := Ω ≃ₐ[K] Ω)) :=
  (perfectDeg_eval_trivZMod_iff n).2.1.2 (perfectDeg1_trivZMod n)

/-! ### `M = μ_n` -/

include hp in
theorem exists_generator_mu : ∃ γ : Mu n Ω, orderOf γ = n ∧ ∀ x, x ∈ Subgroup.zpowers γ := by
  haveI : IsCyclic (Mu n Ω) := inferInstanceAs (IsCyclic (rootsOfUnity n Ω))
  haveI : Finite (Mu n Ω) := inferInstance
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Mu n Ω)
  refine ⟨γ, ?_, hγ⟩
  rw [orderOf_eq_card_of_forall_mem_zpowers hγ, card_mu (p := p)]

variable (p Ω) in
/-- A generator of `μ_n(Ω)`. -/
noncomputable def genMu : Mu n Ω := (exists_generator_mu (p := p) (Ω := Ω) n).choose

theorem orderOf_genMu : orderOf (genMu p Ω n) = n :=
  (exists_generator_mu (p := p) (Ω := Ω) n).choose_spec.1

theorem powHomZMod_genMu_injective : Function.Injective (powHomZMod n (genMu p Ω n)) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  rw [powHomZMod_apply, ← pow_zero (genMu p Ω n), pow_eq_pow_iff_modEq, orderOf_genMu,
    Nat.ModEq, Nat.zero_mod, Nat.mod_eq_of_lt (ZMod.val_lt _)] at hk
  apply TrivZMod.equiv.injective
  rw [map_one, ← ofAdd_toAdd (TrivZMod.equiv k), ← ofAdd_zero]
  congr 1
  exact (ZMod.val_eq_zero _).1 hk

variable (p Ω) in
/-- `ℤ/n ≃ μ_n(Ω)`, `k ↦ γ^k` for the generator `γ = genMu`. -/
noncomputable def trivZModMuEquiv : TrivZMod n ≃* Mu n Ω :=
  MulEquiv.ofBijective (powHomZMod n (genMu p Ω n))
    ((powHomZMod_genMu_injective n).bijective_of_nat_card_le
      (by rw [TrivZMod.card, card_mu (p := p)]))

theorem trivZModMuEquiv_apply (k : TrivZMod n) :
    trivZModMuEquiv p Ω n k = genMu p Ω n ^ (Multiplicative.toAdd (TrivZMod.equiv k)).val :=
  rfl

/-- `k ↦ (ζ ↦ ζ^k)`, `ℤ/n → Hom(μ_n, μ_n)`. -/
def dualMuHom : TrivZMod n →* CartierDual n Ω (Mu n Ω) where
  toFun k := CartierDual.toHom.symm (powMonoidHom (Multiplicative.toAdd (TrivZMod.equiv k)).val)
  map_one' := by
    apply CartierDual.toHom.injective
    exact MonoidHom.ext fun ζ => by simp [TrivZMod.equiv]
  map_mul' a b := by
    apply CartierDual.toHom.injective
    exact MonoidHom.ext fun ζ => by
      change ζ ^ _ = ζ ^ _ * ζ ^ _
      simp only [map_mul, toAdd_mul, ZMod.val_add, mu_pow_mod, pow_add]

include hp in
theorem dualMuHom_bijective : Function.Bijective (dualMuHom (Ω := Ω) n) := by
  have hinj : Function.Injective (dualMuHom (Ω := Ω) n) := by
    intro a b h
    have h' := DFunLike.congr_fun (congrArg CartierDual.toHom h) (genMu p Ω n)
    apply (powHomZMod_genMu_injective (p := p) (Ω := Ω) n)
    exact h'
  haveI : Finite (CartierDual n Ω (Mu n Ω)) :=
    Finite.of_injective (fun φ => (CartierDual.toHom φ : Mu n Ω → Mu n Ω))
      (fun _ _ h => CartierDual.toHom.injective (DFunLike.coe_injective h))
  refine hinj.bijective_of_nat_card_le ?_
  -- `Hom(μ_n, μ_n) ↪ μ_n`, `φ ↦ φ(γ)` for a generator `γ`
  let f : CartierDual n Ω (Mu n Ω) → Mu n Ω := fun φ =>
    CartierDual.toHom φ (trivZModMuEquiv p Ω n (oneZMod n))
  have hf : Function.Injective f := by
    intro φ ψ h
    apply CartierDual.toHom.injective
    refine MonoidHom.ext fun ζ => ?_
    obtain ⟨k, rfl⟩ := (trivZModMuEquiv p Ω n).surjective ζ
    rw [← oneZMod_pow n k, map_pow, map_pow, map_pow]
    exact congrArg (· ^ _) h
  calc Nat.card (CartierDual n Ω (Mu n Ω)) ≤ Nat.card (Mu n Ω) :=
        Nat.card_le_card_of_injective f hf
    _ = Nat.card (TrivZMod n) := by rw [TrivZMod.card, card_mu (p := p)]

variable (p Ω) in
/-- **`ℤ/n ≃ Hom(μ_n, μ_n)`**, `k ↦ (ζ ↦ ζ^k)`. -/
noncomputable def dualMuEquiv : TrivZMod n ≃* CartierDual n Ω (Mu n Ω) :=
  MulEquiv.ofBijective (dualMuHom n) (dualMuHom_bijective (p := p) n)

theorem perfectDeg_eval_mu_iff :
    (PerfectDeg0 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := Mu n Ω)
      (G := Ω ≃ₐ[K] Ω)) ↔ PerfectDeg0 (invMu p K Ω n) (powPairing (K := K) (Ω := Ω) n).swap) ∧
    (PerfectDeg1 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := Mu n Ω)
      (G := Ω ≃ₐ[K] Ω)) ↔ PerfectDeg1 (invMu p K Ω n) (powPairing (K := K) (Ω := Ω) n).swap) ∧
    (PerfectDeg2 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := Mu n Ω)
      (G := Ω ≃ₐ[K] Ω)) ↔ PerfectDeg2 (invMu p K Ω n) (powPairing (K := K) (Ω := Ω) n).swap) := by
  set τ := dualMuEquiv p Ω n
  have hτ : ∀ (g : Ω ≃ₐ[K] Ω) (k : TrivZMod n), τ (g • k) = g • τ k := by
    intro g k
    apply CartierDual.toHom.injective
    refine MonoidHom.ext fun ζ => ?_
    rw [CartierDual.smul_apply, TrivZMod.smul_eq]
    change ζ ^ _ = g • (g⁻¹ • ζ) ^ _
    rw [smul_pow', smul_inv_smul]
  have he : ∀ (ζ : Mu n Ω) (k : TrivZMod n),
      (CartierDual.evalPairing (G := Ω ≃ₐ[K] Ω)).toHom ζ (τ k) =
        (powPairing (K := K) n).swap.toHom ζ k := fun _ _ => rfl
  exact ⟨perfectDeg0_iff_of_equiv _ _ hτ _ _ he, perfectDeg1_iff_of_equiv _ _ hτ _ _ he,
    perfectDeg2_iff_of_equiv _ _ hτ _ _ he⟩

/-- **Local duality for `μ_n` in degree `1`**: `H¹(K, μ_n) × H¹(K, Hom(μ_n, μ_n)) → ℤ/n` is
perfect. -/
theorem perfectDeg1_eval_mu :
    PerfectDeg1 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := Mu n Ω)
      (G := Ω ≃ₐ[K] Ω)) :=
  (perfectDeg_eval_mu_iff n).2.1.2 (perfectDeg1_mu n)

/-- **Local duality for `μ_n` in degree `2`**: `H²(K, μ_n) × H⁰(K, Hom(μ_n, μ_n)) → ℤ/n` is
perfect. -/
theorem perfectDeg2_eval_mu :
    PerfectDeg2 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := Mu n Ω)
      (G := Ω ≃ₐ[K] Ω)) :=
  (perfectDeg_eval_mu_iff n).2.2.2 (perfectDeg2_mu n)

/-! ### `μ_n ⊆ K`: the remaining degrees -/

section MuInK

variable {n}
variable (hμ : Nat.card (rootsOfUnity n K) = n)
include hp hμ

theorem h0_mu_eq_top : H0 (Ω ≃ₐ[K] Ω) (Mu n Ω) = ⊤ := by
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [card_h0_mu, hμ, card_mu (p := p)]

theorem smul_mu_eq (g : Ω ≃ₐ[K] Ω) (ζ : Mu n Ω) : g • ζ = ζ := by
  have : ζ ∈ H0 (Ω ≃ₐ[K] Ω) (Mu n Ω) := by
    rw [h0_mu_eq_top (p := p) hμ]
    trivial
  exact this g

theorem trivZModMuEquiv_smul (g : Ω ≃ₐ[K] Ω) (k : TrivZMod n) :
    trivZModMuEquiv p Ω n (g • k) = g • trivZModMuEquiv p Ω n k := by
  rw [TrivZMod.smul_eq, smul_mu_eq (p := p) hμ]

/-- `H²(K, ℤ/n) ≃ ℤ/n` when `μ_n ⊆ K`. -/
noncomputable def h2TrivEquiv : ContH2 (Ω ≃ₐ[K] Ω) (TrivZMod n) ≃* Multiplicative (ZMod n) :=
  (MulEquiv.ofBijective _ (h2Map_bijective (trivZModMuEquiv p Ω n)
    (trivZModMuEquiv_smul (p := p) hμ))).trans
    (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n)))

theorem h2TrivEquiv_apply (β : ContH2 (Ω ≃ₐ[K] Ω) (TrivZMod n)) :
    h2TrivEquiv (p := p) hμ β = invMu p K Ω n
      (h2Map (trivZModMuEquiv p Ω n) (trivZModMuEquiv_smul (p := p) hμ) β) := rfl

/-- The cup product `μ_n(K) × H²(K, ℤ/n) → H²(K, μ_n)` in terms of `H²(K, ℤ/n) ≃ H²(K, μ_n)`. -/
theorem cup02_swap_eq (m : H0 (Ω ≃ₐ[K] Ω) (Mu n Ω)) (β : ContH2 (Ω ≃ₐ[K] Ω) (TrivZMod n)) :
    cup02 (powPairing (K := K) n).swap m β =
      h2Map (trivZModMuEquiv p Ω n) (trivZModMuEquiv_smul (p := p) hμ) β ^
        (Multiplicative.toAdd (TrivZMod.equiv ((trivZModMuEquiv p Ω n).symm m))).val := by
  induction β using induction_on with | h f => ?_
  rw [cup02_mk, h2Map, map_mk, ← map_pow]
  congr 1
  refine cocycles_ext fun a b => ?_
  change (m : Mu n Ω) ^ (Multiplicative.toAdd (TrivZMod.equiv (f (a, b)))).val =
    (trivZModMuEquiv p Ω n (f (a, b))) ^
      (Multiplicative.toAdd (TrivZMod.equiv ((trivZModMuEquiv p Ω n).symm m))).val
  conv_lhs => rw [← (trivZModMuEquiv p Ω n).apply_symm_apply (m : Mu n Ω)]
  rw [trivZModMuEquiv_apply, trivZModMuEquiv_apply, ← pow_mul, ← pow_mul, mul_comm]

/-- `H⁰(K, μ_n) ≃ ℤ/n` when `μ_n ⊆ K`. -/
noncomputable def h0MuEquiv : H0 (Ω ≃ₐ[K] Ω) (Mu n Ω) ≃* Multiplicative (ZMod n) :=
  ((MulEquiv.subgroupCongr (h0_mu_eq_top (p := p) hμ)).trans Subgroup.topEquiv).trans
    ((trivZModMuEquiv p Ω n).symm.trans TrivZMod.equiv)

theorem h0MuEquiv_apply (m : H0 (Ω ≃ₐ[K] Ω) (Mu n Ω)) :
    h0MuEquiv (p := p) hμ m = TrivZMod.equiv ((trivZModMuEquiv p Ω n).symm m) := rfl

/-- **`H⁰(K, μ_n) × H²(K, ℤ/n) → ℤ/n` is perfect** when `μ_n ⊆ K`. -/
theorem perfectDeg0_mu : PerfectDeg0 (invMu p K Ω n) (powPairing (K := K) (Ω := Ω) n).swap := by
  have h : (fun m : H0 (Ω ≃ₐ[K] Ω) (Mu n Ω) =>
      (invMu p K Ω n).comp (cup02 (powPairing (K := K) n).swap m)) =
      (fun k : ZMod n => (powMonoidHom k.val).comp (h2TrivEquiv (p := p) hμ).toMonoidHom) ∘
        (fun m => Multiplicative.toAdd (h0MuEquiv (p := p) hμ m)) := by
    funext m
    refine MonoidHom.ext fun β => ?_
    simp only [Function.comp_apply, MonoidHom.comp_apply, cup02_swap_eq (p := p) hμ, map_pow,
      powMonoidHom_apply, MulEquiv.coe_toMonoidHom, h2TrivEquiv_apply, h0MuEquiv_apply]
  rw [PerfectDeg0, h]
  exact (bijective_pow_comp _).comp
    (Multiplicative.toAdd.bijective.comp (h0MuEquiv (p := p) hμ).bijective)

/-- **`H²(K, ℤ/n) × H⁰(K, μ_n) → ℤ/n` is perfect** when `μ_n ⊆ K`. -/
theorem perfectDeg2_trivZMod : PerfectDeg2 (invMu p K Ω n) (powPairing (K := K) (Ω := Ω) n) :=
  bijective_pow_eval' n (h2TrivEquiv (p := p) hμ) (h0MuEquiv (p := p) hμ) _ fun β m => by
    rw [MonoidHom.comp_apply, cup20_apply, cup02_swap_eq (p := p) hμ, map_pow]
    rfl

/-- **Local Tate duality for `M = ℤ/n`** (all degrees) when `μ_n ⊆ K`. -/
theorem tateDualityFor_trivZMod : TateDualityFor p K Ω (TrivZMod n) n :=
  ⟨perfectDeg0_eval_trivZMod n, perfectDeg1_eval_trivZMod n,
    (perfectDeg_eval_trivZMod_iff n).2.2.2 (perfectDeg2_trivZMod (p := p) hμ)⟩

/-- **Local Tate duality for `M = μ_n`** (all degrees) when `μ_n ⊆ K`. -/
theorem tateDualityFor_mu : TateDualityFor p K Ω (Mu n Ω) n :=
  ⟨(perfectDeg_eval_mu_iff n).1.2 (perfectDeg0_mu (p := p) hμ), perfectDeg1_eval_mu n,
    perfectDeg2_eval_mu n⟩

/-- **The local Euler characteristic formula for `ℤ/n`** when `μ_n ⊆ K`:
`#H⁰(K, ℤ/n) · #H²(K, ℤ/n) / #H¹(K, ℤ/n) = |n|_K`. -/
theorem eulerCharacteristicFor_trivZMod : EulerCharacteristicFor p K Ω (TrivZMod n) := by
  refine ⟨finite_h1_trivZMod (p := p) n, Finite.of_equiv _ (h2TrivEquiv (p := p) hμ).symm.toEquiv,
    ?_⟩
  rw [card_h1_trivZMod (p := p), hμ, TrivZMod.h0_eq_top, Subgroup.card_top, TrivZMod.card,
    Nat.card_congr (h2TrivEquiv (p := p) hμ).toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

end MuInK

end PadicField
