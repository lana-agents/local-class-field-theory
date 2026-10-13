/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.CupProduct
import LocalClassFieldTheory.Brauer.DualityH1

/-!
# Local Tate duality and the local Euler characteristic formula: statements

Let `K` be a finite extension of `ℚ_p`, `Ω` an algebraic closure and `G_K = Gal(Ω/K)`.
For a finite discrete `G_K`-module `M` killed by `n`, the **Cartier dual**
`M^∨ = Hom(M, μ_n)` (`Brauer.CartierDual`, action `(g • φ)(m) = g • φ(g⁻¹ • m)`) pairs with `M`
by evaluation (`Brauer.evalPairing`), and the cup products land in `H²(K, μ_n) ≃ ℤ/n`
(`PadicField.h2MuEquiv`, cyclotomic rigidity).

* `Brauer.PerfectDeg0 χ e`, `Brauer.PerfectDeg1 χ e`, `Brauer.PerfectDeg2 χ e`: for a pairing
  `e : M × N → P` and `χ : H²(G, P) →* ℤ/n`, the map `H^i(G, M) → Hom(H^{2-i}(G, N), ℤ/n)`,
  `x ↦ (y ↦ χ(x ∪ y))`, is bijective.
* `PadicField.TateDualityFor p K Ω M n`: perfectness of `M × M^∨ → μ_n` in degrees `0, 1, 2`.
* **`PadicField.LocalTateDuality p K Ω`**: `TateDualityFor` for **every** finite discrete
  `G_K`-module (statement only: Tate–Poitou local duality, Serre, *Galois cohomology* II.5.2,
  Neukirch–Schmidt–Wingberg 7.2.6).
* `PadicField.EulerCharacteristicFor p K Ω M`: `H¹` and `H²` are finite and
  `#H¹ = #H⁰ · #H² · p^{v_p(#M) [K : ℚ_p]}`, i.e. `#H⁰ · #H² / #H¹ = |#M|_K`.
* **`PadicField.LocalEulerCharacteristic p K Ω`**: `EulerCharacteristicFor` for every finite
  discrete `G_K`-module (statement only: Tate's formula, Serre II.5.7, NSW 7.3.1).

The cases proved so far (`M = μ_n` and `M = ℤ/n` with trivial action) are in
`LocalClassFieldTheory.Duality.MuN`.

The Cartier dual of a finite smooth module is smooth (`Brauer.CartierDual.smoothAction`), which is
needed for the cup product `H¹(M) × H¹(M^∨) → H²(μ_n)` to be defined on locally constant cochains.
-/

open ContH2 groupCohomology KummerTheory

set_option linter.unusedSectionVars false

namespace Brauer

/-! ### Perfectness of cup product pairings -/

section Perfect

variable {G M N P : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [CommGroup N]
  [CommGroup P] [MulDistribMulAction G M] [MulDistribMulAction G N] [MulDistribMulAction G P]
  {n : ℕ}

/-- `H⁰(G, M) → Hom(H²(G, N), ℤ/n)`, `m ↦ (β ↦ χ(m ∪ β))`, is bijective. -/
def PerfectDeg0 (χ : ContH2 G P →* Multiplicative (ZMod n)) (e : GPairing G M N P) : Prop :=
  Function.Bijective fun m : H0 G M => χ.comp (cup02 e m)

/-- `H²(G, M) → Hom(H⁰(G, N), ℤ/n)`, `β ↦ (m ↦ χ(β ∪ m))`, is bijective. -/
def PerfectDeg2 (χ : ContH2 G P →* Multiplicative (ZMod n)) (e : GPairing G M N P) : Prop :=
  Function.Bijective fun β : ContH2 G M => χ.comp (cup20 e β)

variable [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalGroup M]
  [TopologicalSpace N] [DiscreteTopology N] [IsTopologicalGroup N] [SmoothAction G N]

/-- `H¹(G, M) → Hom(H¹(G, N), ℤ/n)`, `x ↦ (y ↦ χ(x ∪ y))`, is bijective. -/
def PerfectDeg1 (χ : ContH2 G P →* Multiplicative (ZMod n)) (e : GPairing G M N P) : Prop :=
  Function.Bijective fun x : ContH1 G M => χ.comp (cup11 e x)

end Perfect

/-! ### The Cartier dual -/

section Cartier

variable (n : ℕ) (Ω : Type*) [Field Ω] (M : Type*) [CommGroup M]

/-- The Cartier dual `M^∨ = Hom(M, μ_n)`. -/
def CartierDual : Type _ := M →* Mu n Ω

namespace CartierDual

instance : CommGroup (CartierDual n Ω M) := inferInstanceAs (CommGroup (M →* Mu n Ω))

instance : TopologicalSpace (CartierDual n Ω M) := ⊥

instance : DiscreteTopology (CartierDual n Ω M) := ⟨rfl⟩

variable {n Ω M}

/-- View an element of the dual as a homomorphism. -/
def toHom : CartierDual n Ω M ≃* (M →* Mu n Ω) := MulEquiv.refl _

variable {G : Type*} [Group G] [MulDistribMulAction G M] [MulDistribMulAction G (Mu n Ω)]

/-- `(g • φ)(m) = g • φ(g⁻¹ • m)`. -/
instance : MulDistribMulAction G (CartierDual n Ω M) where
  smul g φ := toHom.symm
    { toFun := fun m => g • toHom φ (g⁻¹ • m)
      map_one' := by simp
      map_mul' := fun a b => by simp [smul_mul'] }
  one_smul φ := by
    apply toHom.injective
    refine MonoidHom.ext fun m => ?_
    change (1 : G) • toHom φ ((1 : G)⁻¹ • m) = toHom φ m
    simp
  mul_smul g h φ := by
    apply toHom.injective
    refine MonoidHom.ext fun m => ?_
    change (g * h) • toHom φ ((g * h)⁻¹ • m) = g • (h • toHom φ (h⁻¹ • (g⁻¹ • m)))
    rw [mul_inv_rev, mul_smul, mul_smul]
  smul_mul g φ ψ := by
    apply toHom.injective
    refine MonoidHom.ext fun m => ?_
    change g • (toHom φ (g⁻¹ • m) * toHom ψ (g⁻¹ • m)) =
      g • toHom φ (g⁻¹ • m) * g • toHom ψ (g⁻¹ • m)
    rw [smul_mul']
  smul_one g := by
    apply toHom.injective
    refine MonoidHom.ext fun m => ?_
    change g • (1 : Mu n Ω) = 1
    rw [smul_one]

theorem smul_apply (g : G) (φ : CartierDual n Ω M) (m : M) :
    toHom (g • φ) m = g • toHom φ (g⁻¹ • m) := rfl

/-- **The Cartier dual of a finite smooth module is smooth.** -/
instance smoothAction [TopologicalSpace G] [IsTopologicalGroup G] [Finite M]
    [SmoothAction G M] [SmoothAction G (Mu n Ω)] : SmoothAction G (CartierDual n Ω M) := by
  refine ⟨fun φ => ?_⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  have hm : ∀ m : M, ∀ᶠ g in nhds g₀, toHom (g • φ) m = toHom (g₀ • φ) m := by
    intro m
    have h1 : IsLocallyConstant fun g : G => g⁻¹ • m :=
      (SmoothAction.isLocallyConstant_smul (G := G) m).comp_continuous continuous_inv
    have e1 := (IsLocallyConstant.iff_eventually_eq _).1 h1 g₀
    have e2 := (IsLocallyConstant.iff_eventually_eq _).1
      (SmoothAction.isLocallyConstant_smul (G := G) (toHom φ (g₀⁻¹ • m))) g₀
    filter_upwards [e1, e2] with g h1 h2
    rw [smul_apply, smul_apply, h1, h2]
  have hall : ∀ᶠ g in nhds g₀, ∀ m : M, toHom (g • φ) m = toHom (g₀ • φ) m :=
    Filter.eventually_all.2 hm
  filter_upwards [hall] with g hg
  exact toHom.injective (MonoidHom.ext hg)

/-- The evaluation pairing `M × M^∨ → μ_n`. -/
def evalPairing : GPairing G M (CartierDual n Ω M) (Mu n Ω) where
  toHom :=
    { toFun := fun m =>
        { toFun := fun φ => toHom φ m
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      map_one' := MonoidHom.ext fun φ => map_one (toHom φ)
      map_mul' := fun a b => MonoidHom.ext fun φ => map_mul (toHom φ) a b }
  map_smul' g m φ := by
    change toHom (g • φ) (g • m) = g • toHom φ m
    rw [smul_apply, inv_smul_smul]

@[simp]
theorem evalPairing_apply (m : M) (φ : CartierDual n Ω M) :
    (evalPairing (G := G)).toHom m φ = toHom φ m := rfl

end CartierDual

end Cartier

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsIntegral K Ω]

instance smoothAction_mu (n : ℕ) : SmoothAction (Ω ≃ₐ[K] Ω) (Mu n Ω) :=
  ⟨isLocallyConstant_smul_mu n⟩

end Brauer

namespace PadicField

open Brauer

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

/-- The invariant `H²(K, μ_n) ≃ ℤ/n` as a homomorphism. -/
noncomputable def invMu (n : ℕ) [NeZero n] : H2Mu K Ω n →* Multiplicative (ZMod n) :=
  (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n))).toMonoidHom

/-- **Local Tate duality for `M`**: for a finite discrete `G_K`-module `M` killed by `n`, the cup
product pairings `H^i(K, M) × H^{2-i}(K, M^∨) → H²(K, μ_n) ≃ ℤ/n` with the Cartier dual
`M^∨ = Hom(M, μ_n)` are perfect for `i = 0, 1, 2`. -/
def TateDualityFor (M : Type) [CommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M] (n : ℕ) [NeZero n] :
    Prop :=
  PerfectDeg0 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := M)) ∧
    PerfectDeg1 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := M)) ∧
    PerfectDeg2 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := M))

/-- **Local Tate duality** (Tate–Poitou), as a statement: for every finite discrete
`Gal(Ω/K)`-module `M` and every `n` killing `M`, the cup product pairings with the Cartier dual
into `H²(K, μ_n) ≃ ℤ/n` are perfect in degrees `0, 1, 2`. Proved here for `M = μ_n` and
`M = ℤ/n` in the degrees listed in `LocalClassFieldTheory.Duality.MuN`; the general case is
open in this repository. -/
def LocalTateDuality : Prop :=
  ∀ (M : Type) [CommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M] (n : ℕ) [NeZero n],
    (∀ m : M, m ^ n = 1) → TateDualityFor p K Ω M n

/-- **The local Euler characteristic formula for `M`**: `H¹(K, M)` and `H²(K, M)` are finite and
`#H¹ = #H⁰ · #H² · p^{v_p(#M) [K : ℚ_p]}`, i.e. `#H⁰ · #H² / #H¹ = |#M|_K`. -/
def EulerCharacteristicFor (M : Type*) [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] : Prop :=
  Finite (ContH1 (Ω ≃ₐ[K] Ω) M) ∧ Finite (ContH2 (Ω ≃ₐ[K] Ω) M) ∧
    Nat.card (ContH1 (Ω ≃ₐ[K] Ω) M) =
      Nat.card (H0 (Ω ≃ₐ[K] Ω) M) * Nat.card (ContH2 (Ω ≃ₐ[K] Ω) M) *
        p ^ (padicValNat p (Nat.card M) * Module.finrank ℚ_[p] K)

/-- **Tate's local Euler characteristic formula**, as a statement: for every finite discrete
`Gal(Ω/K)`-module `M`, `#H⁰(K, M) · #H²(K, M) / #H¹(K, M) = |#M|_K = p^{-v_p(#M) [K : ℚ_p]}`.
Proved here for `M = μ_n` (`PadicField.eulerCharacteristicFor_mu`); the general case is open in
this repository. -/
def LocalEulerCharacteristic : Prop :=
  ∀ (M : Type) [CommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M],
    EulerCharacteristicFor p K Ω M

end PadicField
