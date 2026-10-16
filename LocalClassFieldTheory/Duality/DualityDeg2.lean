/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.DualityDeg0
import LocalClassFieldTheory.Duality.EulerFinite
import LocalClassFieldTheory.Duality.Products

/-!
# Local duality in degrees `0` and `2` for all finite modules

Let `M` be a finite discrete `G_K`-module killed by `n` and `M' = Hom(M, μ_n)` its Cartier dual.
We prove that the cup product pairings

`H²(K, M) × H⁰(K, M') → H²(K, μ_n) ≃ ℤ/n`,   `H⁰(K, M) × H²(K, M') → ℤ/n`

are perfect (**`PadicField.perfectDeg2_all`**, **`PadicField.perfectDeg0_all`**). The proof uses
only `cd(G_K) ≤ 2`, Shapiro's lemma and the case of modules with trivial action:

1. `H⁰(K, X) → H²(K, Y)^∨` is injective for every left non-degenerate pairing
   (`PadicField.injective_perfectDeg0`); applied to `M' × M → μ_n` and transposed
   (`Brauer.surjective_of_transpose_injective`), `H²(K, M) → H⁰(K, M')^∨` is **surjective**
   (`PadicField.surjective_dualH2`).
2. Let `K'/K` be finite with `G_{K'}` acting trivially on `M` and on `μ_n`, and
   `B = CoInd_{G_{K'}} M`. Then `#H²(K, B) = #H²(K', M) ≤ #M` (`PadicField.card_h2_le_of_trivial`)
   and `#M ≤ #H⁰(K, B')` (`PadicField.card_le_card_h0_coInd_dual`), so the surjection of step 1
   is **bijective for `B`** (`PadicField.injective_dualH2_coInd`).
3. The product map `σ : B → M` is surjective; for `0 → N → B → M → 0` and the dual sequence
   `0 → M' → B' → N' → 0` (`PadicField.dualSES`) a four-lemma chase (naturality of the cup
   product, exactness of `H²(N) → H²(B) → H²(M) → 0` and of the dual of
   `0 → H⁰(M') → H⁰(B') → H⁰(N')`) gives **injectivity for `M`**
   (`PadicField.injective_dualH2_of_ses`, `PadicField.injective_dualH2`).
4. Degree `0`: injectivity is step 1 for `M × M' → μ_n`, surjectivity follows by transposition
   from step 3 for `M'` and the double duality `M ≃ M''` (`PadicField.evDual`).

(Serre, *Galois cohomology*, II.5.2, Theorem 2, the statement for `i = 0, 2`; the argument above
avoids the dualizing-module formalism.)
-/

open ContH2 KummerTheory

set_option linter.unusedSectionVars false

namespace Brauer

namespace CartierDual

variable {n : ℕ} {Ω : Type*} [Field Ω] {G : Type*} [Group G] [MulDistribMulAction G (Mu n Ω)]
variable {X Y : Type*} [CommGroup X] [CommGroup Y] [MulDistribMulAction G X]
  [MulDistribMulAction G Y]

/-- Precomposition `Y^∨ → X^∨` with `f : X → Y`. -/
def comap (f : X →* Y) : CartierDual n Ω Y →* CartierDual n Ω X where
  toFun φ := toHom.symm ((toHom φ).comp f)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem toHom_comap (f : X →* Y) (φ : CartierDual n Ω Y) (x : X) :
    toHom (comap f φ) x = toHom φ (f x) := rfl

theorem comap_smul (f : X →* Y) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) (g : G)
    (φ : CartierDual n Ω Y) : comap f (g • φ) = g • comap f φ := by
  apply toHom.injective
  refine MonoidHom.ext fun x => ?_
  rw [toHom_comap, smul_apply, smul_apply, toHom_comap, hf]

omit [MulDistribMulAction G (Mu n Ω)] [MulDistribMulAction G X] in
theorem pow_eq_one (φ : CartierDual n Ω X) : φ ^ n = 1 := by
  apply toHom.injective
  refine MonoidHom.ext fun x => Mu.ext ?_
  rw [map_pow, MonoidHom.pow_apply, map_pow, Mu.val_pow_n, map_one, MonoidHom.one_apply,
    map_one]

omit [MulDistribMulAction G (Mu n Ω)] [MulDistribMulAction G X] in
instance [NeZero n] [Finite X] : Finite (CartierDual n Ω X) :=
  Finite.of_injective (fun φ : CartierDual n Ω X => (toHom φ : X → Mu n Ω))
    (fun _ _ h => toHom.injective (MonoidHom.ext (congrFun h)))

end CartierDual

end Brauer

namespace PadicField

open Brauer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

local notation "G_K" => Ω ≃ₐ[K] Ω

/-! ### Generalities -/

include hp in
/-- `H²(K, B) → H²(K, C)` is surjective (`cd(G_K) ≤ 2`), for modules in arbitrary universes. -/
theorem h2Hom_surjective' {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] [MulDistribMulAction (Ω ≃ₐ[K] Ω) A]
    [SmoothAction (Ω ≃ₐ[K] Ω) A] [MulDistribMulAction (Ω ≃ₐ[K] Ω) B]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) C] [SmoothAction (Ω ≃ₐ[K] Ω) B]
    (S : GShortExact (Ω ≃ₐ[K] Ω) A B C) :
    Function.Surjective (h2Hom (G := Ω ≃ₐ[K] Ω) S.π S.map_smul_π) :=
  S.h2Hom_surjective_of_h3Trivial (localH3Vanishing p K Ω A)

theorem h0_pow_eq_one {n : ℕ} {X : Type*} [CommGroup X] [MulDistribMulAction (Ω ≃ₐ[K] Ω) X]
    (hX : ∀ x : X, x ^ n = 1) (x : H0 (Ω ≃ₐ[K] Ω) X) : x ^ n = 1 :=
  Subtype.ext (by simpa using hX x)

theorem h2_pow_eq_one {n : ℕ} {X : Type*} [CommGroup X] [MulDistribMulAction (Ω ≃ₐ[K] Ω) X]
    (hX : ∀ x : X, x ^ n = 1) (β : ContH2 (Ω ≃ₐ[K] Ω) X) : β ^ n = 1 := by
  induction β using induction_on with | h f => ?_
  rw [← map_pow, ← map_one (mk (G := Ω ≃ₐ[K] Ω) (M := X))]
  congr 1
  exact cocycles_ext fun a b => by simp [hX]

/-- Naturality of `∪ : H² × H⁰ → H²` for compatible maps of pairings. -/
theorem cup20_h2Hom_eq {G X X₂ Y₁ Y₂ P : Type*} [Group G] [TopologicalSpace G] [CommGroup X]
    [CommGroup X₂] [CommGroup Y₁] [CommGroup Y₂] [CommGroup P] [MulDistribMulAction G X]
    [MulDistribMulAction G X₂] [MulDistribMulAction G Y₁] [MulDistribMulAction G Y₂]
    [MulDistribMulAction G P] (f : X →* X₂) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (f' : Y₂ →* Y₁) (hf' : ∀ (g : G) (y : Y₂), f' (g • y) = g • f' y)
    (e₁ : GPairing G X Y₁ P) (e₂ : GPairing G X₂ Y₂ P)
    (h : ∀ x y, e₂.toHom (f x) y = e₁.toHom x (f' y)) (β : ContH2 G X) (y : H0 G Y₂) :
    cup20 e₂ (h2Hom f hf β) y = cup20 e₁ β (h0Hom f' hf' y) := by
  induction β using induction_on with | h c => ?_
  rw [cup20_apply, cup20_apply, h2Hom_mk, cup02_mk, cup02_mk]
  congr 1
  exact cocycles_ext fun a b => h _ _

/-- Naturality of `∪ : H⁰ × H² → H²` for compatible maps of pairings. -/
theorem cup02_h0Hom_eq {G X X₂ Y₁ Y₂ P : Type*} [Group G] [TopologicalSpace G] [CommGroup X]
    [CommGroup X₂] [CommGroup Y₁] [CommGroup Y₂] [CommGroup P] [MulDistribMulAction G X]
    [MulDistribMulAction G X₂] [MulDistribMulAction G Y₁] [MulDistribMulAction G Y₂]
    [MulDistribMulAction G P] (f : X →* X₂) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (f' : Y₂ →* Y₁) (hf' : ∀ (g : G) (y : Y₂), f' (g • y) = g • f' y)
    (e₁ : GPairing G X Y₁ P) (e₂ : GPairing G X₂ Y₂ P)
    (h : ∀ x y, e₂.toHom (f x) y = e₁.toHom x (f' y)) (x : H0 G X) (β : ContH2 G Y₂) :
    cup02 e₂ (h0Hom f hf x) β = cup02 e₁ x (h2Hom f' hf' β) := by
  induction β using induction_on with | h c => ?_
  rw [h2Hom_mk, cup02_mk, cup02_mk]
  congr 1
  exact cocycles_ext fun a b => h _ _

/-! ### The dual of a short exact sequence -/

section DualSES

variable {n : ℕ} [NeZero n]
variable {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C] [Finite B]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) A] [MulDistribMulAction (Ω ≃ₐ[K] Ω) B]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) C]

variable (n) in
include hp in
/-- **The dual short exact sequence** `0 → C' → B' → A' → 0` of `0 → A → B → C → 0`, for `B`
finite and killed by `n` (Cartier duals `X' = Hom(X, μ_n)`). -/
noncomputable def dualSES (S : GShortExact (Ω ≃ₐ[K] Ω) A B C) (hB : ∀ b : B, b ^ n = 1) :
    GShortExact (Ω ≃ₐ[K] Ω) (CartierDual n Ω C) (CartierDual n Ω B) (CartierDual n Ω A) where
  i := CartierDual.comap S.π
  π := CartierDual.comap S.i
  map_smul_i := CartierDual.comap_smul S.π S.map_smul_π
  map_smul_π := CartierDual.comap_smul S.i S.map_smul_i
  injective φ φ' h := by
    apply CartierDual.toHom.injective
    refine MonoidHom.ext fun c => ?_
    obtain ⟨b, rfl⟩ := S.surjective c
    exact congrArg (fun ψ => CartierDual.toHom ψ b) h
  surjective ψ := by
    haveI := hasEnoughRootsOfUnity_omega (p := p) (Ω := Ω) n
    let ψ' : S.i.range →* Mu n Ω := (CartierDual.toHom ψ).comp
      (MonoidHom.ofInjective S.injective).symm.toMonoidHom
    obtain ⟨φ, hφ⟩ := exists_extend_mu hB S.i.range ψ'
    refine ⟨CartierDual.toHom.symm φ, CartierDual.toHom.injective (MonoidHom.ext fun a => ?_)⟩
    rw [CartierDual.toHom_comap]
    have := hφ ⟨S.i a, a, rfl⟩
    simp only at this
    rw [MulEquiv.apply_symm_apply, this]
    simp only [ψ', MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    congr 1
    rw [MulEquiv.symm_apply_eq]
    rfl
  exact ψ := by
    constructor
    · intro hψ
      have hker : S.π.ker ≤ (CartierDual.toHom ψ).ker := by
        intro b hb
        obtain ⟨a, rfl⟩ := (S.exact b).1 hb
        have := congrArg (fun χ => CartierDual.toHom χ a) hψ
        exact this
      let φ : C →* Mu n Ω := (QuotientGroup.lift S.π.ker (CartierDual.toHom ψ) hker).comp
        (QuotientGroup.quotientKerEquivOfSurjective S.π S.surjective).symm.toMonoidHom
      refine ⟨CartierDual.toHom.symm φ, CartierDual.toHom.injective (MonoidHom.ext fun b => ?_)⟩
      rw [CartierDual.toHom_comap, MulEquiv.apply_symm_apply]
      simp only [φ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
      have e : (QuotientGroup.quotientKerEquivOfSurjective S.π S.surjective).symm (S.π b) =
          (b : B ⧸ S.π.ker) := by
        rw [MulEquiv.symm_apply_eq]
        rfl
      rw [e, QuotientGroup.lift_mk]
    · rintro ⟨φ, rfl⟩
      apply CartierDual.toHom.injective
      refine MonoidHom.ext fun a => ?_
      change CartierDual.toHom φ (S.π (S.i a)) = 1
      rw [S.π_i, map_one]

end DualSES

/-! ### The duality maps -/

section Maps

variable (p K Ω) (n : ℕ) [NeZero n]
variable (M : Type*) [CommGroup M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M]

/-- The evaluation pairing `M × M' → μ_n`. -/
abbrev evalP : GPairing (Ω ≃ₐ[K] Ω) M (CartierDual n Ω M) (Mu n Ω) :=
  CartierDual.evalPairing

/-- `H²(K, M) → Hom(H⁰(K, M'), ℤ/n)`, `β ↦ (φ ↦ inv(β ∪ φ))`. -/
noncomputable def dualH2 :
    ContH2 (Ω ≃ₐ[K] Ω) M →* (H0 (Ω ≃ₐ[K] Ω) (CartierDual n Ω M) →* Multiplicative (ZMod n)) where
  toFun β := (invMu p K Ω n).comp (cup20 (evalP K Ω n M) β)
  map_one' := MonoidHom.ext fun φ => by
    simp only [MonoidHom.coe_comp, Function.comp_apply, cup20_apply, map_one,
      MonoidHom.one_apply]
  map_mul' β β' := MonoidHom.ext fun φ => by
    simp only [MonoidHom.coe_comp, Function.comp_apply, cup20_apply, map_mul,
      MonoidHom.mul_apply]

/-- `H⁰(K, M) → Hom(H²(K, M'), ℤ/n)`, `m ↦ (β ↦ inv(m ∪ β))`. -/
noncomputable def dualH0 :
    H0 (Ω ≃ₐ[K] Ω) M →* (ContH2 (Ω ≃ₐ[K] Ω) (CartierDual n Ω M) →* Multiplicative (ZMod n)) where
  toFun m := (invMu p K Ω n).comp (cup02 (evalP K Ω n M) m)
  map_one' := MonoidHom.ext fun β => by
    simp only [MonoidHom.coe_comp, Function.comp_apply, cup02_one_left, map_one,
      MonoidHom.one_apply]
  map_mul' m m' := MonoidHom.ext fun β => by
    simp only [MonoidHom.coe_comp, Function.comp_apply, cup02_mul_left, map_mul,
      MonoidHom.mul_apply]

theorem dualH2_apply (β : ContH2 (Ω ≃ₐ[K] Ω) M) (φ : H0 (Ω ≃ₐ[K] Ω) (CartierDual n Ω M)) :
    dualH2 p K Ω n M β φ = invMu p K Ω n (cup20 (evalP K Ω n M) β φ) := rfl

theorem dualH0_apply (m : H0 (Ω ≃ₐ[K] Ω) M) (β : ContH2 (Ω ≃ₐ[K] Ω) (CartierDual n Ω M)) :
    dualH0 p K Ω n M m β = invMu p K Ω n (cup02 (evalP K Ω n M) m β) := rfl

end Maps

/-! ### Step 1: surjectivity in degree `2` -/

section Surj

variable {n : ℕ} [NeZero n]
variable {M : Type*} [CommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]

include hp in
/-- **`H²(K, M) → H⁰(K, M')^∨` is surjective.** -/
theorem surjective_dualH2 : Function.Surjective (dualH2 p K Ω n M) := by
  haveI := finite_h2 (p := p) (K := K) (Ω := Ω) M
  refine surjective_of_transpose_injective (h0_pow_eq_one CartierDual.pow_eq_one) _ ?_
  intro φ hφ
  have hinj := injective_perfectDeg0 (p := p) (K := K) (Ω := Ω) (evalP K Ω n M).swap
    (fun ψ hψ => by
      by_contra h
      push Not at h
      exact hψ (CartierDual.toHom.injective (MonoidHom.ext fun m => h m)))
  apply hinj
  refine MonoidHom.ext fun β => ?_
  simp only [MonoidHom.coe_comp, Function.comp_apply, cup02_one_left, map_one]
  exact hφ β

end Surj

/-! ### Step 2: a four-lemma chase -/

section Chase

variable {n : ℕ} [NeZero n]
variable {N B M : Type*} [CommGroup N] [CommGroup B] [CommGroup M] [Finite N] [Finite B]
  [Finite M] [TopologicalSpace N] [DiscreteTopology N] [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace M] [DiscreteTopology M]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) N] [MulDistribMulAction (Ω ≃ₐ[K] Ω) B]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) N]
  [SmoothAction (Ω ≃ₐ[K] Ω) B] [SmoothAction (Ω ≃ₐ[K] Ω) M]

include hp in
/-- **The four-lemma step**: for `0 → N → B → M → 0` with `B` killed by `n`, if
`H²(B) → H⁰(B')^∨` is injective and `H²(N) → H⁰(N')^∨` is surjective, then `H²(M) → H⁰(M')^∨` is
injective. -/
theorem injective_dualH2_of_ses (S : GShortExact (Ω ≃ₐ[K] Ω) N B M) (hB : ∀ b : B, b ^ n = 1)
    (hBinj : Function.Injective (dualH2 p K Ω n B))
    (hNsurj : Function.Surjective (dualH2 p K Ω n N)) :
    Function.Injective (dualH2 p K Ω n M) := by
  rw [injective_iff_map_eq_one]
  intro β hβ
  obtain ⟨γ, rfl⟩ := h2Hom_surjective' (p := p) S β
  set S' := dualSES (p := p) n S hB
  set ξ := dualH2 p K Ω n B γ
  have hξ : ∀ φ, ξ (h0Hom S'.i S'.map_smul_i φ) = 1 := by
    intro φ
    have h1 := DFunLike.congr_fun hβ φ
    rw [dualH2_apply, cup20_h2Hom_eq S.π S.map_smul_π S'.i S'.map_smul_i (evalP K Ω n B)
      (evalP K Ω n M) (fun _ _ => rfl)] at h1
    exact h1
  obtain ⟨ξ', hξ'⟩ := exists_factor_zmod (h0_pow_eq_one CartierDual.pow_eq_one)
    (h0Hom S'.i S'.map_smul_i) (h0Hom S'.π S'.map_smul_π) S'.exact_h0B ξ hξ
  obtain ⟨η, hη⟩ := hNsurj ξ'
  have e : ∀ ψ, dualH2 p K Ω n B (h2Hom S.i S.map_smul_i η) ψ = ξ ψ := by
    intro ψ
    rw [dualH2_apply p K Ω n B (h2Hom S.i S.map_smul_i η) ψ,
      cup20_h2Hom_eq S.i S.map_smul_i S'.π S'.map_smul_π (evalP K Ω n N) (evalP K Ω n B)
        (fun _ _ => rfl), ← dualH2_apply, hη, ← hξ']
    rfl
  have hγ : γ / h2Hom S.i S.map_smul_i η = 1 := by
    apply hBinj
    rw [map_one]
    refine MonoidHom.ext fun ψ => ?_
    rw [map_div, MonoidHom.div_apply, MonoidHom.one_apply, e, div_self']
  rw [div_eq_one] at hγ
  rw [hγ]
  have : h2Hom S.i S.map_smul_i η ∈ (h2Hom (G := Ω ≃ₐ[K] Ω) S.π S.map_smul_π).ker := by
    rw [S.exact_h2B]
    exact ⟨η, rfl⟩
  exact this

end Chase

/-! ### Step 3: coinduced modules -/

section Trivial

variable {n : ℕ}

universe u

include hp in
/-- `#H²(K, ∏ Z_j) ≤ #∏ Z_j` if `#H²(K, Z_j) ≤ #Z_j` for all `j`. -/
theorem card_h2_pi_le : ∀ (k : ℕ) (Z : Fin k → Type u) [∀ j, CommGroup (Z j)]
    [∀ j, Finite (Z j)] [∀ j, MulDistribMulAction (Ω ≃ₐ[K] Ω) (Z j)],
    (∀ j, Nat.card (ContH2 (Ω ≃ₐ[K] Ω) (Z j)) ≤ Nat.card (Z j)) →
    Nat.card (ContH2 (Ω ≃ₐ[K] Ω) (∀ j, Z j)) ≤ Nat.card (∀ j, Z j)
  | 0, Z, _, _, _, _ => by
    haveI : Subsingleton (∀ j, Z j) := ⟨fun a b => funext fun j => j.elim0⟩
    haveI := subsingleton_h2_of_subsingleton (K := K) (Ω := Ω) (N := ∀ j, Z j)
    rw [Nat.card_unique (α := ∀ j, Z j)]
    haveI : Finite (ContH2 (Ω ≃ₐ[K] Ω) (∀ j, Z j)) := Finite.of_subsingleton
    exact Finite.card_le_one_iff_subsingleton.2 inferInstance
  | k + 1, Z, _, _, _, h => by
    have ih := card_h2_pi_le k (fun j => Z j.succ) fun j => h j.succ
    have e1 : Nat.card (ContH2 (Ω ≃ₐ[K] Ω) (∀ j, Z j)) =
        Nat.card (ContH2 (Ω ≃ₐ[K] Ω) (Z 0 × ∀ j : Fin k, Z j.succ)) :=
      Nat.card_congr (Equiv.ofBijective _ (h2Map_bijective (piFinSuccMulEquiv Z)
        (fun _ _ => rfl)))
    have e2 : Nat.card (ContH2 (Ω ≃ₐ[K] Ω) (Z 0 × ∀ j : Fin k, Z j.succ)) =
        Nat.card (ContH2 (Ω ≃ₐ[K] Ω) (Z 0)) *
          Nat.card (ContH2 (Ω ≃ₐ[K] Ω) (∀ j : Fin k, Z j.succ)) := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (Equiv.ofBijective _ h2_prod_bijective)
    have e3 : Nat.card (∀ j, Z j) = Nat.card (Z 0) * Nat.card (∀ j : Fin k, Z j.succ) := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (piFinSuccMulEquiv Z).toEquiv
    rw [e1, e2, e3]
    exact Nat.mul_le_mul (h 0) ih

include hp in
/-- **`#H²(K, M) ≤ #M` for a finite module with trivial action** (by the structure theorem and
`#H²(K, ℤ/m) = #μ_m(K)`, `PadicField.card_h2_trivZMod`). -/
theorem card_h2_le_of_trivial (M : Type*) [CommGroup M] [Finite M]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] (htriv : ∀ (g : Ω ≃ₐ[K] Ω) (m : M), g • m = m) :
    Nat.card (ContH2 (Ω ≃ₐ[K] Ω) M) ≤ Nat.card M := by
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite M
  let eι := Fintype.equivFin ι
  let m : Fin (Fintype.card ι) → ℕ := fun j => n (eι.symm j)
  haveI : ∀ j, NeZero (m j) := fun j => ⟨by have := hn (eι.symm j); simp only [m]; omega⟩
  have hm : ∀ j, Nat.card (ContH2 (Ω ≃ₐ[K] Ω) (TrivZMod (m j))) ≤ Nat.card (TrivZMod (m j)) := by
    intro j
    rw [card_h2_trivZMod (p := p) (K := K) (Ω := Ω) (m j), TrivZMod.card]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _))
      (card_rootsOfUnity_dvd (p := p) (Ω := Ω) (K := K) (m j))
  have hP := card_h2_pi_le (p := p) (K := K) (Ω := Ω) (Fintype.card ι)
    (fun j => TrivZMod (m j)) hm
  let τ' : ((i : ι) → Multiplicative (ZMod (n i))) ≃* ∀ j, TrivZMod (m j) :=
    { Equiv.piCongrLeft' (fun i => Multiplicative (ZMod (n i))) eι with
      map_mul' := fun _ _ => rfl }
  let τ : M ≃* ∀ j, TrivZMod (m j) := e.trans τ'
  have hτ : ∀ (g : Ω ≃ₐ[K] Ω) (x : M), τ (g • x) = g • τ x := fun g x => by rw [htriv]; rfl
  rw [Nat.card_congr (Equiv.ofBijective _ (h2Map_bijective τ hτ)), Nat.card_congr τ.toEquiv]
  exact hP

end Trivial

section CoInd

variable {n : ℕ} [NeZero n]
variable {M : Type*} [CommGroup M] [Finite M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M]

/-- The map `M' → (CoInd_U M)'`, `φ ↦ (F ↦ ∏_c (c.out • φ)(F c))`. -/
noncomputable def coIndDualMap (U : Subgroup (Ω ≃ₐ[K] Ω)) [Fintype ((Ω ≃ₐ[K] Ω) ⧸ U)]
    (φ : CartierDual n Ω M) : CartierDual n Ω (ContH2.CoInd U M) :=
  CartierDual.toHom.symm
    { toFun := fun F => ∏ c : (Ω ≃ₐ[K] Ω) ⧸ U, CartierDual.toHom (c.out • φ) (F c)
      map_one' := Finset.prod_eq_one fun c _ => map_one (CartierDual.toHom (c.out • φ))
      map_mul' := fun F F' => by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun c _ =>
          map_mul (CartierDual.toHom (c.out • φ)) (F c) (F' c) }

theorem toHom_coIndDualMap (U : Subgroup (Ω ≃ₐ[K] Ω)) [Fintype ((Ω ≃ₐ[K] Ω) ⧸ U)]
    (φ : CartierDual n Ω M) (F : ContH2.CoInd U M) :
    CartierDual.toHom (coIndDualMap U φ) F =
      ∏ c : (Ω ≃ₐ[K] Ω) ⧸ U, CartierDual.toHom (c.out • φ) (F c) := rfl

variable (U : Subgroup (Ω ≃ₐ[K] Ω)) [Fintype ((Ω ≃ₐ[K] Ω) ⧸ U)]
  (htriv : ∀ u ∈ U, ∀ m : M, u • m = m) (hmu : ∀ u ∈ U, ∀ ζ : Mu n Ω, u • ζ = ζ)

omit [Fintype ((Ω ≃ₐ[K] Ω) ⧸ U)] in
include htriv hmu in
theorem smul_dual_eq_of_mem (u : Ω ≃ₐ[K] Ω) (hu : u ∈ U) (φ : CartierDual n Ω M) :
    u • φ = φ := by
  apply CartierDual.toHom.injective
  refine MonoidHom.ext fun m => ?_
  rw [CartierDual.smul_apply, htriv u⁻¹ (U.inv_mem hu), hmu u hu]

omit [Fintype ((Ω ≃ₐ[K] Ω) ⧸ U)] in
include htriv hmu in
theorem smul_dual_eq_of_mk_eq {s s' : Ω ≃ₐ[K] Ω} (h : (QuotientGroup.mk s : (Ω ≃ₐ[K] Ω) ⧸ U) =
    QuotientGroup.mk s') (φ : CartierDual n Ω M) : s • φ = s' • φ := by
  have hu : s⁻¹ * s' ∈ U := QuotientGroup.eq.1 h
  have : s' = s * (s⁻¹ * s') := by group
  rw [this, mul_smul, smul_dual_eq_of_mem U htriv hmu _ hu]

include htriv hmu in
theorem coIndDualMap_mem_h0 (φ : CartierDual n Ω M) :
    coIndDualMap U φ ∈ H0 (Ω ≃ₐ[K] Ω) (CartierDual n Ω (ContH2.CoInd U M)) := by
  intro g
  apply CartierDual.toHom.injective
  refine MonoidHom.ext fun F => ?_
  rw [CartierDual.smul_apply, toHom_coIndDualMap, toHom_coIndDualMap, Finset.smul_prod']
  refine Fintype.prod_equiv (MulAction.toPerm g) _ _ fun c => ?_
  rw [MulAction.toPerm_apply]
  change g • CartierDual.toHom (c.out • φ) (g⁻¹ • F (g⁻¹⁻¹ • c)) =
    CartierDual.toHom ((g • c).out • φ) (F (g • c))
  rw [inv_inv, ← CartierDual.smul_apply, ← mul_smul]
  have h : (QuotientGroup.mk (g * c.out) : (Ω ≃ₐ[K] Ω) ⧸ U) = QuotientGroup.mk (g • c).out := by
    rw [QuotientGroup.out_eq']
    change g • (QuotientGroup.mk c.out : (Ω ≃ₐ[K] Ω) ⧸ U) = g • c
    rw [QuotientGroup.out_eq']
  rw [smul_dual_eq_of_mk_eq U htriv hmu h]

include htriv hmu in
theorem coIndDualMap_injective : Function.Injective (coIndDualMap (n := n) (M := M) U) := by
  classical
  intro φ φ' h
  apply CartierDual.toHom.injective
  refine MonoidHom.ext fun m => ?_
  set o : (Ω ≃ₐ[K] Ω) ⧸ U := QuotientGroup.mk 1
  have key : ∀ ψ : CartierDual n Ω M, CartierDual.toHom (coIndDualMap U ψ)
      (Pi.mulSingle o m : ContH2.CoInd U M) = CartierDual.toHom ψ m := by
    intro ψ
    rw [toHom_coIndDualMap, Fintype.prod_eq_single o (fun c hc => ?_)]
    · rw [Pi.mulSingle_eq_same,
        smul_dual_eq_of_mk_eq U htriv hmu (s' := 1) (QuotientGroup.out_eq' o), one_smul]
    · change CartierDual.toHom (c.out • ψ) ((Pi.mulSingle o m : (Ω ≃ₐ[K] Ω) ⧸ U → M) c) = 1
      rw [Pi.mulSingle_eq_of_ne hc, map_one]
  rw [← key φ, ← key φ', h]

omit [Fintype ((Ω ≃ₐ[K] Ω) ⧸ U)] in
include hp htriv hmu in
/-- **`#M ≤ #H⁰(K, (CoInd_U M)')`** when `U` acts trivially on `M` and on `μ_n`. -/
theorem card_le_card_h0_coInd_dual [Finite ((Ω ≃ₐ[K] Ω) ⧸ U)] (hM : ∀ m : M, m ^ n = 1) :
    Nat.card M ≤ Nat.card (H0 (Ω ≃ₐ[K] Ω) (CartierDual n Ω (ContH2.CoInd U M))) := by
  letI : Fintype ((Ω ≃ₐ[K] Ω) ⧸ U) := Fintype.ofFinite _
  haveI := hasEnoughRootsOfUnity_omega (p := p) (Ω := Ω) n
  rw [← card_hom_mu (Ω := Ω) hM]
  change Nat.card (CartierDual n Ω M) ≤ _
  haveI : Finite (CartierDual n Ω (ContH2.CoInd U M)) := by
    haveI : Finite (ContH2.CoInd U M) := inferInstanceAs (Finite ((Ω ≃ₐ[K] Ω) ⧸ U → M))
    infer_instance
  exact Nat.card_le_card_of_injective
    (fun φ => (⟨coIndDualMap U φ, coIndDualMap_mem_h0 U htriv hmu φ⟩ :
      H0 (Ω ≃ₐ[K] Ω) (CartierDual n Ω (ContH2.CoInd U M))))
    (fun φ φ' h => coIndDualMap_injective U htriv hmu (congrArg Subtype.val h))

end CoInd

/-! ### Step 3: injectivity in degree `2` -/

section Inj

variable {n : ℕ} [NeZero n]

include hp in
/-- **Duality in degree `2` for `CoInd_{G_{K'}} M`** when `G_{K'}` acts trivially on `M` and `μ_n`:
`H²(K, B) → H⁰(K, B')^∨` is injective. -/
theorem injective_dualH2_coInd {M : Type*} [CommGroup M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]
    (hM : ∀ m : M, m ^ n = 1) (K' : IntermediateField K Ω) [FiniteDimensional K K']
    (htriv : ∀ u ∈ K'.fixingSubgroup, ∀ m : M, u • m = m)
    (hmu : ∀ u ∈ K'.fixingSubgroup, ∀ ζ : Mu n Ω, u • ζ = ζ) :
    haveI := ContH2.CoInd.smoothAction (A := M) K'.fixingSubgroup_isOpen
    Function.Injective (dualH2 p K Ω n (ContH2.CoInd K'.fixingSubgroup M)) := by
  set U := K'.fixingSubgroup
  haveI := ContH2.CoInd.smoothAction (A := M) K'.fixingSubgroup_isOpen
  haveI : Finite (ContH2.CoInd U M) := inferInstanceAs (Finite ((Ω ≃ₐ[K] Ω) ⧸ U → M))
  haveI := finite_h2 (p := p) (K := K) (Ω := Ω) (ContH2.CoInd U M)
  have hs := surjective_dualH2 (p := p) (K := K) (Ω := Ω) (n := n) (M := ContH2.CoInd U M)
  refine (hs.bijective_of_nat_card_le ?_).1
  rw [card_hom_zmod (h0_pow_eq_one CartierDual.pow_eq_one)]
  have h1 : Nat.card (ContH2 (Ω ≃ₐ[K] Ω) (ContH2.CoInd U M)) ≤ Nat.card M := by
    letI := resAction K' M
    rw [card_h2_coInd (resCompat_resAction K' M)]
    exact card_h2_le_of_trivial (p := p) (K := K') (Ω := Ω) M fun σ m =>
      htriv _ ((IntermediateField.fixingSubgroupEquiv K').symm σ).2 m
  exact h1.trans (card_le_card_h0_coInd_dual (p := p) U htriv hmu hM)

/-- The product map `σ : CoInd_U M → M`, `F ↦ ∏_c F(c)`. -/
noncomputable def coIndProd {M : Type*} [CommGroup M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M]
    (U : Subgroup (Ω ≃ₐ[K] Ω)) [Fintype ((Ω ≃ₐ[K] Ω) ⧸ U)] : ContH2.CoInd U M →* M where
  toFun F := ∏ c : (Ω ≃ₐ[K] Ω) ⧸ U, F c
  map_one' := Finset.prod_eq_one fun _ _ => rfl
  map_mul' _ _ := Finset.prod_mul_distrib

theorem coIndProd_smul {M : Type*} [CommGroup M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M]
    (U : Subgroup (Ω ≃ₐ[K] Ω)) [Fintype ((Ω ≃ₐ[K] Ω) ⧸ U)] (g : Ω ≃ₐ[K] Ω)
    (F : ContH2.CoInd U M) : coIndProd U (g • F) = g • coIndProd U F := by
  change ∏ c, g • F (g⁻¹ • c) = g • ∏ c, F c
  rw [Finset.smul_prod']
  exact Fintype.prod_equiv (MulAction.toPerm g⁻¹) _ _ fun c => rfl

theorem coIndProd_surjective {M : Type*} [CommGroup M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M]
    (U : Subgroup (Ω ≃ₐ[K] Ω)) [Fintype ((Ω ≃ₐ[K] Ω) ⧸ U)] :
    Function.Surjective (coIndProd (M := M) U) := by
  classical
  intro m
  set o : (Ω ≃ₐ[K] Ω) ⧸ U := QuotientGroup.mk 1
  refine ⟨(Pi.mulSingle o m : (Ω ≃ₐ[K] Ω) ⧸ U → M), ?_⟩
  change ∏ c, (Pi.mulSingle o m : (Ω ≃ₐ[K] Ω) ⧸ U → M) c = m
  rw [Fintype.prod_eq_single o (fun c hc => by rw [Pi.mulSingle_eq_of_ne hc]),
    Pi.mulSingle_eq_same]

include hp in
/-- **Duality in degree `2`, injectivity**: `H²(K, M) → H⁰(K, M')^∨` is injective for every
finite discrete `G_K`-module `M` killed by `n`. -/
theorem injective_dualH2 (M : Type*) [CommGroup M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]
    (hM : ∀ m : M, m ^ n = 1) : Function.Injective (dualH2 p K Ω n M) := by
  -- a finite `K'` with `G_{K'}` acting trivially on `M` and on `μ_n`
  have hU0 : IsOpen (((MulAction.toPermHom (Ω ≃ₐ[K] Ω) M).ker ⊓
      (MulAction.toPermHom (Ω ≃ₐ[K] Ω) (Mu n Ω)).ker : Subgroup (Ω ≃ₐ[K] Ω)) :
        Set (Ω ≃ₐ[K] Ω)) := by
    rw [Subgroup.coe_inf]
    exact (isOpen_ker_toPermHom (G := Ω ≃ₐ[K] Ω) (A := M)).inter
      (isOpen_ker_toPermHom (G := Ω ≃ₐ[K] Ω) (A := Mu n Ω))
  obtain ⟨K', hK', hU⟩ := exists_fixingSubgroup_eq _ hU0
  set U := K'.fixingSubgroup
  have htriv : ∀ u ∈ U, ∀ m : M, u • m = m := fun u hu m =>
    smul_eq_of_mem_ker (Subgroup.mem_inf.1 (hU ▸ hu)).1 m
  have hmu : ∀ u ∈ U, ∀ ζ : Mu n Ω, u • ζ = ζ := fun u hu ζ =>
    smul_eq_of_mem_ker (Subgroup.mem_inf.1 (hU ▸ hu)).2 ζ
  -- the short exact sequence `0 → N → CoInd_U M → M → 0`
  haveI := ContH2.CoInd.smoothAction (A := M) K'.fixingSubgroup_isOpen
  haveI : Finite (ContH2.CoInd U M) := inferInstanceAs (Finite ((Ω ≃ₐ[K] Ω) ⧸ U → M))
  have hB : ∀ F : ContH2.CoInd U M, F ^ n = 1 := fun F => funext fun c => hM (F c)
  set σ := coIndProd (M := M) U
  set N := σ.ker
  have hN : IsGStable (G := Ω ≃ₐ[K] Ω) N := fun g F hF => by
    rw [MonoidHom.mem_ker] at hF ⊢
    rw [coIndProd_smul, hF, smul_one]
  letI := subAction N hN
  haveI := smoothAction_sub N hN
  let S : GShortExact (Ω ≃ₐ[K] Ω) N (ContH2.CoInd U M) M :=
    { i := N.subtype
      π := σ
      map_smul_i := fun _ _ => rfl
      map_smul_π := coIndProd_smul U
      injective := Subtype.val_injective
      surjective := coIndProd_surjective U
      exact := fun F => by rw [Subgroup.range_subtype]; exact MonoidHom.mem_ker.symm }
  exact injective_dualH2_of_ses (p := p) S hB
    (injective_dualH2_coInd (p := p) hM K' htriv hmu)
    (surjective_dualH2 (p := p) (K := K) (Ω := Ω) (n := n) (M := N))

include hp in
/-- **Local duality in degree `2`**: `H²(K, M) × H⁰(K, M') → ℤ/n` is perfect. -/
theorem perfectDeg2_all (M : Type*) [CommGroup M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]
    (hM : ∀ m : M, m ^ n = 1) :
    PerfectDeg2 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := M)
      (G := Ω ≃ₐ[K] Ω)) :=
  ⟨injective_dualH2 (p := p) M hM, surjective_dualH2 (p := p)⟩

end Inj

/-! ### Double duality and degree `0` -/

section Deg0

variable {n : ℕ} [NeZero n]
variable (M : Type*) [CommGroup M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M]

/-- The double duality map `M → M''`, `m ↦ (φ ↦ φ(m))`. -/
def evDual : M →* CartierDual n Ω (CartierDual n Ω M) where
  toFun m := CartierDual.toHom.symm
    { toFun := fun φ => CartierDual.toHom φ m
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  map_one' := CartierDual.toHom.injective (MonoidHom.ext fun φ => map_one (CartierDual.toHom φ))
  map_mul' m m' := CartierDual.toHom.injective
    (MonoidHom.ext fun φ => map_mul (CartierDual.toHom φ) m m')

theorem toHom_evDual (m : M) (φ : CartierDual n Ω M) :
    CartierDual.toHom (evDual (n := n) (Ω := Ω) M m) φ = CartierDual.toHom φ m := rfl

theorem evDual_smul (g : Ω ≃ₐ[K] Ω) (m : M) :
    evDual (n := n) (Ω := Ω) M (g • m) = g • evDual M m := by
  apply CartierDual.toHom.injective
  refine MonoidHom.ext fun φ => ?_
  rw [CartierDual.smul_apply, toHom_evDual, toHom_evDual, CartierDual.smul_apply, inv_inv,
    smul_inv_smul]

include hp in
theorem evDual_bijective [Finite M] (hM : ∀ m : M, m ^ n = 1) :
    Function.Bijective (evDual (n := n) (Ω := Ω) M) := by
  haveI := hasEnoughRootsOfUnity_omega (p := p) (Ω := Ω) n
  have hinj : Function.Injective (evDual (n := n) (Ω := Ω) M) := by
    rw [injective_iff_map_eq_one]
    intro m hm
    by_contra h
    obtain ⟨φ, hφ⟩ := exists_hom_mu_ne_one (Ω := Ω) hM h
    apply hφ
    have := congrArg (fun Ψ => CartierDual.toHom Ψ (CartierDual.toHom.symm φ)) hm
    exact this
  refine hinj.bijective_of_nat_card_le ?_
  change Nat.card (CartierDual n Ω M →* Mu n Ω) ≤ Nat.card M
  rw [card_hom_mu (Ω := Ω) (A := CartierDual n Ω M) CartierDual.pow_eq_one]
  change Nat.card (M →* Mu n Ω) ≤ Nat.card M
  rw [card_hom_mu hM]

include hp in
/-- **Local duality in degree `0`**: `H⁰(K, M) × H²(K, M') → ℤ/n` is perfect. -/
theorem perfectDeg0_all [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    [SmoothAction (Ω ≃ₐ[K] Ω) M] (hM : ∀ m : M, m ^ n = 1) :
    PerfectDeg0 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := M)
      (G := Ω ≃ₐ[K] Ω)) := by
  haveI := hasEnoughRootsOfUnity_omega (p := p) (Ω := Ω) n
  refine ⟨injective_perfectDeg0 (p := p) _ fun m hm => ?_, ?_⟩
  · obtain ⟨φ, hφ⟩ := exists_hom_mu_ne_one (Ω := Ω) hM hm
    exact ⟨CartierDual.toHom.symm φ, hφ⟩
  · haveI := finite_h2 (p := p) (K := K) (Ω := Ω) (CartierDual n Ω M)
    refine surjective_of_transpose_injective (h2_pow_eq_one CartierDual.pow_eq_one)
      (dualH0 p K Ω n M) fun β hβ => ?_
    apply injective_dualH2 (p := p) (CartierDual n Ω M) CartierDual.pow_eq_one
    rw [map_one]
    refine MonoidHom.ext fun Ψ => ?_
    obtain ⟨m, hm⟩ := (evDual_bijective (p := p) M hM).2 (Ψ : CartierDual n Ω (CartierDual n Ω M))
    have hmG : m ∈ H0 (Ω ≃ₐ[K] Ω) M := fun g =>
      (evDual_bijective (p := p) M hM).1 (by rw [evDual_smul, hm, smul_H0 Ψ g])
    have := hβ ⟨m, hmG⟩
    rw [MonoidHom.one_apply, ← this, dualH2_apply, dualH0_apply]
    congr 1
    induction β using induction_on with | h c => ?_
    rw [cup20_apply, cup02_mk, cup02_mk]
    congr 1
    refine cocycles_ext fun a b => ?_
    change CartierDual.toHom (Ψ : CartierDual n Ω (CartierDual n Ω M)) (c (a, b)) =
      CartierDual.toHom (c (a, b)) m
    rw [← hm]
    rfl

end Deg0

end PadicField
