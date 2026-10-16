/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.DualityDeg2

/-!
# Local Tate duality for all finite modules

Let `K` be a finite extension of `ℚ_p`, `M` a finite discrete `G_K`-module killed by `n` and
`M' = Hom(M, μ_n)`. **`PadicField.localTateDuality`**: the cup product pairings

`Hⁱ(K, M) × H²⁻ⁱ(K, M') → H²(K, μ_n) ≃ ℤ/n`,  `i = 0, 1, 2`,

are perfect, i.e. `PadicField.LocalTateDuality p K Ω` holds (Tate–Poitou local duality; Serre,
*Galois cohomology*, II.5.2, Theorem 2).

Degrees `0` and `2` are `PadicField.perfectDeg0_all`, `PadicField.perfectDeg2_all`
(`LocalClassFieldTheory.Duality.DualityDeg2`). Degree `1`:

* **`Brauer.GShortExact.cup11_delta0_mul_cup02_delta1`** : for `0 → A → B → C → 0`, a "dual"
  sequence `0 → C' → B' → A' → 0` and compatible pairings, `δ⁰x ∪ y = -(x ∪ δ¹y)` in
  `H²(G, P)` for `x ∈ H⁰(C)`, `y ∈ H¹(A')` (the two cocycles differ by the coboundary of
  `g ↦ e_B(b, yt(g))`, `b` a lift of `x`, `yt` a lift of `y`);
* `PadicField.exists_coInd_kill_h1` : there is a finite `K'/K` such that
  `H¹(K, M) → H¹(K, CoInd_{G_{K'}} M)` is zero (each cocycle vanishes on an open subgroup, and a
  cocycle vanishing on `U` becomes the coboundary of `c ↦ f(c.out)⁻¹` in `CoInd_U M`);
* **`PadicField.injective_dualH1`** : from `0 → M → CoInd M → Q → 0` and its dual, the exact
  sequences `H⁰(CoInd M) → H⁰(Q) → H¹(M) → 0` and `H¹(M') → H²(Q') → H²((CoInd M)')`, duality in
  degree `0` for `CoInd M` and `Q` and the compatibility of `δ`, the map
  `H¹(K, M) → H¹(K, M')^∨` is injective;
* `PadicField.perfectDeg1_all` : applied to `M` and `M'` (with `M ≃ M''`) this gives
  `#H¹(K, M) = #H¹(K, M')`, hence bijectivity.
-/

open ContH2 KummerTheory

set_option linter.unusedSectionVars false

namespace Brauer

namespace GShortExact

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B C A' B' C' P : Type*} [CommGroup A] [CommGroup B] [CommGroup C] [CommGroup A']
  [CommGroup B'] [CommGroup C'] [CommGroup P]
  [MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]
  [MulDistribMulAction G A'] [MulDistribMulAction G B'] [MulDistribMulAction G C']
  [MulDistribMulAction G P]
  [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace C] [DiscreteTopology C] [TopologicalSpace A'] [DiscreteTopology A']
  [TopologicalSpace B'] [DiscreteTopology B'] [TopologicalSpace C'] [DiscreteTopology C']
  [SmoothAction G B] [SmoothAction G B'] [SmoothAction G A']

/-- **Compatibility of the connecting maps with cup products**: for compatible pairings
`e_A : A × A' → P`, `e_B : B × B' → P`, `e_C : C × C' → P` between `0 → A → B → C → 0` and
`0 → C' → B' → A' → 0`, `δ⁰x ∪ y + x ∪ δ¹y = 0` in `H²(G, P)`. -/
theorem cup11_delta0_mul_cup02_delta1 (S : GShortExact G A B C) (S' : GShortExact G C' B' A')
    (eA : GPairing G A A' P) (eB : GPairing G B B' P) (eC : GPairing G C C' P)
    (h1 : ∀ a ψ, eA.toHom a (S'.π ψ) = eB.toHom (S.i a) ψ)
    (h2 : ∀ b w, eC.toHom (S.π b) w = eB.toHom b (S'.i w))
    (x : H0 G C) (y : ContH1 G A') :
    cup11 eA (S.delta0 x) y * cup02 eC x (S'.delta1 y) = 1 := by
  induction y using ContH1.induction_on with | h y => ?_
  set b := S.sec x
  set yt : G → B' := fun g => S'.sec (y g)
  rw [S.delta0_eq x b (S.π_sec x), S'.delta1_mk y (S'.isLocallyConstant_sec_comp y)
    (fun g => S'.π_sec _), cup11_mk, cup02_mk, ← map_mul, mk_eq_one_iff]
  refine ⟨fun g => eB.toHom b (yt g), (S'.isLocallyConstant_sec_comp y).comp _, ?_⟩
  funext gh
  obtain ⟨g, h⟩ := gh
  have hy : ∀ k, y k = S'.π (yt k) := fun k => (S'.π_sec _).symm
  have hx : (x : C) = S.π b := (S.π_sec x).symm
  change _ = cup11Cocycle eA (S.delta0Cocycle b _) y (g, h) *
    eC.toHom x (S'.delta1Cocycle yt _ _ (g, h))
  rw [cup11Cocycle_apply, hy h, ← S'.map_smul_π, h1, S.i_delta0Cocycle, hx, h2,
    S'.i_delta1Cocycle, dx_apply, dx_apply]
  simp only [map_div, map_mul, MonoidHom.div_apply]
  rw [← eB.map_smul]
  mul_abel

end GShortExact

end Brauer

namespace PadicField

open Brauer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

local notation "G_K" => Ω ≃ₐ[K] Ω

theorem h1_pow_eq_one {n : ℕ} {X : Type*} [CommGroup X] [MulDistribMulAction (Ω ≃ₐ[K] Ω) X]
    [TopologicalSpace X] [DiscreteTopology X] (hX : ∀ x : X, x ^ n = 1)
    (ξ : ContH1 (Ω ≃ₐ[K] Ω) X) : ξ ^ n = 1 := by
  induction ξ using ContH1.induction_on with | h f => ?_
  rw [← map_pow, ← map_one (ContH1.mk (G := Ω ≃ₐ[K] Ω) (M := X))]
  congr 1
  exact Subtype.ext (funext fun g => hX _)

/-! ### The duality map in degree `1` -/

section Map

variable (p K Ω) (n : ℕ) [NeZero n]
variable (M : Type*) [CommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]

/-- `H¹(K, M) → Hom(H¹(K, M'), ℤ/n)`, `x ↦ (y ↦ inv(x ∪ y))`. -/
noncomputable def dualH1 :
    ContH1 (Ω ≃ₐ[K] Ω) M →* (ContH1 (Ω ≃ₐ[K] Ω) (CartierDual n Ω M) →*
      Multiplicative (ZMod n)) where
  toFun x := (invMu p K Ω n).comp (cup11 (evalP K Ω n M) x)
  map_one' := MonoidHom.ext fun y => by
    simp only [MonoidHom.coe_comp, Function.comp_apply, map_one, MonoidHom.one_apply]
  map_mul' x x' := MonoidHom.ext fun y => by
    simp only [MonoidHom.coe_comp, Function.comp_apply, map_mul, MonoidHom.mul_apply]

theorem dualH1_apply (x : ContH1 (Ω ≃ₐ[K] Ω) M) (y : ContH1 (Ω ≃ₐ[K] Ω) (CartierDual n Ω M)) :
    dualH1 p K Ω n M x y = invMu p K Ω n (cup11 (evalP K Ω n M) x y) := rfl

end Map

/-! ### Killing `H¹` by coinduction -/

section Kill

variable {M : Type*} [CommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]

/-- The subgroup on which a `1`-cocycle vanishes. -/
def cocycleKer (f : ContH1.cocycles (Ω ≃ₐ[K] Ω) M) : Subgroup (Ω ≃ₐ[K] Ω) where
  carrier := {g | (f : _ → M) g = 1}
  one_mem' := ContH1.map_one_eq f
  mul_mem' {g h} hg hh := by
    simp only [Set.mem_setOf_eq] at hg hh ⊢
    rw [ContH1.isMulCocycle₁ f g h, hg, hh, smul_one, one_mul]
  inv_mem' {g} hg := by
    simp only [Set.mem_setOf_eq] at hg ⊢
    have h := ContH1.isMulCocycle₁ f g g⁻¹
    rw [mul_inv_cancel, ContH1.map_one_eq, hg, mul_one] at h
    have := congrArg (fun m => g⁻¹ • m) h
    simp only [smul_one, inv_smul_smul] at this
    exact this.symm

theorem isOpen_cocycleKer (f : ContH1.cocycles (Ω ≃ₐ[K] Ω) M) :
    IsOpen (cocycleKer f : Set (Ω ≃ₐ[K] Ω)) :=
  (ContH1.continuous f).isOpen_preimage {1} (isOpen_discrete _)

/-- A cocycle vanishing on `U` becomes a coboundary in `CoInd_U M`. -/
theorem h1Hom_diag_eq_one (U : Subgroup (Ω ≃ₐ[K] Ω)) (f : ContH1.cocycles (Ω ≃ₐ[K] Ω) M)
    (hf : ∀ u ∈ U, (f : _ → M) u = 1) :
    h1Hom (diag M U) (diag_smul M U) (ContH1.mk f) = 1 := by
  rw [h1Hom_mk, ContH1.mk_eq_one_iff]
  refine ⟨(fun c => ((f : _ → M) c.out)⁻¹ : (Ω ≃ₐ[K] Ω) ⧸ U → M), fun g => ?_⟩
  refine ContH2.CoInd.ext fun c => ?_
  set s := c.out
  set t := (g⁻¹ • c).out
  have hmk : (QuotientGroup.mk (g * t) : (Ω ≃ₐ[K] Ω) ⧸ U) = QuotientGroup.mk s := by
    rw [QuotientGroup.out_eq']
    change g • (QuotientGroup.mk t : (Ω ≃ₐ[K] Ω) ⧸ U) = c
    rw [QuotientGroup.out_eq', smul_inv_smul]
  have hu : s⁻¹ * (g * t) ∈ U := QuotientGroup.eq.1 hmk.symm
  have hst : (f : _ → M) (g * t) = (f : _ → M) s := by
    have e : g * t = s * (s⁻¹ * (g * t)) := by group
    rw [e, ContH1.isMulCocycle₁ f, hf _ hu, smul_one, one_mul]
  have hc := ContH1.isMulCocycle₁ f g t
  rw [hst] at hc
  change g • ((f : _ → M) t)⁻¹ / ((f : _ → M) s)⁻¹ = (f : _ → M) g
  rw [hc, smul_inv']
  mul_abel

include hp in
/-- **There is a finite `K'/K` such that `H¹(K, M) → H¹(K, CoInd_{G_{K'}} M)` is zero.** -/
theorem exists_coInd_kill_h1 :
    ∃ K' : IntermediateField K Ω, FiniteDimensional K K' ∧
      ∀ ξ : ContH1 (Ω ≃ₐ[K] Ω) M,
        h1Hom (diag M K'.fixingSubgroup) (diag_smul M K'.fixingSubgroup) ξ = 1 := by
  haveI := finite_h1 (p := p) (K := K) (Ω := Ω) M
  let rep : ContH1 (Ω ≃ₐ[K] Ω) M → ContH1.cocycles (Ω ≃ₐ[K] Ω) M := fun ξ =>
    Classical.choose (ContH1.mk_surjective ξ)
  have hrep : ∀ ξ, ContH1.mk (rep ξ) = ξ := fun ξ =>
    Classical.choose_spec (ContH1.mk_surjective ξ)
  let U₀ : Subgroup (Ω ≃ₐ[K] Ω) := ⨅ ξ, cocycleKer (rep ξ)
  have hU₀ : IsOpen (U₀ : Set (Ω ≃ₐ[K] Ω)) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun ξ => isOpen_cocycleKer (rep ξ)
  obtain ⟨K', hK', hU⟩ := exists_fixingSubgroup_eq U₀ hU₀
  refine ⟨K', hK', fun ξ => ?_⟩
  rw [← hrep ξ]
  refine h1Hom_diag_eq_one _ _ fun u hu => ?_
  rw [hU] at hu
  exact (Subgroup.mem_iInf.1 hu) ξ

end Kill

/-! ### Injectivity in degree `1` -/

section Inj

variable {n : ℕ} [NeZero n]

include hp in
/-- **Duality in degree `1`, injectivity**: `H¹(K, M) → H¹(K, M')^∨` is injective for every
finite discrete `G_K`-module `M` killed by `n`. -/
theorem injective_dualH1 (M : Type*) [CommGroup M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]
    (hM : ∀ m : M, m ^ n = 1) : Function.Injective (dualH1 p K Ω n M) := by
  obtain ⟨K', hK', hkill⟩ := exists_coInd_kill_h1 (p := p) (K := K) (Ω := Ω) (M := M)
  set U := K'.fixingSubgroup
  haveI := ContH2.CoInd.smoothAction (A := M) K'.fixingSubgroup_isOpen
  haveI : Finite (ContH2.CoInd U M) := inferInstanceAs (Finite ((Ω ≃ₐ[K] Ω) ⧸ U → M))
  have hB : ∀ F : ContH2.CoInd U M, F ^ n = 1 := fun F => funext fun c => hM (F c)
  -- the short exact sequence `0 → M → CoInd_U M → Q → 0`
  set R := (diag M U).range
  have hR : IsGStable (G := Ω ≃ₐ[K] Ω) R := by
    rintro g _ ⟨m, rfl⟩
    exact ⟨g • m, diag_smul M U g m⟩
  letI := quotAction R hR
  haveI := smoothAction_quot R hR
  letI : TopologicalSpace (ContH2.CoInd U M ⧸ R) := ⊥
  haveI : DiscreteTopology (ContH2.CoInd U M ⧸ R) := ⟨rfl⟩
  haveI : Finite (ContH2.CoInd U M ⧸ R) := Finite.of_surjective _ (QuotientGroup.mk'_surjective R)
  have hQ : ∀ q : ContH2.CoInd U M ⧸ R, q ^ n = 1 := fun q => by
    induction q using QuotientGroup.induction_on with | H F => ?_
    rw [← QuotientGroup.mk_pow, hB, QuotientGroup.mk_one]
  let S : GShortExact (Ω ≃ₐ[K] Ω) M (ContH2.CoInd U M) (ContH2.CoInd U M ⧸ R) :=
    { i := diag M U
      π := QuotientGroup.mk' R
      map_smul_i := diag_smul M U
      map_smul_π := fun _ _ => rfl
      injective := diag_injective M U
      surjective := QuotientGroup.mk'_surjective R
      exact := fun F => by rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] }
  set S' := dualSES (p := p) n S hB
  -- the chase
  rw [injective_iff_map_eq_one]
  intro a ha
  have ha' : a ∈ (h1Hom (G := Ω ≃ₐ[K] Ω) S.i S.map_smul_i).ker := hkill a
  rw [S.exact_h1A] at ha'
  obtain ⟨x, rfl⟩ := ha'
  set ξ := dualH0 p K Ω n (ContH2.CoInd U M ⧸ R) x
  have hξ : ∀ y, ξ (S'.delta1 y) = 1 := by
    intro y
    have key := S.cup11_delta0_mul_cup02_delta1 S' (evalP K Ω n M) (evalP K Ω n _)
      (evalP K Ω n _) (fun _ _ => rfl) (fun _ _ => rfl) x y
    have h1 := DFunLike.congr_fun ha y
    rw [dualH1_apply, MonoidHom.one_apply] at h1
    have := congrArg (invMu p K Ω n) key
    rw [map_mul, h1, one_mul, map_one] at this
    exact this
  haveI := finite_h2 (p := p) (K := K) (Ω := Ω) (CartierDual n Ω (ContH2.CoInd U M))
  obtain ⟨ξ', hξ'⟩ := exists_factor_zmod (h2_pow_eq_one CartierDual.pow_eq_one)
    S'.delta1 (h2Hom S'.i S'.map_smul_i) S'.exact_h2A ξ hξ
  obtain ⟨x', hx'⟩ := (perfectDeg0_all (p := p) (ContH2.CoInd U M) hB).2 ξ'
  have hxx' : x = h0Hom S.π S.map_smul_π x' := by
    apply (perfectDeg0_all (p := p) (ContH2.CoInd U M ⧸ R) hQ).1
    refine MonoidHom.ext fun β => ?_
    change invMu p K Ω n (cup02 (evalP K Ω n _) x β) =
      invMu p K Ω n (cup02 (evalP K Ω n _) (h0Hom S.π S.map_smul_π x') β)
    rw [cup02_h0Hom_eq S.π S.map_smul_π S'.i S'.map_smul_i (evalP K Ω n (ContH2.CoInd U M))
      (evalP K Ω n _) (fun _ _ => rfl)]
    change ξ β = (invMu p K Ω n).comp (cup02 (evalP K Ω n (ContH2.CoInd U M)) x')
      (h2Hom S'.i S'.map_smul_i β)
    have hx'' : (invMu p K Ω n).comp (cup02 (evalP K Ω n (ContH2.CoInd U M)) x') = ξ' := hx'
    rw [hx'', ← hξ']
    rfl
  have : x ∈ S.delta0.ker := by
    rw [S.exact_h0C]
    exact ⟨x', hxx'.symm⟩
  exact this

include hp in
/-- **Local duality in degree `1`**: `H¹(K, M) × H¹(K, M') → ℤ/n` is perfect. -/
theorem perfectDeg1_all (M : Type*) [CommGroup M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]
    (hM : ∀ m : M, m ^ n = 1) :
    PerfectDeg1 (invMu p K Ω n) (CartierDual.evalPairing (n := n) (Ω := Ω) (M := M)
      (G := Ω ≃ₐ[K] Ω)) := by
  have hinj := injective_dualH1 (p := p) (K := K) (Ω := Ω) M hM
  haveI := finite_h1 (p := p) (K := K) (Ω := Ω) M
  haveI := finite_h1 (p := p) (K := K) (Ω := Ω) (CartierDual n Ω M)
  haveI := finite_h1 (p := p) (K := K) (Ω := Ω) (CartierDual n Ω (CartierDual n Ω M))
  haveI : Finite (ContH1 (Ω ≃ₐ[K] Ω) (CartierDual n Ω M) →* Multiplicative (ZMod n)) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_hom_zmod (h1_pow_eq_one CartierDual.pow_eq_one)]
      exact Nat.card_pos.ne')
  refine hinj.bijective_of_nat_card_le ?_
  rw [card_hom_zmod (h1_pow_eq_one CartierDual.pow_eq_one)]
  -- `#H¹(M') ≤ #H¹(M'') = #H¹(M)`
  haveI : Finite (ContH1 (Ω ≃ₐ[K] Ω) (CartierDual n Ω (CartierDual n Ω M)) →*
      Multiplicative (ZMod n)) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_hom_zmod (h1_pow_eq_one CartierDual.pow_eq_one)]
      exact Nat.card_pos.ne')
  have h1 := Nat.card_le_card_of_injective _
    (injective_dualH1 (p := p) (K := K) (Ω := Ω) (CartierDual n Ω M) CartierDual.pow_eq_one)
  rw [card_hom_zmod (h1_pow_eq_one CartierDual.pow_eq_one)] at h1
  let τ : M ≃* CartierDual n Ω (CartierDual n Ω M) :=
    MulEquiv.ofBijective _ (evDual_bijective (p := p) M hM)
  have hτ : ∀ (g : Ω ≃ₐ[K] Ω) (m : M), τ (g • m) = g • τ m := evDual_smul M
  rw [← Nat.card_congr (Equiv.ofBijective _ (h1Map_bijective τ hτ))] at h1
  exact h1

end Inj

/-! ### Local Tate duality -/

universe u

variable (p K Ω) in
include hp in
/-- **Local Tate duality** (Tate–Poitou): for every finite discrete `G_K`-module `M` and every
`n` killing `M`, the cup product pairings `Hⁱ(K, M) × H²⁻ⁱ(K, M') → H²(K, μ_n) ≃ ℤ/n` with the
Cartier dual `M' = Hom(M, μ_n)` are perfect for `i = 0, 1, 2`. -/
theorem localTateDuality : LocalTateDuality.{u} p K Ω := by
  intro M _ _ _ _ _ _ n _ hM
  exact ⟨perfectDeg0_all (p := p) M hM, perfectDeg1_all (p := p) M hM,
    perfectDeg2_all (p := p) M hM⟩

end PadicField
