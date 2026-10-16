/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.FiniteDual
import LocalClassFieldTheory.Duality.TrivialDuality
import LocalClassFieldTheory.Duality.TateH3Local

/-!
# Local duality: injectivity in degree `0`

Let `e : X × Y → μ_n` be a `G_K`-equivariant pairing with `Y` a finite discrete `G_K`-module.
If `e` is non-degenerate on the left (`x ≠ 1 ⇒ e(x, -) ≠ 1`), then

`H⁰(K, X) → Hom(H²(K, Y), ℤ/n)`, `x ↦ (β ↦ inv(x ∪ β))`

is injective (**`PadicField.injective_perfectDeg0`**). Indeed, for `x ∈ X^{G_K}`, `x ≠ 1`, the
map `f = e(x, -) : Y → μ_n` is equivariant with image `μ_d` for some `1 < d ∣ n`; the map
`H²(K, Y) → H²(K, μ_d)` is surjective (`cd(G_K) ≤ 2`, `PadicField.h2Hom_surjective`),
`H²(K, μ_d) ≃ ℤ/d` is non-trivial (`PadicField.h2MuEquiv`) and `H²(K, μ_d) → H²(K, μ_n)` is
injective (`PadicField.h2MuIncl_injective`), so `x ∪ β = f_* β ≠ 0` for a suitable `β`.

This is the first step of the proof of local Tate duality for arbitrary finite modules in
`LocalClassFieldTheory.Duality.General`.
-/

open ContH2 KummerTheory

set_option linter.unusedSectionVars false

namespace PadicField

open Brauer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

local notation "G_K" => Ω ≃ₐ[K] Ω

include hp in
theorem charZero_omega : CharZero Ω :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] Ω).injective

include hp in
theorem hasEnoughRootsOfUnity_omega (n : ℕ) [NeZero n] : HasEnoughRootsOfUnity Ω n := by
  haveI := charZero_omega (p := p) (Ω := Ω)
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 (NeZero.ne n)⟩
  infer_instance

/-- `h2Hom` only depends on the underlying homomorphism. -/
theorem h2Hom_congr {G M N : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N] {f f' : M →* N}
    (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (hf' : ∀ (g : G) (m : M), f' (g • m) = g • f' m)
    (h : ∀ m, f m = f' m) (β : ContH2 G M) : h2Hom f hf β = h2Hom f' hf' β := by
  induction β using induction_on with | h c => ?_
  rw [h2Hom_mk, h2Hom_mk]
  congr 1
  exact cocycles_ext fun a b => h _

theorem invMu_injective {n : ℕ} [NeZero n] : Function.Injective (invMu p K Ω n) :=
  (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n))).injective

section Deg0

variable {n : ℕ} [NeZero n]
variable {X Y : Type*} [CommGroup X] [CommGroup Y] [Finite Y] [TopologicalSpace Y]
  [DiscreteTopology Y] [MulDistribMulAction (Ω ≃ₐ[K] Ω) X] [MulDistribMulAction (Ω ≃ₐ[K] Ω) Y]
  [SmoothAction (Ω ≃ₐ[K] Ω) Y]

include hp in
/-- **The key step**: if `x ∈ H⁰(K, X)` pairs non-trivially with some element of `Y`, then
`x ∪ β ≠ 0` for some `β ∈ H²(K, Y)`. -/
theorem exists_cup02_ne_one (e : GPairing G_K X Y (Mu n Ω)) (x : H0 G_K X)
    (hx : ∃ y, e.toHom x y ≠ 1) : ∃ β : ContH2 G_K Y, cup02 e x β ≠ 1 := by
  haveI := hasEnoughRootsOfUnity_omega (p := p) (Ω := Ω) n
  set f : Y →* Mu n Ω := e.toHom x with hf_def
  have hf : ∀ (g : G_K) (y : Y), f (g • y) = g • f y := fun g y => by
    have h := e.map_smul g x y
    rwa [smul_H0 x g] at h
  set d := Nat.card f.range with hd_def
  have hcardn : Nat.card (Mu n Ω) = n := HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω n
  have hd : d ∣ n := hcardn ▸ Subgroup.card_subgroup_dvd_card f.range
  obtain ⟨y₀, hy₀⟩ := hx
  have hd1 : 1 < d := by
    rw [hd_def, Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    have hmem : f y₀ ∈ f.range := ⟨y₀, rfl⟩
    rw [hbot] at hmem
    exact hy₀ (Subgroup.mem_bot.1 hmem)
  haveI : NeZero d := ⟨by omega⟩
  haveI := hasEnoughRootsOfUnity_omega (p := p) (Ω := Ω) d
  have hpow : ∀ y, Mu.val (f y) ^ d = 1 := fun y => by
    have : (⟨f y, y, rfl⟩ : f.range) ^ d = 1 := pow_card_eq_one'
    have := congrArg Subtype.val this
    rw [← map_pow]
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this
    rw [this, map_one]
  -- `f` factors through `μ_d`
  let f' : Y →* Mu d Ω :=
    { toFun := fun y => Mu.mk (Mu.val (f y)) (hpow y)
      map_one' := Mu.ext (by simp)
      map_mul' := fun a b => Mu.ext (by simp) }
  have hff' : ∀ y, muIncl hd (f' y) = f y := fun y => Mu.ext rfl
  have hf' : ∀ (g : G_K) (y : Y), f' (g • y) = g • f' y := fun g y => by
    apply Mu.ext
    have h1 : Mu.val (g • f' y) = Mu.val (muIncl hd (g • f' y)) := rfl
    rw [h1, ← smul_muIncl (p := p) hd g (f' y), hff', ← hf]
    rfl
  have hsurj : Function.Surjective f' := by
    have hr : f'.range = ⊤ := by
      apply Subgroup.eq_top_of_le_card
      change Nat.card (rootsOfUnity d Ω) ≤ _
      rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω d]
      refine Nat.card_le_card_of_surjective
        (fun z : f'.range => (⟨muIncl hd z, ?_⟩ : f.range)) ?_
      · obtain ⟨y, hy⟩ := z.2
        exact ⟨y, by rw [← hff', hy]⟩
      · rintro ⟨_, y, rfl⟩
        exact ⟨⟨f' y, y, rfl⟩, Subtype.ext (hff' y)⟩
    exact MonoidHom.range_eq_top.1 hr
  -- `H²(K, Y) → H²(K, μ_d)` is surjective
  set N := f'.ker
  have hN : IsGStable (G := G_K) N := fun g y hy => by
    rw [MonoidHom.mem_ker] at hy ⊢
    rw [hf', hy, smul_one]
  letI := subAction N hN
  letI := quotAction N hN
  haveI := smoothAction_sub N hN
  haveI := smoothAction_quot N hN
  let S := subQuotSES N hN
  have hS := h2Hom_surjective (p := p) (K := K) (Ω := Ω) S
  let τ : Y ⧸ N ≃* Mu d Ω := QuotientGroup.quotientKerEquivOfSurjective f' hsurj
  have hτ : ∀ (g : G_K) (q : Y ⧸ N), τ (g • q) = g • τ q := by
    intro g q
    induction q using QuotientGroup.induction_on with | H y => ?_
    exact hf' g y
  have hcomp : ∀ β, h2Map τ hτ (h2Hom S.π S.map_smul_π β) = h2Hom f' hf' β := by
    intro β
    induction β using induction_on with | h c => ?_
    rfl
  have hf'surj : Function.Surjective (h2Hom (G := G_K) f' hf') := by
    intro β'
    obtain ⟨γ, hγ⟩ := (h2Map_bijective τ hτ).2 β'
    obtain ⟨β, hβ⟩ := hS γ
    exact ⟨β, by rw [← hcomp, hβ, hγ]⟩
  -- a non-trivial class in `H²(K, μ_d)`
  haveI : Fact (1 < d) := ⟨hd1⟩
  set β' : H2Mu K Ω d := (h2MuEquiv p K Ω (n := d) (by omega)).symm (Multiplicative.ofAdd 1)
  have hβ' : β' ≠ 1 := by
    intro h
    have := congrArg (h2MuEquiv p K Ω (n := d) (by omega)) h
    rw [MulEquiv.apply_symm_apply, MulEquiv.map_one] at this
    exact one_ne_zero (ofAdd_eq_one.1 this)
  obtain ⟨β, hβ⟩ := hf'surj β'
  refine ⟨β, fun h => hβ' ?_⟩
  have e1 : cup02 e x β = h2MuIncl hd (h2Hom f' hf' β) := by
    induction β using induction_on with | h c => ?_
    rw [cup02_mk, h2Hom_mk]
    simp only [h2MuIncl, map_mk]
    congr 1
  rw [e1, hβ] at h
  exact h2MuIncl_injective (p := p) hd (h.trans (map_one _).symm)

include hp in
/-- **Injectivity of the degree-`0` duality map** for a pairing that is non-degenerate on the
left. -/
theorem injective_perfectDeg0 (e : GPairing G_K X Y (Mu n Ω))
    (he : ∀ x : X, x ≠ 1 → ∃ y, e.toHom x y ≠ 1) :
    Function.Injective fun m : H0 G_K X => (invMu p K Ω n).comp (cup02 e m) := by
  intro m m' h
  by_contra hne
  have hx : m / m' ≠ 1 := fun h' => hne (div_eq_one.1 h')
  obtain ⟨β, hβ⟩ := exists_cup02_ne_one (p := p) e (m / m')
    (he _ fun h' => hx (Subtype.ext h'))
  apply hβ
  have h1 := DFunLike.congr_fun h β
  simp only [MonoidHom.coe_comp, Function.comp_apply] at h1
  have h2 : cup02 e m β = cup02 e m' β := invMu_injective h1
  have h3 : cup02 e m β = cup02 e (m / m') β * cup02 e m' β := by
    rw [← cup02_mul_left, div_mul_cancel]
  rw [h2] at h3
  exact (mul_eq_right.1 h3.symm)

end Deg0

end PadicField
