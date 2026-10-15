/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.H3Cores
import LocalClassFieldTheory.Duality.ZModPrime

/-!
# `H³(K, μ_n) = 0` from `H³(K, Ωˣ) = 0` (Kummer sequence in degree three)

Let `K` be finite over `ℚ_p` and `Ω` an algebraic closure. We isolate the statement

* **`Brauer.H3UnitsVanishing K Ω`** : `H³(Gal(Ω/K), Ωˣ) = 0` in cocycle form (every locally
  constant `Ωˣ`-valued `3`-cocycle is the coboundary of a locally constant `2`-cochain).

This is a classical theorem for local fields (by inflation it amounts to
`H³(Gal(L/K), Lˣ) ≅ Ĥ¹(Gal(L/K), ℤ) = 0` for finite Galois `L/K`, i.e. Tate's theorem /
Tate–Nakayama in degree three, Serre, *Local fields* IX, Cassels–Fröhlich VI.1); it is proved for
finite extensions of `ℚ_p` in `LocalClassFieldTheory.Duality.TateH3Local`
(`PadicField.h3UnitsVanishing`).

From it and the divisibility of `Br(K) ≃ ℚ/ℤ` we deduce, via the Kummer sequence
`1 → μ_n → Ωˣ → Ωˣ → 1`:

* **`PadicField.h3Trivial_mu`** : `H3UnitsVanishing K Ω → H3Trivial (Gal(Ω/K)) μ_n` for all
  `n > 0` (no condition on roots of unity in `K`): if `ι z = d f`, then `fⁿ` is a `2`-cocycle,
  `[fⁿ] = [g]ⁿ` in `Br(K)`, `fⁿ = gⁿ · d x`, and `f · d(x^{1/n}) / g` is a `μ_n`-valued primitive
  of `z`;
* `Brauer.h3Trivial_of_groupEquiv` : transport along topological group isomorphisms, and
  **`PadicField.h3Trivial_fixingSubgroup_mu`** : the same for the open subgroup
  `Gal(Ω/K') ≤ Gal(Ω/K)` of a finite extension `K' ⊆ Ω`.
-/

open ContH2 groupCohomology KummerTheory

set_option linter.unusedSectionVars false

namespace ContH2

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

theorem dc2_pow (f : G × G → M) (n : ℕ) : dc2 (f ^ n) = dc2 f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, dc2_one]
  | succ n ih => rw [pow_succ, pow_succ, dc2_mul, ih]

theorem dc2_eq_one_of_isMulCocycle₂ {f : G × G → M} (hf : IsMulCocycle₂ f) : dc2 f = 1 := by
  funext ⟨a, b, c⟩
  exact (isMulCocycle₂_iff_dc2 f).1 hf a b c

end ContH2

namespace Brauer

/-- **`H³(K, Ωˣ) = 0` in cocycle form** (statement only): every locally constant `3`-cocycle of
`Gal(Ω/K)` with values in `Ωˣ` is the coboundary of a locally constant `2`-cochain. True for
local fields (Tate; `PadicField.h3UnitsVanishing`). -/
def H3UnitsVanishing (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω] : Prop :=
  H3Trivial (Ω ≃ₐ[K] Ω) Ωˣ

/-- Transport of `H3Trivial` along an isomorphism of topological groups compatible with the
actions. -/
theorem h3Trivial_of_groupEquiv {G G' A : Type*} [Group G] [Group G'] [TopologicalSpace G]
    [TopologicalSpace G'] [CommGroup A] [MulDistribMulAction G A] [MulDistribMulAction G' A]
    (φ : G ≃* G') (hφ : Continuous φ) (hφ' : Continuous φ.symm)
    (hcompat : ∀ (g : G) (a : A), φ g • a = g • a) (h : H3Trivial G A) : H3Trivial G' A := by
  intro z hzl hz
  have hcompat' : ∀ (g : G') (a : A), φ.symm g • a = g • a := fun g a => by
    rw [← hcompat, MulEquiv.apply_symm_apply]
  obtain ⟨f, hfl, hf⟩ := h (fun x => z (φ x.1, φ x.2.1, φ x.2.2))
    (hzl.comp_continuous ((hφ.comp continuous_fst).prodMk ((hφ.comp
      (continuous_fst.comp continuous_snd)).prodMk (hφ.comp (continuous_snd.comp continuous_snd)))))
    (fun a b c d => by
      have := hz (φ a) (φ b) (φ c) (φ d)
      rw [hcompat] at this
      simpa only [map_mul] using this)
  refine ⟨fun x => f (φ.symm x.1, φ.symm x.2),
    hfl.comp_continuous ((hφ'.comp continuous_fst).prodMk (hφ'.comp continuous_snd)), ?_⟩
  funext ⟨a, b, c⟩
  have := congrFun hf (φ.symm a, φ.symm b, φ.symm c)
  simp only [dc2_apply, hcompat', MulEquiv.apply_symm_apply, ← map_mul] at this
  simpa only [dc2_apply] using this

end Brauer

namespace PadicField

open Brauer IntermediateField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

variable (p) in
include hp in
/-- `Br(K)` is divisible. -/
theorem br_divisible {n : ℕ} (hn : 0 < n) (α : Br K Ω) : ∃ β : Br K Ω, β ^ n = α := by
  obtain ⟨y, hy⟩ := exists_nsmul_eq_QZ hn (Multiplicative.toAdd (invEquiv p K Ω α))
  refine ⟨(invEquiv p K Ω).symm (Multiplicative.ofAdd y), (invEquiv p K Ω).injective ?_⟩
  rw [map_pow, MulEquiv.apply_symm_apply, ← ofAdd_nsmul, hy, ofAdd_toAdd]

variable (p) in
include hp in
/-- **Kummer sequence in degree three**: `H³(K, Ωˣ) = 0` implies `H³(K, μ_n) = 0`
(cocycle form), for every `n > 0`. -/
theorem h3Trivial_mu (h : H3UnitsVanishing K Ω) {n : ℕ} (hn : 0 < n) :
    H3Trivial (Ω ≃ₐ[K] Ω) (Mu n Ω) := by
  intro z hzl hz
  obtain ⟨f, hfl, hf⟩ := h (fun x => Mu.val (z x)) (hzl.comp _)
    (isMulCocycle₃_comp Mu.val (fun _ _ => rfl) hz)
  have hdn : dc2 (f ^ n) = 1 := by
    rw [dc2_pow, hf]
    funext x
    rw [Pi.pow_apply, Mu.val_pow_n, Pi.one_apply]
  have hc : IsMulCocycle₂ (f ^ n) :=
    (isMulCocycle₂_iff_dc2 _).2 fun a b c => by rw [hdn]; rfl
  have hfnl : IsLocallyConstant (f ^ n) := hfl.comp (· ^ n)
  obtain ⟨β, hβ⟩ := br_divisible p hn (mk (mkCocycle _ hfnl hc))
  induction β using induction_on with | h g => ?_
  rw [← map_pow, mk_eq_mk_iff] at hβ
  obtain ⟨x, hxl, hx⟩ := hβ
  let r : Ωˣ → Ωˣ := fun u => Classical.choose (exists_root n hn u)
  have hr : ∀ u, r u ^ n = u := fun u => Classical.choose_spec (exists_root n hn u)
  let y : (Ω ≃ₐ[K] Ω) → Ωˣ := fun σ => r (x σ)
  have hyl : IsLocallyConstant y := hxl.comp r
  have hyn : y ^ n = x := funext fun σ => hr (x σ)
  let f' : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → Ωˣ := f * dx (Ω ≃ₐ[K] Ω) Ωˣ y /
    ((g : cocycles (Ω ≃ₐ[K] Ω) Ωˣ) : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → Ωˣ)
  have h1 : IsLocallyConstant (dx (Ω ≃ₐ[K] Ω) Ωˣ y) :=
    ContH2.isLocallyConstant_dx (G := Ω ≃ₐ[K] Ω) (M := Ωˣ)
      (fun u => Brauer.isLocallyConstant_smul_units (K := K) (Ω := Ω) u) hyl
  have h2 : IsLocallyConstant
      ((g : cocycles (Ω ≃ₐ[K] Ω) Ωˣ) : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → Ωˣ) :=
    ContH2.isLocallyConstant g
  have hf'l : IsLocallyConstant f' := (hfl.mul h1).div h2
  have hf'n : ∀ gh, f' gh ^ n = 1 := by
    intro gh
    have e := congrFun hx gh
    simp only [f', Pi.mul_apply, Pi.div_apply, mul_pow, div_pow]
    rw [← Pi.pow_apply (dx _ _ y) n, ← dx_pow, hyn, e]
    simp only [SubgroupClass.coe_pow, Pi.pow_apply, coe_mkCocycle, Pi.div_apply]
    mul_abel
  let F : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → Mu n Ω := fun gh => Mu.mk (f' gh) (hf'n gh)
  refine ⟨F, isLocallyConstant_mu n hf'l, funext fun w => Mu.ext ?_⟩
  refine (map_dc2 Mu.val (fun _ _ => rfl) F w).trans ?_
  have hF : (fun v => Mu.val (F v)) = f' := rfl
  rw [hF, dc2_div, dc2_mul, dc2_eq_one_of_isMulCocycle₂ (isMulCocycle₂_dx _),
    dc2_eq_one_of_isMulCocycle₂ (isMulCocycle₂ g), hf]
  simp

variable (p) in
include hp in
/-- **`H³(Gal(Ω/K'), μ_n) = 0`** for the open subgroup `Gal(Ω/K') ≤ Gal(Ω/K)` of a finite
extension `K' ⊆ Ω`, given `H³(K', Ωˣ) = 0`. -/
theorem h3Trivial_fixingSubgroup_mu (K' : IntermediateField K Ω) [FiniteDimensional K K']
    (h : H3UnitsVanishing K' Ω) {n : ℕ} (hn : 0 < n) :
    H3Trivial K'.fixingSubgroup (Mu n Ω) :=
  h3Trivial_of_groupEquiv (fixingSubgroupEquiv K').symm
    (continuous_fixingSubgroupEquiv_symm K') (continuous_fixingSubgroupEquiv K')
    (fun _ _ => rfl) (h3Trivial_mu p h hn)

end PadicField
