/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.Invariant
import ContinuousKummerTheory.Kummer.Basic
import LocalClassFieldTheory.Brauer.InfRes

/-!
# `H²(K, μ_n) ≃ Br(K)[n] ≃ ℤ/n` (cyclotomic rigidity)

For `Ω/K` Galois with `Ω` algebraically closed and `n > 0`, the inclusion `μ_n → Ωˣ` induces an
isomorphism of `H²(Gal(Ω/K), μ_n)` onto the `n`-torsion of the Brauer group (Kummer sequence in
degree two):

* injectivity (`Brauer.toBr_injective`): if `ι ∘ f = dx`, then `xⁿ` is a 1-cocycle, hence
  `xⁿ = dβ` by Hilbert 90, and `x / d(β^{1/n})` is a `μ_n`-valued primitive of `f`;
* the image is the `n`-torsion (`Brauer.mem_range_toBr_iff`): if `fⁿ = dy`, then `f / d(y^{1/n})`
  takes values in `μ_n`.

Composed with the invariant map this gives the **canonical** isomorphism
`PadicField.h2MuEquiv : H²(Gal(Ω/K), μ_n) ≃* ℤ/n` for `K` finite over `ℚ_[p]`: no choice of a
primitive root of unity is involved (cyclotomic rigidity).
-/

open ContH2 groupCohomology KummerTheory

namespace Brauer

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (n : ℕ)

variable (K Ω) in
/-- `H²(Gal(Ω/K), μ_n(Ω))`. -/
abbrev H2Mu : Type _ := ContH2 (Ω ≃ₐ[K] Ω) (Mu n Ω)

/-- `H²(K, μ_n) → Br(K)`. -/
def toBr : H2Mu K Ω n →* Br K Ω :=
  ContH2.map (MonoidHom.id _) continuous_id Mu.val (fun _ _ => rfl)

theorem toBr_mk (f : cocycles (Ω ≃ₐ[K] Ω) (Mu n Ω)) :
    toBr n (mk f) = mk (cocyclesMap (MonoidHom.id _) continuous_id Mu.val (fun _ _ => rfl) f) :=
  rfl

theorem isLocallyConstant_mu {X : Type*} [TopologicalSpace X] {x : X → Mu n Ω}
    (hx : IsLocallyConstant fun a => Mu.val (x a)) : IsLocallyConstant x :=
  IsLocallyConstant.desc _ _ hx Mu.val_injective

variable [IsGalois K Ω] [IsAlgClosed Ω]

omit [IsGalois K Ω] in
theorem exists_root (hn : 0 < n) (u : Ωˣ) : ∃ c : Ωˣ, c ^ n = u := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (u : Ω) hn
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hc
    exact u.ne_zero hc.symm
  exact ⟨Units.mk0 c hc0, Units.ext (by simpa using hc)⟩

/-- **Kummer sequence in degree two, injectivity**: `H²(K, μ_n) → Br(K)` is injective. -/
theorem toBr_injective (hn : 0 < n) : Function.Injective (toBr (K := K) (Ω := Ω) n) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro α hα
  induction α using ContH2.induction_on with | h f => ?_
  rw [MonoidHom.mem_ker, toBr_mk, mk_eq_one_iff] at hα
  obtain ⟨x, hx, hxf⟩ := hα
  have hxf' : ∀ g h, g • x h / x (g * h) * x g = Mu.val (f (g, h)) := fun g h =>
    congrFun hxf (g, h)
  -- `xⁿ` is a 1-cocycle
  have hy : IsMulCocycle₁ (x ^ n) := by
    intro g h
    have e := hxf' g h
    have e2 : (g • x h / x (g * h) * x g) ^ n = 1 := by rw [e, Mu.val_pow_n]
    simp only [Pi.pow_apply]
    rw [div_mul_eq_mul_div, div_pow, mul_pow, div_eq_one] at e2
    rw [smul_pow', e2]
  have hyl : IsLocallyConstant (x ^ n) := hx.comp (· ^ n)
  have h1 : {σ : Ω ≃ₐ[K] Ω | (x ^ n) σ = 1} ∈ nhds 1 := by
    have := (IsLocallyConstant.iff_eventually_eq _).1 hyl 1
    rw [map_one_of_isMulCocycle₁ hy] at this
    exact this
  obtain ⟨b, hb⟩ := isMulCoboundary₁_of_eventually_eq_one hy h1
  obtain ⟨c, hc⟩ := exists_root n hn b
  let x' : (Ω ≃ₐ[K] Ω) → Ωˣ := fun g => x g / (g • c / c)
  have hx'n : ∀ g, x' g ^ n = 1 := by
    intro g
    simp only [x', div_pow, ← smul_pow', hc, hb]
    simp
  let x'' : (Ω ≃ₐ[K] Ω) → Mu n Ω := fun g => Mu.mk (x' g) (hx'n g)
  have hx'' : IsLocallyConstant x'' := isLocallyConstant_mu n (by
    simp only [x'', Mu.val_mk]
    exact hx.div ((isLocallyConstant_smul_units c).div (IsLocallyConstant.const _)))
  rw [Subgroup.mem_bot, mk_eq_one_iff]
  refine ⟨x'', hx'', funext fun gh => ?_⟩
  obtain ⟨g, h⟩ := gh
  apply Mu.ext
  rw [← hxf', dx_apply, map_mul, map_div, Mu.val_smul]
  simp only [x'', x', Mu.val_mk, smul_div', smul_smul]
  mul_abel

omit [IsGalois K Ω] [IsAlgClosed Ω] in
theorem dx_pow (x : (Ω ≃ₐ[K] Ω) → Ωˣ) : dx _ _ (x ^ n) = dx _ _ x ^ n := by
  funext gh
  obtain ⟨g, h⟩ := gh
  simp only [dx_apply, Pi.pow_apply, smul_pow', div_pow, mul_pow]

/-- **Kummer sequence in degree two, image**: the image of `H²(K, μ_n) → Br(K)` is the
`n`-torsion. -/
theorem mem_range_toBr_iff (hn : 0 < n) (α : Br K Ω) :
    α ∈ (toBr (K := K) (Ω := Ω) n).range ↔ α ^ n = 1 := by
  constructor
  · rintro ⟨β, rfl⟩
    induction β using ContH2.induction_on with | h f => ?_
    rw [← map_pow, ← map_pow]
    have : f ^ n = 1 := cocycles_ext fun g h => by
      apply Mu.ext
      simp only [SubgroupClass.coe_pow, Pi.pow_apply, coe_one_apply, map_one]
      rw [map_pow, Mu.val_pow_n]
    rw [this, map_one, map_one]
  · intro hα
    induction α using ContH2.induction_on with | h f => ?_
    rw [← map_pow, mk_eq_one_iff] at hα
    obtain ⟨y, hy, hyf⟩ := hα
    let r : Ωˣ → Ωˣ := fun u => Classical.choose (exists_root n hn u)
    have hr : ∀ u, r u ^ n = u := fun u => Classical.choose_spec (exists_root n hn u)
    let z : (Ω ≃ₐ[K] Ω) → Ωˣ := fun g => r (y g)
    have hz : IsLocallyConstant z := hy.comp r
    have hzn : z ^ n = y := funext fun g => hr (y g)
    let f' : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → Ωˣ := (f : _ → Ωˣ) * dx _ _ z⁻¹
    have hf'c : IsMulCocycle₂ f' := isMulCocycle₂_mul (isMulCocycle₂ f) (isMulCocycle₂_dx _)
    have hf'l : IsLocallyConstant f' := (isLocallyConstant f).mul
      (isLocallyConstant_dx (fun u => isLocallyConstant_smul_units u) hz.inv)
    have hf'n : ∀ gh, f' gh ^ n = 1 := by
      intro gh
      have e := congrFun hyf gh
      simp only [f', Pi.mul_apply, mul_pow, dx_inv, Pi.inv_apply, inv_pow]
      rw [← Pi.pow_apply (dx _ _ z) n, ← dx_pow, hzn, e]
      simp only [SubgroupClass.coe_pow, Pi.pow_apply, mul_inv_cancel]
    let F : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → Mu n Ω := fun gh => Mu.mk (f' gh) (hf'n gh)
    have hFl : IsLocallyConstant F := isLocallyConstant_mu n hf'l
    have hFc : IsMulCocycle₂ F := by
      intro a b c
      apply Mu.ext
      simp only [F, map_mul, Mu.val_smul, Mu.val_mk]
      exact hf'c a b c
    refine ⟨mk (mkCocycle F hFl hFc), ?_⟩
    rw [toBr_mk, mk_eq_mk_iff]
    refine ⟨z⁻¹, hz.inv, funext fun gh => ?_⟩
    obtain ⟨g, h⟩ := gh
    rw [Pi.div_apply, cocyclesMap_apply, coe_mkCocycle]
    simp only [F, Mu.val_mk, f', Pi.mul_apply, MonoidHom.id_apply]
    mul_abel

end Brauer

namespace Brauer

/-- `ℤ/n → ℚ/ℤ`, `k ↦ k/n`. -/
noncomputable def zmodToQZ (n : ℕ) : ZMod n →+ QZ :=
  ZMod.lift n ⟨zmultiplesHom QZ (((1 / n : ℚ) : ℚ) : QZ), by
    simp only [zmultiplesHom_apply, natCast_zsmul]
    rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [mul_one_div_cancel (by exact_mod_cast hn), AddCircle.coe_period]⟩

theorem zmodToQZ_intCast (n : ℕ) (m : ℤ) :
    zmodToQZ n (m : ZMod n) = (((m / n : ℚ) : ℚ) : QZ) := by
  rw [zmodToQZ, ZMod.lift_coe]
  simp only [zmultiplesHom_apply, ← QuotientAddGroup.mk_zsmul, zsmul_eq_mul]
  congr 1
  ring

theorem zmodToQZ_injective {n : ℕ} (hn : 0 < n) : Function.Injective (zmodToQZ n) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [injective_iff_map_eq_zero]
  intro k hk
  have hk' : zmodToQZ n ((k.val : ℤ) : ZMod n) = 0 := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]; exact hk
  rw [zmodToQZ_intCast, AddCircle.coe_eq_zero_iff] at hk'
  obtain ⟨m, hm⟩ := hk'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [zsmul_eq_mul, mul_one, eq_div_iff hn'] at hm
  have hval : ((k.val : ℤ) : ℚ) = m * n := hm.symm
  have hlt := ZMod.val_lt k
  have h0 : (k.val : ℤ) = m * n := by exact_mod_cast hval
  have hm0 : m = 0 := by
    rcases lt_trichotomy m 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  rw [hm0, zero_mul] at h0
  exact (ZMod.val_eq_zero k).1 (by exact_mod_cast h0)

theorem nsmul_eq_zero_iff_mem_range {n : ℕ} (hn : 0 < n) (x : QZ) :
    n • x = 0 ↔ x ∈ (zmodToQZ n).range := by
  constructor
  · intro h
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [← QuotientAddGroup.mk_nsmul, AddCircle.coe_eq_zero_iff] at h
    obtain ⟨m, hm⟩ := h
    refine ⟨(m : ZMod n), ?_⟩
    rw [zmodToQZ_intCast]
    congr 1
    rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hm
    rw [hm]
    field_simp
  · rintro ⟨k, rfl⟩
    rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]

end Brauer

namespace PadicField

open Brauer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

/-- The invariant of a class of `H²(K, μ_n)` lies in `(1/n)ℤ/ℤ`. -/
theorem exists_invEquiv_toBr {n : ℕ} (hn : 0 < n) (β : H2Mu K Ω n) :
    ∃! k : ZMod n, invEquiv p K Ω (toBr n β) = Multiplicative.ofAdd (zmodToQZ n k) := by
  have h1 : (toBr n β) ^ n = 1 := (mem_range_toBr_iff n hn _).1 ⟨β, rfl⟩
  have h2 : n • Multiplicative.toAdd (invEquiv p K Ω (toBr n β)) = 0 := by
    rw [← toAdd_pow, ← map_pow, h1, map_one, toAdd_one]
  obtain ⟨k, hk⟩ := (nsmul_eq_zero_iff_mem_range hn _).1 h2
  refine ⟨k, ?_, fun k' hk' => zmodToQZ_injective hn ?_⟩
  · change _ = Multiplicative.ofAdd (zmodToQZ n k)
    rw [hk, ofAdd_toAdd]
  · rw [hk, hk', toAdd_ofAdd]

/-- The element `k ∈ ℤ/n` with `inv = k/n`. -/
noncomputable def invZMod {n : ℕ} (hn : 0 < n) (β : H2Mu K Ω n) : ZMod n :=
  (exists_invEquiv_toBr (p := p) hn β).exists.choose

theorem invEquiv_toBr {n : ℕ} (hn : 0 < n) (β : H2Mu K Ω n) :
    invEquiv p K Ω (toBr n β) = Multiplicative.ofAdd (zmodToQZ n (invZMod (p := p) hn β)) :=
  (exists_invEquiv_toBr (p := p) hn β).exists.choose_spec

theorem invZMod_eq {n : ℕ} (hn : 0 < n) (β : H2Mu K Ω n) (k : ZMod n)
    (h : invEquiv p K Ω (toBr n β) = Multiplicative.ofAdd (zmodToQZ n k)) :
    invZMod (p := p) hn β = k :=
  (exists_invEquiv_toBr (p := p) hn β).unique (invEquiv_toBr hn β) h

/-- `β ↦ k` with `inv(β) = k/n`, as a homomorphism. -/
noncomputable def invZModHom {n : ℕ} (hn : 0 < n) : H2Mu K Ω n →* Multiplicative (ZMod n) where
  toFun β := Multiplicative.ofAdd (invZMod (p := p) hn β)
  map_one' := by
    rw [invZMod_eq hn 1 0 (by rw [map_one, map_one, map_zero, ofAdd_zero])]
    rfl
  map_mul' β β' := by
    rw [← ofAdd_add]
    congr 1
    apply invZMod_eq
    rw [map_mul, map_mul, invEquiv_toBr hn, invEquiv_toBr hn, map_add, ofAdd_add]

theorem invZModHom_bijective {n : ℕ} (hn : 0 < n) :
    Function.Bijective (invZModHom (p := p) (K := K) (Ω := Ω) hn) := by
  constructor
  · intro β β' h
    have h' : invZMod (p := p) hn β = invZMod (p := p) hn β' := by
      simpa [invZModHom] using h
    apply toBr_injective n hn
    apply (invEquiv p K Ω).injective
    rw [invEquiv_toBr hn, invEquiv_toBr hn, h']
  · intro k
    obtain ⟨α, hα⟩ := (invEquiv p K Ω).surjective
      (Multiplicative.ofAdd (zmodToQZ n (Multiplicative.toAdd k)))
    have hαn : α ^ n = 1 := by
      apply (invEquiv p K Ω).injective
      rw [map_pow, hα, map_one, ← ofAdd_nsmul, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_self,
        zero_mul, map_zero, ofAdd_zero]
    obtain ⟨β, rfl⟩ := (mem_range_toBr_iff n hn α).2 hαn
    refine ⟨β, ?_⟩
    simp only [invZModHom, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [invZMod_eq hn β _ hα]
    rfl

variable (p K Ω) in
/-- **Cyclotomic rigidity**: the canonical isomorphism `H²(Gal(Ω/K), μ_n) ≃ ℤ/n`, `β ↦ k` with
`inv(β) = k/n`. -/
noncomputable def h2MuEquiv {n : ℕ} (hn : 0 < n) : H2Mu K Ω n ≃* Multiplicative (ZMod n) :=
  MulEquiv.ofBijective _ (invZModHom_bijective (p := p) hn)

theorem invEquiv_toBr_h2MuEquiv {n : ℕ} (hn : 0 < n) (β : H2Mu K Ω n) :
    invEquiv p K Ω (toBr n β) =
      Multiplicative.ofAdd (zmodToQZ n (Multiplicative.toAdd (h2MuEquiv p K Ω hn β))) :=
  invEquiv_toBr (p := p) hn β

end PadicField
