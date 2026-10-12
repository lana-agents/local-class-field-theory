/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Second cohomology with locally constant cochains (multiplicative model)

For a topological group `G` acting on a commutative group `M` (written multiplicatively, no
topology on `M`) we define

`ContH2 G M = Z²(G, M) / B²(G, M)`,

where `Z²(G, M)` is the group of *locally constant* functions `f : G × G → M` satisfying the
multiplicative 2-cocycle condition `groupCohomology.IsMulCocycle₂` and `B²(G, M)` consists of the
cocycles of the form `(g, h) ↦ g • x h / x (g * h) * x g` with `x : G → M` locally constant.
For a profinite `G` and a discrete `G`-module `M` this is the continuous cohomology
`H²_cont(G, M)`; for a discrete group `G` it is the ordinary group cohomology `H²(G, M)`.

This is the degree-two analogue of `ContH1` (from `continuous-kummer-theory`).

## Main definitions

* `ContH2.cocycles G M`, `ContH2.coboundaries G M`, `ContH2 G M`, `ContH2.mk`.
* `ContH2.map φ ψ hφ h` : functoriality for a continuous `φ : G' →* G` and a compatible
  `ψ : M →* M'` (inflation and restriction are special cases).

## Main results

* `ContH2.mk_eq_one_iff`, `ContH2.mk_eq_mk_iff`.
* `ContH2.map_injective` : **inflation is injective** in degree two when the first cohomology
  of the kernel vanishes: for `φ : G →* Q` surjective with `Q` discrete, `ψ : A →* M` injective
  onto the invariants of `ker φ`, and `H¹(ker φ, M) = 0`, the map
  `ContH2 Q A → ContH2 G M` is injective.
-/

open groupCohomology

/-- Normalise an identity in a multiplicative commutative group (via `Additive` and `abel`). -/
macro "mul_abel" : tactic =>
  `(tactic| (apply Additive.ofMul.injective
             simp only [ofMul_mul, ofMul_div, ofMul_inv, ofMul_one]
             abel))

namespace ContH2

section Dx

variable (G M : Type*) [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- The 2-coboundary `(g, h) ↦ g • x h / x (g * h) * x g` of a 1-cochain `x`. -/
def dx (x : G → M) : G × G → M := fun gh => gh.1 • x gh.2 / x (gh.1 * gh.2) * x gh.1

variable {G M} in
@[simp]
theorem dx_apply (x : G → M) (g h : G) : dx G M x (g, h) = g • x h / x (g * h) * x g := rfl

variable {G M} in
theorem dx_mul (x y : G → M) : dx G M (x * y) = dx G M x * dx G M y := by
  ext ⟨g, h⟩
  simp only [dx_apply, Pi.mul_apply, smul_mul']
  mul_abel

variable {G M} in
theorem dx_inv (x : G → M) : dx G M x⁻¹ = (dx G M x)⁻¹ := by
  ext ⟨g, h⟩
  simp only [dx_apply, Pi.inv_apply, smul_inv']
  mul_abel

variable {G M} in
theorem dx_one : dx G M 1 = 1 := by
  ext ⟨g, h⟩
  simp

variable {G M} in
theorem isMulCocycle₂_dx (x : G → M) : IsMulCocycle₂ (dx G M x) := by
  intro a b c
  simp only [dx_apply, smul_mul', smul_div', smul_smul, mul_assoc]
  mul_abel

end Dx

section Defs

variable (G M : Type*) [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]

/-- The subgroup of locally constant 2-cocycles `G × G → M`. -/
def cocycles : Subgroup (G × G → M) where
  carrier := {f | IsLocallyConstant f ∧ IsMulCocycle₂ f}
  mul_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨hf.mul hg, fun a b c => ?_⟩
    simp only [Pi.mul_apply, smul_mul']
    calc f (a * b, c) * g (a * b, c) * (f (a, b) * g (a, b))
        = (f (a * b, c) * f (a, b)) * (g (a * b, c) * g (a, b)) := by mul_abel
      _ = (a • f (b, c) * f (a, b * c)) * (a • g (b, c) * g (a, b * c)) := by
          rw [hf' a b c, hg' a b c]
      _ = _ := by mul_abel
  one_mem' := ⟨IsLocallyConstant.const 1, fun a b c => by simp⟩
  inv_mem' := by
    rintro f ⟨hf, hf'⟩
    refine ⟨hf.inv, fun a b c => ?_⟩
    simp only [Pi.inv_apply, smul_inv', ← mul_inv, hf' a b c]

instance : CoeFun (cocycles G M) (fun _ => G × G → M) := ⟨fun c => (c : G × G → M)⟩

variable {G M} in
theorem mem_cocycles_iff {f : G × G → M} :
    f ∈ cocycles G M ↔ IsLocallyConstant f ∧ IsMulCocycle₂ f := Iff.rfl

variable {G M} in
@[simp]
theorem coe_mul_apply (c d : cocycles G M) (g : G × G) : (c * d) g = c g * d g := rfl

variable {G M} in
@[simp]
theorem coe_inv_apply (c : cocycles G M) (g : G × G) : c⁻¹ g = (c g)⁻¹ := rfl

variable {G M} in
@[simp]
theorem coe_div_apply (c d : cocycles G M) (g : G × G) : (c / d) g = c g / d g := rfl

variable {G M} in
@[simp]
theorem coe_one_apply (g : G × G) : (1 : cocycles G M) g = 1 := rfl

variable {G M} in
theorem cocycles_ext {c d : cocycles G M} (h : ∀ x y, c (x, y) = d (x, y)) : c = d :=
  Subtype.ext (funext fun xy => h xy.1 xy.2)

variable {G M} in
theorem isMulCocycle₂ (c : cocycles G M) : IsMulCocycle₂ (c : G × G → M) := c.2.2

variable {G M} in
theorem isLocallyConstant (c : cocycles G M) : IsLocallyConstant (c : G × G → M) := c.2.1

/-- The subgroup of coboundaries of locally constant 1-cochains. -/
def coboundaries : Subgroup (cocycles G M) where
  carrier := {f | ∃ x : G → M, IsLocallyConstant x ∧ dx G M x = f}
  mul_mem' := by
    rintro f g ⟨x, hx, hxf⟩ ⟨y, hy, hyg⟩
    exact ⟨x * y, hx.mul hy, by rw [dx_mul, hxf, hyg]; rfl⟩
  one_mem' := ⟨1, IsLocallyConstant.const 1, by rw [dx_one]; rfl⟩
  inv_mem' := by
    rintro f ⟨x, hx, hxf⟩
    exact ⟨x⁻¹, hx.inv, by rw [dx_inv, hxf]; rfl⟩

variable {G M} in
theorem mem_coboundaries_iff {f : cocycles G M} :
    f ∈ coboundaries G M ↔ ∃ x : G → M, IsLocallyConstant x ∧ dx G M x = f := Iff.rfl

end Defs

end ContH2

section

variable (G M : Type*) [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]

/-- Second cohomology of `G` with values in `M`, computed with locally constant cochains. -/
def ContH2 : Type _ := ContH2.cocycles G M ⧸ ContH2.coboundaries G M

instance : CommGroup (ContH2 G M) := inferInstanceAs (CommGroup (_ ⧸ _))

end

namespace ContH2

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]

/-- The class of a cocycle. -/
def mk : cocycles G M →* ContH2 G M := QuotientGroup.mk' _

theorem mk_surjective : Function.Surjective (mk (G := G) (M := M)) :=
  QuotientGroup.mk'_surjective _

@[elab_as_elim]
theorem induction_on {P : ContH2 G M → Prop} (x : ContH2 G M) (h : ∀ c, P (mk c)) : P x := by
  obtain ⟨c, rfl⟩ := mk_surjective x
  exact h c

theorem mk_eq_one_iff (c : cocycles G M) :
    mk c = 1 ↔ ∃ x : G → M, IsLocallyConstant x ∧ dx G M x = c :=
  QuotientGroup.eq_one_iff c

theorem mk_eq_mk_iff (c d : cocycles G M) :
    mk c = mk d ↔ ∃ x : G → M, IsLocallyConstant x ∧ dx G M x = (c : G × G → M) / d := by
  rw [← div_eq_one, ← map_div, mk_eq_one_iff]
  rfl

/-- Build a cocycle from a function. -/
def mkCocycle (f : G × G → M) (hf : IsLocallyConstant f) (hc : IsMulCocycle₂ f) :
    cocycles G M := ⟨f, hf, hc⟩

@[simp]
theorem coe_mkCocycle (f : G × G → M) (hf : IsLocallyConstant f) (hc : IsMulCocycle₂ f) :
    (mkCocycle f hf hc : G × G → M) = f := rfl

theorem map_one_fst (c : cocycles G M) (g : G) : c (1, g) = c (1, 1) :=
  map_one_fst_of_isMulCocycle₂ (isMulCocycle₂ c) g

theorem map_one_snd (c : cocycles G M) (g : G) : c (g, 1) = g • c (1, 1) :=
  map_one_snd_of_isMulCocycle₂ (isMulCocycle₂ c) g

/-! ### Functoriality -/

section Map

variable {G' M' : Type*} [Group G'] [TopologicalSpace G'] [CommGroup M']
  [MulDistribMulAction G' M']

/-- Pull back a cochain along `φ` and push it forward along `ψ`. -/
def mapFun (φ : G' →* G) (ψ : M →* M') (f : G × G → M) : G' × G' → M' :=
  fun gh => ψ (f (φ gh.1, φ gh.2))

omit [TopologicalSpace G] [TopologicalSpace G'] in
theorem isMulCocycle₂_mapFun (φ : G' →* G) (ψ : M →* M')
    (h : ∀ (g : G') (m : M), ψ (φ g • m) = g • ψ m) {f : G × G → M} (hf : IsMulCocycle₂ f) :
    IsMulCocycle₂ (mapFun φ ψ f) := by
  intro a b c
  simp only [mapFun]
  rw [← h, ← map_mul, ← map_mul, map_mul φ, map_mul φ, hf]

omit [TopologicalSpace G] [TopologicalSpace G'] in
theorem mapFun_dx (φ : G' →* G) (ψ : M →* M') (h : ∀ (g : G') (m : M), ψ (φ g • m) = g • ψ m)
    (x : G → M) : mapFun φ ψ (dx G M x) = dx G' M' (fun g => ψ (x (φ g))) := by
  ext ⟨a, b⟩
  simp only [mapFun, dx_apply, map_mul, map_div, h]

/-- The map on cocycles induced by `(φ, ψ)`. -/
def cocyclesMap (φ : G' →* G) (hφ : Continuous φ) (ψ : M →* M')
    (h : ∀ (g : G') (m : M), ψ (φ g • m) = g • ψ m) : cocycles G M →* cocycles G' M' where
  toFun f := ⟨mapFun φ ψ f, by
    refine ⟨?_, isMulCocycle₂_mapFun φ ψ h (isMulCocycle₂ f)⟩
    exact ((isLocallyConstant f).comp_continuous (hφ.prodMap hφ)).comp _⟩
  map_one' := by ext; simp [mapFun]
  map_mul' f g := by ext; simp [mapFun]

@[simp]
theorem cocyclesMap_apply (φ : G' →* G) (hφ : Continuous φ) (ψ : M →* M')
    (h : ∀ (g : G') (m : M), ψ (φ g • m) = g • ψ m) (f : cocycles G M) (a b : G') :
    cocyclesMap φ hφ ψ h f (a, b) = ψ (f (φ a, φ b)) := rfl

/-- The map `ContH2 G M → ContH2 G' M'` induced by a continuous `φ : G' →* G` and a compatible
`ψ : M →* M'`. -/
def map (φ : G' →* G) (hφ : Continuous φ) (ψ : M →* M')
    (h : ∀ (g : G') (m : M), ψ (φ g • m) = g • ψ m) : ContH2 G M →* ContH2 G' M' :=
  QuotientGroup.map _ _ (cocyclesMap φ hφ ψ h) (by
    rintro f ⟨x, hx, hxf⟩
    refine ⟨fun g => ψ (x (φ g)), ?_, ?_⟩
    · exact (hx.comp_continuous hφ).comp _
    · ext ⟨a, b⟩
      rw [← mapFun_dx φ ψ h, hxf]
      rfl)

@[simp]
theorem map_mk (φ : G' →* G) (hφ : Continuous φ) (ψ : M →* M')
    (h : ∀ (g : G') (m : M), ψ (φ g • m) = g • ψ m) (f : cocycles G M) :
    map φ hφ ψ h (mk f) = mk (cocyclesMap φ hφ ψ h f) := rfl

end Map

/-! ### Injectivity of inflation -/

section Inflation

variable {Q A : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [CommGroup A]
  [MulDistribMulAction Q A]

/-- **Inflation is injective in degree two** if the first cohomology of the kernel vanishes.

Let `φ : G →* Q` be surjective and continuous, `Q` discrete, and `ψ : A →* M` an injective
compatible map whose image consists of the invariants of `ker φ`. Assume that the stabilisers
of elements of `M` are such that `g ↦ g • m` is locally constant, and that every locally
constant 1-cocycle `ker φ → M` is a coboundary. Then `ContH2 Q A → ContH2 G M` is injective. -/
theorem map_injective (φ : G →* Q) (hφ : Continuous φ) (hφs : Function.Surjective φ)
    (ψ : A →* M) (hψ : Function.Injective ψ) (h : ∀ (g : G) (m : A), ψ (φ g • m) = g • ψ m)
    (hfix : ∀ m : M, (∀ n ∈ φ.ker, n • m = m) → m ∈ ψ.range)
    (hsmooth : ∀ m : M, IsLocallyConstant fun g : G => g • m)
    (hH1 : ∀ c : φ.ker → M, IsLocallyConstant c → IsMulCocycle₁ c → IsMulCoboundary₁ c) :
    Function.Injective (map φ hφ ψ h) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro α hα
  rw [MonoidHom.mem_ker] at hα
  induction α using induction_on with | h f => ?_
  rw [Subgroup.mem_bot, mk_eq_one_iff]
  rw [map_mk, mk_eq_one_iff] at hα
  obtain ⟨x, hx, hxf⟩ := hα
  have hF : ∀ a b, dx G M x (a, b) = ψ (f (φ a, φ b)) := fun a b => congrFun hxf (a, b)
  set c := f (1, 1) with hc
  -- `y = x / ψ c` is a cocycle on the kernel.
  have hNN : ∀ n ∈ φ.ker, ∀ n' ∈ φ.ker, n • x n' / x (n * n') * x n = ψ c := by
    intro n hn n' hn'
    rw [MonoidHom.mem_ker] at hn hn'
    have := hF n n'
    rw [dx_apply, hn, hn'] at this
    exact this
  have hfixc : ∀ n ∈ φ.ker, n • ψ c = ψ c := by
    intro n hn
    rw [← h, MonoidHom.mem_ker.1 hn, one_smul]
  let y : φ.ker → M := fun n => x n / ψ c
  have hy : IsMulCocycle₁ y := by
    intro n n'
    have h1 := hNN n n.2 n' n'.2
    have h2 : x (n * n') = (n : G) • x n' * x n / ψ c := by rw [← h1]; mul_abel
    simp only [y, Subgroup.coe_mul, Subgroup.smul_def, smul_div', hfixc n n.2, h2]
    mul_abel
  have hyl : IsLocallyConstant y :=
    ((hx.comp_continuous continuous_subtype_val).div (IsLocallyConstant.const _))
  obtain ⟨m, hm⟩ := hH1 y hyl hy
  -- `z = x / (ψ c * (g • m / m))` vanishes on the kernel.
  let z : G → M := fun g => x g / (ψ c * (g • m / m))
  have hzl : IsLocallyConstant z :=
    hx.div ((IsLocallyConstant.const _).mul ((hsmooth m).div (IsLocallyConstant.const _)))
  have hdz : ∀ a b, dx G M z (a, b) = ψ (f (φ a, φ b)) / a • ψ c := by
    intro a b
    rw [← hF]
    simp only [dx_apply, z, smul_div', smul_mul', smul_smul]
    mul_abel
  have hzN : ∀ n ∈ φ.ker, z n = 1 := by
    intro n hn
    have := hm ⟨n, hn⟩
    simp only [Subgroup.smul_def, y] at this
    simp only [z]
    rw [this]
    mul_abel
  have hψc : ∀ g : G, ψ (f (φ g, 1)) = g • ψ c := by
    intro g
    rw [map_one_snd ⟨f, f.2⟩ (φ g), h]
  have hzr : ∀ g, ∀ n ∈ φ.ker, z (g * n) = z g := by
    intro g n hn
    have := hdz g n
    rw [dx_apply, hzN n hn, smul_one, MonoidHom.mem_ker.1 hn, hψc, div_self'] at this
    rw [one_div, inv_mul_eq_one] at this
    exact this
  have hzl' : ∀ g, ∀ n ∈ φ.ker, n • z g = z (n * g) := by
    intro n g hn
    have := hdz g n
    rw [dx_apply, hzN g hn, mul_one, MonoidHom.mem_ker.1 hn, map_one_fst ⟨f, f.2⟩ (φ n),
      hfixc g hn, div_self', div_eq_one] at this
    exact this
  have hzfix : ∀ g, ∀ n ∈ φ.ker, n • z g = z g := by
    intro g n hn
    have hk : g⁻¹ * n * g ∈ φ.ker := by
      rw [MonoidHom.mem_ker] at hn ⊢
      simp [hn]
    rw [hzl' g n hn, show n * g = g * (g⁻¹ * n * g) by group, hzr g _ hk]
  have hzmem : ∀ g, z g ∈ ψ.range := fun g => hfix _ (hzfix g)
  let s := Function.surjInv hφs
  let w : Q → A := fun q => Classical.choose (hzmem (s q))
  have hw : ∀ g, ψ (w (φ g)) = z g := by
    intro g
    rw [Classical.choose_spec (hzmem (s (φ g)))]
    have hk : g⁻¹ * s (φ g) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, Function.surjInv_eq hφs, map_inv, inv_mul_cancel]
    rw [← hzr g _ hk, mul_inv_cancel_left]
  have hdw : ∀ a b, dx Q A w (a, b) = f (a, b) / a • c := by
    intro a b
    obtain ⟨g, rfl⟩ := hφs a
    obtain ⟨g', rfl⟩ := hφs b
    apply hψ
    rw [map_div, h, ← hdz, dx_apply, dx_apply, map_mul, map_div, h, ← map_mul, hw, hw, hw]
  refine ⟨w * fun _ => c, IsLocallyConstant.of_discrete _, ?_⟩
  ext ⟨a, b⟩
  rw [dx_mul, Pi.mul_apply, hdw]
  simp only [dx_apply]
  mul_abel

end Inflation

end ContH2
