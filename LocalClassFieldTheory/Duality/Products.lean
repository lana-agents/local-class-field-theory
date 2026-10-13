/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.ZModPrime

/-!
# Local Tate duality for products and along isomorphisms

* `H^i(G, M₁ × M₂) ≃ H^i(G, M₁) × H^i(G, M₂)` for `i = 0, 1, 2` (`Brauer.h0_prod_bijective`,
  `Brauer.h1_prod_bijective`, `Brauer.h2_prod_bijective`, via the projections);
* the product `e₁ × e₂ : (M₁ × M₂) × (N₁ × N₂) → P` of two pairings (`Brauer.GPairing.prod`), whose
  cup products are the products of the cup products of `e₁` and `e₂`; perfectness of `e₁` and
  `e₂` in a degree implies perfectness of `e₁ × e₂` (`Brauer.perfectDeg0_prod`, ...);
* the Cartier dual of a product is the product of the Cartier duals
  (`Brauer.CartierDual.prodEquiv`);
* **`PadicField.tateDualityFor_prod`**: local Tate duality for `M` and `N` (killed by `n`) implies
  it for `M × N`; **`PadicField.tateDualityFor_of_equiv`**: invariance under equivariant
  isomorphisms (transport in both arguments of the pairing).

Consequently local Tate duality holds for all finite products of copies of `ℤ/ℓ` and `μ_ℓ`
(`ℓ` prime, `PadicField.tateDualityFor_trivZMod_prime`, `PadicField.tateDualityFor_mu_prime`) and,
when `μ_n ⊆ K`, of `ℤ/n` and `μ_n`; e.g. every finite module with trivial action killed by a
prime `ℓ` (`PadicField.tateDualityFor_of_trivial_prime`).
-/

open ContH2 groupCohomology KummerTheory

set_option linter.unusedSectionVars false

namespace Brauer

/-! ### An abstract bijectivity criterion -/

/-- If `F₁ : X₁ → Hom(A₁, Z)` and `F₂ : X₂ → Hom(A₂, Z)` are bijective, `X ≃ X₁ × X₂` and
`B ≃ A₁ × A₂`, then `x ↦ (b ↦ F₁(x₁)(b₁) F₂(x₂)(b₂))` is a bijection `X → Hom(B, Z)`. -/
theorem bijective_prod_hom {X X₁ X₂ A₁ A₂ B Z : Type*} [Group A₁] [Group A₂] [Group B]
    [CommGroup Z] (F₁ : X₁ → (A₁ →* Z)) (F₂ : X₂ → (A₂ →* Z)) (hF₁ : Function.Bijective F₁)
    (hF₂ : Function.Bijective F₂) (d₁ : X → X₁) (d₂ : X → X₂)
    (hd : Function.Bijective fun x => (d₁ x, d₂ x)) (q₁ : B →* A₁) (q₂ : B →* A₂)
    (hq : Function.Bijective fun b => (q₁ b, q₂ b)) (F : X → (B →* Z))
    (hF : ∀ x b, F x b = F₁ (d₁ x) (q₁ b) * F₂ (d₂ x) (q₂ b)) : Function.Bijective F := by
  set e : B ≃* A₁ × A₂ := MulEquiv.ofBijective (q₁.prod q₂) hq
  have he : ∀ b, e b = (q₁ b, q₂ b) := fun _ => rfl
  have hq₁ : ∀ a, q₁ (e.symm (a, 1)) = a := fun a => congrArg Prod.fst (e.apply_symm_apply (a, 1))
  have hq₂ : ∀ a, q₂ (e.symm (a, 1)) = 1 := fun a => congrArg Prod.snd (e.apply_symm_apply (a, 1))
  have hq₁' : ∀ a, q₁ (e.symm (1, a)) = 1 := fun a => congrArg Prod.fst (e.apply_symm_apply (1, a))
  have hq₂' : ∀ a, q₂ (e.symm (1, a)) = a := fun a => congrArg Prod.snd (e.apply_symm_apply (1, a))
  constructor
  · intro x y hxy
    have h1 : F₁ (d₁ x) = F₁ (d₁ y) := MonoidHom.ext fun a => by
      have := DFunLike.congr_fun hxy (e.symm (a, 1))
      rwa [hF, hF, hq₁, hq₂, map_one, map_one, mul_one, mul_one] at this
    have h2 : F₂ (d₂ x) = F₂ (d₂ y) := MonoidHom.ext fun a => by
      have := DFunLike.congr_fun hxy (e.symm (1, a))
      rwa [hF, hF, hq₁', hq₂', map_one, map_one, one_mul, one_mul] at this
    exact hd.1 (Prod.ext (hF₁.1 h1) (hF₂.1 h2))
  · intro ψ
    obtain ⟨x₁, hx₁⟩ := hF₁.2 (ψ.comp (e.symm.toMonoidHom.comp (MonoidHom.inl A₁ A₂)))
    obtain ⟨x₂, hx₂⟩ := hF₂.2 (ψ.comp (e.symm.toMonoidHom.comp (MonoidHom.inr A₁ A₂)))
    obtain ⟨x, hx⟩ := hd.2 (x₁, x₂)
    refine ⟨x, MonoidHom.ext fun b => ?_⟩
    have h1 : d₁ x = x₁ := congrArg Prod.fst hx
    have h2 : d₂ x = x₂ := congrArg Prod.snd hx
    rw [hF, h1, h2, hx₁, hx₂]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.inl_apply,
      MonoidHom.inr_apply]
    rw [← map_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, ← he, e.symm_apply_apply]

variable {G : Type*} [Group G] [TopologicalSpace G]

/-! ### Cohomology of products -/

section ProdCohomology

variable {M₁ M₂ : Type*} [CommGroup M₁] [CommGroup M₂] [MulDistribMulAction G M₁]
  [MulDistribMulAction G M₂]

theorem fst_smul (g : G) (m : M₁ × M₂) : MonoidHom.fst M₁ M₂ (g • m) = g • m.1 := rfl

theorem snd_smul (g : G) (m : M₁ × M₂) : MonoidHom.snd M₁ M₂ (g • m) = g • m.2 := rfl

theorem h0_prod_bijective :
    Function.Bijective fun x : H0 G (M₁ × M₂) =>
      (h0Hom (MonoidHom.fst M₁ M₂) fst_smul x, h0Hom (MonoidHom.snd M₁ M₂) snd_smul x) := by
  refine ⟨fun x y h => Subtype.ext (Prod.ext (congrArg Subtype.val (congrArg Prod.fst h))
    (congrArg Subtype.val (congrArg Prod.snd h))), fun y => ?_⟩
  refine ⟨⟨((y.1 : M₁), (y.2 : M₂)), fun g => Prod.ext (smul_H0 y.1 g) (smul_H0 y.2 g)⟩, ?_⟩
  rfl

theorem h2_prod_bijective :
    Function.Bijective fun β : ContH2 G (M₁ × M₂) =>
      (h2Hom (MonoidHom.fst M₁ M₂) fst_smul β, h2Hom (MonoidHom.snd M₁ M₂) snd_smul β) := by
  constructor
  · intro β β' h
    induction β using induction_on with | h f => ?_
    induction β' using induction_on with | h f' => ?_
    simp only [h2Hom_mk, Prod.mk.injEq, mk_eq_mk_iff] at h
    obtain ⟨⟨x₁, hx₁, h₁⟩, ⟨x₂, hx₂, h₂⟩⟩ := h
    rw [mk_eq_mk_iff]
    refine ⟨fun g => (x₁ g, x₂ g), hx₁.prodMk hx₂, funext fun gh => ?_⟩
    obtain ⟨g, h⟩ := gh
    exact Prod.ext (congrFun h₁ (g, h)) (congrFun h₂ (g, h))
  · rintro ⟨β₁, β₂⟩
    induction β₁ using induction_on with | h f₁ => ?_
    induction β₂ using induction_on with | h f₂ => ?_
    refine ⟨mk (mkCocycle (fun gh => (f₁ gh, f₂ gh))
      ((isLocallyConstant f₁).prodMk (isLocallyConstant f₂))
      (fun a b c => Prod.ext (isMulCocycle₂ f₁ a b c) (isMulCocycle₂ f₂ a b c))), ?_⟩
    rfl

variable [TopologicalSpace M₁] [DiscreteTopology M₁] [IsTopologicalGroup M₁]
  [TopologicalSpace M₂] [DiscreteTopology M₂] [IsTopologicalGroup M₂]

theorem h1_prod_bijective :
    Function.Bijective fun x : ContH1 G (M₁ × M₂) =>
      (h1Hom (MonoidHom.fst M₁ M₂) fst_smul x, h1Hom (MonoidHom.snd M₁ M₂) snd_smul x) := by
  constructor
  · intro x x' h
    induction x using ContH1.induction_on with | h f => ?_
    induction x' using ContH1.induction_on with | h f' => ?_
    simp only [h1Hom_mk, Prod.mk.injEq, ContH1.mk_eq_mk_iff] at h
    obtain ⟨⟨m₁, h₁⟩, ⟨m₂, h₂⟩⟩ := h
    rw [ContH1.mk_eq_mk_iff]
    exact ⟨(m₁, m₂), fun g => Prod.ext (h₁ g) (h₂ g)⟩
  · rintro ⟨x₁, x₂⟩
    induction x₁ using ContH1.induction_on with | h f₁ => ?_
    induction x₂ using ContH1.induction_on with | h f₂ => ?_
    refine ⟨ContH1.mk (ContH1.mkCocycle (fun g => (f₁ g, f₂ g))
      ((ContH1.continuous f₁).prodMk (ContH1.continuous f₂))
      (fun a b => Prod.ext (ContH1.isMulCocycle₁ f₁ a b) (ContH1.isMulCocycle₁ f₂ a b))), ?_⟩
    rfl

end ProdCohomology

/-! ### Products of pairings -/

section ProdPairing

variable {M₁ M₂ N₁ N₂ P : Type*} [CommGroup M₁] [CommGroup M₂] [CommGroup N₁] [CommGroup N₂]
  [CommGroup P] [MulDistribMulAction G M₁] [MulDistribMulAction G M₂] [MulDistribMulAction G N₁]
  [MulDistribMulAction G N₂] [MulDistribMulAction G P]

/-- The product pairing `((m₁, m₂), (n₁, n₂)) ↦ e₁(m₁, n₁) e₂(m₂, n₂)`. -/
def GPairing.prod (e₁ : GPairing G M₁ N₁ P) (e₂ : GPairing G M₂ N₂ P) :
    GPairing G (M₁ × M₂) (N₁ × N₂) P where
  toHom :=
    { toFun := fun m => (e₁.toHom m.1).comp (MonoidHom.fst N₁ N₂) *
        (e₂.toHom m.2).comp (MonoidHom.snd N₁ N₂)
      map_one' := MonoidHom.ext fun n => by simp
      map_mul' := fun m m' => MonoidHom.ext fun n => by
        change e₁.toHom (m.1 * m'.1) n.1 * e₂.toHom (m.2 * m'.2) n.2 =
          (e₁.toHom m.1 n.1 * e₂.toHom m.2 n.2) * (e₁.toHom m'.1 n.1 * e₂.toHom m'.2 n.2)
        rw [map_mul, map_mul, MonoidHom.mul_apply, MonoidHom.mul_apply]
        mul_abel }
  map_smul' g m n := by
    change e₁.toHom (g • m.1) (g • n.1) * e₂.toHom (g • m.2) (g • n.2) = _
    rw [e₁.map_smul, e₂.map_smul]
    exact (smul_mul' g _ _).symm

theorem GPairing.prod_apply (e₁ : GPairing G M₁ N₁ P) (e₂ : GPairing G M₂ N₂ P) (m : M₁ × M₂)
    (n : N₁ × N₂) : (e₁.prod e₂).toHom m n = e₁.toHom m.1 n.1 * e₂.toHom m.2 n.2 := rfl

theorem cup02_prod (e₁ : GPairing G M₁ N₁ P) (e₂ : GPairing G M₂ N₂ P) (x : H0 G (M₁ × M₂))
    (β : ContH2 G (N₁ × N₂)) :
    cup02 (e₁.prod e₂) x β = cup02 e₁ (h0Hom (MonoidHom.fst M₁ M₂) fst_smul x)
      (h2Hom (MonoidHom.fst N₁ N₂) fst_smul β) *
      cup02 e₂ (h0Hom (MonoidHom.snd M₁ M₂) snd_smul x)
        (h2Hom (MonoidHom.snd N₁ N₂) snd_smul β) := by
  induction β using induction_on with | h f => ?_
  rw [cup02_mk, h2Hom_mk, h2Hom_mk, cup02_mk, cup02_mk, ← map_mul]
  rfl

theorem cup20_prod (e₁ : GPairing G M₁ N₁ P) (e₂ : GPairing G M₂ N₂ P) (β : ContH2 G (M₁ × M₂))
    (x : H0 G (N₁ × N₂)) :
    cup20 (e₁.prod e₂) β x = cup20 e₁ (h2Hom (MonoidHom.fst M₁ M₂) fst_smul β)
      (h0Hom (MonoidHom.fst N₁ N₂) fst_smul x) *
      cup20 e₂ (h2Hom (MonoidHom.snd M₁ M₂) snd_smul β)
        (h0Hom (MonoidHom.snd N₁ N₂) snd_smul x) := by
  induction β using induction_on with | h f => ?_
  rw [cup20_apply, cup20_apply, cup20_apply, cup02_mk, h2Hom_mk, h2Hom_mk, cup02_mk, cup02_mk,
    ← map_mul]
  rfl

variable [TopologicalSpace M₁] [DiscreteTopology M₁] [IsTopologicalGroup M₁]
  [TopologicalSpace M₂] [DiscreteTopology M₂] [IsTopologicalGroup M₂]
  [TopologicalSpace N₁] [DiscreteTopology N₁] [IsTopologicalGroup N₁] [SmoothAction G N₁]
  [TopologicalSpace N₂] [DiscreteTopology N₂] [IsTopologicalGroup N₂] [SmoothAction G N₂]

theorem cup11_prod (e₁ : GPairing G M₁ N₁ P) (e₂ : GPairing G M₂ N₂ P) (x : ContH1 G (M₁ × M₂))
    (y : ContH1 G (N₁ × N₂)) :
    cup11 (e₁.prod e₂) x y = cup11 e₁ (h1Hom (MonoidHom.fst M₁ M₂) fst_smul x)
      (h1Hom (MonoidHom.fst N₁ N₂) fst_smul y) *
      cup11 e₂ (h1Hom (MonoidHom.snd M₁ M₂) snd_smul x)
        (h1Hom (MonoidHom.snd N₁ N₂) snd_smul y) := by
  induction x using ContH1.induction_on with | h x => ?_
  induction y using ContH1.induction_on with | h y => ?_
  rw [cup11_mk, h1Hom_mk, h1Hom_mk, h1Hom_mk, h1Hom_mk, cup11_mk, cup11_mk, ← map_mul]
  rfl

end ProdPairing

/-! ### Perfectness of product pairings -/

section PerfectProd

variable {M₁ M₂ N₁ N₂ P : Type*} [CommGroup M₁] [CommGroup M₂] [CommGroup N₁] [CommGroup N₂]
  [CommGroup P] [MulDistribMulAction G M₁] [MulDistribMulAction G M₂] [MulDistribMulAction G N₁]
  [MulDistribMulAction G N₂] [MulDistribMulAction G P] {n : ℕ}
  (χ : ContH2 G P →* Multiplicative (ZMod n)) (e₁ : GPairing G M₁ N₁ P) (e₂ : GPairing G M₂ N₂ P)

theorem perfectDeg0_prod (h₁ : PerfectDeg0 χ e₁) (h₂ : PerfectDeg0 χ e₂) :
    PerfectDeg0 χ (e₁.prod e₂) :=
  bijective_prod_hom _ _ h₁ h₂ _ _ h0_prod_bijective _ _ h2_prod_bijective _
    fun x β => by simp only [MonoidHom.comp_apply, cup02_prod, map_mul]

theorem perfectDeg2_prod (h₁ : PerfectDeg2 χ e₁) (h₂ : PerfectDeg2 χ e₂) :
    PerfectDeg2 χ (e₁.prod e₂) :=
  bijective_prod_hom _ _ h₁ h₂ _ _ h2_prod_bijective _ _ h0_prod_bijective _
    fun β x => by simp only [MonoidHom.comp_apply, cup20_prod, map_mul]

variable [TopologicalSpace M₁] [DiscreteTopology M₁] [IsTopologicalGroup M₁]
  [TopologicalSpace M₂] [DiscreteTopology M₂] [IsTopologicalGroup M₂]
  [TopologicalSpace N₁] [DiscreteTopology N₁] [IsTopologicalGroup N₁] [SmoothAction G N₁]
  [TopologicalSpace N₂] [DiscreteTopology N₂] [IsTopologicalGroup N₂] [SmoothAction G N₂]

theorem perfectDeg1_prod (h₁ : PerfectDeg1 χ e₁) (h₂ : PerfectDeg1 χ e₂) :
    PerfectDeg1 χ (e₁.prod e₂) :=
  bijective_prod_hom _ _ h₁ h₂ _ _ h1_prod_bijective _ _ h1_prod_bijective _
    fun x y => by simp only [MonoidHom.comp_apply, cup11_prod, map_mul]

end PerfectProd

/-! ### Transport in the first argument -/

section Left

variable {M M' N P : Type*} [CommGroup M] [CommGroup M'] [CommGroup N] [CommGroup P]
  [MulDistribMulAction G M] [MulDistribMulAction G M'] [MulDistribMulAction G N]
  [MulDistribMulAction G P]

/-- The pairing `(m', n) ↦ e(σ m', n)`. -/
def GPairing.comapLeft (e : GPairing G M N P) (σ : M' ≃* M)
    (hσ : ∀ (g : G) (x : M'), σ (g • x) = g • σ x) : GPairing G M' N P where
  toHom := e.toHom.comp σ.toMonoidHom
  map_smul' g m x := by
    change e.toHom (σ (g • m)) (g • x) = g • e.toHom (σ m) x
    rw [hσ, e.map_smul]

theorem cup02_h0Map_left (σ : M ≃* M') (hσ : ∀ (g : G) (x : M), σ (g • x) = g • σ x)
    (e : GPairing G M N P) (e' : GPairing G M' N P) (he : ∀ m x, e'.toHom (σ m) x = e.toHom m x)
    (m : H0 G M) (β : ContH2 G N) : cup02 e' (h0Map σ hσ m) β = cup02 e m β := by
  induction β using induction_on with | h f => ?_
  rw [cup02_mk, cup02_mk]
  congr 1
  exact cocycles_ext fun a b => he _ _

theorem cup20_h2Map_left (σ : M ≃* M') (hσ : ∀ (g : G) (x : M), σ (g • x) = g • σ x)
    (e : GPairing G M N P) (e' : GPairing G M' N P) (he : ∀ m x, e'.toHom (σ m) x = e.toHom m x)
    (β : ContH2 G M) (x : H0 G N) : cup20 e' (h2Map σ hσ β) x = cup20 e β x := by
  induction β using induction_on with | h f => ?_
  rw [cup20_apply, cup20_apply, h2Map, map_mk, cup02_mk, cup02_mk]
  congr 1
  exact cocycles_ext fun a b => he _ _

theorem perfectDeg0_iff_of_equiv_left {n : ℕ} (χ : ContH2 G P →* Multiplicative (ZMod n))
    (σ : M ≃* M') (hσ : ∀ (g : G) (x : M), σ (g • x) = g • σ x)
    (e : GPairing G M N P) (e' : GPairing G M' N P) (he : ∀ m x, e'.toHom (σ m) x = e.toHom m x) :
    PerfectDeg0 χ e' ↔ PerfectDeg0 χ e := by
  have h : (fun m : H0 G M => χ.comp (cup02 e m)) =
      (fun m : H0 G M' => χ.comp (cup02 e' m)) ∘ h0Map σ hσ := by
    funext m
    exact MonoidHom.ext fun β => by simp [cup02_h0Map_left σ hσ e e' he]
  rw [PerfectDeg0, PerfectDeg0, h, Function.Bijective.of_comp_iff _ (h0Map_bijective σ hσ)]

theorem perfectDeg2_iff_of_equiv_left {n : ℕ} (χ : ContH2 G P →* Multiplicative (ZMod n))
    (σ : M ≃* M') (hσ : ∀ (g : G) (x : M), σ (g • x) = g • σ x)
    (e : GPairing G M N P) (e' : GPairing G M' N P) (he : ∀ m x, e'.toHom (σ m) x = e.toHom m x) :
    PerfectDeg2 χ e' ↔ PerfectDeg2 χ e := by
  have h : (fun β : ContH2 G M => χ.comp (cup20 e β)) =
      (fun β : ContH2 G M' => χ.comp (cup20 e' β)) ∘ h2Map σ hσ := by
    funext β
    exact MonoidHom.ext fun x => by simp [cup20_h2Map_left σ hσ e e' he]
  rw [PerfectDeg2, PerfectDeg2, h, Function.Bijective.of_comp_iff _ (h2Map_bijective σ hσ)]

variable [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalGroup M] [SmoothAction G M]
  [TopologicalSpace M'] [DiscreteTopology M'] [IsTopologicalGroup M'] [SmoothAction G M']
  [TopologicalSpace N] [DiscreteTopology N] [IsTopologicalGroup N] [SmoothAction G N]

theorem cup11_h1Map_left (σ : M ≃* M') (hσ : ∀ (g : G) (x : M), σ (g • x) = g • σ x)
    (e : GPairing G M N P) (e' : GPairing G M' N P) (he : ∀ m x, e'.toHom (σ m) x = e.toHom m x)
    (x : ContH1 G M) (y : ContH1 G N) : cup11 e' (h1Map σ hσ x) y = cup11 e x y := by
  induction x using ContH1.induction_on with | h x => ?_
  induction y using ContH1.induction_on with | h y => ?_
  simp only [h1Map, ContH1.map_mk, cup11_mk]
  congr 1
  exact cocycles_ext fun a b => he _ _

theorem perfectDeg1_iff_of_equiv_left {n : ℕ} (χ : ContH2 G P →* Multiplicative (ZMod n))
    (σ : M ≃* M') (hσ : ∀ (g : G) (x : M), σ (g • x) = g • σ x)
    (e : GPairing G M N P) (e' : GPairing G M' N P) (he : ∀ m x, e'.toHom (σ m) x = e.toHom m x) :
    PerfectDeg1 χ e' ↔ PerfectDeg1 χ e := by
  have h : (fun x : ContH1 G M => χ.comp (cup11 e x)) =
      (fun x : ContH1 G M' => χ.comp (cup11 e' x)) ∘ h1Map σ hσ := by
    funext x
    exact MonoidHom.ext fun y => by simp [cup11_h1Map_left σ hσ e e' he]
  rw [PerfectDeg1, PerfectDeg1, h, Function.Bijective.of_comp_iff _ (h1Map_bijective σ hσ)]

end Left

/-! ### Cartier duals of products and isomorphisms -/

namespace CartierDual

variable {n : ℕ} {Ω : Type*} [Field Ω] {M N M' : Type*} [CommGroup M] [CommGroup N]
  [CommGroup M'] [MulDistribMulAction G M] [MulDistribMulAction G N] [MulDistribMulAction G M']
  [MulDistribMulAction G (Mu n Ω)]

/-- `Hom(M × N, μ_n) ≃ Hom(M, μ_n) × Hom(N, μ_n)`. -/
def prodEquiv : CartierDual n Ω (M × N) ≃* CartierDual n Ω M × CartierDual n Ω N where
  toFun φ := (toHom.symm ((toHom φ).comp (MonoidHom.inl M N)),
    toHom.symm ((toHom φ).comp (MonoidHom.inr M N)))
  invFun ψ := toHom.symm ((toHom ψ.1).coprod (toHom ψ.2))
  left_inv φ := by
    apply toHom.injective
    refine MonoidHom.ext fun m => ?_
    change toHom φ (m.1, 1) * toHom φ (1, m.2) = toHom φ m
    rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  right_inv ψ := by
    refine Prod.ext (toHom.injective (MonoidHom.ext fun m => ?_))
      (toHom.injective (MonoidHom.ext fun m => ?_))
    · change toHom ψ.1 m * toHom ψ.2 1 = toHom ψ.1 m
      rw [map_one, mul_one]
    · change toHom ψ.1 1 * toHom ψ.2 m = toHom ψ.2 m
      rw [map_one, one_mul]
  map_mul' _ _ := rfl

theorem prodEquiv_smul (g : G) (φ : CartierDual n Ω (M × N)) :
    prodEquiv (g • φ) = g • prodEquiv φ := by
  refine Prod.ext (toHom.injective (MonoidHom.ext fun m => ?_))
    (toHom.injective (MonoidHom.ext fun m => ?_))
  · change g • toHom φ (g⁻¹ • (m, 1)) = g • toHom φ (g⁻¹ • m, 1)
    rw [Prod.smul_mk, smul_one]
  · change g • toHom φ (g⁻¹ • (1, m)) = g • toHom φ (1, g⁻¹ • m)
    rw [Prod.smul_mk, smul_one]

theorem evalPairing_prodEquiv (m : M × N) (φ : CartierDual n Ω (M × N)) :
    ((evalPairing (G := G)).prod (evalPairing (G := G))).toHom m (prodEquiv φ) =
      (evalPairing (G := G)).toHom m φ := by
  change toHom φ (m.1, 1) * toHom φ (1, m.2) = toHom φ m
  rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

/-- `Hom(M', μ_n) ≃ Hom(M, μ_n)`, `ψ ↦ ψ ∘ σ`, for `σ : M ≃ M'`. -/
def congrEquiv (σ : M ≃* M') : CartierDual n Ω M' ≃* CartierDual n Ω M where
  toFun ψ := toHom.symm ((toHom ψ).comp σ.toMonoidHom)
  invFun φ := toHom.symm ((toHom φ).comp σ.symm.toMonoidHom)
  left_inv ψ := toHom.injective (MonoidHom.ext fun m => by
    change toHom ψ (σ (σ.symm m)) = toHom ψ m
    rw [σ.apply_symm_apply])
  right_inv φ := toHom.injective (MonoidHom.ext fun m => by
    change toHom φ (σ.symm (σ m)) = toHom φ m
    rw [σ.symm_apply_apply])
  map_mul' _ _ := rfl

theorem congrEquiv_smul (σ : M ≃* M') (hσ : ∀ (g : G) (x : M), σ (g • x) = g • σ x) (g : G)
    (ψ : CartierDual n Ω M') : congrEquiv σ (g • ψ) = g • congrEquiv σ ψ := by
  refine toHom.injective (MonoidHom.ext fun m => ?_)
  change g • toHom ψ (g⁻¹ • σ m) = g • toHom ψ (σ (g⁻¹ • m))
  rw [hσ]

end CartierDual

end Brauer

namespace PadicField

open Brauer

universe u

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
variable {n : ℕ} [NeZero n]

section Prod

variable {M N : Type*} [CommGroup M] [CommGroup N] [Finite M] [Finite N]
  [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalGroup M]
  [TopologicalSpace N] [DiscreteTopology N] [IsTopologicalGroup N]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) N]
  [SmoothAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) N]

/-- **Local Tate duality for a product** `M × N`. -/
theorem tateDualityFor_prod (hM : TateDualityFor p K Ω M n) (hN : TateDualityFor p K Ω N n) :
    TateDualityFor p K Ω (M × N) n := by
  obtain ⟨h0M, h1M, h2M⟩ := hM
  obtain ⟨h0N, h1N, h2N⟩ := hN
  have hτ : ∀ (g : Ω ≃ₐ[K] Ω) (φ : CartierDual n Ω (M × N)),
      CartierDual.prodEquiv (g • φ) = g • CartierDual.prodEquiv φ := CartierDual.prodEquiv_smul
  exact ⟨(perfectDeg0_iff_of_equiv _ _ hτ _ _ CartierDual.evalPairing_prodEquiv).1
      (perfectDeg0_prod _ _ _ h0M h0N),
    (perfectDeg1_iff_of_equiv _ _ hτ _ _ CartierDual.evalPairing_prodEquiv).1
      (perfectDeg1_prod _ _ _ h1M h1N),
    (perfectDeg2_iff_of_equiv _ _ hτ _ _ CartierDual.evalPairing_prodEquiv).1
      (perfectDeg2_prod _ _ _ h2M h2N)⟩

end Prod

section Equiv

variable {M M' : Type*} [CommGroup M] [CommGroup M'] [Finite M] [Finite M']
  [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalGroup M]
  [TopologicalSpace M'] [DiscreteTopology M'] [IsTopologicalGroup M']
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M']
  [SmoothAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M']

/-- **Local Tate duality is invariant under equivariant isomorphisms.** -/
theorem tateDualityFor_of_equiv (σ : M ≃* M')
    (hσ : ∀ (g : Ω ≃ₐ[K] Ω) (x : M), σ (g • x) = g • σ x) (h : TateDualityFor p K Ω M n) :
    TateDualityFor p K Ω M' n := by
  obtain ⟨h0, h1, h2⟩ := h
  set ρ : CartierDual n Ω M' ≃* CartierDual n Ω M := CartierDual.congrEquiv σ
  have hρ : ∀ (g : Ω ≃ₐ[K] Ω) (ψ : CartierDual n Ω M'), ρ (g • ψ) = g • ρ ψ :=
    CartierDual.congrEquiv_smul σ hσ
  set e' : GPairing (Ω ≃ₐ[K] Ω) M' (CartierDual n Ω M) (Mu n Ω) :=
    (CartierDual.evalPairing (n := n) (Ω := Ω) (M := M)).comapLeft σ.symm (symm_smul σ hσ)
  have heR : ∀ (m : M') (ψ : CartierDual n Ω M'),
      e'.toHom m (ρ ψ) = (CartierDual.evalPairing (G := Ω ≃ₐ[K] Ω)).toHom m ψ := by
    intro m ψ
    change CartierDual.toHom ψ (σ (σ.symm m)) = CartierDual.toHom ψ m
    rw [σ.apply_symm_apply]
  have heL : ∀ (m : M) (φ : CartierDual n Ω M),
      e'.toHom (σ m) φ = (CartierDual.evalPairing (G := Ω ≃ₐ[K] Ω)).toHom m φ := by
    intro m φ
    change CartierDual.toHom φ (σ.symm (σ m)) = CartierDual.toHom φ m
    rw [σ.symm_apply_apply]
  exact ⟨(perfectDeg0_iff_of_equiv _ ρ hρ _ e' heR).1
      ((perfectDeg0_iff_of_equiv_left _ σ hσ _ e' heL).2 h0),
    (perfectDeg1_iff_of_equiv _ ρ hρ _ e' heR).1
      ((perfectDeg1_iff_of_equiv_left _ σ hσ _ e' heL).2 h1),
    (perfectDeg2_iff_of_equiv _ ρ hρ _ e' heR).1
      ((perfectDeg2_iff_of_equiv_left _ σ hσ _ e' heL).2 h2)⟩

end Equiv

section Subsingleton

variable {M : Type*} [CommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  [IsTopologicalGroup M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]

theorem subsingleton_h1_of_subsingleton {N : Type*} [CommGroup N] [TopologicalSpace N]
    [IsTopologicalGroup N] [MulDistribMulAction (Ω ≃ₐ[K] Ω) N] [Subsingleton N] :
    Subsingleton (ContH1 (Ω ≃ₐ[K] Ω) N) := ⟨fun x y => by
  induction x using ContH1.induction_on with | h x => ?_
  induction y using ContH1.induction_on with | h y => ?_
  congr 1
  exact Subtype.ext (funext fun _ => Subsingleton.elim _ _)⟩

theorem subsingleton_h2_of_subsingleton {N : Type*} [CommGroup N]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) N] [Subsingleton N] :
    Subsingleton (ContH2 (Ω ≃ₐ[K] Ω) N) := ⟨fun x y => by
  induction x using induction_on with | h x => ?_
  induction y using induction_on with | h y => ?_
  congr 1
  exact Subtype.ext (funext fun _ => Subsingleton.elim _ _)⟩

instance subsingleton_cartierDual [Subsingleton M] : Subsingleton (CartierDual n Ω M) :=
  ⟨fun φ ψ => CartierDual.toHom.injective (MonoidHom.ext fun m => by
    rw [Subsingleton.elim m 1, map_one, map_one])⟩

/-- Local Tate duality for the trivial module. -/
theorem tateDualityFor_of_subsingleton [Subsingleton M] : TateDualityFor p K Ω M n := by
  haveI := subsingleton_h1_of_subsingleton (K := K) (Ω := Ω) (N := M)
  haveI := subsingleton_h2_of_subsingleton (K := K) (Ω := Ω) (N := M)
  haveI := subsingleton_h1_of_subsingleton (K := K) (Ω := Ω) (N := CartierDual n Ω M)
  haveI := subsingleton_h2_of_subsingleton (K := K) (Ω := Ω) (N := CartierDual n Ω M)
  exact ⟨bijective_of_subsingleton _, bijective_of_subsingleton _, bijective_of_subsingleton _⟩

end Subsingleton

/-- **Local Tate duality for a finite product.** -/
theorem tateDualityFor_pi : ∀ (k : ℕ) (Z : Fin k → Type u) [∀ j, CommGroup (Z j)]
    [∀ j, Finite (Z j)] [∀ j, TopologicalSpace (Z j)] [∀ j, DiscreteTopology (Z j)]
    [∀ j, IsTopologicalGroup (Z j)] [∀ j, MulDistribMulAction (Ω ≃ₐ[K] Ω) (Z j)]
    [∀ j, SmoothAction (Ω ≃ₐ[K] Ω) (Z j)], (∀ j, TateDualityFor p K Ω (Z j) n) →
    TateDualityFor p K Ω (∀ j, Z j) n
  | 0, _, _, _, _, _, _, _, _, _ => tateDualityFor_of_subsingleton
  | k + 1, Z, _, _, _, _, _, _, _, h => by
    have hP := tateDualityFor_prod (h 0) (tateDualityFor_pi k (fun j => Z j.succ) fun j => h j.succ)
    exact tateDualityFor_of_equiv (piFinSuccMulEquiv Z).symm
      (symm_smul (piFinSuccMulEquiv Z) fun _ _ => rfl) hP

include hp in
/-- **Local Tate duality for finite modules with trivial action killed by a prime `ℓ`**
(`M ≃ (ℤ/ℓ)^r`), without any assumption on `K`. -/
theorem tateDualityFor_of_trivial_prime (ℓ : ℕ) [Fact ℓ.Prime] (M : Type*) [CommGroup M]
    [Finite M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalGroup M]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]
    (htriv : ∀ (g : Ω ≃ₐ[K] Ω) (m : M), g • m = m) (hM : ∀ m : M, m ^ ℓ = 1) :
    TateDualityFor p K Ω M ℓ := by
  obtain ⟨ι, _, e, he, ⟨E⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite M
  have hℓ : ∀ i, e i = ℓ := fun i => by
    have h1 := (dvd_exponent_of_equiv E i).trans (Monoid.exponent_dvd_of_forall_pow_eq_one hM)
    rcases (Nat.dvd_prime (Fact.out : ℓ.Prime)).1 h1 with h | h
    · exact absurd h (he i).ne'
    · exact h
  let eι := Fintype.equivFin ι
  let τ₁ : ((i : ι) → Multiplicative (ZMod (e i))) ≃* ((i : ι) → TrivZMod ℓ) :=
    MulEquiv.piCongrRight fun i => AddEquiv.toMultiplicative (ZMod.ringEquivCongr (hℓ i)).toAddEquiv
  let τ₂ : ((i : ι) → TrivZMod ℓ) ≃* ∀ j : Fin (Fintype.card ι), TrivZMod ℓ :=
    { Equiv.piCongrLeft' (fun _ => TrivZMod ℓ) eι with map_mul' := fun _ _ => rfl }
  have hP := tateDualityFor_pi (Fintype.card ι) (fun _ => TrivZMod ℓ)
    fun _ => tateDualityFor_trivZMod_prime (p := p) (K := K) (Ω := Ω) ℓ
  exact tateDualityFor_of_equiv ((E.trans τ₁).trans τ₂).symm
    (fun g x => by rw [htriv]; rfl) hP

end PadicField
