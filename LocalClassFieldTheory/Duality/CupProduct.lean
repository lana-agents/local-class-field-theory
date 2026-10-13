/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.ContH2
import ContinuousKummerTheory.ContH1.Basic

/-!
# Cup products `H⁰ × H² → H²`, `H² × H⁰ → H²` and `H¹ × H¹ → H²`

Let `G` be a topological group and `e : M × N → P` a `G`-equivariant bilinear pairing of
(multiplicatively written) `G`-modules (`Brauer.GPairing`). With `H⁰(G, M) = M^G`
(`Brauer.H0`), `H¹ = ContH1` (continuous cocycles, from `continuous-kummer-theory`) and
`H² = ContH2` (locally constant cochains) we define the cup products

* `Brauer.cup02 e m : H²(G, N) →* H²(G, P)`, `m ∈ M^G`, induced by `n ↦ e(m, n)`;
* `Brauer.cup20 e β : H⁰(G, N) →* H²(G, P)`, `n ↦ β ∪ n`, induced by `m ↦ e(m, n)`;
* `Brauer.cup11 e : H¹(G, M) →* H¹(G, N) →* H²(G, P)` on cocycles
  `(x ∪ y)(g, h) = e(x(g), g • y(h))` (`Brauer.cup11Fun`), for discrete `M`, `N` on which `G` acts
  smoothly (`Brauer.SmoothAction`: all stabilisers are open).

All three are bilinear. Graded commutativity in degree `(1, 1)`:
`x ∪_e y = (y ∪_{e'} x)⁻¹` for the swapped pairing `e'` (`Brauer.cup11_swap`); on cochains
`x ∪ y · y ∪' x` is the coboundary of `g ↦ e(x(g), y(g))⁻¹`.
-/

open ContH2 groupCohomology

set_option linter.unusedSectionVars false

namespace Brauer

/-- A `G`-equivariant bilinear pairing `M × N → P` of `G`-modules. -/
structure GPairing (G M N P : Type*) [Monoid G] [CommGroup M] [CommGroup N] [CommGroup P]
    [MulDistribMulAction G M] [MulDistribMulAction G N] [MulDistribMulAction G P] where
  /-- The underlying bilinear map. -/
  toHom : M →* N →* P
  map_smul' : ∀ (g : G) (m : M) (n : N), toHom (g • m) (g • n) = g • toHom m n

/-- The action of a topological group `G` on `M` is **smooth** if every stabiliser is open, i.e.
`g ↦ g • m` is locally constant for every `m` (a discrete `G`-module). -/
class SmoothAction (G M : Type*) [TopologicalSpace G] [SMul G M] : Prop where
  isLocallyConstant_smul : ∀ m : M, IsLocallyConstant fun g : G => g • m

variable {G M N P : Type*} [Group G] [CommGroup M] [CommGroup N] [CommGroup P]
  [MulDistribMulAction G M] [MulDistribMulAction G N] [MulDistribMulAction G P]

namespace GPairing

theorem map_smul (e : GPairing G M N P) (g : G) (m : M) (n : N) :
    e.toHom (g • m) (g • n) = g • e.toHom m n :=
  e.map_smul' g m n

/-- The swapped pairing `N × M → P`. -/
def swap (e : GPairing G M N P) : GPairing G N M P :=
  ⟨e.toHom.flip, fun g n m => e.map_smul g m n⟩

@[simp]
theorem swap_swap (e : GPairing G M N P) : e.swap.swap = e := rfl

@[simp]
theorem swap_toHom_apply (e : GPairing G M N P) (n : N) (m : M) :
    e.swap.toHom n m = e.toHom m n := rfl

end GPairing

variable (G M) in
/-- `H⁰(G, M) = M^G`. -/
abbrev H0 : Subgroup M := FixedPoints.subgroup G M

theorem smul_H0 (m : H0 G M) (g : G) : g • (m : M) = m := m.2 g

/-! ### Degrees `(0, 2)` and `(2, 0)` -/

section Deg02

variable [TopologicalSpace G]

/-- The cup product `m ∪ - : H²(G, N) → H²(G, P)` with `m ∈ H⁰(G, M)`. -/
def cup02 (e : GPairing G M N P) (m : H0 G M) : ContH2 G N →* ContH2 G P :=
  ContH2.map (MonoidHom.id G) continuous_id (e.toHom m) (fun g x => by
    have h := e.map_smul g m x
    rwa [smul_H0 m g] at h)

theorem cup02_mk (e : GPairing G M N P) (m : H0 G M) (f : cocycles G N) :
    cup02 e m (mk f) = mk (cocyclesMap (MonoidHom.id G) continuous_id (e.toHom m) (fun g x => by
      have h := e.map_smul g m x
      rwa [smul_H0 m g] at h) f) := rfl

theorem cup02_mul_left (e : GPairing G M N P) (m m' : H0 G M) (β : ContH2 G N) :
    cup02 e (m * m') β = cup02 e m β * cup02 e m' β := by
  induction β using induction_on with | h f => ?_
  rw [cup02_mk, cup02_mk, cup02_mk, ← map_mul]
  congr 1
  exact cocycles_ext fun a b => by simp

theorem cup02_one_left (e : GPairing G M N P) (β : ContH2 G N) : cup02 e 1 β = 1 := by
  induction β using induction_on with | h f => ?_
  rw [cup02_mk, ← map_one (mk (G := G) (M := P))]
  congr 1
  exact cocycles_ext fun a b => by simp

/-- `m ↦ m ∪ β` as a homomorphism `H⁰(G, M) → H²(G, P)`. -/
def cup02Left (e : GPairing G M N P) (β : ContH2 G N) : H0 G M →* ContH2 G P where
  toFun m := cup02 e m β
  map_one' := cup02_one_left e β
  map_mul' m m' := cup02_mul_left e m m' β

/-- The cup product `β ∪ - : H⁰(G, N) → H²(G, P)` with `β ∈ H²(G, M)`. -/
def cup20 (e : GPairing G M N P) (β : ContH2 G M) : H0 G N →* ContH2 G P :=
  cup02Left e.swap β

theorem cup20_apply (e : GPairing G M N P) (β : ContH2 G M) (n : H0 G N) :
    cup20 e β n = cup02 e.swap n β := rfl

theorem cup20_mul_left (e : GPairing G M N P) (β β' : ContH2 G M) :
    cup20 e (β * β') = cup20 e β * cup20 e β' := by
  ext n
  simp [cup20_apply]

end Deg02

/-! ### Degree `(1, 1)` -/

section Deg11

/-- The cup product of 1-cochains: `(x ∪ y)(g, h) = e(x(g), g • y(h))`. -/
def cup11Fun (e : GPairing G M N P) (x : G → M) (y : G → N) : G × G → P :=
  fun gh => e.toHom (x gh.1) (gh.1 • y gh.2)

theorem isMulCocycle₂_cup11Fun (e : GPairing G M N P) {x : G → M} {y : G → N}
    (hx : IsMulCocycle₁ x) (hy : IsMulCocycle₁ y) : IsMulCocycle₂ (cup11Fun e x y) := by
  intro a b c
  simp only [cup11Fun]
  rw [hx a b, hy b c, ← e.map_smul a (x b) (b • y c), smul_mul', mul_smul]
  simp only [map_mul, MonoidHom.mul_apply]
  mul_abel

theorem cup11Fun_mul_left (e : GPairing G M N P) (x x' : G → M) (y : G → N) :
    cup11Fun e (x * x') y = cup11Fun e x y * cup11Fun e x' y := by
  funext gh
  simp [cup11Fun, map_mul]

theorem cup11Fun_mul_right (e : GPairing G M N P) (x : G → M) (y y' : G → N) :
    cup11Fun e x (y * y') = cup11Fun e x y * cup11Fun e x y' := by
  funext gh
  simp [cup11Fun, smul_mul', map_mul]

/-- `dm ∪ y = d(g ↦ e(m, y(g)))`. -/
theorem cup11Fun_coboundary_left (e : GPairing G M N P) (m : M) {y : G → N}
    (hy : IsMulCocycle₁ y) :
    cup11Fun e (fun g => g • m / m) y = dx G P (fun g => e.toHom m (y g)) := by
  funext gh
  obtain ⟨g, h⟩ := gh
  simp only [cup11Fun, dx_apply]
  rw [hy g h, ← e.map_smul g m (y h)]
  simp only [map_mul, map_div, MonoidHom.div_apply]
  mul_abel

/-- `x ∪ dn = d(g ↦ e(x(g), g • n)⁻¹)`. -/
theorem cup11Fun_coboundary_right (e : GPairing G M N P) {x : G → M} (hx : IsMulCocycle₁ x)
    (n : N) :
    cup11Fun e x (fun h => h • n / n) = dx G P (fun g => (e.toHom (x g) (g • n))⁻¹) := by
  funext gh
  obtain ⟨g, h⟩ := gh
  simp only [cup11Fun, dx_apply]
  rw [hx g h, smul_inv', ← e.map_smul g (x h) (h • n), smul_div', ← mul_smul]
  simp only [map_mul, map_div, MonoidHom.mul_apply]
  mul_abel

/-- Graded commutativity on cochains: `x ∪ y · y ∪' x = d(g ↦ e(x(g), y(g))⁻¹)`. -/
theorem cup11Fun_mul_swap (e : GPairing G M N P) {x : G → M} {y : G → N}
    (hx : IsMulCocycle₁ x) (hy : IsMulCocycle₁ y) :
    cup11Fun e x y * cup11Fun e.swap y x = dx G P (fun g => (e.toHom (x g) (y g))⁻¹) := by
  funext gh
  obtain ⟨g, h⟩ := gh
  simp only [cup11Fun, dx_apply, Pi.mul_apply, GPairing.swap_toHom_apply]
  rw [hx g h, hy g h, smul_inv', ← e.map_smul g (x h) (y h)]
  simp only [map_mul, MonoidHom.mul_apply]
  mul_abel

variable [TopologicalSpace G]
variable [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalGroup M]
  [TopologicalSpace N] [DiscreteTopology N] [IsTopologicalGroup N]

theorem isLocallyConstant_cup11Fun [SmoothAction G N] (e : GPairing G M N P) {x : G → M}
    {y : G → N} (hx : Continuous x) (hy : Continuous y) :
    IsLocallyConstant (cup11Fun e x y) := by
  have hxl : IsLocallyConstant x := (IsLocallyConstant.iff_continuous x).2 hx
  have hyl : IsLocallyConstant y := (IsLocallyConstant.iff_continuous y).2 hy
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨g, h⟩
  have e1 : ∀ᶠ q : G × G in nhds (g, h), y q.2 = y h :=
    (continuous_snd.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq y).1 hyl h)
  have e2 : ∀ᶠ q : G × G in nhds (g, h), x q.1 = x g :=
    (continuous_fst.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq x).1 hxl g)
  have e3 : ∀ᶠ q : G × G in nhds (g, h), q.1 • y h = g • y h :=
    (continuous_fst.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq _).1 (SmoothAction.isLocallyConstant_smul (y h)) g)
  filter_upwards [e1, e2, e3] with q h1 h2 h3
  simp only [cup11Fun, h1, h2, h3]

variable [SmoothAction G N]

/-- The cup product of two continuous 1-cocycles, as a locally constant 2-cocycle. -/
def cup11Cocycle (e : GPairing G M N P) (x : ContH1.cocycles G M) (y : ContH1.cocycles G N) :
    cocycles G P :=
  mkCocycle (cup11Fun e x y) (isLocallyConstant_cup11Fun e (ContH1.continuous x)
    (ContH1.continuous y)) (isMulCocycle₂_cup11Fun e (ContH1.isMulCocycle₁ x)
    (ContH1.isMulCocycle₁ y))

@[simp]
theorem cup11Cocycle_apply (e : GPairing G M N P) (x : ContH1.cocycles G M)
    (y : ContH1.cocycles G N) (g h : G) :
    cup11Cocycle e x y (g, h) = e.toHom (x g) (g • y h) := rfl

/-- `y ↦ [x ∪ y]` on cocycles. -/
def cup11Right (e : GPairing G M N P) (x : ContH1.cocycles G M) :
    ContH1.cocycles G N →* ContH2 G P where
  toFun y := mk (cup11Cocycle e x y)
  map_one' := by
    rw [← map_one (mk (G := G) (M := P))]
    congr 1
    exact cocycles_ext fun a b => by simp
  map_mul' y y' := by
    rw [← map_mul]
    congr 1
    exact cocycles_ext fun a b => by simp [smul_mul']

/-- `x ∪ - : H¹(G, N) → H²(G, P)` for a cocycle `x`. -/
def cup11RightH1 (e : GPairing G M N P) (x : ContH1.cocycles G M) : ContH1 G N →* ContH2 G P :=
  QuotientGroup.lift (ContH1.coboundaries G N) (cup11Right e x) (by
    rintro y ⟨n, hn⟩
    rw [MonoidHom.mem_ker]
    change mk (cup11Cocycle e x y) = 1
    rw [mk_eq_one_iff]
    refine ⟨fun g => (e.toHom (x g) (g • n))⁻¹, ?_, ?_⟩
    · have hxl : IsLocallyConstant (x : G → M) :=
        (IsLocallyConstant.iff_continuous _).2 (ContH1.continuous x)
      exact ((hxl.prodMk (SmoothAction.isLocallyConstant_smul n)).comp
        fun c => (e.toHom c.1 c.2)⁻¹)
    · rw [← cup11Fun_coboundary_right e (ContH1.isMulCocycle₁ x) n]
      change _ = cup11Fun e x y
      congr 1
      funext h
      exact hn h)

theorem cup11RightH1_mk (e : GPairing G M N P) (x : ContH1.cocycles G M)
    (y : ContH1.cocycles G N) : cup11RightH1 e x (ContH1.mk y) = mk (cup11Cocycle e x y) := rfl

/-- **The cup product** `H¹(G, M) × H¹(G, N) → H²(G, P)`. -/
def cup11 (e : GPairing G M N P) : ContH1 G M →* ContH1 G N →* ContH2 G P :=
  QuotientGroup.lift (ContH1.coboundaries G M)
    { toFun := cup11RightH1 e
      map_one' := by
        ext y
        induction y using ContH1.induction_on with | h y => ?_
        rw [cup11RightH1_mk, MonoidHom.one_apply, ← map_one (mk (G := G) (M := P))]
        congr 1
        exact cocycles_ext fun a b => by simp
      map_mul' := fun x x' => by
        ext y
        induction y using ContH1.induction_on with | h y => ?_
        rw [MonoidHom.mul_apply, cup11RightH1_mk, cup11RightH1_mk, cup11RightH1_mk, ← map_mul]
        congr 1
        exact cocycles_ext fun a b => by simp }
    (by
      rintro x ⟨m, hm⟩
      rw [MonoidHom.mem_ker]
      ext y
      induction y using ContH1.induction_on with | h y => ?_
      change mk (cup11Cocycle e x y) = 1
      rw [mk_eq_one_iff]
      refine ⟨fun g => e.toHom m (y g), ?_, ?_⟩
      · exact ((IsLocallyConstant.iff_continuous _).2 (ContH1.continuous y)).comp _
      · rw [← cup11Fun_coboundary_left e m (ContH1.isMulCocycle₁ y)]
        change _ = cup11Fun e x y
        congr 1
        funext g
        exact hm g)

theorem cup11_mk (e : GPairing G M N P) (x : ContH1.cocycles G M) (y : ContH1.cocycles G N) :
    cup11 e (ContH1.mk x) (ContH1.mk y) = mk (cup11Cocycle e x y) := rfl

/-- **Graded commutativity** in degree `(1, 1)`: `x ∪_e y = (y ∪_{e'} x)⁻¹`. -/
theorem cup11_swap [SmoothAction G M] (e : GPairing G M N P) (x : ContH1 G M)
    (y : ContH1 G N) : cup11 e x y = (cup11 e.swap y x)⁻¹ := by
  induction x using ContH1.induction_on with | h x => ?_
  induction y using ContH1.induction_on with | h y => ?_
  rw [cup11_mk, cup11_mk, eq_inv_iff_mul_eq_one, ← map_mul, mk_eq_one_iff]
  refine ⟨fun g => (e.toHom (x g) (y g))⁻¹, ?_, ?_⟩
  · exact ((((IsLocallyConstant.iff_continuous _).2 (ContH1.continuous x)).prodMk
      ((IsLocallyConstant.iff_continuous _).2 (ContH1.continuous y))).comp
      fun c => (e.toHom c.1 c.2)⁻¹)
  · rw [← cup11Fun_mul_swap e (ContH1.isMulCocycle₁ x) (ContH1.isMulCocycle₁ y)]
    rfl

end Deg11

end Brauer
