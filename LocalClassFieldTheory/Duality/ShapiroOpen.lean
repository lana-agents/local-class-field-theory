/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.Shapiro

/-!
# Shapiro's lemma for open subgroups (continuous cochains, degrees `0`, `1`, `2`)

Let `G` be a topological group, `H ≤ G` an open subgroup of finite index and `A` a discrete
`G`-module (`SmoothAction`). The coinduced module `ContH2.CoInd H A = Map(G/H, A)`, with
`(g • f)(c) = g • f(g⁻¹ • c)`, is again a discrete `G`-module (`ContH2.CoInd.smoothAction`).
**Shapiro's lemma**: restriction to `H` followed by evaluation at the base coset `o = H`,

`Hⁱ(G, CoInd H A) → Hⁱ(H, A)`,

is bijective for `i = 0, 1, 2` (cohomology with locally constant cochains, i.e. continuous
cohomology of profinite groups with discrete coefficients):

* **`ContH2.CoInd.shapiro0_bijective`**, **`ContH2.CoInd.shapiro1_bijective`**,
  **`ContH2.CoInd.shapiro2_bijective`**;
* `ContH2.CoInd.card_h0_eq`, `card_h1_eq`, `card_h2_eq`: the resulting equalities of orders.

(Serre, *Galois cohomology*, I.2.5; Neukirch–Schmidt–Wingberg, *Cohomology of number fields*,
(1.6.4).) The proof is by explicit cochain formulas. We fix a section `sec : G/H → G` with
`sec(o) = 1` and put `κ(c, g) = sec(c)⁻¹ g sec(g⁻¹ • c) ∈ H` (`ContH2.CoInd.kap`). An
inhomogeneous cocycle `z` of `H` is lifted to

`(lift z)(g₁, …, gₙ)(c) = sec(c) • z(κ(c, g₁), κ(g₁⁻¹ • c, g₂), …)`

(`ContH2.CoInd.lift1Fun`, `ContH2.CoInd.lift2Fun`), a cocycle of `G` with values in `CoInd H A`
whose restriction-evaluation is `z` on the nose (since `sec(o) = 1`). Conversely, for every
cocycle `F` of `G`, `lift(ev ∘ res F) = F · d Y` with an explicit locally constant `Y`
(`ContH2.CoInd.lift1Fun_res`, `ContH2.CoInd.lift2Fun_res`; in degree two this is the per-coset
identity `ContH2.cor_res_aux` behind `cor ∘ res = [G : H]`).
-/

open groupCohomology Brauer

set_option linter.unusedSectionVars false

namespace ContH2

namespace CoInd

/-! ### A section with `sec(o) = 1` -/

section Sec

variable {G : Type*} [Group G] (H : Subgroup G)

/-- A section of `G → G/H` sending the base coset to `1`. -/
noncomputable def sec (c : G ⧸ H) : G := by
  classical exact if c = base H then 1 else c.out

theorem sec_base : sec H (base H) = 1 := by
  classical
  simp [sec]

theorem mk_sec (c : G ⧸ H) : (QuotientGroup.mk (sec H c) : G ⧸ H) = c := by
  classical
  by_cases h : c = base H
  · rw [sec, if_pos h, h]
  · rw [sec, if_neg h, QuotientGroup.out_eq']

theorem sec_smul_base (c : G ⧸ H) : sec H c • base H = c := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, mk_sec]

theorem sec_inv_smul (c : G ⧸ H) : (sec H c)⁻¹ • c = base H := by
  rw [inv_smul_eq_iff, sec_smul_base]

theorem sec_inv_mul_mem (c : G ⧸ H) (g : G) : (sec H c)⁻¹ * g * sec H (g⁻¹ • c) ∈ H := by
  have h1 : (QuotientGroup.mk (sec H (g⁻¹ • c)) : G ⧸ H) = QuotientGroup.mk (g⁻¹ * sec H c) := by
    rw [mk_sec, ← smul_eq_mul, ← MulAction.Quotient.smul_mk, mk_sec]
  rw [QuotientGroup.eq] at h1
  have := H.inv_mem h1
  simpa [mul_inv_rev, mul_assoc] using this

/-- `κ(c, g) = sec(c)⁻¹ g sec(g⁻¹ • c) ∈ H`. -/
noncomputable def kap (c : G ⧸ H) (g : G) : H :=
  ⟨(sec H c)⁻¹ * g * sec H (g⁻¹ • c), sec_inv_mul_mem H c g⟩

theorem coe_kap (c : G ⧸ H) (g : G) : (kap H c g : G) = (sec H c)⁻¹ * g * sec H (g⁻¹ • c) :=
  rfl

theorem kap_mul (c : G ⧸ H) (g h : G) : kap H c (g * h) = kap H c g * kap H (g⁻¹ • c) h := by
  apply Subtype.ext
  simp only [coe_kap, Subgroup.coe_mul, mul_inv_rev, mul_smul]
  group

theorem sec_mul_kap (c : G ⧸ H) (g : G) : sec H c * (kap H c g : G) = g * sec H (g⁻¹ • c) := by
  rw [coe_kap]
  group

theorem kap_base (h : H) : kap H (base H) h = h := by
  apply Subtype.ext
  rw [coe_kap, smul_base_of_mem (H.inv_mem h.2), sec_base, inv_one, one_mul, mul_one]

end Sec

/-! ### Topology -/

section Topology

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CommGroup A]
  [MulDistribMulAction G A] {H : Subgroup G}

instance : TopologicalSpace (CoInd H A) := ⊥

instance : DiscreteTopology (CoInd H A) := ⟨rfl⟩

theorem isLocallyConstant_sec_smul (hH : IsOpen (H : Set G)) (c : G ⧸ H) :
    IsLocallyConstant fun g : G => sec H (g⁻¹ • c) :=
  (isLocallyConstant_smul_quot hH c).comp (sec H)

theorem continuous_kap (hH : IsOpen (H : Set G)) (c : G ⧸ H) : Continuous (kap H c) :=
  ((continuous_const.mul continuous_id).mul (isLocallyConstant_sec_smul hH c).continuous).subtype_mk
    _

/-- A function into `G/H → A` (with `G/H` finite) is locally constant if all its coordinates
are. -/
theorem isLocallyConstant_of_coord [Finite (G ⧸ H)] {X : Type*} [TopologicalSpace X]
    {F : X → CoInd H A} (hF : ∀ c, IsLocallyConstant fun x => F x c) : IsLocallyConstant F := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x₀
  have h : ∀ᶠ x in nhds x₀, ∀ c, F x c = F x₀ c :=
    Filter.eventually_all.2 fun c => (IsLocallyConstant.iff_eventually_eq _).1 (hF c) x₀
  filter_upwards [h] with x hx
  exact ext hx

theorem isLocallyConstant_smul' [SmoothAction G A] {X : Type*} [TopologicalSpace X] {φ : X → G}
    (hφ : Continuous φ) {a : X → A} (ha : IsLocallyConstant a) :
    IsLocallyConstant fun x => φ x • a x := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x₀
  have e1 := (IsLocallyConstant.iff_eventually_eq _).1 ha x₀
  have e2 := (IsLocallyConstant.iff_eventually_eq _).1
    ((SmoothAction.isLocallyConstant_smul (a x₀)).comp_continuous hφ) x₀
  filter_upwards [e1, e2] with x h1 h2
  rw [h1]
  exact h2

/-- `CoInd H A` is a discrete `G`-module when `H` is open of finite index. -/
theorem smoothAction [SmoothAction G A] [Finite (G ⧸ H)] (hH : IsOpen (H : Set G)) :
    SmoothAction G (CoInd H A) := by
  refine ⟨fun f => isLocallyConstant_of_coord fun c => ?_⟩
  simp only [smul_apply]
  exact isLocallyConstant_smul' continuous_id
    ((isLocallyConstant_smul_quot hH c).comp (fun c' => f c'))

end Topology

/-! ### Degree zero -/

section Degree0

variable {G A : Type*} [Group G] [CommGroup A] [MulDistribMulAction G A] (H : Subgroup G)

/-- Evaluation at the base coset on invariants: `H⁰(G, CoInd H A) → H⁰(H, A)`. -/
def shapiro0 : H0 G (CoInd H A) →* H0 H A where
  toFun f := ⟨(f : CoInd H A) (base H), fun h => by
    have := smul_apply_base_of_mem h.2 (f : CoInd H A)
    rw [Brauer.smul_H0 f (h : G)] at this
    exact this.symm⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem eq_sec_smul_of_mem_H0 (f : H0 G (CoInd H A)) (c : G ⧸ H) :
    (f : CoInd H A) c = sec H c • (f : CoInd H A) (base H) := by
  have := congrFun (Brauer.smul_H0 f (sec H c)) c
  rw [smul_apply, sec_inv_smul] at this
  exact this.symm

theorem shapiro0_bijective : Function.Bijective (shapiro0 (A := A) H) := by
  refine ⟨fun f f' hff' => ?_, fun a => ?_⟩
  · have h := congrArg Subtype.val hff'
    apply Subtype.ext
    apply ext
    intro c
    rw [eq_sec_smul_of_mem_H0, eq_sec_smul_of_mem_H0 H f' c]
    exact congrArg _ h
  · refine ⟨⟨fun c => sec H c • (a : A), fun g => ?_⟩, ?_⟩
    · apply ext
      intro c
      change g • (sec H (g⁻¹ • c) • (a : A)) = sec H c • (a : A)
      rw [← mul_smul, ← sec_mul_kap, mul_smul]
      congr 1
      exact Brauer.smul_H0 a (kap H c g)
    · apply Subtype.ext
      change sec H (base H) • (a : A) = a
      rw [sec_base, one_smul]

end Degree0

/-! ### Degree one -/

section Degree1

variable {G A : Type*} [Group G] [CommGroup A] [MulDistribMulAction G A] (H : Subgroup G)

/-- The lift of a `1`-cochain of `H`: `(lift z)(g)(c) = sec(c) • z(κ(c, g))`. -/
noncomputable def lift1Fun (z : H → A) (g : G) : CoInd H A := fun c => sec H c • z (kap H c g)

theorem lift1Fun_apply (z : H → A) (g : G) (c : G ⧸ H) :
    lift1Fun H z g c = sec H c • z (kap H c g) := rfl

/-- The lift of a `0`-cochain `a`: `c ↦ sec(c) • a`. -/
noncomputable def lift0 (a : A) : CoInd H A := fun c => sec H c • a

theorem smul_sec_smul (z : H → A) (g h : G) (c : G ⧸ H) :
    g • (sec H (g⁻¹ • c) • z (kap H (g⁻¹ • c) h)) =
      sec H c • (kap H c g • z (kap H (g⁻¹ • c) h)) := by
  rw [Subgroup.smul_def, ← mul_smul, ← mul_smul, sec_mul_kap]

theorem isMulCocycle₁_lift1Fun {z : H → A} (hz : IsMulCocycle₁ z) :
    IsMulCocycle₁ (lift1Fun H z) := by
  intro g h
  apply ext
  intro c
  rw [mul_apply, smul_apply, lift1Fun_apply, lift1Fun_apply, lift1Fun_apply, kap_mul, hz,
    smul_sec_smul, smul_mul']

theorem lift1Fun_base (z : H → A) (h : H) : lift1Fun H z h (base H) = z h := by
  rw [lift1Fun_apply, sec_base, one_smul, kap_base]

theorem lift1Fun_coboundary (a : A) (g : G) :
    lift1Fun H (fun h : H => h • a / a) g = g • lift0 H a / lift0 H a := by
  apply ext
  intro c
  rw [lift1Fun_apply, div_apply, smul_apply, lift0, lift0, smul_div', Subgroup.smul_def,
    ← mul_smul, ← mul_smul, sec_mul_kap]

/-- The `0`-cochain `c ↦ F(sec c)(c)` of the degree-one homotopy. -/
noncomputable def x1Fun (F : G → CoInd H A) : CoInd H A := fun c => F (sec H c) c

/-- **The homotopy in degree one**: `lift(ev ∘ res F) = F · d x` with `x(c) = F(sec c)(c)`. -/
theorem lift1Fun_res {F : G → CoInd H A} (hF : IsMulCocycle₁ F) (g : G) :
    lift1Fun H (fun h : H => F h (base H)) g =
      F g * (g • x1Fun H F / x1Fun H F) := by
  apply ext
  intro c
  rw [lift1Fun_apply, mul_apply, div_apply, smul_apply, x1Fun, x1Fun]
  have h1 := congrFun (hF (sec H c) (kap H c g)) c
  rw [sec_mul_kap, hF g, mul_apply, mul_apply, smul_apply, smul_apply, sec_inv_smul] at h1
  change sec H c • F (kap H c g) (base H) = _
  rw [show F (sec H (g⁻¹ • c)) (g⁻¹ • c) = F (sec H (g⁻¹ • c)) (g⁻¹ • c) from rfl]
  have h2 : sec H c • F (kap H c g) (base H) =
      g • F (sec H (g⁻¹ • c)) (g⁻¹ • c) * F g c / F (sec H c) c := by
    rw [h1]
    mul_abel
  rw [h2]
  mul_abel

variable [TopologicalSpace G] [IsTopologicalGroup G] [Finite (G ⧸ H)] (hH : IsOpen (H : Set G))

include hH in
theorem isLocallyConstant_lift1Fun {z : H → A} (hz : IsLocallyConstant z) :
    IsLocallyConstant (lift1Fun H z) :=
  isLocallyConstant_of_coord fun c => (hz.comp_continuous (continuous_kap hH c)).comp _

variable [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalGroup A]

include hH in
theorem continuous_lift1Fun {z : H → A} (hz : Continuous z) : Continuous (lift1Fun H z) :=
  (isLocallyConstant_lift1Fun H hH ((IsLocallyConstant.iff_continuous z).2 hz)).continuous

/-- The Shapiro map `H¹(G, CoInd H A) → H¹(H, A)`. -/
noncomputable def shapiro1 : ContH1 G (CoInd H A) →* ContH1 H A :=
  ContH1.map H.subtype continuous_subtype_val (ev H) continuous_of_discreteTopology
    fun h m => ev_smul h m

include hH in
theorem shapiro1_bijective : Function.Bijective (shapiro1 (A := A) H) := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    induction x using ContH1.induction_on with | h F => ?_
    rw [shapiro1, ContH1.map_mk, ContH1.mk_eq_one_iff] at hx
    obtain ⟨a, ha⟩ := hx
    rw [Subgroup.mem_bot, ContH1.mk_eq_one_iff]
    have hres : (fun h : H => (F : G → CoInd H A) h (base H)) = fun h : H => h • a / a :=
      funext fun h => (ha h).symm
    refine ⟨lift0 H a / x1Fun H F, fun g => ?_⟩
    have e1 := lift1Fun_res H (ContH1.isMulCocycle₁ F) g
    rw [hres, lift1Fun_coboundary] at e1
    rw [smul_div', div_div_div_comm, e1, mul_div_cancel_right]
  · intro y
    induction y using ContH1.induction_on with | h z => ?_
    refine ⟨ContH1.mk (ContH1.mkCocycle (lift1Fun H z) (continuous_lift1Fun H hH
      (ContH1.continuous z)) (isMulCocycle₁_lift1Fun H (ContH1.isMulCocycle₁ z))), ?_⟩
    rw [shapiro1, ContH1.map_mk]
    congr 1
    exact Subtype.ext (funext fun h => lift1Fun_base H z h)

end Degree1

/-! ### Degree two -/

section Degree2

variable {G A : Type*} [Group G] [CommGroup A] [MulDistribMulAction G A] (H : Subgroup G)

/-- The lift of a `2`-cochain of `H`:
`(lift z)(g, h)(c) = sec(c) • z(κ(c, g), κ(g⁻¹ • c, h))`. -/
noncomputable def lift2Fun (z : H × H → A) (gh : G × G) : CoInd H A :=
  fun c => sec H c • z (kap H c gh.1, kap H (gh.1⁻¹ • c) gh.2)

theorem lift2Fun_apply (z : H × H → A) (g h : G) (c : G ⧸ H) :
    lift2Fun H z (g, h) c = sec H c • z (kap H c g, kap H (g⁻¹ • c) h) := rfl

theorem isMulCocycle₂_lift2Fun {z : H × H → A} (hz : IsMulCocycle₂ z) :
    IsMulCocycle₂ (lift2Fun H z) := by
  intro g h k
  apply ext
  intro c
  have e : (g • lift2Fun H z (h, k)) c =
      sec H c • (kap H c g • z (kap H (g⁻¹ • c) h, kap H (h⁻¹ • g⁻¹ • c) k)) := by
    rw [smul_apply, lift2Fun_apply, Subgroup.smul_def, smul_smul, smul_smul (sec H c), sec_mul_kap]
  rw [mul_apply, mul_apply, e, lift2Fun_apply, lift2Fun_apply, lift2Fun_apply, ← smul_mul',
    ← smul_mul']
  congr 1
  have := hz (kap H c g) (kap H (g⁻¹ • c) h) (kap H (h⁻¹ • g⁻¹ • c) k)
  rw [← kap_mul, ← kap_mul] at this
  rw [mul_inv_rev, mul_smul]
  exact this

theorem lift2Fun_base (z : H × H → A) (a b : H) : lift2Fun H z (a, b) (base H) = z (a, b) := by
  rw [lift2Fun_apply, sec_base, one_smul, kap_base, smul_base_of_mem (H.inv_mem a.2), kap_base]

theorem lift2Fun_dx (x : H → A) : lift2Fun H (dx H A x) = dx G (CoInd H A) (lift1Fun H x) := by
  funext ⟨g, h⟩
  apply ext
  intro c
  rw [lift2Fun_apply, dx_apply, dx_apply, mul_apply, div_apply, smul_apply, lift1Fun_apply,
    lift1Fun_apply, lift1Fun_apply, kap_mul, smul_mul', smul_div', Subgroup.smul_def,
    ← mul_smul (sec H c), ← mul_smul g, sec_mul_kap]

/-- The primitive in the degree-two homotopy:
`Y(x)(c) = F(sec c, κ(c, x))(c) / F(x, sec(x⁻¹ • c))(c)`. -/
noncomputable def yFun (F : G × G → CoInd H A) (x : G) : CoInd H A :=
  fun c => F (sec H c, (sec H c)⁻¹ * x * sec H (x⁻¹ • c)) c / F (x, sec H (x⁻¹ • c)) c

/-- **The homotopy in degree two**: `lift(ev ∘ res F) = F · d Y`. -/
theorem lift2Fun_res {F : G × G → CoInd H A} (hF : IsMulCocycle₂ F) :
    lift2Fun H (fun ab : H × H => F (ab.1, ab.2) (base H)) =
      F * dx G (CoInd H A) (yFun H F) := by
  funext ⟨g, h⟩
  apply ext
  intro c
  have key := congrFun (cor_res_aux hF (sec H c) g h (sec H (g⁻¹ • c))
    (sec H (h⁻¹ • g⁻¹ • c))) c
  rw [smul_apply, sec_inv_smul] at key
  rw [lift2Fun_apply, Pi.mul_apply, dx_apply, coe_kap, coe_kap]
  change sec H c • F _ (base H) = _
  rw [key]
  simp only [mul_apply, div_apply, smul_apply, yFun, mul_inv_rev, mul_smul]

variable [TopologicalSpace G] [IsTopologicalGroup G] [Finite (G ⧸ H)] (hH : IsOpen (H : Set G))

include hH in
theorem isLocallyConstant_lift2Fun {z : H × H → A} (hz : IsLocallyConstant z) :
    IsLocallyConstant (lift2Fun H z) := by
  refine isLocallyConstant_of_coord fun c => ?_
  have hc : Continuous fun gh : G × G => (kap H c gh.1, kap H (gh.1⁻¹ • c) gh.2) := by
    refine ((continuous_kap hH c).comp continuous_fst).prodMk ?_
    refine Continuous.subtype_mk ?_ _
    have h1 : Continuous fun gh : G × G => sec H (gh.1⁻¹ • c) :=
      (isLocallyConstant_sec_smul hH c).continuous.comp continuous_fst
    have h2 : Continuous fun gh : G × G => sec H (gh.2⁻¹ • gh.1⁻¹ • c) := by
      have : (fun gh : G × G => sec H (gh.2⁻¹ • gh.1⁻¹ • c)) =
          (fun g : G => sec H (g⁻¹ • c)) ∘ fun gh : G × G => gh.1 * gh.2 := by
        funext gh
        simp only [Function.comp_apply, mul_inv_rev, mul_smul]
      rw [this]
      exact (isLocallyConstant_sec_smul hH c).continuous.comp (continuous_fst.mul continuous_snd)
    exact (h1.inv.mul continuous_snd).mul h2
  exact (hz.comp_continuous hc).comp _

include hH in
theorem isLocallyConstant_yFun {F : G × G → CoInd H A} (hF : IsLocallyConstant F) :
    IsLocallyConstant (yFun H F) := by
  refine isLocallyConstant_of_coord fun c => ?_
  have hs := (isLocallyConstant_sec_smul hH c).continuous
  refine IsLocallyConstant.div ?_ ?_
  · exact (hF.comp_continuous (continuous_const.prodMk
      ((continuous_const.mul continuous_id).mul hs))).comp fun m => m c
  · exact (hF.comp_continuous (continuous_id.prodMk hs)).comp fun m => m c

/-- The Shapiro map `H²(G, CoInd H A) → H²(H, A)`: restriction to `H`, then evaluation at the
base coset. -/
noncomputable def shapiro2 : ContH2 G (CoInd H A) →* ContH2 H A :=
  ContH2.map H.subtype continuous_subtype_val (ev H) fun h m => ev_smul h m

include hH in
theorem shapiro2_bijective : Function.Bijective (shapiro2 (A := A) H) := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    induction x using induction_on with | h F => ?_
    rw [shapiro2, map_mk, mk_eq_one_iff] at hx
    obtain ⟨y, hy, hyF⟩ := hx
    rw [Subgroup.mem_bot, mk_eq_one_iff]
    have hres : (fun ab : H × H => (F : G × G → CoInd H A) (ab.1, ab.2) (base H)) =
        dx H A y := funext fun ab => (congrFun hyF ab).symm
    have e1 := lift2Fun_res H (isMulCocycle₂ F)
    rw [hres, lift2Fun_dx] at e1
    refine ⟨lift1Fun H y / yFun H F, ?_, ?_⟩
    · exact (isLocallyConstant_lift1Fun H hH hy).div
        (isLocallyConstant_yFun H hH (isLocallyConstant F))
    · rw [div_eq_mul_inv, dx_mul, dx_inv, e1, mul_inv_cancel_right]
  · intro w
    induction w using induction_on with | h z => ?_
    refine ⟨mk (mkCocycle (lift2Fun H z) (isLocallyConstant_lift2Fun H hH (isLocallyConstant z))
      (isMulCocycle₂_lift2Fun H (isMulCocycle₂ z))), ?_⟩
    rw [shapiro2, map_mk]
    congr 1
    exact cocycles_ext fun a b => lift2Fun_base H z a b

end Degree2

end CoInd

end ContH2
