/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.CupProduct

/-!
# The long exact cohomology sequence in degrees `0, 1, 2`

Let `G` be a topological group and `0 → A → B → C → 0` a short exact sequence of discrete
`G`-modules on which `G` acts smoothly (`Brauer.GShortExact`, multiplicative notation). With
`H⁰ = Brauer.H0`, `H¹ = ContH1` (continuous cocycles) and `H² = ContH2` (locally constant
cochains) we construct the connecting homomorphisms

* `Brauer.GShortExact.delta0 : H⁰(G, C) → H¹(G, A)`, `c ↦ [g ↦ g • b / b]` for a lift `b` of `c`;
* `Brauer.GShortExact.delta1 : H¹(G, C) → H²(G, A)`, `[x] ↦ [d x̃]` for a lift `x̃` of `x`

and prove that

`0 → H⁰(A) → H⁰(B) → H⁰(C) → H¹(A) → H¹(B) → H¹(C) → H²(A) → H²(B) → H²(C)`

is exact (`Brauer.GShortExact.h0Hom_injective`, `exact_h0B`, `exact_h0C`, `exact_h1A`, `exact_h1B`,
`exact_h1C`, `exact_h2A`, `exact_h2B`), each stated as `ker = range`. The induced maps on
cohomology of an equivariant homomorphism `f` are `Brauer.h0Hom`, `Brauer.h1Hom`, `Brauer.h2Hom`.

The sequence does not continue to `H³` here (no `H³` is defined), so the map `H²(B) → H²(C)` is
not surjective in general; for a finite discrete module over a `p`-adic field this surjectivity
is equivalent to the vanishing of `H³(K, A) → H³(K, B)`, i.e. a consequence of `cd(G_K) = 2`,
which is not formalised.
-/

open ContH2 groupCohomology

set_option linter.unusedSectionVars false

namespace Brauer

variable {G : Type*} [Group G] [TopologicalSpace G]

/-! ### Induced maps -/

section Maps

variable {M N : Type*} [CommGroup M] [CommGroup N] [MulDistribMulAction G M]
  [MulDistribMulAction G N]

/-- `H⁰(G, M) → H⁰(G, N)` induced by an equivariant `f`. -/
def h0Hom (f : M →* N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) : H0 G M →* H0 G N where
  toFun x := ⟨f x, fun g => by rw [← hf, smul_H0 x g]⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f (x : M) y)

@[simp]
theorem coe_h0Hom (f : M →* N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (x : H0 G M) :
    (h0Hom f hf x : N) = f x := rfl

/-- `H²(G, M) → H²(G, N)` induced by an equivariant `f`. -/
def h2Hom (f : M →* N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    ContH2 G M →* ContH2 G N :=
  ContH2.map (MonoidHom.id G) continuous_id f hf

theorem h2Hom_mk (f : M →* N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (c : ContH2.cocycles G M) :
    h2Hom f hf (mk c) = mk (cocyclesMap (MonoidHom.id G) continuous_id f hf c) := rfl

theorem h2Hom_comp {P : Type*} [CommGroup P] [MulDistribMulAction G P] (f : M →* N)
    (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) (f' : N →* P)
    (hf' : ∀ (g : G) (m : N), f' (g • m) = g • f' m) (β : ContH2 G M) :
    h2Hom f' hf' (h2Hom f hf β) = h2Hom (f'.comp f) (fun g m => by simp [hf, hf']) β := by
  induction β using induction_on with | h c => ?_
  rfl

theorem h2Hom_id (β : ContH2 G M) : h2Hom (MonoidHom.id M) (fun _ _ => rfl) β = β := by
  induction β using induction_on with | h c => ?_
  rfl

variable [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalGroup M]
  [TopologicalSpace N] [DiscreteTopology N] [IsTopologicalGroup N]

/-- `H¹(G, M) → H¹(G, N)` induced by an equivariant `f`. -/
def h1Hom (f : M →* N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m) :
    ContH1 G M →* ContH1 G N :=
  ContH1.map (MonoidHom.id G) continuous_id f continuous_of_discreteTopology hf

theorem h1Hom_mk (f : M →* N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (c : ContH1.cocycles G M) :
    h1Hom f hf (ContH1.mk c) =
      ContH1.mk (ContH1.cocyclesMap (MonoidHom.id G) continuous_id f
        continuous_of_discreteTopology hf c) := rfl

end Maps

/-! ### Coboundaries of locally constant cochains are locally constant -/

theorem isLocallyConstant_dx [IsTopologicalGroup G] {M : Type*} [CommGroup M]
    [MulDistribMulAction G M] [SmoothAction G M] {x : G → M} (hx : IsLocallyConstant x) :
    IsLocallyConstant (dx G M x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨g, h⟩
  have e1 : ∀ᶠ q : G × G in nhds (g, h), x q.2 = x h :=
    (continuous_snd.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq x).1 hx h)
  have e2 : ∀ᶠ q : G × G in nhds (g, h), x q.1 = x g :=
    (continuous_fst.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq x).1 hx g)
  have e3 : ∀ᶠ q : G × G in nhds (g, h), q.1 • x h = g • x h :=
    (continuous_fst.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq _).1 (SmoothAction.isLocallyConstant_smul (x h)) g)
  have e4 : ∀ᶠ q : G × G in nhds (g, h), x (q.1 * q.2) = x (g * h) :=
    (continuous_mul.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq x).1 hx (g * h))
  filter_upwards [e1, e2, e3, e4] with q h1 h2 h3 h4
  obtain ⟨a, b⟩ := q
  simp only at h1 h2 h3 h4
  simp only [dx_apply, h1, h2, h3, h4]

/-! ### Short exact sequences -/

/-- A short exact sequence `0 → A → B → C → 0` of `G`-modules. -/
structure GShortExact (G A B C : Type*) [Monoid G] [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C] where
  /-- The injection `A → B`. -/
  i : A →* B
  /-- The surjection `B → C`. -/
  π : B →* C
  map_smul_i : ∀ (g : G) (a : A), i (g • a) = g • i a
  map_smul_π : ∀ (g : G) (b : B), π (g • b) = g • π b
  injective : Function.Injective i
  surjective : Function.Surjective π
  exact : ∀ b : B, π b = 1 ↔ b ∈ i.range

namespace GShortExact

variable {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]
  [MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]
  (S : GShortExact G A B C)

/-- A preimage in `A` of an element of `ker π` (`1` elsewhere is irrelevant). -/
noncomputable def pre (b : B) : A := Function.invFun S.i b

theorem i_pre {b : B} (hb : S.π b = 1) : S.i (S.pre b) = b :=
  Function.invFun_eq ((S.exact b).1 hb)

theorem pre_i (a : A) : S.pre (S.i a) = a := Function.leftInverse_invFun S.injective a

theorem π_i (a : A) : S.π (S.i a) = 1 := (S.exact _).2 ⟨a, rfl⟩

/-- A set-theoretic section of `π`. -/
noncomputable def sec (c : C) : B := Function.surjInv S.surjective c

theorem π_sec (c : C) : S.π (S.sec c) = c := Function.surjInv_eq S.surjective c

theorem pre_mul {b b' : B} (hb : S.π b = 1) (hb' : S.π b' = 1) :
    S.pre (b * b') = S.pre b * S.pre b' := by
  apply S.injective
  rw [map_mul, S.i_pre hb, S.i_pre hb', S.i_pre (by rw [map_mul, hb, hb', mul_one])]

theorem pre_div {b b' : B} (hb : S.π b = 1) (hb' : S.π b' = 1) :
    S.pre (b / b') = S.pre b / S.pre b' := by
  apply S.injective
  rw [map_div, S.i_pre hb, S.i_pre hb', S.i_pre (by rw [map_div, hb, hb', div_one])]

theorem pre_smul (g : G) {b : B} (hb : S.π b = 1) : S.pre (g • b) = g • S.pre b := by
  apply S.injective
  rw [S.map_smul_i, S.i_pre hb, S.i_pre (by rw [S.map_smul_π, hb, smul_one])]

theorem pre_one : S.pre 1 = 1 := by
  rw [← map_one S.i, S.pre_i]

/-- `π ∘ dx = dx ∘ π`. -/
theorem π_dx (y : G → B) (gh : G × G) : S.π (dx G B y gh) = dx G C (fun g => S.π (y g)) gh := by
  obtain ⟨g, h⟩ := gh
  simp only [dx_apply, map_mul, map_div, S.map_smul_π]

/-- `i ∘ dx = dx ∘ i`. -/
theorem i_dx (a : G → A) (gh : G × G) : S.i (dx G A a gh) = dx G B (fun g => S.i (a g)) gh := by
  obtain ⟨g, h⟩ := gh
  simp only [dx_apply, map_mul, map_div, S.map_smul_i]

/-! ### Degree `0` -/

theorem h0Hom_injective : Function.Injective (h0Hom (G := G) S.i S.map_smul_i) :=
  fun _ _ h => Subtype.ext (S.injective (congrArg Subtype.val h))

/-- Exactness at `H⁰(B)`. -/
theorem exact_h0B : (h0Hom (G := G) S.π S.map_smul_π).ker = (h0Hom S.i S.map_smul_i).range := by
  ext b
  constructor
  · intro hb
    have h1 : S.π b = 1 := congrArg Subtype.val hb
    refine ⟨⟨S.pre b, fun g => S.injective ?_⟩, Subtype.ext (S.i_pre h1)⟩
    rw [S.map_smul_i, S.i_pre h1, smul_H0 b g]
  · rintro ⟨a, rfl⟩
    exact Subtype.ext (S.π_i a)

/-! ### The connecting map `δ⁰ : H⁰(C) → H¹(A)` -/

section Delta0

variable [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalGroup A]
  [TopologicalSpace B] [DiscreteTopology B] [IsTopologicalGroup B] [SmoothAction G B]
  [TopologicalSpace C] [DiscreteTopology C] [IsTopologicalGroup C]

theorem π_smul_div {b : B} (hb : ∀ g : G, g • S.π b = S.π b) (g : G) :
    S.π (g • b / b) = 1 := by
  rw [map_div, S.map_smul_π, hb, div_self']

/-- The cocycle `g ↦ g • b / b` (with values in `A`) of a lift `b` of an invariant of `C`. -/
noncomputable def delta0Cocycle (b : B) (hb : ∀ g : G, g • S.π b = S.π b) :
    ContH1.cocycles G A :=
  ContH1.mkCocycle (fun g => S.pre (g • b / b))
    (((SmoothAction.isLocallyConstant_smul (G := G) b).div
      (IsLocallyConstant.const b)).comp S.pre).continuous
    (fun g h => by
      apply S.injective
      rw [map_mul, S.map_smul_i, S.i_pre (S.π_smul_div hb _), S.i_pre (S.π_smul_div hb _),
        S.i_pre (S.π_smul_div hb _), smul_div', mul_smul]
      mul_abel)

theorem i_delta0Cocycle (b : B) (hb : ∀ g : G, g • S.π b = S.π b) (g : G) :
    S.i (S.delta0Cocycle b hb g) = g • b / b := S.i_pre (S.π_smul_div hb g)

theorem mk_delta0Cocycle_eq {b b' : B} (hb : ∀ g : G, g • S.π b = S.π b) (h : S.π b = S.π b') :
    ContH1.mk (S.delta0Cocycle b hb) = ContH1.mk (S.delta0Cocycle b' (h ▸ hb)) := by
  rw [ContH1.mk_eq_mk_iff]
  have hq : S.π (b / b') = 1 := by rw [map_div, h, div_self']
  refine ⟨S.pre (b / b'), fun g => S.injective ?_⟩
  beta_reduce
  rw [map_div, map_div, S.map_smul_i, S.i_pre hq, S.i_delta0Cocycle,
    S.i_delta0Cocycle, smul_div']
  mul_abel

/-- **The connecting homomorphism** `δ⁰ : H⁰(G, C) → H¹(G, A)`. -/
noncomputable def delta0 : H0 G C →* ContH1 G A where
  toFun c := ContH1.mk (S.delta0Cocycle (S.sec c) (fun g => by rw [S.π_sec, smul_H0 c g]))
  map_one' := by
    rw [S.mk_delta0Cocycle_eq _ (b' := 1) (by rw [S.π_sec, map_one]; rfl), ContH1.mk_eq_one_iff]
    refine ⟨1, fun g => S.injective ?_⟩
    rw [S.i_delta0Cocycle]
    simp
  map_mul' c c' := by
    rw [← map_mul, S.mk_delta0Cocycle_eq _ (b' := S.sec c * S.sec c')
      (by rw [S.π_sec, map_mul, S.π_sec, S.π_sec]; rfl)]
    congr 1
    refine Subtype.ext (funext fun g => S.injective ?_)
    rw [ContH1.coe_mul_apply, map_mul S.i, S.i_delta0Cocycle, S.i_delta0Cocycle, S.i_delta0Cocycle,
      smul_mul']
    mul_abel

theorem delta0_eq (c : H0 G C) (b : B) (hb : S.π b = c) :
    S.delta0 c = ContH1.mk (S.delta0Cocycle b (fun g => by rw [hb, smul_H0 c g])) :=
  S.mk_delta0Cocycle_eq _ (by rw [S.π_sec, hb])

/-- Exactness at `H⁰(C)`. -/
theorem exact_h0C : S.delta0.ker = (h0Hom (G := G) S.π S.map_smul_π).range := by
  ext c
  constructor
  · intro hc
    rw [MonoidHom.mem_ker, S.delta0_eq c (S.sec c) (S.π_sec c), ContH1.mk_eq_one_iff] at hc
    obtain ⟨a, ha⟩ := hc
    refine ⟨⟨S.sec c / S.i a, fun g => ?_⟩, Subtype.ext ?_⟩
    · have := congrArg S.i (ha g)
      rw [S.i_delta0Cocycle, map_div, S.map_smul_i] at this
      rw [smul_div', div_eq_div_iff_mul_eq_mul]
      rw [div_eq_div_iff_mul_eq_mul] at this
      rw [← this]
      exact mul_comm _ _
    · simp [S.π_sec, S.π_i]
  · rintro ⟨b, rfl⟩
    rw [MonoidHom.mem_ker, S.delta0_eq _ (b : B) rfl, ContH1.mk_eq_one_iff]
    refine ⟨1, fun g => S.injective ?_⟩
    rw [S.i_delta0Cocycle, smul_H0 b g, div_self', smul_one, div_one, map_one]

/-- Exactness at `H¹(A)`. -/
theorem exact_h1A : (h1Hom (G := G) S.i S.map_smul_i).ker = S.delta0.range := by
  ext x
  induction x using ContH1.induction_on with | h x => ?_
  constructor
  · intro hx
    rw [MonoidHom.mem_ker, h1Hom_mk, ContH1.mk_eq_one_iff] at hx
    obtain ⟨b, hb⟩ := hx
    have hπ : ∀ g : G, g • S.π b = S.π b := fun g => by
      have := congrArg S.π (hb g)
      rw [ContH1.cocyclesMap_apply, S.π_i, map_div, S.map_smul_π, div_eq_one] at this
      exact this
    refine ⟨⟨S.π b, hπ⟩, ?_⟩
    rw [S.delta0_eq _ b rfl]
    congr 1
    refine Subtype.ext (funext fun g => S.injective ?_)
    rw [S.i_delta0Cocycle, hb g]
    rfl
  · rintro ⟨c, hc⟩
    rw [← hc, MonoidHom.mem_ker, S.delta0_eq c (S.sec c) (S.π_sec c), h1Hom_mk,
      ContH1.mk_eq_one_iff]
    exact ⟨S.sec c, fun g => (S.i_delta0Cocycle _ _ g).symm⟩

/-- Exactness at `H¹(B)`. -/
theorem exact_h1B : (h1Hom (G := G) S.π S.map_smul_π).ker = (h1Hom S.i S.map_smul_i).range := by
  ext y
  induction y using ContH1.induction_on with | h y => ?_
  constructor
  · intro hy
    rw [MonoidHom.mem_ker, h1Hom_mk, ContH1.mk_eq_one_iff] at hy
    obtain ⟨c, hc⟩ := hy
    set b := S.sec c
    have hker : ∀ g : G, S.π (y g / (g • b / b)) = 1 := fun g => by
      have := hc g
      rw [ContH1.cocyclesMap_apply] at this
      rw [map_div, map_div, S.map_smul_π, S.π_sec, this]
      exact div_self' _
    let a : ContH1.cocycles G A := ContH1.mkCocycle (fun g => S.pre (y g / (g • b / b)))
      ((((IsLocallyConstant.iff_continuous _).2 (ContH1.continuous y)).div
        ((SmoothAction.isLocallyConstant_smul (G := G) b).div
          (IsLocallyConstant.const b))).comp S.pre).continuous
      (fun g h => by
        apply S.injective
        rw [map_mul, S.map_smul_i, S.i_pre (hker _), S.i_pre (hker _), S.i_pre (hker _),
          ContH1.isMulCocycle₁ y g h, smul_div', smul_div', mul_smul]
        mul_abel)
    refine ⟨ContH1.mk a, ?_⟩
    rw [h1Hom_mk, ContH1.mk_eq_mk_iff]
    refine ⟨b⁻¹, fun g => ?_⟩
    beta_reduce
    rw [ContH1.cocyclesMap_apply]
    change g • b⁻¹ / b⁻¹ = S.i (S.pre (y g / (g • b / b))) / y g
    rw [S.i_pre (hker g), smul_inv']
    mul_abel
  · rintro ⟨x, hx⟩
    rw [← hx]
    induction x using ContH1.induction_on with | h x => ?_
    rw [MonoidHom.mem_ker, h1Hom_mk, h1Hom_mk, ContH1.mk_eq_one_iff]
    exact ⟨1, fun g => by simp [S.π_i]⟩

end Delta0

/-! ### The connecting map `δ¹ : H¹(C) → H²(A)` -/

section Delta1

variable [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalGroup A]
  [TopologicalSpace B] [DiscreteTopology B] [IsTopologicalGroup B] [SmoothAction G B]
  [TopologicalSpace C] [DiscreteTopology C] [IsTopologicalGroup C]

theorem π_dx_eq_one {y : G → B} (hc : IsMulCocycle₁ fun g => S.π (y g)) (gh : G × G) :
    S.π (dx G B y gh) = 1 := by
  rw [S.π_dx]
  obtain ⟨g, h⟩ := gh
  have := hc g h
  simp only at this
  rw [dx_apply, this]
  mul_abel

theorem i_pre_dx {y : G → B} (hc : IsMulCocycle₁ fun g => S.π (y g)) (gh : G × G) :
    S.i (S.pre (dx G B y gh)) = dx G B y gh := S.i_pre (S.π_dx_eq_one hc gh)

/-- The `A`-valued 2-cocycle `d ỹ` of a locally constant lift `ỹ` of a 1-cocycle of `C`. -/
noncomputable def delta1Cocycle (y : G → B) (hy : IsLocallyConstant y)
    (hc : IsMulCocycle₁ fun g => S.π (y g)) : ContH2.cocycles G A :=
  mkCocycle (fun gh => S.pre (dx G B y gh)) ((isLocallyConstant_dx hy).comp S.pre) (by
    intro g h j
    apply S.injective
    simp only [map_mul, S.map_smul_i, S.i_pre_dx hc]
    exact isMulCocycle₂_dx y g h j)

theorem i_delta1Cocycle (y : G → B) (hy : IsLocallyConstant y)
    (hc : IsMulCocycle₁ fun g => S.π (y g)) (gh : G × G) :
    S.i (S.delta1Cocycle y hy hc gh) = dx G B y gh := S.i_pre_dx hc gh

theorem mk_delta1Cocycle_eq {y y' : G → B} (hy : IsLocallyConstant y)
    (hy' : IsLocallyConstant y') (hc : IsMulCocycle₁ fun g => S.π (y g))
    (h : ∀ g, S.π (y g) = S.π (y' g)) :
    ContH2.mk (S.delta1Cocycle y hy hc) =
      ContH2.mk (S.delta1Cocycle y' hy' (by simpa only [h] using hc)) := by
  rw [mk_eq_mk_iff]
  have hq : ∀ g, S.π (y g / y' g) = 1 := fun g => by rw [map_div, h, div_self']
  refine ⟨fun g => S.pre (y g / y' g), (hy.div hy').comp S.pre, funext fun gh => ?_⟩
  apply S.injective
  rw [S.i_dx, Pi.div_apply, map_div, S.i_delta1Cocycle, S.i_delta1Cocycle]
  obtain ⟨g, h⟩ := gh
  simp only [S.i_pre (hq _), dx_apply, smul_div']
  mul_abel

theorem isMulCocycle₁_of_dx_eq_one {M : Type*} [CommGroup M] [MulDistribMulAction G M]
    {y : G → M} (h : ∀ a b : G, dx G M y (a, b) = 1) : IsMulCocycle₁ y := by
  intro a b
  have := h a b
  rw [dx_apply, div_mul_eq_mul_div, div_eq_one] at this
  exact this.symm

theorem dx_eq_one_of_isMulCocycle₁ {M : Type*} [CommGroup M] [MulDistribMulAction G M]
    {y : G → M} (hy : IsMulCocycle₁ y) (gh : G × G) : dx G M y gh = 1 := by
  obtain ⟨a, b⟩ := gh
  rw [dx_apply, hy a b]
  mul_abel

theorem delta1Cocycle_eq_one {y : G → B} (hy : IsLocallyConstant y) (hy1 : IsMulCocycle₁ y)
    (hc : IsMulCocycle₁ fun g => S.π (y g)) : S.delta1Cocycle y hy hc = 1 := by
  refine cocycles_ext fun g h => S.injective ?_
  rw [S.i_delta1Cocycle, dx_eq_one_of_isMulCocycle₁ hy1, coe_one_apply, map_one]

theorem isLocallyConstant_sec_comp (x : ContH1.cocycles G C) :
    IsLocallyConstant fun g => S.sec (x g) :=
  ((IsLocallyConstant.iff_continuous _).2 (ContH1.continuous x)).comp S.sec

theorem isMulCocycle₁_of_lift (x : ContH1.cocycles G C) {y : G → B}
    (hyx : ∀ g, S.π (y g) = x g) : IsMulCocycle₁ fun g => S.π (y g) := by
  have : (fun g => S.π (y g)) = x := funext hyx
  rw [this]
  exact ContH1.isMulCocycle₁ x

/-- `δ¹` on cocycles. -/
noncomputable def delta1Cocycles : ContH1.cocycles G C →* ContH2 G A where
  toFun x := ContH2.mk (S.delta1Cocycle (fun g => S.sec (x g)) (S.isLocallyConstant_sec_comp x)
    (S.isMulCocycle₁_of_lift x fun g => S.π_sec _))
  map_one' := by
    rw [S.mk_delta1Cocycle_eq _ (IsLocallyConstant.const 1) _
      (fun g => by rw [S.π_sec]; exact (map_one S.π).symm),
      S.delta1Cocycle_eq_one _ (fun g h => by simp),
      map_one]
  map_mul' x x' := by
    rw [S.mk_delta1Cocycle_eq _ ((S.isLocallyConstant_sec_comp x).mul
      (S.isLocallyConstant_sec_comp x')) _
      (fun g => by rw [S.π_sec, Pi.mul_apply, map_mul, S.π_sec, S.π_sec]; rfl), ← map_mul]
    congr 1
    refine cocycles_ext fun g h => S.injective ?_
    rw [coe_mul_apply, map_mul, S.i_delta1Cocycle, S.i_delta1Cocycle, S.i_delta1Cocycle, dx_mul]
    rfl

/-- **The connecting homomorphism** `δ¹ : H¹(G, C) → H²(G, A)`. -/
noncomputable def delta1 : ContH1 G C →* ContH2 G A :=
  QuotientGroup.lift (ContH1.coboundaries G C) S.delta1Cocycles (by
    rintro x ⟨c, hc⟩
    rw [MonoidHom.mem_ker]
    have hyl : IsLocallyConstant fun g : G => g • S.sec c / S.sec c :=
      (SmoothAction.isLocallyConstant_smul (G := G) (S.sec c)).div (IsLocallyConstant.const _)
    have hyx : ∀ g : G, S.π (g • S.sec c / S.sec c) = x g := fun g => by
      rw [map_div, S.map_smul_π, S.π_sec, hc g]
    change ContH2.mk _ = 1
    rw [S.mk_delta1Cocycle_eq _ hyl _ (fun g => by rw [S.π_sec, hyx]),
      S.delta1Cocycle_eq_one _ (fun g h => by
        rw [mul_smul, smul_div']
        mul_abel), map_one])

/-- `δ¹[x] = [d ỹ]` for any locally constant lift `ỹ` of `x`. -/
theorem delta1_mk (x : ContH1.cocycles G C) {y : G → B} (hy : IsLocallyConstant y)
    (hyx : ∀ g, S.π (y g) = x g) :
    S.delta1 (ContH1.mk x) = ContH2.mk (S.delta1Cocycle y hy (S.isMulCocycle₁_of_lift x hyx)) :=
  S.mk_delta1Cocycle_eq _ hy _ (fun g => by rw [S.π_sec, hyx])

/-- Exactness at `H¹(C)`. -/
theorem exact_h1C : S.delta1.ker = (h1Hom (G := G) S.π S.map_smul_π).range := by
  ext x
  induction x using ContH1.induction_on with | h x => ?_
  constructor
  · intro hx
    rw [MonoidHom.mem_ker, S.delta1_mk x (S.isLocallyConstant_sec_comp x) (fun g => S.π_sec _),
      mk_eq_one_iff] at hx
    obtain ⟨a, ha, hda⟩ := hx
    set y : G → B := fun g => S.sec (x g) / S.i (a g) with hy_def
    have hyl : IsLocallyConstant y :=
      (S.isLocallyConstant_sec_comp x).div (ha.comp S.i)
    have hdy : ∀ g h : G, dx G B y (g, h) = 1 := fun g h => by
      have e1 := congrArg S.i (congrFun hda (g, h))
      rw [S.i_dx, S.i_delta1Cocycle] at e1
      have e2 : y = (fun g => S.sec (x g)) / fun g => S.i (a g) := rfl
      rw [e2, div_eq_mul_inv, dx_mul, dx_inv, Pi.mul_apply, Pi.inv_apply, e1, mul_inv_cancel]
    let yc : ContH1.cocycles G B :=
      ContH1.mkCocycle y hyl.continuous (isMulCocycle₁_of_dx_eq_one hdy)
    refine ⟨ContH1.mk yc, ?_⟩
    rw [h1Hom_mk]
    congr 1
    refine Subtype.ext (funext fun g => ?_)
    change S.π (S.sec (x g) / S.i (a g)) = x g
    rw [map_div, S.π_sec, S.π_i, div_one]
  · rintro ⟨y, hy⟩
    rw [← hy]
    induction y using ContH1.induction_on with | h y => ?_
    rw [MonoidHom.mem_ker, h1Hom_mk, S.delta1_mk _
      ((IsLocallyConstant.iff_continuous _).2 (ContH1.continuous y)) (fun g => rfl),
      S.delta1Cocycle_eq_one _ (ContH1.isMulCocycle₁ y), map_one]

/-- Exactness at `H²(A)`. -/
theorem exact_h2A : (h2Hom (G := G) S.i S.map_smul_i).ker = S.delta1.range := by
  ext f
  induction f using induction_on with | h f => ?_
  constructor
  · intro hf
    rw [MonoidHom.mem_ker, h2Hom_mk, mk_eq_one_iff] at hf
    obtain ⟨β, hβ, hdβ⟩ := hf
    have hdβ' : ∀ gh, dx G B β gh = S.i (f gh) := fun gh => congrFun hdβ gh
    have hc : IsMulCocycle₁ fun g => S.π (β g) := isMulCocycle₁_of_dx_eq_one fun g h => by
      rw [← S.π_dx, hdβ', S.π_i]
    let x : ContH1.cocycles G C :=
      ContH1.mkCocycle (fun g => S.π (β g)) (hβ.comp S.π).continuous hc
    refine ⟨ContH1.mk x, ?_⟩
    rw [S.delta1_mk x hβ (fun g => rfl)]
    congr 1
    refine cocycles_ext fun g h => S.injective ?_
    rw [S.i_delta1Cocycle, hdβ']
  · rintro ⟨x, hx⟩
    rw [← hx]
    induction x using ContH1.induction_on with | h x => ?_
    rw [MonoidHom.mem_ker, S.delta1_mk x (S.isLocallyConstant_sec_comp x) (fun g => S.π_sec _),
      h2Hom_mk, mk_eq_one_iff]
    refine ⟨fun g => S.sec (x g), S.isLocallyConstant_sec_comp x, funext fun gh => ?_⟩
    obtain ⟨g, h⟩ := gh
    rw [cocyclesMap_apply, MonoidHom.id_apply, MonoidHom.id_apply, S.i_delta1Cocycle]

/-- Exactness at `H²(B)`. -/
theorem exact_h2B : (h2Hom (G := G) S.π S.map_smul_π).ker = (h2Hom S.i S.map_smul_i).range := by
  ext f
  induction f using induction_on with | h f => ?_
  constructor
  · intro hf
    rw [MonoidHom.mem_ker, h2Hom_mk, mk_eq_one_iff] at hf
    obtain ⟨γ, hγ, hdγ⟩ := hf
    set b : G → B := fun g => S.sec (γ g) with hb_def
    have hbl : IsLocallyConstant b := hγ.comp S.sec
    let D : ContH2.cocycles G B :=
      mkCocycle (dx G B b) (isLocallyConstant_dx hbl) (isMulCocycle₂_dx b)
    let F : ContH2.cocycles G B := f / D
    have hF : ∀ gh, S.π (F gh) = 1 := fun gh => by
      have e := congrFun hdγ gh
      change S.π (f gh / dx G B b gh) = 1
      rw [map_div, S.π_dx]
      have hb' : (fun g => S.π (b g)) = γ := funext fun g => S.π_sec _
      rw [hb', e]
      exact div_self' _
    let a : ContH2.cocycles G A := mkCocycle (fun gh => S.pre (F gh))
      ((isLocallyConstant F).comp S.pre) (by
        intro g h j
        apply S.injective
        simp only [map_mul, S.map_smul_i, S.i_pre (hF _)]
        exact isMulCocycle₂ F g h j)
    refine ⟨ContH2.mk a, ?_⟩
    rw [h2Hom_mk, mk_eq_mk_iff]
    refine ⟨b⁻¹, hbl.inv, ?_⟩
    rw [dx_inv]
    funext gh
    change (dx G B b gh)⁻¹ = S.i (S.pre (F gh)) / f gh
    rw [S.i_pre (hF gh)]
    change (dx G B b gh)⁻¹ = f gh / dx G B b gh / f gh
    mul_abel
  · rintro ⟨a, ha⟩
    rw [← ha]
    induction a using induction_on with | h a => ?_
    rw [MonoidHom.mem_ker, h2Hom_comp]
    rw [← map_one (ContH2.mk (G := G) (M := C)), h2Hom_mk]
    congr 1
    refine cocycles_ext fun g h => ?_
    simp [S.π_i]

end Delta1

end GShortExact

end Brauer
