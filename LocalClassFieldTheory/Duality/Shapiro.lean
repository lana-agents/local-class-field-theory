/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.H3Cores

/-!
# Shapiro's lemma in degrees two and three (cocycle form)

For a subgroup `H ≤ G` and a `G`-module `A`, the **coinduced module** `ContH2.CoInd H A` is the
group of functions `G/H → A` with `(g • f)(c) = g • f(g⁻¹ • c)`. Shapiro's lemma identifies
`Hⁿ(G, CoInd H A)` with `Hⁿ(H, A)` via restriction to `H` followed by evaluation at the base
coset `o = H`. We prove the two halves needed for Tate's theorem, for a discrete group `G`:

* **`ContH2.CoInd.exists_dx_of_ev`** (degree two): a `2`-cocycle `F` of `G` with values in
  `CoInd H A` whose restriction-evaluation `(a, b) ↦ F(a, b)(o)` is a coboundary on `H` is a
  coboundary on `G`; hence the map `ContH2.CoInd.shapiro : H²(G, CoInd H A) → H²(H, A)` is
  injective (`ContH2.CoInd.shapiro_injective`);
* **`ContH2.CoInd.h3Trivial`** (degree three): `H³(H, A) = 0` implies `H³(G, CoInd H A) = 0`.

The proofs pass through homogeneous cochains: a `G`-cochain `x` with values in `CoInd H A` gives
the `H`-equivariant function `Z(x₀, …, xₙ) = (x₀ • x(x₀⁻¹x₁, …))(o)`. With coset
representatives `c.out` and the retraction `r(x) = x · (x⁻¹H).out ∈ H` (`r(hx) = h r(x)`), the
prism operator `P(x₀, …) = Σᵢ (-1)ⁱ Z(r x₀, …, r xᵢ, xᵢ, …)` is a homotopy between `Z` and
`Z ∘ r`, so `Z = d(W ∘ r · P Z)` when `Z ∘ r = d W` on `H`; the primitive is lifted back to
`CoInd H A` by `c ↦ c.out • Y(c.out⁻¹ x₀, …)` (`ContH2.CoInd.lift₂`, `ContH2.CoInd.lift₃`).
-/

open groupCohomology

set_option linter.unusedSectionVars false

namespace ContH2

variable {G A : Type*} [Group G] [CommGroup A] [MulDistribMulAction G A] (H : Subgroup G)

/-- The coinduced module `Map(G/H, A)` with `(g • f)(c) = g • f(g⁻¹ • c)`. -/
def CoInd (H : Subgroup G) (A : Type*) : Type _ := G ⧸ H → A

namespace CoInd

instance : CommGroup (CoInd H A) := inferInstanceAs (CommGroup (G ⧸ H → A))

instance : CoeFun (CoInd H A) (fun _ => G ⧸ H → A) := ⟨fun f => f⟩

instance : MulDistribMulAction G (CoInd H A) where
  smul g f := fun c => g • (f : G ⧸ H → A) (g⁻¹ • c)
  one_smul f := by
    funext c
    change (1 : G) • (f : G ⧸ H → A) ((1 : G)⁻¹ • c) = f c
    rw [inv_one, one_smul, one_smul]
  mul_smul g h f := by
    funext c
    change (g * h) • (f : G ⧸ H → A) ((g * h)⁻¹ • c) = g • (h • (f : G ⧸ H → A) (h⁻¹ • g⁻¹ • c))
    rw [mul_smul, mul_inv_rev, mul_smul]
  smul_mul g f f' := by
    funext c
    exact smul_mul' g ((f : G ⧸ H → A) (g⁻¹ • c)) ((f' : G ⧸ H → A) (g⁻¹ • c))
  smul_one g := by
    funext c
    exact smul_one g

variable {H}

theorem ext {f f' : CoInd H A} (h : ∀ c, f c = f' c) : f = f' := funext h

@[simp]
theorem smul_apply (g : G) (f : CoInd H A) (c : G ⧸ H) : (g • f) c = g • f (g⁻¹ • c) := rfl

@[simp]
theorem mul_apply (f f' : CoInd H A) (c : G ⧸ H) : (f * f') c = f c * f' c := rfl

@[simp]
theorem div_apply (f f' : CoInd H A) (c : G ⧸ H) : (f / f') c = f c / f' c := rfl

@[simp]
theorem inv_apply (f : CoInd H A) (c : G ⧸ H) : f⁻¹ c = (f c)⁻¹ := rfl

@[simp]
theorem one_apply (c : G ⧸ H) : (1 : CoInd H A) c = 1 := rfl

variable (H) in
/-- The base coset `o = H ∈ G/H`. -/
abbrev base : G ⧸ H := QuotientGroup.mk 1

theorem smul_base_of_mem {h : G} (hh : h ∈ H) : h • base H = base H := by
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
  simpa using H.inv_mem hh

theorem out_smul_base (c : G ⧸ H) : c.out • base H = c := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.out_eq']

theorem smul_apply_base_of_mem {h : G} (hh : h ∈ H) (f : CoInd H A) :
    (h • f) (base H) = h • f (base H) := by
  rw [smul_apply, smul_base_of_mem (H.inv_mem hh)]

variable (H) in
/-- Evaluation at the base coset, an `H`-equivariant homomorphism `CoInd H A → A`. -/
def ev : CoInd H A →* A where
  toFun f := f (base H)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ev_apply (f : CoInd H A) : ev H f = f (base H) := rfl

theorem ev_smul (h : H) (f : CoInd H A) : ev H (h • f) = h • ev H f :=
  smul_apply_base_of_mem h.2 f

/-! ### The retraction `r : G → H` -/

variable (H) in
/-- The retraction `r(x) = x · (x⁻¹H).out`, an element of `H` with `r(hx) = h r(x)`. -/
noncomputable def retr (x : G) : G := x * (QuotientGroup.mk x⁻¹ : G ⧸ H).out

theorem retr_mem (x : G) : retr H x ∈ H := by
  have := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk x⁻¹ : G ⧸ H)).symm
  rwa [inv_inv] at this

theorem retr_mul {h : G} (hh : h ∈ H) (x : G) : retr H (h * x) = h * retr H x := by
  have e : (QuotientGroup.mk (h * x)⁻¹ : G ⧸ H) = QuotientGroup.mk x⁻¹ := by
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using hh
  rw [retr, retr, e, mul_assoc]

/-! ### Lifting `H`-equivariant homogeneous cochains -/

/-- The key identity behind the lifts: with `s = c.out`, `t = (g⁻¹ • c).out`, the element
`k = s⁻¹ g t` lies in `H`. -/
theorem out_inv_mul_mem' (c : G ⧸ H) (g : G) :
    (c.out)⁻¹ * g * (g⁻¹ • c).out ∈ H :=
  out_inv_mul_mem H c g

/-- Lift of an `H`-equivariant homogeneous `1`-cochain `Y` (a function of two variables). -/
noncomputable def lift₂ (Y : G → G → A) (x₀ x₁ : G) : CoInd H A :=
  fun c => c.out • Y (c.out⁻¹ * x₀) (c.out⁻¹ * x₁)

/-- Lift of an `H`-equivariant homogeneous `2`-cochain `Y` (a function of three variables). -/
noncomputable def lift₃ (Y : G → G → G → A) (x₀ x₁ x₂ : G) : CoInd H A :=
  fun c => c.out • Y (c.out⁻¹ * x₀) (c.out⁻¹ * x₁) (c.out⁻¹ * x₂)

theorem lift₂_apply (Y : G → G → A) (x₀ x₁ : G) (c : G ⧸ H) :
    lift₂ (H := H) Y x₀ x₁ c = c.out • Y (c.out⁻¹ * x₀) (c.out⁻¹ * x₁) := rfl

theorem lift₃_apply (Y : G → G → G → A) (x₀ x₁ x₂ : G) (c : G ⧸ H) :
    lift₃ (H := H) Y x₀ x₁ x₂ c = c.out • Y (c.out⁻¹ * x₀) (c.out⁻¹ * x₁) (c.out⁻¹ * x₂) := rfl

/-- Rewriting `t⁻¹ x = k⁻¹ (s⁻¹ (g x))` and `g t k⁻¹ = s`. -/
theorem lift_aux (c : G ⧸ H) (g x : G) :
    ((g⁻¹ • c).out)⁻¹ * x =
      ((c.out)⁻¹ * g * (g⁻¹ • c).out)⁻¹ * ((c.out)⁻¹ * (g * x)) := by
  group

theorem lift_aux' (c : G ⧸ H) (g : G) :
    g * (g⁻¹ • c).out * ((c.out)⁻¹ * g * (g⁻¹ • c).out)⁻¹ = c.out := by
  group

theorem smul_lift₂ {Y : G → G → A}
    (hY : ∀ h ∈ H, ∀ a b : G, Y (h * a) (h * b) = h • Y a b) (g x₀ x₁ : G) :
    g • lift₂ (H := H) Y x₀ x₁ = lift₂ Y (g * x₀) (g * x₁) := by
  apply ext
  intro c
  rw [smul_apply, lift₂_apply, lift₂_apply, lift_aux c g x₀, lift_aux c g x₁,
    hY _ (H.inv_mem (out_inv_mul_mem' c g)), ← mul_smul, ← mul_smul, ← mul_assoc,
    lift_aux' c g]

theorem smul_lift₃ {Y : G → G → G → A}
    (hY : ∀ h ∈ H, ∀ a b d : G, Y (h * a) (h * b) (h * d) = h • Y a b d) (g x₀ x₁ x₂ : G) :
    g • lift₃ (H := H) Y x₀ x₁ x₂ = lift₃ Y (g * x₀) (g * x₁) (g * x₂) := by
  apply ext
  intro c
  rw [smul_apply, lift₃_apply, lift₃_apply, lift_aux c g x₀, lift_aux c g x₁, lift_aux c g x₂,
    hY _ (H.inv_mem (out_inv_mul_mem' c g)), ← mul_smul, ← mul_smul, ← mul_assoc,
    lift_aux' c g]

/-! ### Degree two -/

section Degree2

/-- The homogeneous form `(x₀, x₁, x₂) ↦ (x₀ • F(x₀⁻¹x₁, x₁⁻¹x₂))(o)` of a `2`-cochain. -/
def hom₂ (F : G × G → CoInd H A) (x₀ x₁ x₂ : G) : A :=
  (x₀ • F (x₀⁻¹ * x₁, x₁⁻¹ * x₂)) (base H)

theorem hom₂_mul (F : G × G → CoInd H A) {h : G} (hh : h ∈ H) (x₀ x₁ x₂ : G) :
    hom₂ F (h * x₀) (h * x₁) (h * x₂) = h • hom₂ F x₀ x₁ x₂ := by
  have e : ∀ a b : G, (h * a)⁻¹ * (h * b) = a⁻¹ * b := fun a b => by group
  rw [hom₂, hom₂, e, e, mul_smul, smul_apply_base_of_mem hh]

theorem hom₂_cocycle {F : G × G → CoInd H A} (hF : IsMulCocycle₂ F) (x₀ x₁ x₂ x₃ : G) :
    hom₂ F x₀ x₂ x₃ * hom₂ F x₀ x₁ x₂ = hom₂ F x₁ x₂ x₃ * hom₂ F x₀ x₁ x₃ := by
  have h := congrArg (fun m : CoInd H A => (x₀ • m) (base H))
    (hF (x₀⁻¹ * x₁) (x₁⁻¹ * x₂) (x₂⁻¹ * x₃))
  have e : ∀ a b c : G, a⁻¹ * b * (b⁻¹ * c) = a⁻¹ * c := fun a b c => by group
  simp only [smul_mul', mul_apply, ← mul_smul, e, mul_inv_cancel_left] at h
  exact h

theorem hom₂_rec (F : G × G → CoInd H A) (g₁ g₂ : G) (c : G ⧸ H) :
    F (g₁, g₂) c = c.out • hom₂ F (c.out)⁻¹ ((c.out)⁻¹ * g₁) ((c.out)⁻¹ * (g₁ * g₂)) := by
  have e1 : ((c.out)⁻¹)⁻¹ * ((c.out)⁻¹ * g₁) = g₁ := by group
  have e2 : ((c.out)⁻¹ * g₁)⁻¹ * ((c.out)⁻¹ * (g₁ * g₂)) = g₂ := by group
  rw [hom₂, e1, e2, smul_apply, inv_inv, out_smul_base, smul_inv_smul]

/-- **Shapiro's lemma in degree two (injectivity)**: a `2`-cocycle `F` of `G` with values in
`CoInd H A` whose restriction-evaluation `(a, b) ↦ F(a, b)(o)` is a coboundary on `H` is a
coboundary. -/
theorem exists_dx_of_ev {F : G × G → CoInd H A} (hF : IsMulCocycle₂ F) {y : H → A}
    (hy : ∀ a b : H, F (a, b) (base H) = dx H A y (a, b)) :
    ∃ f : G → CoInd H A, dx G (CoInd H A) f = F := by
  classical
  let yG : G → A := fun a => if ha : a ∈ H then y ⟨a, ha⟩ else 1
  have hyG : ∀ a b : G, a ∈ H → b ∈ H →
      F (a, b) (base H) = a • yG b / yG (a * b) * yG a := by
    intro a b ha hb
    have := hy ⟨a, ha⟩ ⟨b, hb⟩
    simp only [yG, dif_pos ha, dif_pos hb, dif_pos (H.mul_mem ha hb)]
    exact this
  let W : G → G → A := fun y₀ y₁ => y₀ • yG (y₀⁻¹ * y₁)
  have hW : ∀ h ∈ H, ∀ a b : G, W (h * a) (h * b) = h • W a b := by
    intro h _ a b
    simp only [W]
    rw [show (h * a)⁻¹ * (h * b) = a⁻¹ * b by group, mul_smul]
  have hZW : ∀ y₀ y₁ y₂ : G, y₀ ∈ H → y₁ ∈ H → y₂ ∈ H →
      W y₁ y₂ / W y₀ y₂ * W y₀ y₁ / hom₂ F y₀ y₁ y₂ = 1 := by
    intro y₀ y₁ y₂ h0 h1 h2
    rw [div_eq_one, hom₂, smul_apply_base_of_mem h0,
      hyG _ _ (H.mul_mem (H.inv_mem h0) h1) (H.mul_mem (H.inv_mem h1) h2)]
    simp only [W, smul_mul', smul_div', ← mul_smul, mul_inv_cancel_left,
      show y₀⁻¹ * y₁ * (y₁⁻¹ * y₂) = y₀⁻¹ * y₂ by group]
  let Y : G → G → A := fun x₀ x₁ => W (retr H x₀) (retr H x₁) *
    (hom₂ F (retr H x₀) x₀ x₁ / hom₂ F (retr H x₀) (retr H x₁) x₁)
  have hY : ∀ h ∈ H, ∀ a b : G, Y (h * a) (h * b) = h • Y a b := by
    intro h hh a b
    simp only [Y, retr_mul hh, hW _ hh, hom₂_mul F hh, smul_mul', smul_div']
  have hdY : ∀ x₀ x₁ x₂ : G, Y x₁ x₂ / Y x₀ x₂ * Y x₀ x₁ = hom₂ F x₀ x₁ x₂ := by
    intro x₀ x₁ x₂
    have c1 := div_eq_one.2 (hom₂_cocycle hF (retr H x₀) x₀ x₁ x₂)
    have c2 := div_eq_one.2 (hom₂_cocycle hF (retr H x₀) (retr H x₁) x₁ x₂)
    have c3 := div_eq_one.2 (hom₂_cocycle hF (retr H x₀) (retr H x₁) (retr H x₂) x₂)
    have hw := hZW _ _ _ (retr_mem x₀) (retr_mem x₁) (retr_mem x₂)
    rw [← div_eq_one]
    calc _ = (W (retr H x₁) (retr H x₂) / W (retr H x₀) (retr H x₂) * W (retr H x₀) (retr H x₁) /
          hom₂ F (retr H x₀) (retr H x₁) (retr H x₂)) *
        ((hom₂ F (retr H x₀) x₁ x₂ * hom₂ F (retr H x₀) x₀ x₁ /
            (hom₂ F x₀ x₁ x₂ * hom₂ F (retr H x₀) x₀ x₂)) /
          (hom₂ F (retr H x₀) x₁ x₂ * hom₂ F (retr H x₀) (retr H x₁) x₁ /
            (hom₂ F (retr H x₁) x₁ x₂ * hom₂ F (retr H x₀) (retr H x₁) x₂)) *
          (hom₂ F (retr H x₀) (retr H x₂) x₂ * hom₂ F (retr H x₀) (retr H x₁) (retr H x₂) /
            (hom₂ F (retr H x₁) (retr H x₂) x₂ * hom₂ F (retr H x₀) (retr H x₁) x₂))) := by
          simp only [Y]
          mul_abel
      _ = 1 := by rw [hw, c1, c2, c3]; simp
  refine ⟨fun g => lift₂ Y 1 g, ?_⟩
  funext ⟨a, b⟩
  apply ext
  intro c
  rw [dx_apply, smul_lift₂ hY, mul_apply, div_apply, lift₂_apply, lift₂_apply, lift₂_apply,
    hom₂_rec F a b c, ← hdY]
  simp only [mul_one, smul_mul', smul_div']

section Topology

variable [TopologicalSpace G] [DiscreteTopology G]

variable (H A) in
/-- The Shapiro map `H²(G, CoInd H A) → H²(H, A)`: restriction to `H`, then evaluation at the
base coset. -/
noncomputable def shapiro : ContH2 G (CoInd H A) →* ContH2 H A :=
  ContH2.map H.subtype continuous_subtype_val (ev H) fun h m => ev_smul h m

/-- **Shapiro's lemma in degree two**: `H²(G, CoInd H A) → H²(H, A)` is injective. -/
theorem shapiro_injective : Function.Injective (shapiro A H) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using induction_on with | h F => ?_
  rw [shapiro, map_mk, mk_eq_one_iff] at hx
  obtain ⟨y, -, hy⟩ := hx
  obtain ⟨f, hf⟩ := exists_dx_of_ev (isMulCocycle₂ F) (y := y)
    fun a b => (congrFun hy (a, b)).symm
  exact (mk_eq_one_iff F).2 ⟨f, .of_discrete _, hf⟩

end Topology

end Degree2

/-! ### Degree three -/

section Degree3

/-- The homogeneous form `(x₀, …, x₃) ↦ (x₀ • z(x₀⁻¹x₁, x₁⁻¹x₂, x₂⁻¹x₃))(o)` of a `3`-cochain. -/
def hom₃ (z : G × G × G → CoInd H A) (x₀ x₁ x₂ x₃ : G) : A :=
  (x₀ • z (x₀⁻¹ * x₁, x₁⁻¹ * x₂, x₂⁻¹ * x₃)) (base H)

theorem hom₃_mul (z : G × G × G → CoInd H A) {h : G} (hh : h ∈ H) (x₀ x₁ x₂ x₃ : G) :
    hom₃ z (h * x₀) (h * x₁) (h * x₂) (h * x₃) = h • hom₃ z x₀ x₁ x₂ x₃ := by
  have e : ∀ a b : G, (h * a)⁻¹ * (h * b) = a⁻¹ * b := fun a b => by group
  rw [hom₃, hom₃, e, e, e, mul_smul, smul_apply_base_of_mem hh]

theorem hom₃_cocycle {z : G × G × G → CoInd H A} (hz : IsMulCocycle₃ z) (x₀ x₁ x₂ x₃ x₄ : G) :
    hom₃ z x₁ x₂ x₃ x₄ * hom₃ z x₀ x₁ x₃ x₄ * hom₃ z x₀ x₁ x₂ x₃ /
      (hom₃ z x₀ x₂ x₃ x₄ * hom₃ z x₀ x₁ x₂ x₄) = 1 := by
  have h := congrArg (fun m : CoInd H A => (x₀ • m) (base H))
    (hz (x₀⁻¹ * x₁) (x₁⁻¹ * x₂) (x₂⁻¹ * x₃) (x₃⁻¹ * x₄))
  have e : ∀ a b c : G, a⁻¹ * b * (b⁻¹ * c) = a⁻¹ * c := fun a b c => by group
  simp only [smul_mul', mul_apply, ← mul_smul, e, mul_inv_cancel_left] at h
  exact div_eq_one.2 h

theorem hom₃_rec (z : G × G × G → CoInd H A) (g₁ g₂ g₃ : G) (c : G ⧸ H) :
    z (g₁, g₂, g₃) c = c.out • hom₃ z (c.out)⁻¹ ((c.out)⁻¹ * g₁) ((c.out)⁻¹ * (g₁ * g₂))
      ((c.out)⁻¹ * (g₁ * (g₂ * g₃))) := by
  have e1 : ((c.out)⁻¹)⁻¹ * ((c.out)⁻¹ * g₁) = g₁ := by group
  have e2 : ((c.out)⁻¹ * g₁)⁻¹ * ((c.out)⁻¹ * (g₁ * g₂)) = g₂ := by group
  have e3 : ((c.out)⁻¹ * (g₁ * g₂))⁻¹ * ((c.out)⁻¹ * (g₁ * (g₂ * g₃))) = g₃ := by group
  rw [hom₃, e1, e2, e3, smul_apply, inv_inv, out_smul_base, smul_inv_smul]

/-- **The prism homotopy in degree three**: for a homogeneous `3`-cocycle `Z` and any map
`ρ : G → G`, the cochain `P(a, b, d) = Z(ρa, a, b, d) / Z(ρa, ρb, b, d) · Z(ρa, ρb, ρd, d)`
satisfies `dP = Z / Z ∘ ρ`; so `V · P` is a primitive of `Z` if `dV = Z ∘ ρ`. -/
theorem prism₃ {Z : G → G → G → G → A}
    (hZ : ∀ a₀ a₁ a₂ a₃ a₄ : G, Z a₁ a₂ a₃ a₄ * Z a₀ a₁ a₃ a₄ * Z a₀ a₁ a₂ a₃ /
      (Z a₀ a₂ a₃ a₄ * Z a₀ a₁ a₂ a₄) = 1) (ρ : G → G) (V : G → G → G → A) {x₀ x₁ x₂ x₃ : G}
    (hV : V x₁ x₂ x₃ * V x₀ x₁ x₃ / (V x₀ x₂ x₃ * V x₀ x₁ x₂) = Z (ρ x₀) (ρ x₁) (ρ x₂) (ρ x₃)) :
    let Y := fun a b d => V a b d * (Z (ρ a) a b d / Z (ρ a) (ρ b) b d * Z (ρ a) (ρ b) (ρ d) d)
    Y x₁ x₂ x₃ * Y x₀ x₁ x₃ / (Y x₀ x₂ x₃ * Y x₀ x₁ x₂) = Z x₀ x₁ x₂ x₃ := by
  intro Y
  simp only [Y]
  generalize ρ x₀ = r₀ at hV ⊢
  generalize ρ x₁ = r₁ at hV ⊢
  generalize ρ x₂ = r₂ at hV ⊢
  generalize ρ x₃ = r₃ at hV ⊢
  have c1 := hZ r₀ x₀ x₁ x₂ x₃
  have c2 := hZ r₀ r₁ x₁ x₂ x₃
  have c3 := hZ r₀ r₁ r₂ x₂ x₃
  have c4 := hZ r₀ r₁ r₂ r₃ x₃
  rw [← div_eq_one]
  calc _ = (V x₁ x₂ x₃ * V x₀ x₁ x₃ / (V x₀ x₂ x₃ * V x₀ x₁ x₂) / Z r₀ r₁ r₂ r₃) *
        (Z x₀ x₁ x₂ x₃ * Z r₀ x₀ x₂ x₃ * Z r₀ x₀ x₁ x₂ / (Z r₀ x₁ x₂ x₃ * Z r₀ x₀ x₁ x₃))⁻¹ *
        (Z r₁ x₁ x₂ x₃ * Z r₀ r₁ x₂ x₃ * Z r₀ r₁ x₁ x₂ / (Z r₀ x₁ x₂ x₃ * Z r₀ r₁ x₁ x₃)) *
        (Z r₁ r₂ x₂ x₃ * Z r₀ r₁ x₂ x₃ * Z r₀ r₁ r₂ x₂ / (Z r₀ r₂ x₂ x₃ * Z r₀ r₁ r₂ x₃))⁻¹ *
        (Z r₁ r₂ r₃ x₃ * Z r₀ r₁ r₃ x₃ * Z r₀ r₁ r₂ r₃ / (Z r₀ r₂ r₃ x₃ * Z r₀ r₁ r₂ x₃)) := by
        mul_abel
    _ = 1 := by rw [c1, c2, c3, c4, div_eq_one.2 hV]; simp

variable [TopologicalSpace G] [DiscreteTopology G]

/-- **Shapiro's lemma in degree three**: `H³(H, A) = 0` implies `H³(G, CoInd H A) = 0`
(cocycle form). -/
theorem h3Trivial (h : H3Trivial H A) : H3Trivial G (CoInd H A) := by
  classical
  intro z _ hz
  let zH : H × H × H → A := fun x => z (x.1, x.2.1, x.2.2) (base H)
  have hzH : IsMulCocycle₃ zH := by
    intro a b c d
    have := congrArg (fun m : CoInd H A => m (base H)) (hz a b c d)
    simp only [mul_apply, smul_apply_base_of_mem a.2] at this
    exact this
  obtain ⟨w, -, hw⟩ := h zH (.of_discrete _) hzH
  let wG : G → G → A := fun a b => if hab : a ∈ H ∧ b ∈ H then w (⟨a, hab.1⟩, ⟨b, hab.2⟩) else 1
  have hwG : ∀ a b c : G, a ∈ H → b ∈ H → c ∈ H →
      z (a, b, c) (base H) = a • wG b c * wG a (b * c) / (wG (a * b) c * wG a b) := by
    intro a b c ha hb hc
    have := congrFun hw (⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩)
    simp only [wG, dif_pos (And.intro ha hb), dif_pos (And.intro hb hc),
      dif_pos (And.intro ha (H.mul_mem hb hc)), dif_pos (And.intro (H.mul_mem ha hb) hc)]
    exact this.symm
  let W : G → G → G → A := fun y₀ y₁ y₂ => y₀ • wG (y₀⁻¹ * y₁) (y₁⁻¹ * y₂)
  have hW : ∀ h ∈ H, ∀ a b d : G, W (h * a) (h * b) (h * d) = h • W a b d := by
    intro h _ a b d
    simp only [W]
    rw [show (h * a)⁻¹ * (h * b) = a⁻¹ * b by group,
      show (h * b)⁻¹ * (h * d) = b⁻¹ * d by group, mul_smul]
  have hZW : ∀ y₀ y₁ y₂ y₃ : G, y₀ ∈ H → y₁ ∈ H → y₂ ∈ H → y₃ ∈ H →
      W y₁ y₂ y₃ * W y₀ y₁ y₃ / (W y₀ y₂ y₃ * W y₀ y₁ y₂) / hom₃ z y₀ y₁ y₂ y₃ = 1 := by
    intro y₀ y₁ y₂ y₃ h0 h1 h2 h3
    rw [div_eq_one, hom₃, smul_apply_base_of_mem h0,
      hwG _ _ _ (H.mul_mem (H.inv_mem h0) h1) (H.mul_mem (H.inv_mem h1) h2)
        (H.mul_mem (H.inv_mem h2) h3)]
    simp only [W, smul_mul', smul_div', ← mul_smul, mul_inv_cancel_left,
      show y₀⁻¹ * y₁ * (y₁⁻¹ * y₂) = y₀⁻¹ * y₂ by group,
      show y₁⁻¹ * y₂ * (y₂⁻¹ * y₃) = y₁⁻¹ * y₃ by group]
  let Y : G → G → G → A := fun x₀ x₁ x₂ => W (retr H x₀) (retr H x₁) (retr H x₂) *
    (hom₃ z (retr H x₀) x₀ x₁ x₂ / hom₃ z (retr H x₀) (retr H x₁) x₁ x₂ *
      hom₃ z (retr H x₀) (retr H x₁) (retr H x₂) x₂)
  have hY : ∀ h ∈ H, ∀ a b d : G, Y (h * a) (h * b) (h * d) = h • Y a b d := by
    intro h hh a b d
    simp only [Y, retr_mul hh, hW _ hh, hom₃_mul z hh, smul_mul', smul_div']
  have hdY : ∀ x₀ x₁ x₂ x₃ : G, Y x₁ x₂ x₃ * Y x₀ x₁ x₃ / (Y x₀ x₂ x₃ * Y x₀ x₁ x₂) =
      hom₃ z x₀ x₁ x₂ x₃ := fun x₀ x₁ x₂ x₃ =>
    prism₃ (hom₃_cocycle hz) (retr H) (fun a b d => W (retr H a) (retr H b) (retr H d))
      (div_eq_one.1 (hZW _ _ _ _ (retr_mem x₀) (retr_mem x₁) (retr_mem x₂) (retr_mem x₃)))
  refine ⟨fun g => lift₃ Y 1 g.1 (g.1 * g.2), .of_discrete _, ?_⟩
  funext ⟨a, b, d⟩
  apply ext
  intro c
  rw [dc2_apply]
  dsimp only
  rw [smul_lift₃ hY, div_apply, mul_apply, mul_apply, lift₃_apply,
    lift₃_apply, lift₃_apply, lift₃_apply, hom₃_rec z a b d c, ← hdY]
  simp only [mul_one, mul_assoc, smul_mul', smul_div']

end Degree3

end CoInd

end ContH2
