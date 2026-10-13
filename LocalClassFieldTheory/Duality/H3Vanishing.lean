/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.Devissage

/-!
# Surjectivity of `H²(B) → H²(C)` from the vanishing of `H³(A)` (cocycle form)

The long exact sequence of `LocalClassFieldTheory.Duality.LongExact` stops at `H²(C)`. Its
continuation `H²(B) → H²(C) → H³(A)` is not available since `H³` is not formalised. Here we
isolate the missing input as an explicit statement about **locally constant `3`-cocycles**,
without defining `H³` as a group:

* `ContH2.dc2 f` : the coboundary `G³ → M` of a `2`-cochain `f : G × G → M`,
  `(a, b, c) ↦ a • f(b, c) · f(a, bc) / (f(ab, c) · f(a, b))`; a `2`-cochain is a cocycle iff
  `dc2 f = 1` (`ContH2.isMulCocycle₂_iff_dc2`);
* `ContH2.IsMulCocycle₃ z` : the multiplicative `3`-cocycle identity, satisfied by every
  `dc2 f` (`ContH2.isMulCocycle₃_dc2`);
* **`ContH2.H3Trivial G A`** : every locally constant `3`-cocycle with values in `A` is the
  coboundary of a locally constant `2`-cochain, i.e. `H³(G, A) = 0` in the model of
  locally constant cochains.

Main results:

* **`Brauer.GShortExact.h2Hom_surjective_of_h3Trivial`** : for a short exact sequence
  `0 → A → B → C → 0` of smooth `G`-modules, `H3Trivial G A` implies that
  `H²(G, B) → H²(G, C)` is surjective (lift a `C`-valued cocycle `c` to `f = s ∘ c`; `dc2 f` is an
  `A`-valued `3`-cocycle, hence `dc2 f = dc2 g`, and `f / g` is a `B`-valued cocycle over `c`);
* `PadicField.LocalH3Vanishing K Ω` : `H3Trivial (Gal(Ω/K)) A` for every finite discrete
  `Gal(Ω/K)`-module `A` (a consequence of `cd(G_K) = 2`, Serre, *Galois cohomology* II.4.3; not
  proved here);
* **`PadicField.eulerCharacteristicFor_of_shortExact_of_h3Trivial`** : the Euler characteristic
  formula is closed under extensions `0 → A → B → C → 0` with `H3Trivial G_K A`;
* `PadicField.eulerCharacteristicFor_of_shortExact_of_h2_subsingleton` : the same, unconditionally,
  when `H²(K, C) = 0`.
-/

open ContH2 groupCohomology

set_option linter.unusedSectionVars false

namespace ContH2

section Cochains

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

/-- The coboundary `(a, b, c) ↦ a • f(b, c) · f(a, bc) / (f(ab, c) · f(a, b))` of a
`2`-cochain. -/
def dc2 (f : G × G → M) : G × G × G → M := fun x =>
  x.1 • f (x.2.1, x.2.2) * f (x.1, x.2.1 * x.2.2) / (f (x.1 * x.2.1, x.2.2) * f (x.1, x.2.1))

@[simp]
theorem dc2_apply (f : G × G → M) (a b c : G) :
    dc2 f (a, b, c) = a • f (b, c) * f (a, b * c) / (f (a * b, c) * f (a, b)) := rfl

/-- The multiplicative `3`-cocycle identity
`a • z(b, c, d) · z(a, bc, d) · z(a, b, c) = z(ab, c, d) · z(a, b, cd)`. -/
def IsMulCocycle₃ (z : G × G × G → M) : Prop :=
  ∀ a b c d : G, a • z (b, c, d) * z (a, b * c, d) * z (a, b, c) =
    z (a * b, c, d) * z (a, b, c * d)

theorem isMulCocycle₂_iff_dc2 (f : G × G → M) :
    IsMulCocycle₂ f ↔ ∀ a b c : G, dc2 f (a, b, c) = 1 := by
  refine ⟨fun h a b c => ?_, fun h a b c => ?_⟩
  · rw [dc2_apply, div_eq_one, ← h a b c]
  · have := h a b c
    rw [dc2_apply, div_eq_one] at this
    exact this.symm

/-- **`d ∘ d = 0`**: coboundaries of `2`-cochains are `3`-cocycles. -/
theorem isMulCocycle₃_dc2 (f : G × G → M) : IsMulCocycle₃ (dc2 f) := by
  intro a b c d
  simp only [dc2_apply, smul_mul', smul_div', smul_smul, mul_assoc]
  mul_abel

theorem dc2_div (f f' : G × G → M) : dc2 (f / f') = dc2 f / dc2 f' := by
  ext ⟨a, b, c⟩
  simp only [dc2_apply, Pi.div_apply, smul_div']
  mul_abel

theorem map_dc2 {N : Type*} [CommGroup N] [MulDistribMulAction G N] (φ : M →* N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (f : G × G → M) (x : G × G × G) :
    φ (dc2 f x) = dc2 (fun y => φ (f y)) x := by
  obtain ⟨a, b, c⟩ := x
  simp only [dc2_apply, map_mul, map_div, hφ]

theorem isMulCocycle₃_comp_of_injective {N : Type*} [CommGroup N] [MulDistribMulAction G N]
    (φ : M →* N) (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) (hinj : Function.Injective φ)
    {z : G × G × G → M} (hz : IsMulCocycle₃ fun x => φ (z x)) : IsMulCocycle₃ z := by
  intro a b c d
  apply hinj
  simp only [map_mul, hφ]
  exact hz a b c d

end Cochains

variable (G A : Type*) [Group G] [TopologicalSpace G] [CommGroup A] [MulDistribMulAction G A]

/-- **`H³(G, A) = 0` in cocycle form**: every locally constant `3`-cocycle `G³ → A` is the
coboundary of a locally constant `2`-cochain. -/
def H3Trivial : Prop :=
  ∀ z : G × G × G → A, IsLocallyConstant z → IsMulCocycle₃ z →
    ∃ f : G × G → A, IsLocallyConstant f ∧ dc2 f = z

end ContH2

namespace Brauer

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Coboundaries of locally constant `2`-cochains with values in a smooth module are locally
constant. -/
theorem isLocallyConstant_dc2 {M : Type*} [CommGroup M] [MulDistribMulAction G M]
    [SmoothAction G M] {f : G × G → M} (hf : IsLocallyConstant f) :
    IsLocallyConstant (dc2 f) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨a, b, c⟩
  have hc : ∀ (φ : G × G × G → G × G), Continuous φ →
      ∀ᶠ x in nhds (a, b, c), f (φ x) = f (φ (a, b, c)) := fun φ hφ =>
    (hφ.continuousAt).eventually ((IsLocallyConstant.iff_eventually_eq f).1 hf _)
  have e1 := hc (fun x => (x.2.1, x.2.2)) (by fun_prop)
  have e2 := hc (fun x => (x.1, x.2.1 * x.2.2)) (by fun_prop)
  have e3 := hc (fun x => (x.1 * x.2.1, x.2.2)) (by fun_prop)
  have e4 := hc (fun x => (x.1, x.2.1)) (by fun_prop)
  have e5 : ∀ᶠ x : G × G × G in nhds (a, b, c), x.1 • f (b, c) = a • f (b, c) :=
    (continuous_fst.continuousAt (x := (a, b, c))).eventually
      ((IsLocallyConstant.iff_eventually_eq _).1 (SmoothAction.isLocallyConstant_smul _) a)
  filter_upwards [e1, e2, e3, e4, e5] with x h1 h2 h3 h4 h5
  obtain ⟨a', b', c'⟩ := x
  simp only at h1 h2 h3 h4 h5
  simp only [dc2_apply, h1, h2, h3, h4, h5]

namespace GShortExact

variable {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]
  [MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]
  [SmoothAction G B] (S : GShortExact G A B C)

/-- **`H³(A) = 0` makes `H²(B) → H²(C)` surjective.** -/
theorem h2Hom_surjective_of_h3Trivial (hA : H3Trivial G A) :
    Function.Surjective (h2Hom (G := G) S.π S.map_smul_π) := by
  intro γ
  induction γ using induction_on with | h c => ?_
  set f : G × G → B := fun x => S.sec (c x) with hf_def
  have hfl : IsLocallyConstant f := (isLocallyConstant c).comp S.sec
  have hπf : ∀ x, S.π (dc2 f x) = 1 := fun x => by
    rw [map_dc2 S.π S.map_smul_π]
    obtain ⟨a, b, d⟩ := x
    have : (fun y => S.π (f y)) = (c : G × G → C) := funext fun y => S.π_sec _
    rw [this]
    exact (isMulCocycle₂_iff_dc2 _).1 (isMulCocycle₂ c) a b d
  set z : G × G × G → A := fun x => S.pre (dc2 f x) with hz_def
  have hiz : ∀ x, S.i (z x) = dc2 f x := fun x => S.i_pre (hπf x)
  have hzl : IsLocallyConstant z := (isLocallyConstant_dc2 hfl).comp S.pre
  have hzc : IsMulCocycle₃ z := isMulCocycle₃_comp_of_injective S.i S.map_smul_i S.injective
    (by simpa only [hiz] using isMulCocycle₃_dc2 f)
  obtain ⟨g, hgl, hgz⟩ := hA z hzl hzc
  set f' : G × G → B := f / fun x => S.i (g x) with hf'_def
  have hdf' : dc2 f' = 1 := by
    rw [hf'_def, dc2_div]
    funext x
    rw [Pi.div_apply, ← map_dc2 S.i S.map_smul_i, hgz, hiz, div_self', Pi.one_apply]
  have hf'c : IsMulCocycle₂ f' :=
    (isMulCocycle₂_iff_dc2 f').2 fun a b d => by rw [hdf', Pi.one_apply]
  refine ⟨ContH2.mk (mkCocycle f' (hfl.div (hgl.comp S.i)) hf'c), ?_⟩
  rw [h2Hom_mk]
  congr 1
  refine cocycles_ext fun a b => ?_
  change S.π (f (a, b) / S.i (g (a, b))) = c (a, b)
  rw [map_div, S.π_i, div_one, hf_def, S.π_sec]

include S in
/-- If `H²(G, A) = 0` and `H²(G, C) = 0` then `H²(G, B) = 0`. -/
theorem h2_subsingleton [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalGroup A]
    [TopologicalSpace B] [DiscreteTopology B] [IsTopologicalGroup B]
    [TopologicalSpace C] [DiscreteTopology C] [IsTopologicalGroup C]
    (hA : Subsingleton (ContH2 G A)) (hC : Subsingleton (ContH2 G C)) :
    Subsingleton (ContH2 G B) := by
  refine subsingleton_of_forall_eq 1 fun β => ?_
  have hβ : β ∈ (h2Hom (G := G) S.π S.map_smul_π).ker := Subsingleton.elim _ _
  rw [S.exact_h2B] at hβ
  obtain ⟨α, rfl⟩ := hβ
  rw [Subsingleton.elim α 1, map_one]

end GShortExact

end Brauer

namespace PadicField

open Brauer

universe u

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

/-- **`H³(K, A) = 0` for finite discrete modules, in cocycle form** (statement only): for every
finite discrete `Gal(Ω/K)`-module `A` (in universe `u`), every locally constant `3`-cocycle with
values in `A` is a coboundary. This is the consequence `H³(K, A) = 0` of `cd(G_K) = 2` (Serre,
*Galois cohomology*, II.4.3) and is **not** proved in this repository; it is the only input
missing for the surjectivity of `H²(K, B) → H²(K, C)` in the dévissage of the Euler
characteristic (`PadicField.eulerCharacteristicFor_of_shortExact_of_localH3Vanishing`). -/
def LocalH3Vanishing : Prop :=
  ∀ (A : Type u) [CommGroup A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) A] [SmoothAction (Ω ≃ₐ[K] Ω) A],
    H3Trivial (Ω ≃ₐ[K] Ω) A

variable {p K Ω}

section Devissage

variable {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C] [Finite A] [Finite B]
  [Finite C] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalGroup A]
  [TopologicalSpace B] [DiscreteTopology B] [IsTopologicalGroup B]
  [TopologicalSpace C] [DiscreteTopology C] [IsTopologicalGroup C]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) A] [MulDistribMulAction (Ω ≃ₐ[K] Ω) B]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) C] [SmoothAction (Ω ≃ₐ[K] Ω) B]

include hp in
/-- **Dévissage for the Euler characteristic, given `H³(K, A) = 0` in cocycle form.** -/
theorem eulerCharacteristicFor_of_shortExact_of_h3Trivial (S : GShortExact (Ω ≃ₐ[K] Ω) A B C)
    (h3 : H3Trivial (Ω ≃ₐ[K] Ω) A) (hA : EulerCharacteristicFor p K Ω A)
    (hC : EulerCharacteristicFor p K Ω C) : EulerCharacteristicFor p K Ω B :=
  eulerCharacteristicFor_of_shortExact S (S.h2Hom_surjective_of_h3Trivial h3) hA hC

include hp in
/-- **Dévissage for the Euler characteristic when `H²(K, C) = 0`** (unconditional). -/
theorem eulerCharacteristicFor_of_shortExact_of_h2_subsingleton
    (S : GShortExact (Ω ≃ₐ[K] Ω) A B C) (hC2 : Subsingleton (ContH2 (Ω ≃ₐ[K] Ω) C))
    (hA : EulerCharacteristicFor p K Ω A) (hC : EulerCharacteristicFor p K Ω C) :
    EulerCharacteristicFor p K Ω B :=
  eulerCharacteristicFor_of_shortExact S (fun _ => ⟨1, Subsingleton.elim _ _⟩) hA hC

include hp in
/-- **The Euler characteristic formula is closed under extensions**, assuming
`PadicField.LocalH3Vanishing` (for modules in the universe of `A`). -/
theorem eulerCharacteristicFor_of_shortExact_of_localH3Vanishing {A : Type u} [CommGroup A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalGroup A]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) A] [SmoothAction (Ω ≃ₐ[K] Ω) A]
    (h3 : LocalH3Vanishing.{u} K Ω) (S : GShortExact (Ω ≃ₐ[K] Ω) A B C)
    (hA : EulerCharacteristicFor p K Ω A) (hC : EulerCharacteristicFor p K Ω C) :
    EulerCharacteristicFor p K Ω B :=
  eulerCharacteristicFor_of_shortExact_of_h3Trivial S (h3 A) hA hC

end Devissage

end PadicField
