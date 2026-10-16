/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Cohomology.FiveTerm

/-!
# Transgression for central extensions

Let `1 → I → E → Δ → 1` be an extension of profinite groups with `I` closed and **central** in
`E`, and let `A` be a discrete abelian group with trivial action (in the applications `A = ℤ/n`).
Then `H¹(I, A) = Hom_cont(I, A)`, every class is `E`-invariant, `A^I = A`, and the five-term
sequence (`LocalClassFieldTheory/Cohomology/FiveTerm.lean`) specialises to

`0 → H¹(Δ, A) → H¹(E, A) → Hom_cont(I, A) → H²(Δ, A) → H²(E, A)`.

The middle map is the **transgression** `FiveTerm.tgCentral : Hom_cont(I, A) → H²(Δ, A)`.
If `s : Δ → E` is a continuous section with `s 1 = 1`, then
`tgCentral φ` is the class of `(x, y) ↦ φ(s(xy)⁻¹ s(x) s(y))⁻¹`, i.e. (up to sign) `φ` applied to
the extension class (`tgCentral_eq_of_section`); and `tgCentral` is natural in `A`
(`tgCentral_comp`).

This is the cohomological input of the synchronisation `I_x ≅ M_X = Hom(H²(Δ_X, Ẑ), Ẑ)` of
[AbsTopIII] Prop. 1.4(ii) (applied to the maximal cuspidally central quotient
`1 → I_x → Δ_{U_x}^{c-cn} → Δ_X → 1`): the differential `d₂ : Hom(I_x, Ẑ/n) → H²(Δ_X, Ẑ/n)` is
`tgCentral` at each level `n`.
-/

open groupCohomology

namespace FiveTerm

variable {E : Type*} [Group E] [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E]
  [TotallyDisconnectedSpace E] {I : Subgroup E} [I.Normal]
  {A : Type*} [CommGroup A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalGroup A]
  [MulDistribMulAction E A] [ContinuousSMul E A]

section Central

variable (hcent : ∀ i ∈ I, ∀ e : E, e * i = i * e) (htriv : ∀ (e : E) (a : A), e • a = a)

include htriv in
/-- A continuous homomorphism `I → A` is a `1`-cocycle for the trivial action. -/
def homCocycle (φ : ContinuousMonoidHom I A) : ContH1.cocycles I A :=
  ContH1.mkCocycle φ φ.continuous fun g h => by
    rw [map_mul, show g • φ h = φ h from htriv (g : E) (φ h), mul_comm]

include htriv in
/-- `Hom_cont(I, A) → H¹(I, A)`. -/
def homH1 : ContinuousMonoidHom I A →* ContH1 I A where
  toFun φ := ContH1.mk (homCocycle htriv φ)
  map_one' := by
    rw [← map_one ContH1.mk]
    congr 1
  map_mul' φ ψ := by
    rw [← map_mul]
    congr 1

omit [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E] [TotallyDisconnectedSpace E] in
include hcent in
theorem conjN_eq (g : E) (n : I) : conjN g n = n :=
  Subtype.ext (by rw [coe_conjN, mul_assoc, ← hcent n n.2 g, inv_mul_cancel_left])

omit [ContinuousSMul E A] [CompactSpace E] [TotallyDisconnectedSpace E] in
include hcent htriv in
/-- For a central `I` and a trivial action every class of `H¹(I, A)` is invariant. -/
theorem mem_invariants (x : ContH1 I A) : x ∈ invariants I A := by
  induction x using ContH1.induction_on with
  | h c =>
    intro g
    rw [conj₁_mk_eq_iff]
    refine ⟨1, fun n => ?_⟩
    rw [conjN_eq hcent, htriv]
    simp

variable (hI : IsClosed (I : Set E))

include hcent hI in
/-- **The transgression of a central extension**, `Hom_cont(I, A) → H²(E/I, A^I)` (here
`A^I = A`). -/
noncomputable def tgCentral : ContinuousMonoidHom I A →* ContH2 (E ⧸ I) (fixedPts I A) :=
  (tg hI).comp ((homH1 htriv).codRestrict (invariants I A) fun _ => mem_invariants hcent htriv _)

omit [IsTopologicalGroup E] [CompactSpace E] [TotallyDisconnectedSpace E] [DiscreteTopology A]
  [ContinuousSMul E A] in
include hcent in
/-- The extension `F(σ) = φ(s(σ̄)⁻¹ σ)` attached to a section. -/
theorem admissible_of_section (φ : ContinuousMonoidHom I A) (s : E ⧸ I → E)
    (hs : ∀ x, (s x : E ⧸ I) = x) (hs1 : s 1 = 1) :
    Admissible ((homCocycle htriv φ : ContH1.cocycles I A) : I → A)
      (fun σ => φ ⟨(s σ)⁻¹ * σ, QuotientGroup.eq.mp (hs _)⟩) := by
  refine ⟨fun n => ?_, fun σ n => ?_, fun σ n => ?_⟩
  · change φ ⟨(s ((n : E) : E ⧸ I))⁻¹ * n, _⟩ = φ n
    congr 1
    apply Subtype.ext
    simp [(QuotientGroup.eq_one_iff (n : E)).mpr n.2, hs1]
  · change φ ⟨(s ((σ * n : E) : E ⧸ I))⁻¹ * (σ * n), _⟩ =
      φ ⟨(s σ)⁻¹ * σ, _⟩ * σ • φ n
    rw [htriv, ← map_mul]
    congr 1
    apply Subtype.ext
    have hq : ((σ * n : E) : E ⧸ I) = (σ : E ⧸ I) :=
      (QuotientGroup.eq.mpr (by simp)).symm
    simp only [hq, Subgroup.coe_mul]
    group
  · change φ ⟨(s (((n : E) * σ : E) : E ⧸ I))⁻¹ * ((n : E) * σ), _⟩ =
      φ n * (n : E) • φ ⟨(s σ)⁻¹ * σ, _⟩
    rw [htriv, ← map_mul]
    congr 1
    apply Subtype.ext
    have hq : (((n : E) * σ : E) : E ⧸ I) = (σ : E ⧸ I) := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (n : E)).mpr n.2, one_mul]
    simp only [hq, Subgroup.coe_mul]
    rw [← mul_assoc, hcent n n.2 ((s σ)⁻¹), mul_assoc]

omit [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E] [TotallyDisconnectedSpace E] in
theorem mem_of_section (s : E ⧸ I → E) (hs : ∀ x, (s x : E ⧸ I) = x) (x y : E ⧸ I) :
    (s (x * y))⁻¹ * s x * s y ∈ I := by
  rw [← QuotientGroup.eq_one_iff]
  simp [hs]

include hcent in
/-- **The transgression via a section**: for a continuous section `s` of `E → E/I` with
`s 1 = 1`, `tgCentral φ` is the class of `(x, y) ↦ φ(s(xy)⁻¹ s(x) s(y))⁻¹`. -/
theorem tgCentral_eq_of_section (φ : ContinuousMonoidHom I A) (s : E ⧸ I → E)
    (hsc : Continuous s) (hs : ∀ x, (s x : E ⧸ I) = x) (hs1 : s 1 = 1)
    (z : ContH2.cocycles (E ⧸ I) (fixedPts I A))
    (hz : ∀ x y, (z (x, y) : A) = (φ ⟨_, mem_of_section s hs x y⟩)⁻¹) :
    tgCentral hcent htriv hI φ = ContH2.mk z := by
  have hF := admissible_of_section hcent htriv φ s hs hs1
  have hFc : Continuous (fun σ : E => φ ⟨(s σ)⁻¹ * σ, QuotientGroup.eq.mp (hs _)⟩) :=
    φ.continuous.comp (Continuous.subtype_mk
      (((hsc.comp QuotientGroup.continuous_mk).inv).mul continuous_id) _)
  rw [tgCentral, MonoidHom.comp_apply, tg_spec hI _ rfl hF hFc]
  congr 1
  ext ⟨x, y⟩
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective y
  rw [hz]
  -- evaluate `dF` at the representatives `s σ̄, s τ̄`
  have hrel : ∀ a : E, (s (a : E ⧸ I))⁻¹ * a ∈ I := fun a => QuotientGroup.eq.mp (hs _)
  show ContH2.dx E A (fun σ : E => φ ⟨(s σ)⁻¹ * σ, QuotientGroup.eq.mp (hs _)⟩) (σ, τ) = _
  rw [hF.dx_eq_of_rel (σ' := s σ) (τ' := s τ)
    (by rw [← QuotientGroup.eq, hs]) (by rw [← QuotientGroup.eq, hs])]
  simp only [ContH2.dx_apply, htriv, hs]
  have h1 : ∀ (a : E ⧸ I) (h : (s a)⁻¹ * s a ∈ I), φ ⟨(s a)⁻¹ * s a, h⟩ = 1 := by
    intro a h
    rw [← map_one φ]
    congr 1
    exact Subtype.ext (by simp)
  rw [h1, h1, mul_one, one_div]
  congr 2
  apply Subtype.ext
  simp [hs, QuotientGroup.mk_mul, mul_assoc]

include htriv in
/-- `A`-valued cocycles on `I` for the trivial action are homomorphisms. -/
def cocycleHom (c : ContH1.cocycles I A) : ContinuousMonoidHom I A where
  toFun := c
  map_one' := ContH1.map_one_eq c
  map_mul' g h := by
    rw [ContH1.isMulCocycle₁ c, show g • c h = c h from htriv (g : E) (c h), mul_comm]
  continuous_toFun := ContH1.continuous c

omit [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E] [TotallyDisconnectedSpace E]
  [DiscreteTopology A] [ContinuousSMul E A] in
/-- Cohomologous cocycles for the trivial action are equal. -/
theorem eq_of_mk_eq_mk {G : Type*} [Group G] [TopologicalSpace G] [MulDistribMulAction G A]
    (htriv' : ∀ (g : G) (a : A), g • a = a) {c d : ContH1.cocycles G A}
    (h : ContH1.mk c = ContH1.mk d) : (c : G → A) = d := by
  rw [ContH1.mk_eq_mk_iff] at h
  obtain ⟨b, hb⟩ := h
  funext g
  have := hb g
  rw [htriv', div_self'] at this
  exact (div_eq_one.mp this.symm)

omit [IsTopologicalGroup E] [CompactSpace E] [TotallyDisconnectedSpace E] [I.Normal]
  [DiscreteTopology A] [ContinuousSMul E A] in
theorem homH1_cocycleHom (c : ContH1.cocycles I A) :
    homH1 htriv (cocycleHom htriv c) = ContH1.mk c := by
  change ContH1.mk (homCocycle htriv (cocycleHom htriv c)) = _
  congr 1

include hcent in
/-- **Exactness at `Hom(I, A)`**: `tgCentral φ = 1` iff `φ` extends to a continuous homomorphism
`E → A`. -/
theorem tgCentral_eq_one_iff (φ : ContinuousMonoidHom I A) :
    tgCentral hcent htriv hI φ = 1 ↔ ∃ χ : ContH1.cocycles E A, ∀ i : I, χ i = φ i := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := exists_res₁_eq_of_tg_eq_one hI _ h
    induction y using ContH1.induction_on with
    | h c =>
      refine ⟨c, fun i => ?_⟩
      have := eq_of_mk_eq_mk (G := I) (fun g a => htriv g a) (c := ContH1.cocyclesMap I.subtype
        continuous_subtype_val (MonoidHom.id A) continuous_id (fun _ _ => rfl) c)
        (d := homCocycle htriv φ) hy
      exact congrFun this i
  · rintro ⟨χ, hχ⟩
    have hres : res₁ I A (ContH1.mk χ) = homH1 htriv φ := by
      rw [res₁, ContH1.map_mk]
      change ContH1.mk _ = ContH1.mk (homCocycle htriv φ)
      congr 1
      apply Subtype.ext
      funext i
      exact hχ i
    have := tg_res₁ hI (ContH1.mk χ)
    rw [tgCentral, MonoidHom.comp_apply]
    convert this using 2
    exact Subtype.ext hres.symm

include hcent in
/-- `inf₂ ∘ tgCentral = 1`. -/
theorem inf₂_tgCentral (φ : ContinuousMonoidHom I A) :
    inf₂ I A (tgCentral hcent htriv hI φ) = 1 :=
  inf₂_tg hI _

include hcent in
/-- **Exactness at `H²(E/I, A)`**: the kernel of inflation is the image of `tgCentral`. -/
theorem exists_tgCentral_eq_of_inf₂_eq_one {z : ContH2 (E ⧸ I) (fixedPts I A)}
    (hz : inf₂ I A z = 1) : ∃ φ, tgCentral hcent htriv hI φ = z := by
  obtain ⟨x, hx⟩ := exists_tg_eq_of_inf₂_eq_one hI hz
  obtain ⟨c, hc⟩ := ContH1.mk_surjective x.1
  refine ⟨cocycleHom htriv c, ?_⟩
  rw [← hx, tgCentral, MonoidHom.comp_apply]
  congr 1
  exact Subtype.ext ((homH1_cocycleHom htriv c).trans hc)

end Central

section Naturality

variable {A' : Type*} [CommGroup A'] [TopologicalSpace A'] [DiscreteTopology A']
  [IsTopologicalGroup A'] [MulDistribMulAction E A'] [ContinuousSMul E A']

/-- The map `A^I → A'^I` induced by an equivariant `ψ : A → A'`. -/
def fixedPtsMap (ψ : A →* A') (hψ : ∀ (e : E) (a : A), ψ (e • a) = e • ψ a) :
    fixedPts I A →* fixedPts I A' where
  toFun a := ⟨ψ (a : A), fun n hn => by rw [← hψ, a.2 n hn]⟩
  map_one' := Subtype.ext (map_one ψ)
  map_mul' a b := Subtype.ext (map_mul ψ (a : A) (b : A))

omit [TopologicalSpace E] [IsTopologicalGroup E] [CompactSpace E] [TotallyDisconnectedSpace E]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalGroup A] [ContinuousSMul E A]
  [TopologicalSpace A'] [DiscreteTopology A'] [IsTopologicalGroup A'] [ContinuousSMul E A'] in
theorem fixedPtsMap_smul (ψ : A →* A') (hψ : ∀ (e : E) (a : A), ψ (e • a) = e • ψ a)
    (g : E ⧸ I) (a : fixedPts I A) :
    fixedPtsMap ψ hψ ((MonoidHom.id (E ⧸ I)) g • a) = g • fixedPtsMap ψ hψ a := by
  induction g using QuotientGroup.induction_on with
  | H σ => exact Subtype.ext (hψ σ a)

variable (hcent : ∀ i ∈ I, ∀ e : E, e * i = i * e) (htriv : ∀ (e : E) (a : A), e • a = a)
  (htriv' : ∀ (e : E) (a : A'), e • a = a) (hI : IsClosed (I : Set E))

include hcent in
/-- **Naturality of the transgression in the coefficients**: `tg(ψ ∘ φ) = ψ_* tg(φ)`. -/
theorem tgCentral_comp (φ : ContinuousMonoidHom I A) (ψ : ContinuousMonoidHom A A') :
    tgCentral hcent htriv' hI (ψ.comp φ) =
      ContH2.map (MonoidHom.id (E ⧸ I)) continuous_id
        (fixedPtsMap (ψ : A →* A') (fun e a => by rw [htriv, htriv'])) (fixedPtsMap_smul _ _)
        (tgCentral hcent htriv hI φ) := by
  obtain ⟨F, hFc, hF⟩ := exists_admissible hI (homCocycle htriv φ)
    (witness_of_mem_invariants (mem_invariants hcent htriv _))
  have hF' : Admissible ((homCocycle htriv' (ψ.comp φ) : ContH1.cocycles I A') : I → A')
      (fun σ => ψ (F σ)) := by
    refine ⟨fun n => ?_, fun σ n => ?_, fun σ n => ?_⟩
    · change ψ (F n) = ψ (φ n)
      rw [hF.ext]; rfl
    · change ψ (F (σ * n)) = ψ (F σ) * σ • ψ (φ n)
      rw [hF.right, map_mul, htriv, htriv']; rfl
    · change ψ (F (n * σ)) = ψ (φ n) * (n : E) • ψ (F σ)
      rw [hF.left, map_mul, htriv, htriv']; rfl
  rw [tgCentral, MonoidHom.comp_apply, tg_spec hI _ rfl hF' (ψ.continuous.comp hFc),
    tgCentral, MonoidHom.comp_apply, tg_spec hI _ rfl hF hFc, ContH2.map_mk]
  congr 1
  ext ⟨x, y⟩
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective y
  change ContH2.dx E A' (fun σ => ψ (F σ)) (σ, τ) = ψ (ContH2.dx E A F (σ, τ))
  simp only [ContH2.dx_apply, map_mul, map_div, htriv, htriv']

end Naturality

end FiveTerm
