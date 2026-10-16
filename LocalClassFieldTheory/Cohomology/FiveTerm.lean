/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.ContH2
import ContinuousKummerTheory.ContH1.Basic

/-!
# The inflation–restriction–transgression five-term exact sequence

Let `G` be a profinite group, `N` a closed normal subgroup and `A` a discrete `G`-module (a
commutative group with the discrete topology and a continuous action). The Hochschild–Serre
five-term exact sequence (Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Prop. 1.6.7;
Serre, *Galois Cohomology*, I.2.6) is

`0 → H¹(G/N, A^N) → H¹(G, A) → H¹(N, A)^{G/N} → H²(G/N, A^N) → H²(G, A)`.

We use the low-degree models of continuous cohomology already in use in the lana-agents projects:
`ContH1` (continuous crossed homomorphisms modulo principal ones, `continuous-kummer-theory`) and
`ContH2` (locally constant 2-cocycles modulo coboundaries of locally constant cochains,
`LocalClassFieldTheory/Brauer/ContH2.lean`); for discrete `A` both are the continuous cohomology.

## Main definitions

* `FiveTerm.fixedPts N A = A^N`, with its actions of `G` and `G ⧸ N`.
* `FiveTerm.inf₁`, `FiveTerm.res₁`, `FiveTerm.inf₂`: inflation and restriction.
* `FiveTerm.conj₁ g`: the action of `g ∈ G` on `H¹(N, A)`, and `FiveTerm.invariants` the
  `G`-invariant (equivalently `G/N`-invariant) classes.
* `FiveTerm.tg : invariants →* H²(G/N, A^N)`, the **transgression**: for a cocycle `f` on `N` with
  invariant class, a locally constant cochain `F` on `G` extending `f` with `F(σn) = F(σ) σf(n)`
  and `F(nσ) = f(n) nF(σ)` (`FiveTerm.Admissible`) exists (by compactness), and `dF` is inflated
  from a 2-cocycle of `G/N` with values in `A^N`.

## Main results

`inf₁_injective`, `ker_res₁_eq_range_inf₁`, `res₁_mem_invariants`, `ker_tg_eq_range_res₁`,
`ker_inf₂_eq_range_tg`: exactness at each term.
-/

open groupCohomology

namespace FiveTerm

section FixedPts

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal] (A : Type*) [CommGroup A]
  [MulDistribMulAction G A]

/-- The fixed points `A^N`. -/
def fixedPts : Subgroup A where
  carrier := {a | ∀ n ∈ N, n • a = a}
  mul_mem' ha hb n hn := by rw [smul_mul', ha n hn, hb n hn]
  one_mem' n _ := smul_one n
  inv_mem' ha n hn := by rw [smul_inv', ha n hn]

variable {N A}

omit [N.Normal] in
theorem mem_fixedPts {a : A} : a ∈ fixedPts N A ↔ ∀ n ∈ N, n • a = a := Iff.rfl

theorem smul_mem_fixedPts (g : G) {a : A} (ha : a ∈ fixedPts N A) : g • a ∈ fixedPts N A := by
  intro n hn
  have hn' : g⁻¹ * n * g ∈ N := by simpa using Subgroup.Normal.conj_mem ‹_› n hn g⁻¹
  rw [← mul_smul, show n * g = g * (g⁻¹ * n * g) by group, mul_smul, ha _ hn']

instance : MulDistribMulAction G (fixedPts N A) where
  smul g a := ⟨g • (a : A), smul_mem_fixedPts g a.2⟩
  one_smul a := Subtype.ext (one_smul G (a : A))
  mul_smul g h a := Subtype.ext (mul_smul g h (a : A))
  smul_mul g a b := Subtype.ext (smul_mul' g (a : A) (b : A))
  smul_one g := Subtype.ext (smul_one g)

@[simp]
theorem coe_smul_fixedPts (g : G) (a : fixedPts N A) : ((g • a : fixedPts N A) : A) = g • (a : A) :=
  rfl

/-- The action of `G ⧸ N` on `A^N`. -/
instance : MulDistribMulAction (G ⧸ N) (fixedPts N A) :=
  MulDistribMulAction.compHom _
    (QuotientGroup.lift N (MulDistribMulAction.toMulAut G (fixedPts N A)) fun n hn => by
      ext a
      exact a.2 n hn)

@[simp]
theorem coe_mk_smul_fixedPts (g : G) (a : fixedPts N A) :
    (((g : G ⧸ N) • a : fixedPts N A) : A) = g • (a : A) := rfl

end FixedPts

section Maps

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G)
  [N.Normal] (A : Type*) [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [IsTopologicalGroup A] [MulDistribMulAction G A]

/-- **Inflation** `H¹(G/N, A^N) → H¹(G, A)`. -/
noncomputable def inf₁ : ContH1 (G ⧸ N) (fixedPts N A) →* ContH1 G A :=
  ContH1.map (QuotientGroup.mk' N) QuotientGroup.continuous_mk (fixedPts N A).subtype
    continuous_subtype_val fun _ _ => rfl

/-- **Restriction** `H¹(G, A) → H¹(N, A)`. -/
noncomputable def res₁ : ContH1 G A →* ContH1 N A :=
  ContH1.map N.subtype continuous_subtype_val (MonoidHom.id A) continuous_id fun _ _ => rfl

/-- **Inflation** `H²(G/N, A^N) → H²(G, A)`. -/
noncomputable def inf₂ : ContH2 (G ⧸ N) (fixedPts N A) →* ContH2 G A :=
  ContH2.map (QuotientGroup.mk' N) QuotientGroup.continuous_mk (fixedPts N A).subtype
    fun _ _ => rfl

variable {N}

/-- Conjugation `n ↦ g⁻¹ n g` on `N`. -/
def conjN (g : G) : N →* N where
  toFun n := ⟨g⁻¹ * n * g, by simpa using Subgroup.Normal.conj_mem ‹N.Normal› (n : G) n.2 g⁻¹⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem coe_conjN (g : G) (n : N) : (conjN g n : G) = g⁻¹ * n * g := rfl

theorem continuous_conjN (g : G) : Continuous (conjN (N := N) g) :=
  Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _

variable (N) in
/-- The action of `g ∈ G` on `H¹(N, A)`: `(g ⋆ c)(n) = g • c(g⁻¹ n g)`. -/
noncomputable def conj₁ (g : G) : ContH1 N A →* ContH1 N A :=
  ContH1.map (conjN g) (continuous_conjN g) (MulDistribMulAction.toMonoidHom A g)
    continuous_of_discreteTopology fun n m => by
      change g • ((g⁻¹ * n * g : G) • m) = (n : G) • g • m
      rw [← mul_smul, ← mul_smul]
      congr 1
      group

variable (N) in
/-- The `G`-invariant classes `H¹(N, A)^{G/N}`. -/
def invariants : Subgroup (ContH1 N A) where
  carrier := {x | ∀ g : G, conj₁ N A g x = x}
  mul_mem' hx hy g := by rw [map_mul, hx g, hy g]
  one_mem' g := map_one _
  inv_mem' hx g := by rw [map_inv, hx g]

/-- The class of `c` is invariant under `g` iff there is a witness `b` with
`g • c(g⁻¹ n g) = c(n) · (n • b / b)`. -/
theorem conj₁_mk_eq_iff (g : G) (c : ContH1.cocycles N A) :
    conj₁ N A g (ContH1.mk c) = ContH1.mk c ↔
      ∃ b : A, ∀ n : N, g • c (conjN g n) = c n * ((n : G) • b / b) := by
  rw [conj₁, ContH1.map_mk, ContH1.mk_eq_mk_iff]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, fun n => ?_⟩
    have := hb n
    simp only [ContH1.cocyclesMap_apply, MulDistribMulAction.toMonoidHom_apply] at this
    change (n : G) • b / b = g • c (conjN g n) / c n at this
    rw [this, mul_div_cancel]
  · rintro ⟨b, hb⟩
    refine ⟨b, fun n => ?_⟩
    simp only [ContH1.cocyclesMap_apply, MulDistribMulAction.toMonoidHom_apply]
    change (n : G) • b / b = g • c (conjN g n) / c n
    rw [hb n, mul_div_cancel_left]

end Maps

section Admissible

variable {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {A : Type*} [CommGroup A]
  [MulDistribMulAction G A]

/-- `F : G → A` extends `f : N → A` and satisfies `F(σn) = F(σ) · σ•f(n)` and
`F(nσ) = f(n) · n•F(σ)` (the cochains used to define the transgression; local constancy is
required separately). -/
structure Admissible (f : N → A) (F : G → A) : Prop where
  ext : ∀ n : N, F n = f n
  right : ∀ (σ : G) (n : N), F (σ * n) = F σ * σ • f n
  left : ∀ (σ : G) (n : N), F (n * σ) = f n * (n : G) • F σ

variable {f : N → A} {F : G → A}

omit [N.Normal] in
theorem Admissible.dx_mul_right (hF : Admissible f F) (σ τ : G) (n : N) :
    ContH2.dx G A F (σ, τ * n) = ContH2.dx G A F (σ, τ) := by
  simp only [ContH2.dx_apply]
  rw [hF.right, ← mul_assoc, hF.right, smul_mul', smul_smul]
  mul_abel

theorem Admissible.dx_mul_left (hF : Admissible f F) (σ τ : G) (n : N) :
    ContH2.dx G A F (σ * n, τ) = ContH2.dx G A F (σ, τ) := by
  have hm : (n : G) * τ = τ * (conjN τ n : G) := by simp only [coe_conjN]; group
  have h1 : (n : G) • F τ = F τ * τ • f (conjN τ n) / f n := by
    have h2 := hF.left τ n
    rw [hm, hF.right] at h2
    rw [h2]
    mul_abel
  have h3 : σ * n * τ = σ * τ * (conjN τ n : G) := by rw [mul_assoc, hm, ← mul_assoc]
  simp only [ContH2.dx_apply]
  rw [h3, hF.right, hF.right, mul_smul, h1, smul_div', smul_mul', smul_smul]
  mul_abel

omit [N.Normal] in
theorem Admissible.dx_one_left (hF : Admissible f F) (n : N) (σ : G) :
    ContH2.dx G A F (n, σ) = 1 := by
  simp only [ContH2.dx_apply]
  rw [hF.left, hF.ext]
  mul_abel

theorem Admissible.smul_dx (hF : Admissible f F) (σ τ : G) (n : N) :
    (n : G) • ContH2.dx G A F (σ, τ) = ContH2.dx G A F (σ, τ) := by
  have hc := ContH2.isMulCocycle₂_dx (G := G) (M := A) F n σ τ
  have hnσ : (n : G) * σ = σ * (conjN σ n : G) := by simp only [coe_conjN]; group
  rw [hF.dx_one_left, hF.dx_one_left, mul_one, mul_one, hnσ, hF.dx_mul_left] at hc
  exact hc.symm

theorem Admissible.dx_mem (hF : Admissible f F) (σ τ : G) :
    ContH2.dx G A F (σ, τ) ∈ fixedPts N A :=
  fun n hn => hF.smul_dx σ τ ⟨n, hn⟩

/-- `dF` is constant on `N`-cosets. -/
theorem Admissible.dx_eq_of_rel (hF : Admissible f F) {σ σ' τ τ' : G} (hσ : σ⁻¹ * σ' ∈ N)
    (hτ : τ⁻¹ * τ' ∈ N) : ContH2.dx G A F (σ, τ) = ContH2.dx G A F (σ', τ') := by
  have e1 : σ' = σ * (⟨σ⁻¹ * σ', hσ⟩ : N) := by simp
  have e2 : τ' = τ * (⟨τ⁻¹ * τ', hτ⟩ : N) := by simp
  rw [e1, e2, hF.dx_mul_left, hF.dx_mul_right]

/-- The descended 2-cochain `G/N × G/N → A^N`. -/
def Admissible.zbar (hF : Admissible f F) : (G ⧸ N) × (G ⧸ N) → fixedPts N A := fun xy =>
  Quotient.lift₂ (s₁ := QuotientGroup.leftRel N) (s₂ := QuotientGroup.leftRel N)
    (fun σ τ => (⟨ContH2.dx G A F (σ, τ), hF.dx_mem σ τ⟩ : fixedPts N A))
    (fun _ _ _ _ h1 h2 => Subtype.ext (hF.dx_eq_of_rel (QuotientGroup.leftRel_apply.mp h1)
      (QuotientGroup.leftRel_apply.mp h2))) xy.1 xy.2

@[simp]
theorem Admissible.zbar_mk (hF : Admissible f F) (σ τ : G) :
    (hF.zbar ((σ : G ⧸ N), (τ : G ⧸ N)) : A) = ContH2.dx G A F (σ, τ) := rfl

theorem Admissible.isMulCocycle₂_zbar (hF : Admissible f F) : IsMulCocycle₂ hF.zbar := by
  intro x y z
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective z
  apply Subtype.ext
  simp only [Subgroup.coe_mul, ← QuotientGroup.mk_mul, Admissible.zbar_mk, coe_mk_smul_fixedPts]
  exact ContH2.isMulCocycle₂_dx F a b c

end Admissible

section Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {N : Subgroup G}
  [N.Normal] {A : Type*} [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [IsTopologicalGroup A] [MulDistribMulAction G A] [ContinuousSMul G A]

omit [IsTopologicalGroup A] [N.Normal] in
theorem continuous_dx {F : G → A} (hF : Continuous F) :
    Continuous (ContH2.dx G A F) := by
  change Continuous (fun gh : G × G => gh.1 • F gh.2 / F (gh.1 * gh.2) * F gh.1)
  exact ((continuous_fst.smul (hF.comp continuous_snd)).div'
    (hF.comp (continuous_fst.mul continuous_snd))).mul (hF.comp continuous_fst)

omit [IsTopologicalGroup A] in
theorem Admissible.isLocallyConstant_zbar {f : N → A} {F : G → A} (hF : Admissible f F)
    (hFc : Continuous F) : IsLocallyConstant hF.zbar := by
  rw [IsLocallyConstant.iff_continuous]
  have hq : Topology.IsQuotientMap (Prod.map (QuotientGroup.mk : G → G ⧸ N)
      (QuotientGroup.mk : G → G ⧸ N)) :=
    IsOpenMap.isQuotientMap ((QuotientGroup.isOpenMap_coe).prodMap QuotientGroup.isOpenMap_coe)
      (QuotientGroup.continuous_mk.prodMap QuotientGroup.continuous_mk)
      (Prod.map_surjective.mpr ⟨QuotientGroup.mk_surjective, QuotientGroup.mk_surjective⟩)
  rw [hq.continuous_iff]
  exact Continuous.subtype_mk (continuous_dx hFc) _

/-- The 2-cocycle of `G/N` with values in `A^N` attached to a continuous admissible cochain. -/
noncomputable def Admissible.zcocycle {f : N → A} {F : G → A} (hF : Admissible f F)
    (hFc : Continuous F) : ContH2.cocycles (G ⧸ N) (fixedPts N A) :=
  ContH2.mkCocycle hF.zbar (hF.isLocallyConstant_zbar hFc) hF.isMulCocycle₂_zbar

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Existence of admissible cochains**: a continuous `1`-cocycle on the closed normal subgroup
`N` whose class is `G`-invariant extends to a continuous admissible cochain on `G`. The proof
chooses an open subgroup `V` on which the cocycle is trivial and under which it is invariant
(tube lemma, `N` compact), and defines `F` on the finitely many cosets of `N V`. -/
theorem exists_admissible (hN : IsClosed (N : Set G)) (c : ContH1.cocycles N A)
    (hc : ∀ g : G, ∃ b : A, ∀ n : N, g • c (conjN g n) = c n * ((n : G) • b / b)) :
    ∃ F : G → A, Continuous F ∧ Admissible (c : N → A) F := by
  classical
  -- `c` is trivial near `1`
  obtain ⟨W1, hW1o, hW1⟩ : ∃ W1 : Set G, IsOpen W1 ∧ Subtype.val ⁻¹' W1 = (c : N → A) ⁻¹' {1} :=
    isOpen_induced_iff.mp ((ContH1.continuous c).isOpen_preimage _ (isOpen_discrete _))
  have h1W1 : (1 : G) ∈ W1 := by
    have : (1 : N) ∈ (c : N → A) ⁻¹' {1} := by simp [ContH1.map_one_eq]
    rw [← hW1] at this
    exact this
  -- `c` is invariant under conjugation by elements near `1`, uniformly (tube lemma)
  haveI : CompactSpace N := isCompact_iff_compactSpace.mp hN.isCompact
  let cj : G × N → N := fun p => conjN p.1 p.2
  have hcj : Continuous cj := Continuous.subtype_mk
    (((continuous_fst.inv).mul (continuous_subtype_val.comp continuous_snd)).mul continuous_fst) _
  let Φ : G × N → A := fun p => p.1 • c (cj p) / c p.2
  have hΦ : Continuous Φ :=
    (continuous_fst.smul ((ContH1.continuous c).comp hcj)).div'
      ((ContH1.continuous c).comp continuous_snd)
  have hS : IsOpen (Φ ⁻¹' {1}) := hΦ.isOpen_preimage _ (isOpen_discrete _)
  have hsub : ({1} : Set G) ×ˢ (Set.univ : Set N) ⊆ Φ ⁻¹' {1} := by
    rintro ⟨g, m⟩ ⟨hg, -⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have : cj (1, m) = m := Subtype.ext (by simp [cj])
    simp [Φ, this]
  obtain ⟨u, v, huo, -, h1u, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hS hsub
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (hW1o.inter huo)
    ⟨h1W1, h1u rfl⟩
  set V : Subgroup G := H.toSubgroup
  have hVo : IsOpen (V : Set G) := H.isOpen'
  have hVb : ∀ x : N, (x : G) ∈ V → c x = 1 := by
    intro x hx
    have : x ∈ Subtype.val ⁻¹' W1 := (hH hx).1
    rw [hW1] at this
    exact this
  have hVc : ∀ w ∈ V, ∀ m : N, w • c (conjN w m) = c m := by
    intro w hw m
    have : Φ (w, m) = 1 := huv ⟨(hH hw).2, hv (Set.mem_univ m)⟩
    exact div_eq_one.mp this
  -- the open subgroup `K = N V` and coset representatives
  set K : Subgroup G := N ⊔ V
  let rep : G ⧸ K → G := fun q => if q = 1 then 1 else q.out
  have hrep : ∀ q, ((rep q : G) : G ⧸ K) = q := by
    intro q
    by_cases hq : q = 1
    · simp [rep, hq]
    · simp [rep, hq]
  have hrep1 : rep 1 = 1 := by simp [rep]
  let wit : G → A := fun g => if g = 1 then 1 else (hc g).choose
  have hwit : ∀ g (n : N), g • c (conjN g n) = c n * ((n : G) • wit g / wit g) := by
    intro g n
    by_cases hg : g = 1
    · subst hg
      have : conjN (1 : G) n = n := Subtype.ext (by simp)
      simp [wit, this]
    · simp only [wit, hg, if_false]
      exact (hc g).choose_spec n
  have hdec : ∀ σ : G, ∃ y : N, ∃ z ∈ V, rep (σ : G ⧸ K) * y * z = σ := by
    intro σ
    have hmem : (rep (σ : G ⧸ K))⁻¹ * σ ∈ K :=
      QuotientGroup.eq.mp ((hrep (σ : G ⧸ K)).trans rfl)
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    refine ⟨⟨y, hy⟩, z, hz, ?_⟩
    rw [mul_assoc, hyz, mul_inv_cancel_left]
  choose y z hz hyz using hdec
  let F : G → A := fun σ => wit (rep (σ : G ⧸ K)) * rep (σ : G ⧸ K) • c (y σ)
  -- independence of the decomposition
  have hind : ∀ (σ : G) (n : N) (v : G), v ∈ V → rep (σ : G ⧸ K) * n * v = σ →
      F σ = wit (rep (σ : G ⧸ K)) * rep (σ : G ⧸ K) • c n := by
    intro σ n v hv hσ
    have h1 : ((n : G))⁻¹ * (y σ : G) = v * (z σ)⁻¹ := by
      have := (hyz σ).trans hσ.symm
      rw [mul_assoc, mul_assoc] at this
      have := mul_left_cancel this
      calc ((n : G))⁻¹ * (y σ : G) = ((n : G))⁻¹ * (y σ * z σ) * (z σ)⁻¹ := by group
        _ = v * (z σ)⁻¹ := by rw [this]; group
    have hmemN : ((n : G))⁻¹ * (y σ : G) ∈ N := N.mul_mem (N.inv_mem n.2) (y σ).2
    have hmemV : ((n : G))⁻¹ * (y σ : G) ∈ V := by rw [h1]; exact V.mul_mem hv (V.inv_mem (hz σ))
    have hy' : y σ = n * ⟨_, hmemN⟩ := Subtype.ext (by simp)
    have hc' : c (y σ) = c n := by
      rw [hy', ContH1.isMulCocycle₁ c, hVb ⟨_, hmemN⟩ hmemV, smul_one, one_mul]
    simp only [F, hc']
  refine ⟨F, ?_, ⟨?_, ?_, ?_⟩⟩
  · -- continuity: `F` is right `V`-invariant
    refine continuous_of_mul_right_invariant V hVo F fun σ v hv => ?_
    have hq : ((σ * v : G) : G ⧸ K) = (σ : G ⧸ K) :=
      (QuotientGroup.eq.mpr (by simpa using Subgroup.mem_sup_right hv)).symm
    have := hind (σ * v) (y σ) (z σ * v) (V.mul_mem (hz σ) hv)
      (by rw [hq, ← mul_assoc, hyz σ])
    rw [this, hq]
  · -- extension
    intro m
    have hq : ((m : G) : G ⧸ K) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left m.2)
    have := hind m m 1 V.one_mem (by rw [hq, hrep1]; simp)
    rw [this, hq, hrep1]
    simp [wit]
  · -- right equivariance
    intro σ m
    have hq : ((σ * m : G) : G ⧸ K) = (σ : G ⧸ K) :=
      (QuotientGroup.eq.mpr (by simpa using Subgroup.mem_sup_left m.2)).symm
    have hw : (z σ : G) * m * (z σ)⁻¹ ∈ N := Subgroup.Normal.conj_mem ‹N.Normal› (m : G) m.2 (z σ)
    let w : N := ⟨_, hw⟩
    have hdec' : (rep (σ : G ⧸ K)) * (y σ * w : N) * z σ = σ * m := by
      simp only [Subgroup.coe_mul, w]
      conv_rhs => rw [← hyz σ]
      group
    rw [hind (σ * m) (y σ * w) (z σ) (hz σ) (by rw [hq]; exact hdec'), hq]
    have hcw : c w = z σ • c m := by
      have h := hVc (z σ) (hz σ) w
      have : conjN (z σ) w = m := Subtype.ext (by simp [w]; group)
      rw [this] at h
      exact h.symm
    rw [ContH1.isMulCocycle₁ c, hcw]
    have e : σ • c m = ((rep (σ : G ⧸ K)) * (y σ : G) * z σ) • c m := by rw [hyz σ]
    simp only [Subgroup.smul_def, smul_mul', smul_smul] at e ⊢
    rw [e]
    simp only [mul_smul]
    simp only [F]
    mul_abel
  · -- left equivariance
    intro σ m
    have hq : (((m : G) * σ : G) : G ⧸ K) = (σ : G ⧸ K) := by
      apply QuotientGroup.eq.mpr
      have : ((m : G) * σ)⁻¹ * σ = σ⁻¹ * ((m : G))⁻¹ * σ := by group
      rw [this]
      exact Subgroup.mem_sup_left
        (by simpa using Subgroup.Normal.conj_mem ‹N.Normal› _ (N.inv_mem m.2) σ⁻¹)
    have hdec' : (rep (σ : G ⧸ K)) * (conjN (rep (σ : G ⧸ K)) m * y σ : N) * z σ = (m : G) * σ := by
      simp only [Subgroup.coe_mul, coe_conjN]
      conv_rhs => rw [← hyz σ]
      group
    rw [hind ((m : G) * σ) (conjN (rep (σ : G ⧸ K)) m * y σ) (z σ) (hz σ)
      (by rw [hq]; exact hdec'), hq]
    rw [ContH1.isMulCocycle₁ c]
    have hw := hwit (rep (σ : G ⧸ K)) m
    have e2 : (rep (σ : G ⧸ K)) * (conjN (rep (σ : G ⧸ K)) m : G) =
        (m : G) * (rep (σ : G ⧸ K)) := by
      simp only [coe_conjN]; group
    simp only [Subgroup.smul_def, smul_mul'] at hw ⊢
    rw [smul_smul, e2, hw, mul_smul]
    simp only [F, smul_mul']
    mul_abel

end Topology

section Admissible'

variable {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {A : Type*} [CommGroup A]
  [MulDistribMulAction G A]

/-- An admissible extension witnesses the invariance of the class of `f`: `b = F(g)`. -/
theorem Admissible.witness {f : N → A} {F : G → A} (hF : Admissible f F) (g : G) (n : N) :
    g • f (conjN g n) = f n * ((n : G) • F g / F g) := by
  have h1 := hF.left g n
  have e : (n : G) * g = g * (conjN g n : G) := by simp only [coe_conjN]; group
  rw [e, hF.right] at h1
  rw [mul_div_assoc', ← h1]
  mul_abel

end Admissible'

section Transgression

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {N : Subgroup G}
  [N.Normal] {A : Type*} [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [IsTopologicalGroup A] [MulDistribMulAction G A] [ContinuousSMul G A]
  [CompactSpace G] [TotallyDisconnectedSpace G]

omit [ContinuousSMul G A] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem witness_of_mem_invariants {c : ContH1.cocycles N A}
    (hx : ContH1.mk c ∈ invariants N A) (g : G) :
    ∃ b : A, ∀ n : N, g • c (conjN g n) = c n * ((n : G) • b / b) :=
  (conj₁_mk_eq_iff A g c).mp (hx g)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Two continuous admissible extensions of cohomologous cocycles give cohomologous `2`-cocycles
of `G/N`. -/
theorem Admissible.mk_zcocycle_eq {c₁ c₂ : ContH1.cocycles N A} (h12 : ContH1.mk c₁ = ContH1.mk c₂)
    {F₁ F₂ : G → A} (hF₁ : Admissible (c₁ : N → A) F₁) (hF₁c : Continuous F₁)
    (hF₂ : Admissible (c₂ : N → A) F₂) (hF₂c : Continuous F₂) :
    ContH2.mk (hF₁.zcocycle hF₁c) = ContH2.mk (hF₂.zcocycle hF₂c) := by
  rw [ContH1.mk_eq_mk_iff] at h12
  obtain ⟨a, ha⟩ := h12
  -- `h = F₁ / (F₂ · d a)` is trivial on `N`, right `N`-invariant and `N`-fixed
  let h : G → A := fun σ => F₁ σ / (F₂ σ * (σ • a / a))
  have hN1 : ∀ n : N, h n = 1 := by
    intro n
    simp only [h, hF₁.ext, hF₂.ext]
    have := ha n
    change (n : G) • a / a = c₁ n / c₂ n at this
    rw [this]
    mul_abel
  have hright : ∀ (σ : G) (n : N), h (σ * n) = h σ := by
    intro σ n
    simp only [h, hF₁.right, hF₂.right, mul_smul]
    have := ha n
    change (n : G) • a / a = c₁ n / c₂ n at this
    have e : σ • c₁ n = σ • c₂ n * σ • ((n : G) • a / a) := by
      rw [this, ← smul_mul']; congr 1; mul_abel
    rw [e, smul_div']
    mul_abel
  have hleft : ∀ (σ : G) (n : N), h ((n : G) * σ) = (n : G) • h σ := by
    intro σ n
    simp only [h, hF₁.left, hF₂.left, mul_smul, smul_div', smul_mul']
    have := ha n
    change (n : G) • a / a = c₁ n / c₂ n at this
    have e : c₁ n = c₂ n * ((n : G) • a / a) := by rw [this]; mul_abel
    rw [e]
    mul_abel
  have hfix : ∀ σ : G, h σ ∈ fixedPts N A := by
    intro σ n hn
    have e : n * σ = σ * (conjN σ ⟨n, hn⟩ : G) := by simp only [coe_conjN]; group
    have := hleft σ ⟨n, hn⟩
    rw [show ((⟨n, hn⟩ : N) : G) = n from rfl, e, hright] at this
    exact this.symm
  let hbar : G ⧸ N → fixedPts N A := Quotient.lift (s := QuotientGroup.leftRel N)
    (fun σ => (⟨h σ, hfix σ⟩ : fixedPts N A)) (fun σ τ hστ => Subtype.ext (by
      have e : τ = σ * (⟨σ⁻¹ * τ, QuotientGroup.leftRel_apply.mp hστ⟩ : N) := by simp
      change h σ = h τ
      rw [e, hright]))
  have hhc : Continuous h := by
    simp only [h]
    exact hF₁c.div' (hF₂c.mul ((continuous_id.smul continuous_const).div' continuous_const))
  have hbarlc : IsLocallyConstant hbar := by
    rw [IsLocallyConstant.iff_continuous]
    rw [(QuotientGroup.isQuotientMap_mk N).continuous_iff]
    exact Continuous.subtype_mk hhc _
  rw [ContH2.mk_eq_mk_iff]
  refine ⟨hbar, hbarlc, ?_⟩
  ext ⟨x, y⟩
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective y
  change (σ : G) • h τ / h (σ * τ) * h σ =
    ContH2.dx G A F₁ (σ, τ) / ContH2.dx G A F₂ (σ, τ)
  simp only [h, ContH2.dx_apply, smul_div', smul_mul', smul_smul]
  mul_abel

variable (hN : IsClosed (N : Set G))

include hN in
/-- The transgression on representatives (see `tg`). -/
noncomputable def tgFun (x : invariants N A) : ContH2 (G ⧸ N) (fixedPts N A) :=
  have hc := ContH1.mk_surjective x.1
  have hF := exists_admissible hN hc.choose
    (witness_of_mem_invariants (by rw [hc.choose_spec]; exact x.2))
  ContH2.mk (hF.choose_spec.2.zcocycle hF.choose_spec.1)

/-- The transgression of `x` may be computed from any representative and any continuous
admissible extension. -/
theorem tgFun_spec (x : invariants N A) {c : ContH1.cocycles N A} (hcx : ContH1.mk c = x.1)
    {F : G → A} (hF : Admissible (c : N → A) F) (hFc : Continuous F) :
    tgFun hN x = ContH2.mk (hF.zcocycle hFc) := by
  unfold tgFun
  exact Admissible.mk_zcocycle_eq ((ContH1.mk_surjective x.1).choose_spec.trans hcx.symm) _ _ hF hFc

omit [IsTopologicalGroup G] [N.Normal] [DiscreteTopology A] [ContinuousSMul G A] [CompactSpace G]
  [TotallyDisconnectedSpace G] in
theorem admissible_one : Admissible ((1 : ContH1.cocycles N A) : N → A) (1 : G → A) :=
  ⟨fun _ => rfl, fun σ n => by simp, fun σ n => by simp⟩

omit [IsTopologicalGroup G] [N.Normal] [DiscreteTopology A] [ContinuousSMul G A] [CompactSpace G]
  [TotallyDisconnectedSpace G] in
theorem Admissible.mul {c₁ c₂ : ContH1.cocycles N A} {F₁ F₂ : G → A}
    (h₁ : Admissible (c₁ : N → A) F₁) (h₂ : Admissible (c₂ : N → A) F₂) :
    Admissible ((c₁ * c₂ : ContH1.cocycles N A) : N → A) (F₁ * F₂) := by
  refine ⟨fun n => ?_, fun σ n => ?_, fun σ n => ?_⟩
  · simp [h₁.ext, h₂.ext]
  · simp only [Pi.mul_apply, h₁.right, h₂.right, ContH1.coe_mul_apply, smul_mul']
    mul_abel
  · simp only [Pi.mul_apply, h₁.left, h₂.left, ContH1.coe_mul_apply, smul_mul']
    mul_abel

include hN in
/-- **The transgression** `tg : H¹(N, A)^{G/N} → H²(G/N, A^N)`. -/
noncomputable def tg : invariants N A →* ContH2 (G ⧸ N) (fixedPts N A) where
  toFun := tgFun hN
  map_one' := by
    rw [tgFun_spec hN 1 (c := 1) (map_one _) admissible_one continuous_const,
      ContH2.mk_eq_one_iff]
    refine ⟨1, IsLocallyConstant.const 1, ?_⟩
    ext ⟨x, y⟩
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective y
    change ((ContH2.dx (G ⧸ N) (fixedPts N A) 1 ((σ : G ⧸ N), (τ : G ⧸ N)) : fixedPts N A) : A) =
      ContH2.dx G A (1 : G → A) (σ, τ)
    simp [ContH2.dx_apply]
  map_mul' x y := by
    obtain ⟨c, hc⟩ := ContH1.mk_surjective x.1
    obtain ⟨d, hd⟩ := ContH1.mk_surjective y.1
    obtain ⟨F₁, hF₁c, hF₁⟩ := exists_admissible hN c (witness_of_mem_invariants (hc ▸ x.2))
    obtain ⟨F₂, hF₂c, hF₂⟩ := exists_admissible hN d (witness_of_mem_invariants (hd ▸ y.2))
    rw [tgFun_spec hN x hc hF₁ hF₁c, tgFun_spec hN y hd hF₂ hF₂c,
      tgFun_spec hN (x * y) (c := c * d) (by rw [map_mul, hc, hd]; rfl) (hF₁.mul hF₂)
        (hF₁c.mul hF₂c), ← map_mul]
    congr 1
    ext ⟨a, b⟩
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective b
    change ContH2.dx G A (F₁ * F₂) (σ, τ) = ContH2.dx G A F₁ (σ, τ) * ContH2.dx G A F₂ (σ, τ)
    rw [ContH2.dx_mul]
    rfl

theorem tg_spec (x : invariants N A) {c : ContH1.cocycles N A} (hcx : ContH1.mk c = x.1)
    {F : G → A} (hF : Admissible (c : N → A) F) (hFc : Continuous F) :
    tg hN x = ContH2.mk (hF.zcocycle hFc) :=
  tgFun_spec hN x hcx hF hFc

/-! ### Exactness -/

omit [IsTopologicalGroup G] [DiscreteTopology A] [ContinuousSMul G A] [CompactSpace G]
  [TotallyDisconnectedSpace G] in
/-- **Exactness at `H¹(G/N, A^N)`**: inflation is injective. -/
theorem inf₁_injective : Function.Injective (inf₁ N A) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  induction x using ContH1.induction_on with
  | h c =>
    rw [inf₁, ContH1.map_mk, ContH1.mk_eq_one_iff] at hx
    obtain ⟨a, ha⟩ := hx
    have hafix : a ∈ fixedPts N A := by
      intro n hn
      have := ha n
      change n • a / a = ((c ((n : G) : G ⧸ N)) : A) at this
      rw [(QuotientGroup.eq_one_iff (n : G)).mpr hn, ContH1.map_one_eq] at this
      exact div_eq_one.mp this
    rw [ContH1.mk_eq_one_iff]
    refine ⟨⟨a, hafix⟩, fun q => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    apply Subtype.ext
    exact ha g

omit [IsTopologicalGroup G] [DiscreteTopology A] [ContinuousSMul G A] [CompactSpace G]
  [TotallyDisconnectedSpace G] in
/-- `res ∘ inf = 1`. -/
theorem res₁_inf₁ (x : ContH1 (G ⧸ N) (fixedPts N A)) : res₁ N A (inf₁ N A x) = 1 := by
  induction x using ContH1.induction_on with
  | h c =>
    rw [inf₁, res₁, ContH1.map_mk, ContH1.map_mk, ContH1.mk_eq_one_iff]
    refine ⟨1, fun n => ?_⟩
    change (n : G) • (1 : A) / 1 = ((c ((n : G) : G ⧸ N)) : A)
    rw [(QuotientGroup.eq_one_iff (n : G)).mpr n.2, ContH1.map_one_eq]
    simp

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- **Exactness at `H¹(G, A)`**: a class restricting to `1` on `N` is inflated from `G/N`. -/
theorem exists_inf₁_eq_of_res₁_eq_one {x : ContH1 G A} (hx : res₁ N A x = 1) :
    ∃ y, inf₁ N A y = x := by
  induction x using ContH1.induction_on with
  | h c =>
    rw [res₁, ContH1.map_mk, ContH1.mk_eq_one_iff] at hx
    obtain ⟨a, ha⟩ := hx
    -- `c' = c / d a` vanishes on `N`
    let c' : G → A := fun g => c g / (g • a / a)
    have hc'N : ∀ n : N, c' n = 1 := by
      intro n
      have := ha n
      change (n : G) • a / a = c n at this
      simp only [c', ← this, div_self']
    have hc'coc : IsMulCocycle₁ c' := by
      intro g h
      simp only [c', ContH1.isMulCocycle₁ c g h, mul_smul, smul_div']
      mul_abel
    have hc'right : ∀ (g : G) (n : N), c' (g * n) = c' g := by
      intro g n
      rw [hc'coc, hc'N, smul_one, one_mul]
    have hc'fix : ∀ g, c' g ∈ fixedPts N A := by
      intro g n hn
      have e : n * g = g * (g⁻¹ * n * g) := by group
      have hm : g⁻¹ * n * g ∈ N := by simpa using Subgroup.Normal.conj_mem ‹N.Normal› n hn g⁻¹
      have h1 := hc'coc n g
      rw [e, hc'right g ⟨_, hm⟩, hc'N ⟨n, hn⟩, mul_one] at h1
      exact h1.symm
    let cbar : G ⧸ N → fixedPts N A := Quotient.lift (s := QuotientGroup.leftRel N)
      (fun g => (⟨c' g, hc'fix g⟩ : fixedPts N A)) (fun g h hgh => Subtype.ext (by
        have e : h = g * (⟨g⁻¹ * h, QuotientGroup.leftRel_apply.mp hgh⟩ : N) := by simp
        change c' g = c' h
        rw [e, hc'right]))
    have hc'c : Continuous c' :=
      (ContH1.continuous c).div' ((continuous_id.smul continuous_const).div' continuous_const)
    have hcbar : Continuous cbar :=
      (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr (Continuous.subtype_mk hc'c _)
    have hcbarcoc : IsMulCocycle₁ cbar := by
      intro p q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective p
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      apply Subtype.ext
      exact hc'coc g h
    refine ⟨ContH1.mk (ContH1.mkCocycle cbar hcbar hcbarcoc), ?_⟩
    rw [inf₁, ContH1.map_mk, ContH1.mk_eq_mk_iff]
    refine ⟨a⁻¹, fun g => ?_⟩
    change g • a⁻¹ / a⁻¹ = c' g / c g
    simp only [c', smul_inv']
    mul_abel

omit [ContinuousSMul G A] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- Restrictions are `G`-invariant. -/
theorem res₁_mem_invariants (x : ContH1 G A) : res₁ N A x ∈ invariants N A := by
  induction x using ContH1.induction_on with
  | h c =>
    intro g
    rw [res₁, ContH1.map_mk, conj₁_mk_eq_iff]
    refine ⟨c g, fun n => ?_⟩
    change g • c (g⁻¹ * n * g) = c n * ((n : G) • c g / c g)
    have h1 := ContH1.isMulCocycle₁ c (n : G) g
    have h2 := ContH1.isMulCocycle₁ c g (g⁻¹ * n * g)
    rw [show g * (g⁻¹ * n * g) = (n : G) * g by group, h1] at h2
    apply mul_right_cancel (b := c g)
    rw [← h2]
    mul_abel

omit [TopologicalSpace G] [IsTopologicalGroup G] [N.Normal] [TopologicalSpace A]
  [DiscreteTopology A] [IsTopologicalGroup A] [ContinuousSMul G A] [CompactSpace G]
  [TotallyDisconnectedSpace G] in
theorem dx_eq_one_iff (F : G → A) (σ τ : G) :
    ContH2.dx G A F (σ, τ) = 1 ↔ F (σ * τ) = σ • F τ * F σ := by
  rw [ContH2.dx_apply, div_mul_eq_mul_div, div_eq_one, eq_comm]

/-- **Exactness at `H¹(N, A)^{G/N}`, first half**: transgressions of restrictions vanish. -/
theorem tg_res₁ (x : ContH1 G A) : tg hN ⟨res₁ N A x, res₁_mem_invariants x⟩ = 1 := by
  induction x using ContH1.induction_on with
  | h c =>
    have hadm : Admissible ((ContH1.cocyclesMap N.subtype continuous_subtype_val
        (MonoidHom.id A) continuous_id (fun _ _ => rfl) c : ContH1.cocycles N A) : N → A)
        (c : G → A) := by
      refine ⟨fun n => rfl, fun σ n => ?_, fun σ n => ?_⟩
      · change c (σ * n) = c σ * σ • c n
        rw [ContH1.isMulCocycle₁ c, mul_comm]
      · change c (n * σ) = c n * (n : G) • c σ
        rw [ContH1.isMulCocycle₁ c, mul_comm]
    rw [tg_spec hN _ (c := ContH1.cocyclesMap N.subtype continuous_subtype_val
        (MonoidHom.id A) continuous_id (fun _ _ => rfl) c) rfl hadm (ContH1.continuous c),
      ContH2.mk_eq_one_iff]
    refine ⟨1, IsLocallyConstant.const 1, ?_⟩
    ext ⟨a, b⟩
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective b
    change ((ContH2.dx (G ⧸ N) (fixedPts N A) 1 ((σ : G ⧸ N), (τ : G ⧸ N)) : fixedPts N A) : A) =
      ContH2.dx G A c (σ, τ)
    rw [(dx_eq_one_iff (c : G → A) σ τ).mpr (ContH1.isMulCocycle₁ c σ τ)]
    simp [ContH2.dx_apply]

/-- **Exactness at `H¹(N, A)^{G/N}`, second half**: an invariant class with trivial transgression
is a restriction. -/
theorem exists_res₁_eq_of_tg_eq_one (x : invariants N A) (hx : tg hN x = 1) :
    ∃ y, res₁ N A y = x.1 := by
  obtain ⟨c, hc⟩ := ContH1.mk_surjective x.1
  obtain ⟨F, hFc, hF⟩ := exists_admissible hN c (witness_of_mem_invariants (hc ▸ x.2))
  rw [tg_spec hN x hc hF hFc, ContH2.mk_eq_one_iff] at hx
  obtain ⟨h, hlc, hh⟩ := hx
  have key : ∀ σ τ : G, ContH2.dx G A F (σ, τ) =
      σ • (h τ : A) / h ((σ : G ⧸ N) * τ) * h σ := by
    intro σ τ
    have := congrArg (fun z : (G ⧸ N) × (G ⧸ N) → fixedPts N A =>
      (z ((σ : G ⧸ N), (τ : G ⧸ N)) : A)) hh
    exact this.symm
  let F' : G → A := fun σ => F σ / (h σ : A)
  have hF'coc : IsMulCocycle₁ F' := by
    intro σ τ
    have hk := key σ τ
    rw [ContH2.dx_apply] at hk
    have e : F' (σ * τ) / (σ • F' τ * F' σ) =
        (σ • (h τ : A) / h ((σ : G ⧸ N) * τ) * h σ) / (σ • F τ / F (σ * τ) * F σ) := by
      simp only [F', smul_div', QuotientGroup.mk_mul]
      mul_abel
    rw [hk, div_self'] at e
    exact div_eq_one.mp e
  have hhc : Continuous (fun σ : G => (h σ : A)) :=
    continuous_subtype_val.comp
      ((IsLocallyConstant.iff_continuous h).mp hlc |>.comp QuotientGroup.continuous_mk)
  have hF'c : Continuous F' := hFc.div' hhc
  have hF1 : F 1 = 1 := by
    have := hF.ext 1
    rw [show ((1 : N) : G) = 1 from rfl] at this
    rw [this]
    exact ContH1.map_one_eq c
  have h1 : (h ((1 : G) : G ⧸ N) : A) = 1 := by
    have hk := key 1 1
    simp only [ContH2.dx_apply, one_smul, mul_one, hF1, QuotientGroup.mk_one, div_self',
      one_mul] at hk
    simpa using hk.symm
  refine ⟨ContH1.mk (ContH1.mkCocycle F' hF'c hF'coc), ?_⟩
  rw [← hc, res₁, ContH1.map_mk]
  congr 1
  ext n
  change F n / (h ((n : G) : G ⧸ N) : A) = c n
  rw [(QuotientGroup.eq_one_iff (n : G)).mpr n.2, hF.ext, ← QuotientGroup.mk_one, h1, div_one]

/-- **Exactness at `H²(G/N, A^N)`, first half**: inflations of transgressions vanish. -/
theorem inf₂_tg (x : invariants N A) : inf₂ N A (tg hN x) = 1 := by
  obtain ⟨c, hc⟩ := ContH1.mk_surjective x.1
  obtain ⟨F, hFc, hF⟩ := exists_admissible hN c (witness_of_mem_invariants (hc ▸ x.2))
  rw [tg_spec hN x hc hF hFc, inf₂, ContH2.map_mk, ContH2.mk_eq_one_iff]
  exact ⟨F, (IsLocallyConstant.iff_continuous F).mpr hFc, rfl⟩

/-- **Exactness at `H²(G/N, A^N)`, second half**: a class inflating to `1` is a transgression. -/
theorem exists_tg_eq_of_inf₂_eq_one {z : ContH2 (G ⧸ N) (fixedPts N A)}
    (hz : inf₂ N A z = 1) : ∃ x, tg hN x = z := by
  induction z using ContH2.induction_on with
  | h z =>
    rw [inf₂, ContH2.map_mk, ContH2.mk_eq_one_iff] at hz
    obtain ⟨F, hFlc, hF⟩ := hz
    have hFz : ∀ σ τ : G, ContH2.dx G A F (σ, τ) = (z ((σ : G ⧸ N), (τ : G ⧸ N)) : A) :=
      fun σ τ => congrFun hF (σ, τ)
    set a : A := (z (1, 1) : A)
    have ha : a ∈ fixedPts N A := (z (1, 1)).2
    have hz1 : ∀ p : G ⧸ N, (z (p, 1) : A) = (p • z (1, 1) : fixedPts N A) := fun p =>
      congrArg Subtype.val (ContH2.map_one_snd z p)
    have hz2 : ∀ p : G ⧸ N, z (1, p) = z (1, 1) := fun p => ContH2.map_one_fst z p
    let F₁ : G → A := fun σ => F σ / a
    have hF₁ : ∀ σ τ : G, ContH2.dx G A F₁ (σ, τ) = (z ((σ : G ⧸ N), (τ : G ⧸ N)) : A) / σ • a := by
      intro σ τ
      have := hFz σ τ
      simp only [ContH2.dx_apply, F₁] at this ⊢
      rw [← this, smul_div']
      mul_abel
    have hF₁c : Continuous F₁ :=
      ((IsLocallyConstant.iff_continuous F).mp hFlc).div' continuous_const
    -- `F₁` is admissible for its restriction to `N`
    have hdN : ∀ (n : N) (σ : G), ContH2.dx G A F₁ ((n : G), σ) = 1 := by
      intro n σ
      rw [hF₁, (QuotientGroup.eq_one_iff (n : G)).mpr n.2, hz2, ha n n.2, div_self']
    have hdN' : ∀ (σ : G) (n : N), ContH2.dx G A F₁ (σ, (n : G)) = 1 := by
      intro σ n
      rw [hF₁, (QuotientGroup.eq_one_iff (n : G)).mpr n.2, hz1]
      simp only [coe_mk_smul_fixedPts]
      exact div_self' _
    let f : N → A := fun n => F₁ n
    have hfcoc : IsMulCocycle₁ f := fun n m =>
      (dx_eq_one_iff F₁ n m).mp (hdN n m)
    have hfc : Continuous f := hF₁c.comp continuous_subtype_val
    let fc : ContH1.cocycles N A := ContH1.mkCocycle f hfc hfcoc
    have hadm : Admissible (fc : N → A) F₁ := by
      refine ⟨fun n => rfl, fun σ n => ?_, fun σ n => ?_⟩
      · rw [(dx_eq_one_iff F₁ σ n).mp (hdN' σ n), mul_comm]; rfl
      · rw [(dx_eq_one_iff F₁ n σ).mp (hdN n σ), mul_comm]; rfl
    have hinv : ContH1.mk fc ∈ invariants N A := fun g =>
      (conj₁_mk_eq_iff A g fc).mpr ⟨F₁ g, fun n => hadm.witness g n⟩
    refine ⟨⟨ContH1.mk fc, hinv⟩, ?_⟩
    rw [tg_spec hN _ rfl hadm hF₁c, ContH2.mk_eq_mk_iff]
    refine ⟨fun _ => ⟨a, ha⟩⁻¹, IsLocallyConstant.const _, ?_⟩
    ext ⟨p, q⟩
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective q
    change ((σ : G ⧸ N) • (⟨a, ha⟩⁻¹ : fixedPts N A) / ⟨a, ha⟩⁻¹ * ⟨a, ha⟩⁻¹ : fixedPts N A) =
      ContH2.dx G A F₁ (σ, τ) / (z ((σ : G ⧸ N), (τ : G ⧸ N)) : A)
    rw [hF₁]
    simp only [Subgroup.coe_mul, Subgroup.coe_div, Subgroup.coe_inv, coe_mk_smul_fixedPts,
      smul_inv']
    mul_abel

end Transgression

end FiveTerm
