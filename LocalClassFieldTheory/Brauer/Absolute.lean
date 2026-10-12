/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.Relative
import ContinuousKummerTheory.Hilbert90
import LocalClassFieldTheory.Reciprocity.OmegaLevel

/-!
# The Brauer group `H²(Gal(Ω/K), Ωˣ)` and inflation from finite levels

Let `Ω/K` be a Galois extension (in applications an algebraic closure). We put
`Brauer.Br K Ω = H²_cont(Gal(Ω/K), Ωˣ)` (`ContH2` with locally constant cochains for the Krull
topology), and for a finite Galois `L ⊆ Ω` we define the inflation map
`Brauer.infl L : Br(L/K) →* Br K Ω`.

## Main results

* `Brauer.isLocallyConstant_smul_units` : `Ωˣ` is a discrete `Gal(Ω/K)`-module.
* `Brauer.isMulCoboundary₁_ker` : continuous Hilbert 90 for `Gal(Ω/L) = ker(Gal(Ω/K) → Gal(L/K))`.
* `Brauer.infl_injective` : inflation `Br(L/K) → Br(K)` is injective.
* `Brauer.inflRel` : inflation `Br(E/K) → Br(E'/K)` for `E ≤ E'`, with
  `Brauer.infl_inflRel : infl E' ∘ inflRel = infl E`; hence `Brauer.inflRel_injective`.
* `Brauer.exists_infl_eq` : every class of `Br K Ω` is inflated from some finite Galois `L ⊆ Ω`,
  i.e. `Br K Ω = ⋃_L Br(L/K)` is the direct limit of the relative Brauer groups.
-/

open ContH2 IntermediateField groupCohomology


/-- A function on a topological group which is invariant under right translation by an open
subgroup is locally constant. -/
theorem isLocallyConstant_of_mul_right_invariant {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) (f : G → X)
    (hf : ∀ g, ∀ u ∈ U, f (g * u) = f g) : IsLocallyConstant f := by
  intro s
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g * x) '' (U : Set G), ?_, ?_, ⟨1, U.one_mem, mul_one g⟩⟩
  · rintro _ ⟨u, hu, rfl⟩
    simpa [Set.mem_preimage, hf g u hu] using hg
  · exact (Homeomorph.mulLeft g).isOpenMap _ hU

open scoped Topology in
/-- A locally constant function on `G × G`, `G` a compact group whose open subgroups form a basis
of neighbourhoods of `1`, is invariant under right translation by `U × U` for an open
subgroup `U`. -/
theorem exists_openSubgroup_prod_invariant {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G]
    (hbasis : ∀ V ∈ 𝓝 (1 : G), ∃ U : Subgroup G, IsOpen (U : Set G) ∧ (U : Set G) ⊆ V)
    (f : G × G → X) (hf : IsLocallyConstant f) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧
      ∀ g h : G, ∀ u ∈ U, ∀ u' ∈ U, f (g * u, h * u') = f (g, h) := by
  classical
  -- for each point `q` an open subgroup `U q` with `f` constant on `q (U q × U q)`
  have hloc : ∀ q : G × G, ∃ U : Subgroup G, IsOpen (U : Set G) ∧
      ∀ u ∈ U, ∀ u' ∈ U, f (q.1 * u, q.2 * u') = f q := by
    intro q
    have hF : f ⁻¹' {f q} ∈ 𝓝 q := (hf.isOpen_fiber (f q)).mem_nhds rfl
    have hc : Continuous fun r : G × G => (q.1 * r.1, q.2 * r.2) := by fun_prop
    have h1 : (fun r : G × G => (q.1 * r.1, q.2 * r.2)) ⁻¹' (f ⁻¹' {f q}) ∈ 𝓝 (1 : G × G) :=
      hc.continuousAt.preimage_mem_nhds (by simpa using hF)
    rw [Prod.one_eq_mk, mem_nhds_prod_iff] at h1
    obtain ⟨V₁, hV₁, V₂, hV₂, hV⟩ := h1
    obtain ⟨U₁, hU₁o, hU₁⟩ := hbasis V₁ hV₁
    obtain ⟨U₂, hU₂o, hU₂⟩ := hbasis V₂ hV₂
    refine ⟨U₁ ⊓ U₂, hU₁o.inter hU₂o, fun u hu u' hu' => ?_⟩
    have := hV (Set.mk_mem_prod (hU₁ hu.1) (hU₂ hu'.2))
    simpa using this
  choose U hUo hU using hloc
  let W : G × G → Set (G × G) := fun q => {r | q.1⁻¹ * r.1 ∈ U q ∧ q.2⁻¹ * r.2 ∈ U q}
  have hWo : ∀ q, IsOpen (W q) := by
    intro q
    have hc1 : Continuous fun r : G × G => q.1⁻¹ * r.1 := by fun_prop
    have hc2 : Continuous fun r : G × G => q.2⁻¹ * r.2 := by fun_prop
    exact (hc1.isOpen_preimage _ (hUo q)).inter (hc2.isOpen_preimage _ (hUo q))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo
    (fun q _ => Set.mem_iUnion.2 ⟨q, by simp [W, (U q).one_mem]⟩)
  refine ⟨⨅ q ∈ t, U q, ?_, ?_⟩
  · have : ((⨅ q ∈ t, U q : Subgroup G) : Set G) = ⋂ q ∈ t, (U q : Set G) := by
      simp [Subgroup.coe_iInf]
    rw [this]
    exact isOpen_biInter_finset fun q _ => hUo q
  · intro g h u hu u' hu'
    obtain ⟨q, hq, hgh⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (g, h)))
    have huq : u ∈ U q := (Subgroup.mem_iInf.1 hu q |> Subgroup.mem_iInf.1) hq
    have hu'q : u' ∈ U q := (Subgroup.mem_iInf.1 hu' q |> Subgroup.mem_iInf.1) hq
    obtain ⟨h1, h2⟩ := hgh
    have e1 := hU q _ h1 _ h2
    have e2 := hU q _ ((U q).mul_mem h1 huq) _ ((U q).mul_mem h2 hu'q)
    simp only [mul_assoc, mul_inv_cancel_left] at e1 e2
    rw [e2, ← e1]

namespace Brauer

variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]

/-- The Brauer group `H²(Gal(Ω/K), Ωˣ)` (locally constant cochains). -/
abbrev Br : Type _ := ContH2 (Ω ≃ₐ[K] Ω) Ωˣ

variable {K Ω}

theorem isLocallyConstant_smul_units [Algebra.IsIntegral K Ω] (u : Ωˣ) :
    IsLocallyConstant fun σ : Ω ≃ₐ[K] Ω => σ • u := by
  refine isLocallyConstant_of_mul_right_invariant (MulAction.stabilizer (Ω ≃ₐ[K] Ω) (u : Ω))
    (stabilizer_isOpen_of_isIntegral (u : Ω)) _ fun σ ν hν => ?_
  have hν' : ν • u = u := Units.ext hν
  simp only [mul_smul, hν']

section Infl

variable (L : IntermediateField K Ω) [Normal K L]

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
theorem units_map_restrictNormalHom_smul (g : Ω ≃ₐ[K] Ω) (u : Lˣ) :
    Units.map (algebraMap L Ω : L →* Ω) (AlgEquiv.restrictNormalHom L g • u) =
      g • Units.map (algebraMap L Ω : L →* Ω) u := by
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, AlgEquiv.smul_units_def]
  exact AlgEquiv.restrictNormalHom_apply L g u

variable [FiniteDimensional K L]

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
/-- Inflation `Br(L/K) = H²(Gal(L/K), Lˣ) → H²(Gal(Ω/K), Ωˣ)`. -/
noncomputable def infl : RelBr K L →* Br K Ω :=
  ContH2.map (AlgEquiv.restrictNormalHom L) (InfiniteGalois.restrictNormalHom_continuous L)
    (Units.map (algebraMap L Ω : L →* Ω)) (units_map_restrictNormalHom_smul L)

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
omit [FiniteDimensional K L] in
theorem infl_mk (f : cocycles (L ≃ₐ[K] L) Lˣ) :
    infl L (mk f) = mk (cocyclesMap (AlgEquiv.restrictNormalHom L)
      (InfiniteGalois.restrictNormalHom_continuous L) (Units.map (algebraMap L Ω : L →* Ω))
      (units_map_restrictNormalHom_smul L) f) := rfl

end Infl

section Hilbert90

variable [IsGalois K Ω]

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
/-- Continuous Hilbert 90 for the kernel `Gal(Ω/L)` of `Gal(Ω/K) → Gal(L/K)`. -/
theorem isMulCoboundary₁_ker (L : IntermediateField K Ω) [Normal K L]
    (c : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker → Ωˣ) (hc : IsLocallyConstant c)
    (hcoc : IsMulCocycle₁ c) : IsMulCoboundary₁ c := by
  have hker : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker ↔
      ∀ x ∈ L, σ x = x := by
    intro σ
    rw [IntermediateField.restrictNormalHom_ker, IntermediateField.mem_fixingSubgroup_iff]
  have hmem : ∀ τ : Ω ≃ₐ[L] Ω,
      τ.restrictScalars K ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker := by
    intro τ
    rw [hker]
    intro x hx
    exact τ.commutes ⟨x, hx⟩
  let ι : (Ω ≃ₐ[L] Ω) → (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker :=
    fun τ => ⟨τ.restrictScalars K, hmem τ⟩
  have hι_mul : ∀ τ₁ τ₂, ι (τ₁ * τ₂) = ι τ₁ * ι τ₂ := fun _ _ => rfl
  have hι_smul : ∀ τ (u : Ωˣ), ι τ • u = τ • u := fun _ _ => rfl
  have hι_surj : ∀ k, ∃ τ, ι τ = k := by
    rintro ⟨k, hk⟩
    rw [hker] at hk
    refine ⟨{ k.toRingEquiv with commutes' := fun x => hk x x.2 }, ?_⟩
    rfl
  let c' : (Ω ≃ₐ[L] Ω) → Ωˣ := fun τ => c (ι τ)
  have hc' : IsMulCocycle₁ c' := by
    intro τ₁ τ₂
    simp only [c', hι_mul]
    rw [hcoc, hι_smul]
  have hc1 : c 1 = 1 := map_one_of_isMulCocycle₁ hcoc
  -- `c'` is trivial on `Gal(Ω/E')` for a finite `E'/L`.
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 (hc.isOpen_fiber (c 1))
  have h1V : (1 : Ω ≃ₐ[K] Ω) ∈ V := by
    have : (1 : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker) ∈
        Subtype.val ⁻¹' V := by rw [hV]; rfl
    exact this
  obtain ⟨E, hE, hEV⟩ := (krullTopology_mem_nhds_one_iff K Ω V).1 (hVo.mem_nhds h1V)
  let b := Module.finBasis K E
  let S : Set Ω := Set.range fun i => (b i : Ω)
  haveI : Finite S := Set.finite_range _ |>.to_subtype
  let E' : IntermediateField L Ω := adjoin L S
  haveI : FiniteDimensional L E' := finiteDimensional_adjoin fun x _ =>
    (Algebra.IsIntegral.isIntegral (R := K) x).tower_top
  have hE' : ∀ τ ∈ E'.fixingSubgroup, c' τ = 1 := by
    intro τ hτ
    have hS : ∀ i, τ (b i : Ω) = b i := fun i =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ _ (subset_adjoin L S ⟨i, rfl⟩)
    have hτE : τ.restrictScalars K ∈ E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      suffices h : ∀ y : E, τ.restrictScalars K (y : Ω) = y from fun x hx => h ⟨x, hx⟩
      intro y
      have key : (y : Ω) = ∑ i, b.repr y i • (b i : Ω) := by
        conv_lhs => rw [← b.sum_repr y]
        simp only [IntermediateField.coe_sum, IntermediateField.coe_smul]
      rw [key, map_sum]
      simp only [map_smul, AlgEquiv.restrictScalars_apply, hS]
    have := hEV hτE
    have h2 : ι τ ∈ Subtype.val ⁻¹' V := this
    rw [hV] at h2
    simpa [c', hc1] using h2
  obtain ⟨m, hm⟩ := KummerTheory.isMulCoboundary₁_of_fixingSubgroup hc' E' hE'
  refine ⟨m, fun k => ?_⟩
  obtain ⟨τ, rfl⟩ := hι_surj k
  rw [hι_smul]
  exact hm τ

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
/-- Inflation `Br(L/K) → Br(K)` is injective. -/
theorem infl_injective (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L] :
    Function.Injective (infl (Ω := Ω) L) := by
  haveI : Algebra.IsIntegral K Ω := inferInstance
  refine ContH2.map_injective _ _ (AlgEquiv.restrictNormalHom_surjective Ω) _ ?_ _ ?_
    isLocallyConstant_smul_units (isMulCoboundary₁_ker L)
  · exact Units.map_injective (algebraMap L Ω).injective
  · intro m hm
    have hmL : (m : Ω) ∈ L := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup L]
      intro σ
      have := hm σ (by rw [IntermediateField.restrictNormalHom_ker]; exact σ.2)
      exact congrArg Units.val this
    refine ⟨Units.mk0 ⟨m, hmL⟩ (by simp [Subtype.ext_iff]), ?_⟩
    ext
    rfl

end Hilbert90

section InflRel

variable {E E' : IntermediateField K Ω} [Normal K E] (h : E ≤ E')

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
theorem units_map_inclusion_resHom_smul (g : E' ≃ₐ[K] E') (u : Eˣ) :
    Units.map (inclusion h : E →* E') (PadicField.resHom h g • u) =
      g • Units.map (inclusion h : E →* E') u := by
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, AlgEquiv.smul_units_def]
  exact PadicField.resHom_apply h g u

variable [FiniteDimensional K E] [FiniteDimensional K E']

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
/-- Inflation `Br(E/K) → Br(E'/K)` for `E ≤ E'` inside `Ω`. -/
noncomputable def inflRel : RelBr K E →* RelBr K E' :=
  ContH2.map (PadicField.resHom h) continuous_of_discreteTopology
    (Units.map (inclusion h : E →* E')) (units_map_inclusion_resHom_smul h)

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
omit [FiniteDimensional K E] [FiniteDimensional K E'] in
theorem resHom_restrictNormalHom [Normal K E'] (g : Ω ≃ₐ[K] Ω) :
    PadicField.resHom h (AlgEquiv.restrictNormalHom E' g) = AlgEquiv.restrictNormalHom E g := by
  rw [PadicField.resHom_eq_iff]
  intro x
  rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
omit [FiniteDimensional K E] in
theorem infl_inflRel [Normal K E'] (α : RelBr K E) : infl E' (inflRel h α) = infl E α := by
  induction α using ContH2.induction_on with | h f => ?_
  simp only [infl, inflRel, map_mk]
  congr 1
  ext ⟨a, b⟩ : 2
  simp only [cocyclesMap_apply, resHom_restrictNormalHom]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
theorem inflRel_injective [IsGalois K Ω] [IsGalois K E] [IsGalois K E'] :
    Function.Injective (inflRel (Ω := Ω) h) := by
  intro α β hαβ
  apply infl_injective E
  rw [← infl_inflRel h, hαβ, infl_inflRel]

end InflRel

section Exhaustion

variable [IsGalois K Ω]

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
theorem exists_fixingSubgroup_invariant (f : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → Ωˣ)
    (hf : IsLocallyConstant f) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ g h : Ω ≃ₐ[K] Ω, ∀ u ∈ E.fixingSubgroup, ∀ u' ∈ E.fixingSubgroup,
        f (g * u, h * u') = f (g, h) := by
  obtain ⟨U, hUo, hU⟩ := exists_openSubgroup_prod_invariant (fun V hV => by
    obtain ⟨E, hE, hEV⟩ := (krullTopology_mem_nhds_one_iff K Ω V).1 hV
    exact ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, hEV⟩) f hf
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω U).1 (hUo.mem_nhds U.one_mem)
  exact ⟨E, hE, fun g h u hu u' hu' => hU g h u (hEU hu) u' (hEU hu')⟩

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
/-- **`Br(K)` is the union of the relative Brauer groups**: every class of `H²(Gal(Ω/K), Ωˣ)`
is inflated from `Br(L/K)` for some finite Galois `L ⊆ Ω`. -/
theorem exists_infl_eq (α : Br K Ω) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (_ : IsGalois K L)
      (β : RelBr K L), infl L β = α := by
  induction α using ContH2.induction_on with | h f => ?_
  classical
  obtain ⟨E, hE, hinv⟩ := exists_fixingSubgroup_invariant f (isLocallyConstant f)
  -- the values of `f`
  have hfin : (Set.range fun q => (f q : Ω)).Finite :=
    ((isLocallyConstant f).range_finite).image (fun u : Ωˣ => (u : Ω)) |>.subset (by
      rintro _ ⟨q, rfl⟩
      exact ⟨f q, ⟨q, rfl⟩, rfl⟩)
  set S := Set.range fun q => (f q : Ω)
  haveI : Finite S := hfin.to_subtype
  haveI : FiniteDimensional K (adjoin K S) :=
    finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral (R := K) x
  set F := E ⊔ adjoin K S
  set L := normalClosure K F Ω
  have hEL : E ≤ L := le_sup_left.trans (le_normalClosure F)
  have hmem : ∀ q, (f q : Ω) ∈ L := fun q =>
    le_normalClosure F (le_sup_right (a := E) (subset_adjoin K S ⟨q, rfl⟩))
  have hfixL : ∀ u ∈ L.fixingSubgroup, u ∈ E.fixingSubgroup :=
    fun u hu => fixingSubgroup_antitone hEL hu
  have hsurj := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := Ω)
  set lift := Function.surjInv hsurj
  have hres : ∀ τ, AlgEquiv.restrictNormalHom L (lift τ) = τ := Function.surjInv_eq hsurj
  have hdep1 : ∀ g g' : Ω ≃ₐ[K] Ω,
      AlgEquiv.restrictNormalHom L g = AlgEquiv.restrictNormalHom L g' →
        g⁻¹ * g' ∈ E.fixingSubgroup := by
    intro g g' hgg'
    apply hfixL
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, hgg',
      inv_mul_cancel]
  have hdep : ∀ g g' h h' : Ω ≃ₐ[K] Ω,
      AlgEquiv.restrictNormalHom L g = AlgEquiv.restrictNormalHom L g' →
      AlgEquiv.restrictNormalHom L h = AlgEquiv.restrictNormalHom L h' → f (g, h) = f (g', h') := by
    intro g g' h h' hg hh
    have := hinv g h _ (hdep1 g g' hg) _ (hdep1 h h' hh)
    simpa only [mul_inv_cancel_left] using this.symm
  -- the descended cocycle on `Gal(L/K)`
  let fL : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ := fun ab =>
    Units.mk0 ⟨f (lift ab.1, lift ab.2), hmem _⟩ (by simp [Subtype.ext_iff])
  have hfLval : ∀ ab, ((fL ab : L) : Ω) = f (lift ab.1, lift ab.2) := fun _ => rfl
  have hfL : IsMulCocycle₂ fL := by
    intro a b c
    apply Units.ext
    apply Subtype.ext
    have hc := isMulCocycle₂ f (lift a) (lift b) (lift c)
    have e1 : f (lift (a * b), lift c) = f (lift a * lift b, lift c) :=
      hdep _ _ _ _ (by rw [map_mul, hres, hres, hres]) rfl
    have e2 : f (lift a, lift (b * c)) = f (lift a, lift b * lift c) :=
      hdep _ _ _ _ rfl (by rw [map_mul, hres, hres, hres])
    have hsmul : (((a • fL (b, c) : Lˣ) : L) : Ω) = ((lift a • f (lift b, lift c) : Ωˣ) : Ω) := by
      rw [smul_units_coe, AlgEquiv.smul_units_def, ← hres a, AlgEquiv.restrictNormalHom_apply,
        hres]
      rfl
    simp only [Units.val_mul, MulMemClass.coe_mul, hsmul, hfLval, e1, e2]
    exact congrArg Units.val hc
  refine ⟨L, inferInstance, inferInstance, mk (mkCocycle fL (.of_discrete _) hfL), ?_⟩
  rw [infl_mk]
  congr 1
  ext ⟨g, h⟩ : 2
  rw [cocyclesMap_apply]
  apply Units.ext
  simp only [Units.coe_map, MonoidHom.coe_coe, coe_mkCocycle]
  exact congrArg Units.val (hdep _ _ _ _ (hres _) (hres _))

end Exhaustion

end Brauer
