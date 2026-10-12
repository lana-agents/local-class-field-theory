/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.BaseChange

/-!
# Compatibility of reciprocity with norms

Let `K' ⊆ Ω` be a finite (not necessarily Galois) extension of `K`. For a cyclic `E/K`, the
compositum `E K'` is cyclic over `K'` (`PadicField.baseChange`), and for `x ∈ K'ˣ`
`cycRec_{K'} (E K') x |_E = cycRec_K E (N_{K'/K} x)` (`PadicField.cycRec_baseChange`).

Proof: both sides are homomorphisms `K'ˣ → Gal(E/K)` trivial on `N_{E K'/K'}`; they agree on the
Neukirch values `N_{Σ/K'} π` of Frobenius lifts `τ` over `K'`, since `τ`, viewed over `K`, is a
Frobenius lift of degree `f(K'/K)` with the same fixed field `Σ`; and these values generate
modulo the norm group.
-/

set_option linter.unusedSectionVars false

open IntermediateField
open scoped IsMulCommutative

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]
variable (K' : IntermediateField K Ω) [FiniteDimensional K K']

/-- The norm `K'ˣ → Kˣ`. -/
noncomputable abbrev normU : K'ˣ →* Kˣ := Units.map (Algebra.norm K : K' →* K)

section BaseChange

variable (E : IntermediateField K Ω)

/-- The compositum `E K'`, as an extension of `K'` (irreducible, to keep unification cheap). -/
noncomputable irreducible_def baseChange : IntermediateField K' Ω :=
  extendScalars (le_sup_right : K' ≤ E ⊔ K')

theorem mem_baseChange {x : Ω} : x ∈ baseChange K' E ↔ x ∈ E ⊔ K' := by
  rw [baseChange_def]; exact Iff.rfl

theorem restrictScalars_baseChange : (baseChange K' E).restrictScalars K = E ⊔ K' := by
  ext x; rw [mem_restrictScalars, mem_baseChange]

theorem le_baseChange : E ≤ (baseChange K' E).restrictScalars K := by
  rw [restrictScalars_baseChange]; exact le_sup_left

theorem le_baseChange' : K' ≤ (baseChange K' E).restrictScalars K := by
  rw [restrictScalars_baseChange]; exact le_sup_right

variable [FiniteDimensional K E]

instance baseChange_finiteDimensional_K : FiniteDimensional K (baseChange K' E) := by
  rw [baseChange_def]
  exact (inferInstance : FiniteDimensional K (E ⊔ K' : IntermediateField K Ω))

instance baseChange_finiteDimensional : FiniteDimensional K' (baseChange K' E) :=
  FiniteDimensional.right K K' (baseChange K' E)

variable [IsGalois K E]

/-- `E K' / K'` is Galois (for any finite `K'/K`). -/
instance baseChange_isGalois : IsGalois K' (baseChange K' E) := by
  obtain ⟨P, hP⟩ := Normal.exists_isSplittingField K E
  have halg : ∀ x ∈ P.rootSet Ω, IsAlgebraic K x := fun x hx ↦ by
    obtain ⟨h1, h2⟩ := Polynomial.mem_rootSet'.1 hx
    exact ⟨P, fun h ↦ h1 (by simp [h]), h2⟩
  have hE : adjoin K (P.rootSet Ω) = E := by
    apply IntermediateField.toSubalgebra_injective
    rw [adjoin_toSubalgebra_of_isAlgebraic halg,
      Polynomial.IsSplittingField.adjoin_rootSet_eq_range E P E.val, IntermediateField.range_val]
  have h1 : (baseChange K' E).restrictScalars K =
      (adjoin K' (P.rootSet Ω)).restrictScalars K := by
    rw [restrictScalars_baseChange, restrictScalars_adjoin_eq_sup, hE, sup_comm]
  have h2 : baseChange K' E = adjoin K' (P.rootSet Ω) := restrictScalars_injective K h1
  have h3 : P.rootSet Ω = (P.map (algebraMap K K')).rootSet Ω := by
    ext x
    rw [Polynomial.mem_rootSet', Polynomial.mem_rootSet', Polynomial.map_map,
      ← IsScalarTower.algebraMap_eq, Polynomial.aeval_map_algebraMap]
  haveI : Polynomial.IsSplittingField K' (adjoin K' (P.rootSet Ω)) (P.map (algebraMap K K')) := by
    rw [h3]
    exact adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI : Normal K' (adjoin K' (P.rootSet Ω)) :=
    Normal.of_isSplittingField (P.map (algebraMap K K'))
  haveI : Algebra.IsSeparable K' (adjoin K' (P.rootSet Ω)) := by
    rw [isSeparable_adjoin_iff_isSeparable]
    intro x hx
    have hxE : x ∈ E := hE ▸ subset_adjoin K _ hx
    exact (IsSeparable.map E.val E.val.injective
      (Algebra.IsSeparable.isSeparable K (⟨x, hxE⟩ : E))).tower_top K'
  rw [h2]
  exact ⟨⟩

section Galois

variable [IsGalois K K']

instance baseChange_isGalois_K : IsGalois K (baseChange K' E) := by
  rw [baseChange_def]
  exact (inferInstance : IsGalois K (E ⊔ K' : IntermediateField K Ω))

instance baseChange_normal_K : Normal K ((baseChange K' E).restrictScalars K) :=
  (inferInstance : Normal K (baseChange K' E))

end Galois

/-- Restriction `Gal(E K'/K') → Gal(E/K)`. -/
noncomputable def resBaseChange :
    (baseChange K' E ≃ₐ[K'] baseChange K' E) →* (E ≃ₐ[K] E) :=
  (resHom (le_baseChange K' E)).comp
    { toFun := fun σ ↦
        (σ.restrictScalars K : (baseChange K' E).restrictScalars K ≃ₐ[K] _)
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }

theorem resBaseChange_apply (σ : baseChange K' E ≃ₐ[K'] baseChange K' E) (y : E) :
    (resBaseChange K' E σ y : Ω) = (σ ⟨y, le_baseChange K' E y.2⟩ : Ω) :=
  resHom_apply _ _ y

theorem resBaseChange_injective : Function.Injective (resBaseChange K' E) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  set F := lift (fixedField (Subgroup.zpowers σ))
  have hEF : E ≤ F.restrictScalars K := fun y hy ↦ by
    change (⟨y, le_baseChange K' E hy⟩ : baseChange K' E).1 ∈ F
    refine (mem_lift _).2 ?_
    have h1 := resBaseChange_apply K' E σ ⟨y, hy⟩
    rw [hσ, AlgEquiv.one_apply] at h1
    rintro ⟨_, i, rfl⟩
    exact zpow_apply_eq_of_apply_eq (Subtype.ext h1.symm) i
  have hK'F : K' ≤ F.restrictScalars K := fun y hy ↦ F.algebraMap_mem ⟨y, hy⟩
  ext a
  have ha : (a : Ω) ∈ F := sup_le hEF hK'F ((mem_baseChange K' E).1 a.2)
  rw [AlgEquiv.one_apply]
  exact congrArg Subtype.val ((mem_lift a).1 ha ⟨σ, Subgroup.mem_zpowers σ⟩)

instance baseChange_isCyclic [IsCyclic (E ≃ₐ[K] E)] :
    IsCyclic (baseChange K' E ≃ₐ[K'] baseChange K' E) :=
  isCyclic_of_injective _ (resBaseChange_injective K' E)

end BaseChange

section Main

variable (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
  [IsCyclic (E ≃ₐ[K] E)]

/-- The fixed field of `τ` over `K'` agrees with the fixed field of `τ` over `K`. -/
noncomputable def fixedFieldEquiv {D : IntermediateField K Ω} (h : K' ≤ D)
    (τ : extendScalars h ≃ₐ[K'] extendScalars h) :
    fixedField (Subgroup.zpowers τ) ≃ₐ[K] fixedField (Subgroup.zpowers (autRestrict K' h τ)) :=
  AlgEquiv.ofBijective
    { toFun := fun a ↦ ⟨a.1, by
        have ha : autRestrict K' h τ a.1 = a.1 := a.2 ⟨τ, Subgroup.mem_zpowers τ⟩
        rintro ⟨_, i, rfl⟩
        exact zpow_apply_eq_of_apply_eq ha i⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
    ⟨fun a b hab ↦ by
        apply Subtype.ext; apply Subtype.ext
        exact congrArg (fun z ↦ ((z.1 : extendScalars h) : Ω)) hab,
      fun b ↦ ⟨⟨b.1, by
        have hb : τ b.1 = b.1 := b.2 ⟨autRestrict K' h τ, Subgroup.mem_zpowers _⟩
        rintro ⟨_, i, rfl⟩
        exact zpow_apply_eq_of_apply_eq hb i⟩, rfl⟩⟩

theorem f_fixedField_autRestrict {D : IntermediateField K Ω} (h : K' ≤ D)
    [FiniteDimensional K D] [FiniteDimensional K' (extendScalars h)]
    (τ : extendScalars h ≃ₐ[K'] extendScalars h) :
    f p K (fixedField (Subgroup.zpowers (autRestrict K' h τ))) =
      f p K K' * f p K' (fixedField (Subgroup.zpowers τ)) := by
  haveI : IsScalarTower ℚ_[p] K (fixedField (Subgroup.zpowers τ)) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply ℚ_[p] K' (fixedField (Subgroup.zpowers τ)),
        IsScalarTower.algebraMap_apply K K' (fixedField (Subgroup.zpowers τ)),
        IsScalarTower.algebraMap_apply ℚ_[p] K K']
  rw [← f_eq_of_algEquiv (fixedFieldEquiv K' h τ), f_mul_f]

theorem v_fixedFieldEquiv {D : IntermediateField K Ω} (h : K' ≤ D)
    [FiniteDimensional K D] [FiniteDimensional K' (extendScalars h)]
    (τ : extendScalars h ≃ₐ[K'] extendScalars h) (a : fixedField (Subgroup.zpowers τ)) :
    v p (fixedFieldEquiv K' h τ a) = v p a := by
  haveI : IsScalarTower ℚ_[p] K (fixedField (Subgroup.zpowers τ)) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply ℚ_[p] K' (fixedField (Subgroup.zpowers τ)),
        IsScalarTower.algebraMap_apply K K' (fixedField (Subgroup.zpowers τ)),
        IsScalarTower.algebraMap_apply ℚ_[p] K K']
  exact v_algEquiv _ a

theorem norm_fixedFieldEquiv {D : IntermediateField K Ω} (h : K' ≤ D)
    [FiniteDimensional K D] [FiniteDimensional K' (extendScalars h)]
    (τ : extendScalars h ≃ₐ[K'] extendScalars h) (a : fixedField (Subgroup.zpowers τ)) :
    Algebra.norm K (fixedFieldEquiv K' h τ a) = Algebra.norm K (Algebra.norm K' a) := by
  haveI : Module.Free K' (fixedField (Subgroup.zpowers τ)) := Module.Free.of_divisionRing _ _
  rw [Algebra.norm_eq_of_algEquiv, Algebra.norm_norm]

/-- Norms from `E K'` to `K'` have norms to `K` in `N_{E/K} Eˣ`. -/
theorem normU_mem_normGroup (z : K'ˣ) (hz : z ∈ normGroup K' (baseChange K' E)) :
    normU K' z ∈ normGroup K E := by
  haveI : Module.Free K' (baseChange K' E) := Module.Free.of_divisionRing _ _
  obtain ⟨w, hw⟩ := (mem_normGroup_iff).1 hz
  let ι : E →ₐ[K] baseChange K' E :=
    { toFun := fun y ↦ ⟨y, le_baseChange K' E y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  refine normGroup_le_of_algHom ι ((mem_normGroup_iff).2 ⟨w, ?_⟩)
  change Algebra.norm K ((w : baseChange K' E)) = Algebra.norm K (z : K')
  rw [← hw, Algebra.norm_norm]

/-- Neukirch values of Frobenius lifts over `K'` (auxiliary for `cycRec_baseChange`). -/
theorem exists_norm_frobLift_baseChange {D : IntermediateField K Ω} [FiniteDimensional K D]
    [IsGalois K D] (hK'D : K' ≤ D) (hED : E ≤ D)
    (hfin : FiniteDimensional K' (extendScalars hK'D)) (hgal : IsGalois K' (extendScalars hK'D))
    {s : ℕ} (hs : 0 < s) (hsdef : f p K' (extendScalars hK'D) = s)
    (hKs : unramifiedOfDegree p K' Ω s ≤ extendScalars hK'D)
    (hdeg₁ : cycDeg p (baseChange K' E) ∣ s)
    (hdeg : cycDegPow p E (f p K K') f_pos ∣ f p K K' * s)
    (τ₁ : extendScalars hK'D ≃ₐ[K'] extendScalars hK'D) (hτ₁ : resHom hKs τ₁ = frobT p K' Ω s) :
    ∃ y : K'ˣ, cycRec p (baseChange K' E) y =
        resHom (fun _ hy ↦ (sup_le hED hK'D : E ⊔ K' ≤ D) ((mem_baseChange K' E).1 hy) :
          baseChange K' E ≤ _) τ₁ ∧
      cycRec p E (normU K' y) = resBaseChange K' E (cycRec p (baseChange K' E) y) := by
  have hE₁D₁ : baseChange K' E ≤ extendScalars hK'D :=
    fun y hy ↦ (sup_le hED hK'D : E ⊔ K' ≤ D) ((mem_baseChange K' E).1 hy)
  have h3 : ∀ τ : extendScalars hK'D ≃ₐ[K'] extendScalars hK'D,
      resHom hED (autRestrict K' hK'D τ) = resBaseChange K' E (resHom hE₁D₁ τ) := by
    intro τ
    ext z
    rw [resBaseChange_apply, resHom_apply, resHom_apply]
    rfl
  haveI := hfin
  haveI := hgal
  set f' := f p K K'
  have hf' : 0 < f' := f_pos
  have hKfsD : unramifiedOfDegree p K Ω (f' * s) ≤ D := fun y hy ↦
    hKs (unramifiedOfDegree_le_baseChange K' hs hy)
  have hf₁ := f_fixedField_frobLift hs hsdef hKs τ₁ hτ₁
  set Fx := fixedField (Subgroup.zpowers τ₁)
  haveI : Module.Free K' Fx := Module.Free.of_divisionRing _ _
  have hπ := uniformizer_spec (p := p) (K := Fx)
  have hπ0 : Algebra.norm K' (uniformizer p Fx) ≠ 0 := Algebra.norm_ne_zero_iff.2 hπ.ne_zero
  have h1 := @cycRec_norm_frobLift p _ K' _ _ _ Ω _ _ _ _ _ (baseChange K' E)
    (baseChange_finiteDimensional K' E) (baseChange_isGalois K' E) (baseChange_isCyclic K' E)
    s hs hdeg₁ _ hfin hgal hE₁D₁ hKs τ₁ hτ₁ hf₁ _ hπ hπ0
  refine ⟨Units.mk0 _ hπ0, h1, ?_⟩
  -- over `K`
  have hτK : resHom hKfsD (autRestrict K' hK'D τ₁) = frobT p K Ω (f' * s) ^ f' :=
    resHom_frob_baseChange K' hK'D hs hKs hKfsD τ₁ hτ₁
  have hfK : f p K (fixedField (Subgroup.zpowers (autRestrict K' hK'D τ₁))) = f' := by
    rw [f_fixedField_autRestrict K' hK'D τ₁, hf₁, mul_one]
  have hπ' : v p (fixedFieldEquiv K' hK'D τ₁ (uniformizer p Fx)) = 1 := by
    rw [v_fixedFieldEquiv]; exact hπ
  have hNπ' : Algebra.norm K (fixedFieldEquiv K' hK'D τ₁ (uniformizer p Fx)) =
      Algebra.norm K (Algebra.norm K' (uniformizer p Fx)) := by
    rw [norm_fixedFieldEquiv]
  have h2 := cycRec_norm_frobLift_pow' E hf' (Nat.mul_pos hf' hs) hdeg D hED hKfsD _ hτK hfK _
    hπ' (normU K' (Units.mk0 _ hπ0)) hNπ'.symm
  exact h2.trans ((h3 τ₁).trans (congrArg (resBaseChange K' E) h1.symm))

set_option maxHeartbeats 1000000 in
-- The proof unifies reciprocity maps over the bases `K` and `K'`, whose definitions are expensive
-- to unfold; this exceeds the default heartbeat limit.
/-- **Norm compatibility of the cyclic reciprocity maps**: for `x ∈ K'ˣ`,
`cycRec_{K'} (E K') x |_E = cycRec_K E (N_{K'/K} x)`. -/
theorem cycRec_baseChange (x : K'ˣ) :
    resBaseChange K' E (cycRec p (baseChange K' E) x) = cycRec p E (normU K' x) := by
  classical
  set f' := f p K K'
  have hf' : 0 < f' := f_pos
  obtain ⟨φ, hφ⟩ : ∃ φ : K'ˣ →* (E ≃ₐ[K] E),
      φ = (resBaseChange K' E).comp (cycRec p (baseChange K' E)) := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : K'ˣ →* (E ≃ₐ[K] E), ψ = (cycRec p E).comp (normU K') := ⟨_, rfl⟩
  suffices hφψ : φ = ψ by
    have := DFunLike.congr_fun hφψ x
    rw [hφ, hψ] at this
    exact this
  haveI : Module.Free K' (baseChange K' E) := Module.Free.of_divisionRing _ _
  have hN₁ := @cycRec_norm_frobLift p _ K' _ _ _ Ω _ _ _ _ _ (baseChange K' E) _ _ _
  have hker₁ := cycRec_eq_one_iff (p := p) (K := K') (Ω := Ω) (baseChange K' E)
  have hcyc₁ := cycDeg_pos (p := p) (K := K') (Ω := Ω) (baseChange K' E)
  -- the Frobenius-lift data
  set s₀ := cycDeg p (baseChange K' E) * cycDegPow p E f' hf'
  have hs₀ : 0 < s₀ := Nat.mul_pos hcyc₁ (StdLevel.pos _)
  obtain ⟨K'', hK''fin, hK''gal, hK'K''⟩ := exists_isGalois_le (p := p) K'
  obtain ⟨D, hDdef⟩ : ∃ D, D = E ⊔ (K'' ⊔ unramifiedOfDegree p K Ω (f' * s₀)) := ⟨_, rfl⟩
  haveI : FiniteDimensional K D := hDdef ▸ inferInstance
  haveI : IsGalois K D := hDdef ▸ inferInstance
  have hK'D : K' ≤ D := hK'K''.trans (hDdef ▸ le_sup_left.trans le_sup_right)
  have hED : E ≤ D := hDdef ▸ le_sup_left
  haveI : FiniteDimensional K (extendScalars hK'D) := (inferInstance : FiniteDimensional K D)
  haveI : FiniteDimensional K' (extendScalars hK'D) :=
    FiniteDimensional.right K K' (extendScalars hK'D)
  haveI : IsGalois K (extendScalars hK'D) := (inferInstance : IsGalois K D)
  haveI : IsGalois K' (extendScalars hK'D) :=
    IsGalois.tower_top_of_isGalois K K' (extendScalars hK'D)
  obtain ⟨s, hsdef⟩ : ∃ s, s = f p K' (extendScalars hK'D) := ⟨_, rfl⟩
  have hs : 0 < s := hsdef ▸ f_pos
  have hKs : unramifiedOfDegree p K' Ω s ≤ extendScalars hK'D :=
    unramifiedOfDegree_le_of_f_eq (extendScalars hK'D) hsdef.symm
  have hs₀s : s₀ ∣ s := by
    have h1 : unramifiedOfDegree p K' Ω s₀ ≤ (extendScalars hK'D) := by
      intro y hy
      have : y ∈ (unramifiedOfDegree p K' Ω s₀).restrictScalars K := hy
      rw [restrictScalars_unramifiedOfDegree K' hs₀] at this
      change y ∈ D
      rw [hDdef]
      exact (sup_le_sup_right hK'K'' _ |>.trans
        (le_sup_right : K'' ⊔ unramifiedOfDegree p K Ω (f' * s₀) ≤ _)) this
    have := f_dvd_f_of_le (p := p) h1
    rwa [(isUnramified_unramifiedOfDegree p K' Ω s₀).f_eq,
      finrank_unramifiedOfDegree p K' Ω hs₀, ← hsdef] at this
  have hE₁D₁ : baseChange K' E ≤ (extendScalars hK'D) := fun y hy ↦
    (sup_le hED hK'D : E ⊔ K' ≤ D) ((mem_baseChange K' E).1 hy)
  have hKfsD : unramifiedOfDegree p K Ω (f' * s) ≤ D := fun y hy ↦
    hKs (unramifiedOfDegree_le_baseChange K' hs hy)
  have key : ∀ τ₁ : extendScalars hK'D ≃ₐ[K'] extendScalars hK'D,
      resHom hKs τ₁ = frobT p K' Ω s →
      ∃ y : K'ˣ, cycRec p (baseChange K' E) y = resHom hE₁D₁ τ₁ ∧ ψ y = φ y := by
    intro τ₁ hτ₁
    obtain ⟨y, h1, h2⟩ := exists_norm_frobLift_baseChange K' E hK'D hED inferInstance
      inferInstance hs hsdef.symm hKs
      ((dvd_mul_right _ _).trans hs₀s) ((dvd_mul_left _ _).trans (hs₀s.trans (dvd_mul_left _ _)))
      τ₁ hτ₁
    refine ⟨y, h1, ?_⟩
    subst hφ hψ
    exact h2
  -- the subgroup where `φ` and `ψ` agree
  have hker : (cycRec p (baseChange K' E)).ker ≤ MonoidHom.eqLocus φ ψ := by
    intro z hz
    rw [MonoidHom.mem_ker, hker₁] at hz
    subst hφ hψ
    change resBaseChange K' E (cycRec p (baseChange K' E) z) = cycRec p E (normU K' z)
    exact (congrArg (resBaseChange K' E) ((hker₁ z).2 hz)).trans ((map_one _).trans
      ((cycRec_eq_one_iff E _).2 (normU_mem_normGroup K' E z hz)).symm)
  -- the Frobenius lifts generate
  have hrange : ∀ σ : baseChange K' E ≃ₐ[K'] baseChange K' E,
      ∃ h ∈ MonoidHom.eqLocus φ ψ, cycRec p (baseChange K' E) h = σ := by
    intro σ
    obtain ⟨φ₀, hφ₀⟩ := resHom_surjective hKs (frobT p K' Ω s)
    obtain ⟨g, rfl⟩ := resHom_surjective hE₁D₁ σ
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
      ((zpowers_frob (isUnramified_unramifiedOfDegree p K' Ω s)).symm ▸ Subgroup.mem_top
        (resHom hKs g))
    obtain ⟨a, ha⟩ : ∃ a, a = g * φ₀ ^ (-j) * φ₀ := ⟨_, rfl⟩
    have h1 : resHom hKs a = frobT p K' Ω s := by
      rw [ha, map_mul, map_mul, map_zpow, hφ₀, ← hj, zpow_neg, mul_inv_cancel, one_mul]
    have hg : g = a * φ₀⁻¹ * φ₀ ^ j := by
      rw [ha, mul_inv_cancel_right, zpow_neg, inv_mul_cancel_right]
    obtain ⟨ya, hya, hya'⟩ := key a h1
    obtain ⟨yφ, hyφ, hyφ'⟩ := key φ₀ hφ₀
    refine ⟨ya * yφ⁻¹ * yφ ^ j, ?_, ?_⟩
    · exact mul_mem (mul_mem hya'.symm (inv_mem hyφ'.symm)) (zpow_mem hyφ'.symm j)
    · rw [map_mul, map_mul, map_inv, map_zpow, hya, hyφ, hg, map_mul, map_mul, map_inv, map_zpow]
  refine MonoidHom.ext fun z ↦ ?_
  obtain ⟨h, hH, hh⟩ := hrange (cycRec p (baseChange K' E) z)
  have hzh : z * h⁻¹ ∈ (cycRec p (baseChange K' E)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hh, mul_inv_cancel]
  have := mul_mem (hker hzh) hH
  rw [inv_mul_cancel_right] at this
  exact this

end Main

section Abelian

variable (L : IntermediateField K Ω) [FiniteDimensional K L]
  [IsAbelianGalois K L]

instance baseChange_isAbelianGalois : IsAbelianGalois K' (baseChange K' L) where
  is_comm := ⟨fun σ τ ↦ resBaseChange_injective K' L (by
    rw [map_mul, map_mul, mul_comm])⟩

theorem baseChange_mono {E : IntermediateField K Ω} (h : E ≤ L) :
    baseChange K' E ≤ baseChange K' L :=
  fun _ hy ↦ (mem_baseChange K' L).2 (sup_le_sup_right h K' ((mem_baseChange K' E).1 hy))

/-- **Norm compatibility of the local reciprocity maps**: for finite abelian `L/K` and `x ∈ K'ˣ`,
`abRec_{K'} (L K') x |_L = abRec_K L (N_{K'/K} x)`. -/
theorem abRec_baseChange (x : K'ˣ) :
    resBaseChange K' L (abRec p (baseChange K' L) x) = abRec p L (normU K' x) := by
  rw [eq_abRec_iff (p := p)]
  intro E
  have hE := baseChange_mono K' L E.2.1
  have h1 := resHom_abRec (p := p) (baseChange K' L) (baseChange K' E.1) hE x
  have h2 := cycRec_baseChange (p := p) K' E.1 x
  rw [← h2, ← h1]
  rw [resHom_eq_iff]
  intro y
  rw [resBaseChange_apply, resBaseChange_apply, resHom_apply]
  rfl

end Abelian

section Artin

theorem maxAbelian_le_baseChange : maxAbelian K Ω ≤ (maxAbelian K' Ω).restrictScalars K := by
  intro y hy
  obtain ⟨L, hyL⟩ := mem_maxAbelian_iff.1 hy
  exact le_maxAbelian ⟨baseChange K' L.1, inferInstance, inferInstance⟩
    (le_baseChange K' L.1 hyL)

/-- **Norm compatibility of the Artin map** for a finite `K'/K`:
`artin_{K'}(x)|_{K^ab} = artin_K(N_{K'/K} x)`. -/
theorem artin_baseChange (x : K'ˣ) (y : maxAbelian K Ω) :
    (artin p K' Ω x ⟨y, maxAbelian_le_baseChange K' y.2⟩ : Ω) =
      (artin p K Ω (normU K' x) y : Ω) := by
  obtain ⟨L, hyL⟩ := mem_maxAbelian_iff.1 y.2
  have h1 := artin_apply (p := p) x (baseChange K' L.1) y (le_baseChange K' L.1 hyL)
  have h2 := artin_apply (p := p) (normU K' x) L.1 y hyL
  rw [h1]
  change _ = ((artin p K Ω (normU K' x) ⟨y, _⟩ : maxAbelian K Ω) : Ω)
  rw [h2, ← abRec_baseChange, resBaseChange_apply]

end Artin

end PadicField
