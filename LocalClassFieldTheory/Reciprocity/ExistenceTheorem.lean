/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.NormLimitation
import LocalClassFieldTheory.Reciprocity.Kummer

/-!
# The existence theorem

* `PadicField.exists_abelian_closure`: for finite Galois `K₁/K` and finite abelian `E/K₁`, there
  is a finite abelian `L ⊇ E` over `K₁` which is Galois over `K`;
* `PadicField.exists_abFin_pow_of_cyclic`: if `K₁/K` is cyclic and `(K₁ˣ)ⁿ` contains a norm
  group, then so does `(Kˣ)ⁿ` (norm limitation, `PadicField.exists_abFin_le_norm`);
* `PadicField.existence`: every subgroup of finite index of `Kˣ` is a norm group;
* `PadicField.le_iff_normGroup_le`, `PadicField.existsUnique_normGroup_eq`: `L ↦ N_{L/K} Lˣ` is an
  order-reversing bijection onto the subgroups of finite index.
-/

set_option linter.unusedSectionVars false

open IntermediateField Polynomial
open scoped commutatorElement

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

section Closure

variable (K₁ : IntermediateField K Ω) [FiniteDimensional K K₁] [IsGalois K K₁]
variable (E : IntermediateField K₁ Ω) [FiniteDimensional K₁ E] [IsAbelianGalois K₁ E]

include hp in
/-- For finite Galois `K₁/K` and finite abelian `E/K₁`, there is a finite abelian `L ⊇ E` over
`K₁` which is Galois over `K`. -/
theorem exists_abelian_closure :
    ∃ L : IntermediateField K₁ Ω, E ≤ L ∧ FiniteDimensional K₁ L ∧ IsAbelianGalois K₁ L ∧
      Normal K (L.restrictScalars K) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  haveI : FiniteDimensional K (E.restrictScalars K) :=
    (FiniteDimensional.trans K K₁ E : FiniteDimensional K E)
  obtain ⟨D, hDfin, hDgal, hED⟩ := exists_isGalois_le (p := p) (E.restrictScalars K)
  have hK₁D : K₁ ≤ D := (le_restrictScalars K₁ E).trans hED
  obtain ⟨A, hA⟩ : ∃ A, A = (resHom hK₁D).ker := ⟨_, rfl⟩
  haveI : A.Normal := hA ▸ MonoidHom.normal_ker _
  have hfixA : ∀ a ∈ A, ∀ x : K₁, (a ⟨x, hK₁D x.2⟩ : Ω) = x := by
    intro a ha x
    rw [hA, MonoidHom.mem_ker] at ha
    have := resHom_apply hK₁D a x
    rw [ha, AlgEquiv.one_apply] at this
    exact this.symm
  obtain ⟨H, hH⟩ : ∃ H, H = ⁅A, A⁆ := ⟨_, rfl⟩
  haveI : H.Normal := hH ▸ inferInstance
  have hHA : H ≤ A := hH ▸ Subgroup.commutator_le_left A A
  set LK := lift (fixedField H)
  let εL : fixedField H ≃ₐ[K] LK := liftAlgEquiv _
  haveI : FiniteDimensional K LK := LinearEquiv.finiteDimensional εL.toLinearEquiv
  haveI : IsGalois K LK := IsGalois.of_algEquiv εL
  have hLKD : LK ≤ D := lift_le _
  have hK₁L : K₁ ≤ LK := fun x hx ↦ (mem_lift ⟨x, hK₁D hx⟩).2 fun σ ↦
    Subtype.ext (hfixA σ.1 (hHA σ.2) ⟨x, hx⟩)
  -- `H` fixes `E`
  haveI : FiniteDimensional K (extendScalars hK₁D) := (inferInstance : FiniteDimensional K D)
  haveI : FiniteDimensional K₁ (extendScalars hK₁D) :=
    FiniteDimensional.right K K₁ (extendScalars hK₁D)
  haveI : IsGalois K (extendScalars hK₁D) := (inferInstance : IsGalois K D)
  haveI : IsGalois K₁ (extendScalars hK₁D) :=
    IsGalois.tower_top_of_isGalois K K₁ (extendScalars hK₁D)
  have hED' : E ≤ extendScalars hK₁D := fun y hy ↦ hED hy
  let ext : A →* (extendScalars hK₁D ≃ₐ[K₁] extendScalars hK₁D) :=
    { toFun := fun a ↦ autExtend K₁ hK₁D a.1 (hfixA a.1 a.2)
      map_one' := AlgEquiv.ext fun _ ↦ rfl
      map_mul' := fun _ _ ↦ AlgEquiv.ext fun _ ↦ rfl }
  have hle : H ≤ (((resHom hED').comp ext).ker).map A.subtype := by
    rw [hH, Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : A), (⟨b, hb⟩ : A)⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact (inferInstance : IsMulCommutative (E ≃ₐ[K₁] E)).is_comm.comm _ _
  have hfixE : ∀ h ∈ H, ∀ y : Ω, ∀ hy : y ∈ E, (h ⟨y, hED hy⟩ : Ω) = y := by
    intro h hh y hy
    obtain ⟨c, hc, rfl⟩ := hle hh
    have h1 := resHom_apply hED' (ext c) ⟨y, hy⟩
    have hc' : resHom hED' (ext c) = 1 := MonoidHom.mem_ker.1 hc
    rw [hc', AlgEquiv.one_apply] at h1
    exact h1.symm
  have hEL : E.restrictScalars K ≤ LK := fun y hy ↦ (mem_lift ⟨y, hED hy⟩).2 fun σ ↦
    Subtype.ext (hfixE σ.1 σ.2 y hy)
  -- the extension `L = LK` of `K₁`
  haveI : FiniteDimensional K (extendScalars hK₁L) := (inferInstance : FiniteDimensional K LK)
  haveI hfin : FiniteDimensional K₁ (extendScalars hK₁L) :=
    FiniteDimensional.right K K₁ (extendScalars hK₁L)
  haveI : IsGalois K (extendScalars hK₁L) := (inferInstance : IsGalois K LK)
  haveI : IsGalois K₁ (extendScalars hK₁L) :=
    IsGalois.tower_top_of_isGalois K K₁ (extendScalars hK₁L)
  have hLD' : extendScalars hK₁L ≤ extendScalars hK₁D := fun y hy ↦ hLKD hy
  refine ⟨extendScalars hK₁L, fun y hy ↦ hEL hy, hfin, ?_, (inferInstance : Normal K LK)⟩
  refine { toIsGalois := inferInstance, toIsMulCommutative := ⟨⟨fun σ τ ↦ ?_⟩⟩ }
  obtain ⟨σ', rfl⟩ := resHom_surjective hLD' σ
  obtain ⟨τ', rfl⟩ := resHom_surjective hLD' τ
  have hmem : ∀ ρ : extendScalars hK₁D ≃ₐ[K₁] extendScalars hK₁D,
      autRestrict K₁ hK₁D ρ ∈ A := by
    intro ρ
    rw [hA, MonoidHom.mem_ker, resHom_eq_iff]
    intro x
    exact congrArg Subtype.val (ρ.commutes x)
  have hc : ⁅autRestrict K₁ hK₁D σ', autRestrict K₁ hK₁D τ'⁆ ∈ H :=
    hH ▸ Subgroup.commutator_mem_commutator (hmem σ') (hmem τ')
  have h1 : resHom hLD' ⁅σ', τ'⁆ = 1 := by
    rw [resHom_eq_iff]
    intro y
    rw [AlgEquiv.one_apply]
    have := (mem_lift (inclusion hLKD y)).1 y.2 ⟨_, hc⟩
    exact congrArg Subtype.val this
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

end Closure

include hp in
/-- **Descent along cyclic extensions**: if `K₁/K` is cyclic and `(K₁ˣ)ⁿ` contains the norm group
of a finite abelian extension of `K₁`, then `(Kˣ)ⁿ` contains the norm group of a finite abelian
extension of `K`. -/
theorem exists_abFin_pow_of_cyclic (K₁ : IntermediateField K Ω) [FiniteDimensional K K₁]
    [IsGalois K K₁] [IsCyclic (K₁ ≃ₐ[K] K₁)] (n : ℕ)
    (h : ∃ E : AbFin K₁ Ω, ∀ x ∈ normGroup K₁ E.1, ∃ y : K₁ˣ, y ^ n = x) :
    ∃ M : AbFin K Ω, ∀ x ∈ normGroup K M.1, ∃ y : Kˣ, y ^ n = x := by
  obtain ⟨E, hE⟩ := h
  obtain ⟨L, hEL, hLfin, hLab, hLn⟩ := exists_abelian_closure (p := p) K₁ E.1
  obtain ⟨M, -, hM⟩ := exists_abFin_le_norm (p := p) K₁ L
  refine ⟨M, fun x hx ↦ ?_⟩
  obtain ⟨z, hz, rfl⟩ := hM x hx
  obtain ⟨y, rfl⟩ := hE z (normGroup_le_of_algHom (inclusion hEL) hz)
  exact ⟨normU K₁ y, (map_pow _ _ _).symm⟩

section Cyclotomic

variable (K Ω) in
/-- The field `K(μ_n) ⊆ Ω`. -/
noncomputable def cycField (n : ℕ) : IntermediateField K Ω :=
  adjoin K {b : Ω | ∃ m ∈ ({n} : Set ℕ), m ≠ 0 ∧ b ^ m = 1}

include hp in
theorem isCyclotomicExtension_cycField {n : ℕ} :
    IsCyclotomicExtension {n} K (cycField K Ω n) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  apply IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
  intro m hm hm0
  rw [Set.mem_singleton_iff] at hm
  subst hm
  haveI : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.2 hm0⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω m

include hp in
theorem finiteDimensional_cycField {n : ℕ} : FiniteDimensional K (cycField K Ω n) := by
  haveI := isCyclotomicExtension_cycField (p := p) (K := K) (Ω := Ω) (n := n)
  exact IsCyclotomicExtension.finiteDimensional {n} K _

include hp in
theorem isAbelianGalois_cycField {n : ℕ} (hn : 0 < n) :
    IsAbelianGalois K (cycField K Ω n) := by
  haveI := isCyclotomicExtension_cycField (p := p) (K := K) (Ω := Ω) (n := n)
  haveI : NeZero n := ⟨hn.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n K (cycField K Ω n)
  haveI : IsGalois K (cycField K Ω n) := IsCyclotomicExtension.isGalois {n} K _
  exact { is_comm := ⟨fun σ τ ↦ hζ.autToPow_injective K (by rw [map_mul, map_mul, mul_comm])⟩ }

include hp in
theorem exists_isPrimitiveRoot_of_finrank_cycField {n : ℕ} (hn : 0 < n)
    (h : Module.finrank K (cycField K Ω n) = 1) : ∃ ζ : K, IsPrimitiveRoot ζ n := by
  haveI := isCyclotomicExtension_cycField (p := p) (K := K) (Ω := Ω) (n := n)
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [IntermediateField.finrank_eq_one_iff] at h
  have hζ := IsCyclotomicExtension.zeta_spec n K (cycField K Ω n)
  have hz : ((IsCyclotomicExtension.zeta n K (cycField K Ω n) : cycField K Ω n) : Ω) ∈
      (⊥ : IntermediateField K Ω) := h ▸ (IsCyclotomicExtension.zeta n K (cycField K Ω n)).2
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hz
  refine ⟨c, ?_⟩
  have h2 := hζ.map_of_injective (cycField K Ω n).val.injective
  have h3 : IsPrimitiveRoot (algebraMap K Ω c) n := by rw [hc]; exact h2
  exact h3.of_map_of_injective (algebraMap K Ω).injective

include hp in
/-- **Reduction to cyclic steps**: if `(K₁ˣ)ⁿ` contains a norm group for all cyclic
`K ⊊ K₁ ⊆ K(μ_n)`, then so does `(Kˣ)ⁿ`. -/
theorem exists_abFin_pow_of_forall_cyclic {n : ℕ} (hn : 0 < n)
    (h : ∀ K₁ : IntermediateField K Ω, ∀ _ : FiniteDimensional K K₁, ∀ _ : IsGalois K K₁,
      ∀ _ : IsCyclic (K₁ ≃ₐ[K] K₁), 1 < Module.finrank K K₁ → K₁ ≤ cycField K Ω n →
      ∃ E : AbFin K₁ Ω, ∀ x ∈ normGroup K₁ E.1, ∃ y : K₁ˣ, y ^ n = x) :
    ∃ M : AbFin K Ω, ∀ x ∈ normGroup K M.1, ∃ y : Kˣ, y ^ n = x := by
  haveI := finiteDimensional_cycField (p := p) (K := K) (Ω := Ω) (n := n)
  haveI := isAbelianGalois_cycField (p := p) (K := K) (Ω := Ω) hn
  by_cases h1 : Module.finrank K (cycField K Ω n) = 1
  · exact exists_abFin_normGroup_le_pow (p := p) n hn
      (exists_isPrimitiveRoot_of_finrank_cycField (p := p) (Ω := Ω) hn h1)
  set C := cycField K Ω n
  have hne : ∃ σ : C ≃ₐ[K] C, σ ≠ 1 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have : Nat.card (C ≃ₐ[K] C) = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b ↦ (hall a).trans (hall b).symm⟩, inferInstance⟩
    rw [IsGalois.card_aut_eq_finrank] at this
    exact h1 this
  obtain ⟨σ, hσ⟩ := hne
  obtain ⟨H, hσH, hcyc⟩ := exists_isCyclic_quotient hσ
  set K₁ := lift (fixedField H)
  let ε : fixedField H ≃ₐ[K] K₁ := liftAlgEquiv _
  haveI : FiniteDimensional K K₁ := LinearEquiv.finiteDimensional ε.toLinearEquiv
  haveI : IsGalois K K₁ := IsGalois.of_algEquiv ε
  haveI : IsCyclic (K₁ ≃ₐ[K] K₁) :=
    isCyclic_of_surjective ((AlgEquiv.autCongr ε).toMonoidHom.comp
      (IsGalois.normalAutEquivQuotient H).toMonoidHom)
      ((AlgEquiv.autCongr ε).surjective.comp (IsGalois.normalAutEquivQuotient H).surjective)
  have hfin : 1 < Module.finrank K K₁ := by
    by_contra hle
    have h2 : Module.finrank K (fixedField H) = 1 := by
      rw [LinearEquiv.finrank_eq ε.toLinearEquiv]
      exact le_antisymm (not_lt.1 hle) Module.finrank_pos
    rw [IntermediateField.finrank_eq_one_iff] at h2
    apply hσH
    rw [← fixingSubgroup_fixedField H, h2, IntermediateField.fixingSubgroup_bot]
    exact Subgroup.mem_top σ
  exact exists_abFin_pow_of_cyclic (p := p) K₁ n
    (h K₁ inferInstance inferInstance inferInstance hfin (lift_le _))

end Cyclotomic

section Main

universe u

include hp in
/-- The existence theorem for `(Fˣ)ⁿ`, by induction on `[F(μ_n) : F]` (all fields in the universe
of `Ω`). -/
theorem existence_pow_aux {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra ℚ_[p] Ω] {n : ℕ}
    (hn : 0 < n) (d : ℕ) : ∀ (F : Type u) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
      [Algebra F Ω] [IsScalarTower ℚ_[p] F Ω], Module.finrank F (cycField F Ω n) ≤ d →
      ∃ M : AbFin F Ω, ∀ x ∈ normGroup F M.1, ∃ y : Fˣ, y ^ n = x := by
  induction d with
  | zero =>
    intro F _ _ _ _ _ hd
    haveI := finiteDimensional_cycField (p := p) (K := F) (Ω := Ω) (n := n)
    exact absurd (Module.finrank_pos (R := F) (M := cycField F Ω n)) (by omega)
  | succ d ih =>
    intro F _ _ _ _ _ hd
    refine exists_abFin_pow_of_forall_cyclic (p := p) hn fun K₁ _ _ _ hK₁ hK₁C ↦ ih K₁ ?_
    set C := cycField F Ω n
    set C₁ := cycField K₁ Ω n
    haveI := finiteDimensional_cycField (p := p) (K := K₁) (Ω := Ω) (n := n)
    have heq : C₁.restrictScalars F = C := by
      change (adjoin K₁ _).restrictScalars F = _
      rw [restrictScalars_adjoin_eq_sup]
      exact sup_eq_right.2 hK₁C
    have h1 : Module.finrank F K₁ * Module.finrank K₁ C₁ = Module.finrank F C := by
      haveI : Module.Free K₁ C₁ := Module.Free.of_divisionRing _ _
      rw [Module.finrank_mul_finrank F K₁ C₁, ← heq]
      rfl
    have h2 : Module.finrank K₁ C₁ < Module.finrank F K₁ * Module.finrank K₁ C₁ :=
      lt_mul_left Module.finrank_pos hK₁
    omega

include hp in
/-- **Existence theorem for `(Kˣ)ⁿ`**: for `n ≥ 1`, `(Kˣ)ⁿ` contains the norm group of a finite
abelian extension of `K` inside `Ω`. -/
theorem exists_abFin_normGroup_le_pow' {n : ℕ} (hn : 0 < n) :
    ∃ L : AbFin K Ω, ∀ x ∈ normGroup K L.1, ∃ y : Kˣ, y ^ n = x :=
  exists_abFin_pow_of_forall_cyclic (p := p) hn fun K₁ _ _ _ _ _ ↦
    existence_pow_aux (p := p) hn _ K₁ le_rfl

include hp in
/-- **The existence theorem of local class field theory**: every subgroup of finite index of
`Kˣ` is the norm group `N_{L/K} Lˣ` of a finite abelian extension `L ⊆ Ω` of `K`. -/
theorem existence (N : Subgroup Kˣ) (hN : N.index ≠ 0) :
    ∃ L : AbFin K Ω, normGroup K L.1 = N :=
  existence_of_pow (p := p) (fun _ hn ↦ exists_abFin_normGroup_le_pow' (p := p) hn) N hN

include hp in
/-- `[Kˣ : N_{L/K} Lˣ] = [L : K]` for finite abelian `L ⊆ Ω`. -/
theorem index_normGroup_eq_finrank (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] : (normGroup K L).index = Module.finrank K L := by
  rw [Subgroup.index, Nat.card_congr (abRecEquiv p L).toEquiv, IsGalois.card_aut_eq_finrank]

include hp in
/-- **Norm groups determine the extension**: `L₁ ⊆ L₂ ↔ N_{L₂} ⊆ N_{L₁}`. -/
theorem le_iff_normGroup_le (L₁ L₂ : IntermediateField K Ω) [FiniteDimensional K L₁]
    [IsAbelianGalois K L₁] [FiniteDimensional K L₂] [IsAbelianGalois K L₂] :
    L₁ ≤ L₂ ↔ normGroup K L₂ ≤ normGroup K L₁ := by
  constructor
  · intro h
    exact normGroup_le_of_algHom (inclusion h)
  · intro h
    haveI := isAbelianGalois_sup L₁ L₂
    have h1 : normGroup K (L₁ ⊔ L₂ : IntermediateField K Ω) = normGroup K L₂ := by
      rw [normGroup_sup (p := p), inf_eq_right.2 h]
    have h2 : Module.finrank K L₂ = Module.finrank K (L₁ ⊔ L₂ : IntermediateField K Ω) := by
      rw [← index_normGroup_eq_finrank (p := p), ← index_normGroup_eq_finrank (p := p), h1]
    have h3 := IntermediateField.eq_of_le_of_finrank_eq (le_sup_right : L₂ ≤ L₁ ⊔ L₂) h2
    exact le_sup_left.trans_eq h3.symm

include hp in
/-- **Main theorem of local class field theory**: `L ↦ N_{L/K} Lˣ` is a bijection from finite
abelian extensions `L ⊆ Ω` of `K` onto the subgroups of finite index of `Kˣ`. -/
theorem existsUnique_normGroup_eq (N : Subgroup Kˣ) (hN : N.index ≠ 0) :
    ∃! L : AbFin K Ω, normGroup K L.1 = N := by
  obtain ⟨L, hL⟩ := existence (p := p) (Ω := Ω) N hN
  refine ⟨L, hL, fun L' hL' ↦ Subtype.ext (le_antisymm ?_ ?_)⟩
  · exact (le_iff_normGroup_le (p := p) L'.1 L.1).2 (hL.trans hL'.symm).le
  · exact (le_iff_normGroup_le (p := p) L.1 L'.1).2 (hL'.trans hL.symm).le

end Main

end PadicField
