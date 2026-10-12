/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.UnitIndex

/-!
# The unit map `Ψ` of a cyclic totally ramified extension

Let `F = M U` be a standard extension (see `Reciprocity/Standard.lean`) with `M/K` cyclic totally
ramified of degree `e`, `U/K` unramified of degree divisible by `e`, `s` a generator of
`Gal(M/K)`, `sU ∈ Gal(F/U)` the corresponding generator and `φ ∈ Gal(F/M)` the Frobenius.

For a unit `u` of `K` write `u = N_{F/U}(η)` (vanishing at the unramified level) and
`φ η / η = sU y / y` (Hilbert 90); then `Ψ(u) = s ^ (- v_F(y))` is well defined.
-/

set_option linter.unusedSectionVars false

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]

section General

variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L] [FiniteDimensional K L] [IsGalois K L]

include hp in
/-- Hilbert 90 in the form `N(z) = 1 ⇒ z = σ y / y`. -/
theorem hilbert90_norm (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (z : Lˣ)
    (hz : Algebra.norm K (z : L) = 1) : ∃ y : Lˣ, Units.map (σ : L →* L) y / y = z := by
  apply exists_div_of_prod_eq_one σ hσ
  rw [← normUnits_eq_partialNorm (p := p) σ hσ]
  ext
  rw [coe_normUnits_eq_norm, hz, map_one, Units.val_one]

omit [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] L] in
/-- An element fixed by a generator of the Galois group lies in the base. -/
theorem exists_algebraMap_eq_of_generator (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    {x : L} (h : σ x = x) : ∃ a : K, algebraMap K L a = x := by
  have hbot : x ∈ (⊥ : IntermediateField K L) :=
    (IsGalois.mem_bot_iff_fixed x).2 (apply_eq_of_generator σ hσ h)
  exact IntermediateField.mem_bot.1 hbot

omit [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] L] [IsGalois K L] in
theorem norm_div' (a b : L) : Algebra.norm K (a / b) = Algebra.norm K a / Algebra.norm K b := by
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, div_eq_mul_inv]

omit [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] L] in
/-- The norm is invariant under the Galois group. -/
theorem norm_galois (g : L ≃ₐ[K] L) (x : L) : Algebra.norm K (g x) = Algebra.norm K x := by
  apply (algebraMap K L).injective
  rw [Algebra.norm_eq_prod_automorphisms, Algebra.norm_eq_prod_automorphisms]
  exact Fintype.prod_equiv (Equiv.mulRight g) _ _ fun h ↦ by simp [AlgEquiv.mul_apply]

end General

variable {K M U F : Type*} [Field K] [Field M] [Field U] [Field F]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] M] [Algebra ℚ_[p] U] [Algebra ℚ_[p] F]
  [Algebra K M] [Algebra K U] [Algebra K F] [Algebra M F] [Algebra U F]
  [IsScalarTower ℚ_[p] K M] [IsScalarTower ℚ_[p] K U] [IsScalarTower ℚ_[p] K F]
  [IsScalarTower ℚ_[p] M F] [IsScalarTower ℚ_[p] U F]
  [IsScalarTower K M F] [IsScalarTower K U F]
  [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] M] [FiniteDimensional ℚ_[p] U]
  [FiniteDimensional ℚ_[p] F] [IsGalois K F] [IsGalois K M] [IsCyclic (M ≃ₐ[K] M)]

variable (hM : e p K M = Module.finrank K M) (hU : IsUnramified p K U)
  (hdeg : Module.finrank K F = Module.finrank K M * Module.finrank K U)
include hM hU hdeg

/-- Automorphisms over `U` and over `M` commute. -/
theorem std_comm (g : F ≃ₐ[U] F) (h : F ≃ₐ[M] F) (x : F) : g (h x) = h (g x) := by
  have hg : ∀ k : K, g (algebraMap K F k) = algebraMap K F k := fun k ↦ by
    rw [IsScalarTower.algebraMap_apply K U F]; exact g.commutes _
  have hh : ∀ k : K, h (algebraMap K F k) = algebraMap K F k := fun k ↦ by
    rw [IsScalarTower.algebraMap_apply K M F]; exact h.commutes _
  let E : IntermediateField K F :=
    { carrier := {x | g (h x) = h (g x)}
      mul_mem' := fun {a b} ha hb ↦ by simp only [Set.mem_setOf_eq, map_mul] at *; rw [ha, hb]
      add_mem' := fun {a b} ha hb ↦ by simp only [Set.mem_setOf_eq, map_add] at *; rw [ha, hb]
      algebraMap_mem' := fun k ↦ by
        simp only [Set.mem_setOf_eq, hg, hh]
      inv_mem' := fun a ha ↦ by simp only [Set.mem_setOf_eq, map_inv₀] at *; rw [ha] }
  have hE := std_eq_top hM hU hdeg E
    (fun m ↦ by
      change g (h (algebraMap M F m)) = h (g (algebraMap M F m))
      rw [h.commutes, ← stdResM_apply (K := K) g m, h.commutes])
    (fun u ↦ by
      change g (h (algebraMap U F u)) = h (g (algebraMap U F u))
      rw [g.commutes, ← stdResU_apply hU h u, g.commutes])
  have : x ∈ E := hE ▸ IntermediateField.mem_top
  exact this


section Psi

variable (s : M ≃ₐ[K] M)

/-- The generator of `Gal(F/U)` corresponding to `s ∈ Gal(M/K)`. -/
noncomputable def stdGen : F ≃ₐ[U] F :=
  (MulEquiv.ofBijective _ (stdResM_bijective hM hU hdeg)).symm s

theorem stdResM_stdGen : stdResM (K := K) (stdGen hM hU hdeg s) = s :=
  (MulEquiv.ofBijective _ (stdResM_bijective hM hU hdeg)).apply_symm_apply s

theorem stdGen_generates (hs : ∀ g, g ∈ Subgroup.zpowers s) (g : F ≃ₐ[U] F) :
    g ∈ Subgroup.zpowers (stdGen hM hU hdeg s) := by
  set ψ := MulEquiv.ofBijective _ (stdResM_bijective hM hU hdeg)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hs (ψ g))
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ψ.injective ?_⟩
  rw [map_zpow]
  change ψ (ψ.symm s) ^ k = ψ g
  rw [ψ.apply_symm_apply, hk]

theorem orderOf_stdGen : orderOf (stdGen hM hU hdeg s) = orderOf s := by
  rw [← orderOf_injective (MulEquiv.ofBijective _ (stdResM_bijective hM hU hdeg)).toMonoidHom
    (MulEquiv.ofBijective _ (stdResM_bijective hM hU hdeg)).injective]
  change orderOf ((MulEquiv.ofBijective _ _) ((MulEquiv.ofBijective _ _).symm s)) = _
  rw [MulEquiv.apply_symm_apply]

/-- The Frobenius of `F/M`. -/
noncomputable def stdFrob : F ≃ₐ[M] F := frob (std_isUnramified_top hM hU hdeg)

theorem stdFrob_generates (g : F ≃ₐ[M] F) : g ∈ Subgroup.zpowers (stdFrob hM hU hdeg) :=
  (zpowers_frob (std_isUnramified_top hM hU hdeg)).symm ▸ Subgroup.mem_top g

/-- Units version of an automorphism. -/
abbrev uMap {R : Type*} [Field R] [Algebra R F] (g : F ≃ₐ[R] F) : Fˣ →* Fˣ :=
  Units.map (g : F →* F)

omit hM hU hdeg in
theorem coe_uMap {R : Type*} [Field R] [Algebra R F] (g : F ≃ₐ[R] F) (x : Fˣ) :
    ((uMap g x : Fˣ) : F) = g x := rfl

/-- `Ψ`-data for a unit `u`: `u = N_{F/U}(η)` and `φ η / η = sU y / y`. -/
def PsiData (u : Kˣ) (η y : Fˣ) : Prop :=
  Algebra.norm U (η : F) = algebraMap K U u ∧
    uMap (stdFrob hM hU hdeg) η / η = uMap (stdGen hM hU hdeg s) y / y

theorem norm_stdFrob (x : F) :
    Algebra.norm U (stdFrob hM hU hdeg x) =
      stdResU hU (stdFrob hM hU hdeg) (Algebra.norm U x) := by
  haveI := finiteDimensional_tower (p := p) U F
  haveI : IsGalois U F := IsGalois.tower_top_of_isGalois K U F
  apply (algebraMap U F).injective
  rw [stdResU_apply, Algebra.norm_eq_prod_automorphisms, Algebra.norm_eq_prod_automorphisms,
    map_prod]
  exact Finset.prod_congr rfl fun g _ ↦ std_comm hM hU hdeg g _ x

/-- Existence of `Ψ`-data, when `[M : K] ∣ [U : K]`. -/
theorem exists_psiData (hs : ∀ g, g ∈ Subgroup.zpowers s)
    (he : Module.finrank K M ∣ Module.finrank K U) (u : Kˣ) (hu : nrm p K (u : K) = 1) :
    ∃ η y : Fˣ, PsiData hM hU hdeg s u η y := by
  haveI := finiteDimensional_tower (p := p) U F
  haveI : IsGalois U F := IsGalois.tower_top_of_isGalois K U F
  obtain ⟨η, -, hη⟩ := std_exists_norm_eq hM hU hdeg he u hu
  have hz : Algebra.norm U ((uMap (stdFrob hM hU hdeg) η / η : Fˣ) : F) = 1 := by
    rw [Units.val_div_eq_div_val, norm_div', coe_uMap, norm_stdFrob, hη, AlgEquiv.commutes,
      div_self ((map_ne_zero_iff _ (algebraMap K U).injective).2 u.ne_zero)]
  obtain ⟨y, hy⟩ := hilbert90_norm (p := p) (stdGen hM hU hdeg s)
    (stdGen_generates hM hU hdeg s hs) _ hz
  exact ⟨η, y, hη, hy.symm⟩

/-- Well-definedness of `Ψ`: the valuations of `y` agree modulo `[M : K]`. -/
theorem psiData_wd {u : Kˣ} {η₁ y₁ η₂ y₂ : Fˣ} (hs : ∀ g, g ∈ Subgroup.zpowers s)
    (h₁ : PsiData hM hU hdeg s u η₁ y₁) (h₂ : PsiData hM hU hdeg s u η₂ y₂) :
    (Module.finrank K M : ℤ) ∣ v p (y₂ : F) - v p (y₁ : F) := by
  haveI := finiteDimensional_tower (p := p) U F
  haveI : IsGalois U F := IsGalois.tower_top_of_isGalois K U F
  set sU := stdGen hM hU hdeg s
  set φ := stdFrob hM hU hdeg
  -- `η₂ / η₁` has norm one
  have hw0 : Algebra.norm U ((η₂ / η₁ : Fˣ) : F) = 1 := by
    rw [Units.val_div_eq_div_val, norm_div', h₁.1, h₂.1,
      div_self ((map_ne_zero_iff _ (algebraMap K U).injective).2 u.ne_zero)]
  obtain ⟨w, hw⟩ := hilbert90_norm (p := p) sU (stdGen_generates hM hU hdeg s hs) _ hw0
  set c : Fˣ := uMap φ w / w
  -- `y₂ / (y₁ c)` is fixed by `sU`
  have hcomm : ∀ x : Fˣ, uMap sU (uMap φ x) = uMap φ (uMap sU x) := fun x ↦
    Units.ext (std_comm hM hU hdeg sU φ x)
  have hd : uMap sU (y₂ / (y₁ * c)) = y₂ / (y₁ * c) := by
    have key : uMap φ η₂ / η₂ = (uMap φ η₁ / η₁) * (uMap sU c / c) := by
      have hη₂ : η₂ = η₁ * (uMap sU w / w) := by rw [hw, mul_div_cancel]
      rw [hη₂]
      simp only [map_mul, map_div, c, hcomm]
      apply Units.ext
      simp only [Units.val_mul, Units.val_div_eq_div_val]
      field_simp
    rw [h₁.2, h₂.2] at key
    apply Units.ext
    have keyF := congrArg Units.val key
    simp only [map_mul, map_div, Units.val_mul, Units.val_div_eq_div_val] at keyF ⊢
    have h1 := (uMap sU y₁).ne_zero
    have h2 := y₁.ne_zero
    have h3 := (uMap sU c).ne_zero
    have h4 := c.ne_zero
    have h5 := y₂.ne_zero
    field_simp at keyF ⊢
    linear_combination keyF
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_generator sU (stdGen_generates hM hU hdeg s hs)
    (congrArg Units.val hd)
  have ha0 : a ≠ 0 := by
    rintro rfl; rw [map_zero] at ha; exact (Units.ne_zero _) ha.symm
  have hva := v_algebraMap (p := p) (K := U) (L := F) a
  rw [ha, std_e_U hM hU hdeg, std_finrank_U hM hU hdeg] at hva
  have hvc : v p (c : F) = 0 := by
    have : nrm p F (c : F) = 1 := by
      simp only [c, Units.val_div_eq_div_val, coe_uMap, nrm_div]
      rw [nrm_algEquiv_tower (p := p) M F φ, div_self (nrm_pos_iff.2 w.ne_zero).ne']
    exact (nrm_eq_one_iff_v_eq_zero c.ne_zero).1 this
  rw [Units.val_div_eq_div_val, Units.val_mul, v_div y₂.ne_zero (mul_ne_zero y₁.ne_zero
    c.ne_zero), v_mul y₁.ne_zero c.ne_zero, hvc, add_zero] at hva
  exact ⟨_, hva⟩


theorem psiData_mul {u₁ u₂ : Kˣ} {η₁ y₁ η₂ y₂ : Fˣ} (h₁ : PsiData hM hU hdeg s u₁ η₁ y₁)
    (h₂ : PsiData hM hU hdeg s u₂ η₂ y₂) :
    PsiData hM hU hdeg s (u₁ * u₂) (η₁ * η₂) (y₁ * y₂) := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, map_mul, h₁.1, h₂.1, Units.val_mul, map_mul]
  · have := congrArg₂ (· * ·) h₁.2 h₂.2
    rw [map_mul, map_mul]
    rw [mul_div_mul_comm, this, mul_div_mul_comm]

theorem psiData_one : PsiData hM hU hdeg s 1 1 1 := by
  refine ⟨by simp, by simp⟩

theorem zpow_eq_of_dvd (hs : ∀ g, g ∈ Subgroup.zpowers s) {a b : ℤ}
    (h : (Module.finrank K M : ℤ) ∣ a - b) : s ^ a = s ^ b := by
  haveI := finiteDimensional_tower (p := p) K M
  rw [zpow_eq_zpow_iff_modEq, orderOf_eq_card_of_forall_mem_zpowers hs,
    IsGalois.card_aut_eq_finrank]
  exact (Int.modEq_iff_dvd.2 h).symm

variable (hs : ∀ g, g ∈ Subgroup.zpowers s) (he : Module.finrank K M ∣ Module.finrank K U)

/-- The chosen `y` for a unit `u`. -/
noncomputable def psiY (u : unitGroup p K) : Fˣ :=
  (exists_psiData hM hU hdeg s hs he u u.2).choose_spec.choose

theorem psiY_spec (u : unitGroup p K) :
    PsiData hM hU hdeg s u (exists_psiData hM hU hdeg s hs he u u.2).choose
      (psiY hM hU hdeg s hs he u) :=
  (exists_psiData hM hU hdeg s hs he u u.2).choose_spec.choose_spec

/-- **The unit map** `Ψ_s : 𝒪ˣ_K → Gal(M/K)`, `u ↦ s ^ (- v(y))`. -/
noncomputable def psi : unitGroup p K →* (M ≃ₐ[K] M) where
  toFun u := s ^ (-v p (psiY hM hU hdeg s hs he u : F))
  map_one' := by
    have h := psiData_wd hM hU hdeg s hs (psiData_one hM hU hdeg s)
      (psiY_spec hM hU hdeg s hs he 1)
    rw [Units.val_one, v_one, sub_zero] at h
    rw [show (1 : M ≃ₐ[K] M) = s ^ (-(0 : ℤ)) by simp]
    exact zpow_eq_of_dvd hM hU hdeg s hs (by simpa using (dvd_neg).2 h)
  map_mul' a b := by
    have h := psiData_wd hM hU hdeg s hs
      (psiData_mul hM hU hdeg s (psiY_spec hM hU hdeg s hs he a) (psiY_spec hM hU hdeg s hs he b))
      (psiY_spec hM hU hdeg s hs he (a * b))
    rw [← zpow_add]
    apply zpow_eq_of_dvd hM hU hdeg s hs
    rw [Units.val_mul, v_mul (Units.ne_zero _) (Units.ne_zero _)] at h
    have : -v p ((psiY hM hU hdeg s hs he (a * b) : Fˣ) : F) -
        (-v p ((psiY hM hU hdeg s hs he a : Fˣ) : F) +
          -v p ((psiY hM hU hdeg s hs he b : Fˣ) : F)) =
        -(v p ((psiY hM hU hdeg s hs he (a * b) : Fˣ) : F) -
          (v p ((psiY hM hU hdeg s hs he a : Fˣ) : F) +
            v p ((psiY hM hU hdeg s hs he b : Fˣ) : F))) := by ring
    rw [this]
    exact (dvd_neg).2 h

/-- `Ψ` can be computed from any data. -/
theorem psi_eq_of_psiData {u : unitGroup p K} {η y : Fˣ}
    (h : PsiData hM hU hdeg s u η y) : psi hM hU hdeg s hs he u = s ^ (-v p (y : F)) := by
  have hwd := psiData_wd hM hU hdeg s hs h (psiY_spec hM hU hdeg s hs he u)
  apply zpow_eq_of_dvd hM hU hdeg s hs
  have : -v p ((psiY hM hU hdeg s hs he u : Fˣ) : F) - -v p (y : F) =
      -(v p ((psiY hM hU hdeg s hs he u : Fˣ) : F) - v p (y : F)) := by ring
  rw [this]
  exact (dvd_neg).2 hwd


/-- Norms of units of `M` are in the kernel of `Ψ`. -/
theorem psi_norm (m : Mˣ) (hm : (Units.map (Algebra.norm K : M →* K) m) ∈ unitGroup p K) :
    psi hM hU hdeg s hs he ⟨_, hm⟩ = 1 := by
  have hdata : PsiData hM hU hdeg s (Units.map (Algebra.norm K : M →* K) m)
      (Units.map (algebraMap M F : M →* F) m) 1 := by
    refine ⟨?_, ?_⟩
    · exact std_norm_M hM hU hdeg (m : M)
    · have : uMap (stdFrob hM hU hdeg) (Units.map (algebraMap M F : M →* F) m) =
          Units.map (algebraMap M F : M →* F) m := Units.ext ((stdFrob hM hU hdeg).commutes _)
      rw [this, div_self', map_one, div_one]
  rw [psi_eq_of_psiData hM hU hdeg s hs he hdata]
  simp

theorem norm_stdGen (x : F) :
    Algebra.norm M (stdGen hM hU hdeg s x) = s (Algebra.norm M x) := by
  haveI := finiteDimensional_tower (p := p) M F
  haveI : IsGalois M F := IsGalois.tower_top_of_isGalois K M F
  apply (algebraMap M F).injective
  have hs' : algebraMap M F (s (Algebra.norm M x)) =
      stdGen hM hU hdeg s (algebraMap M F (Algebra.norm M x)) := by
    rw [← stdResM_apply (K := K) (stdGen hM hU hdeg s), stdResM_stdGen]
  rw [hs', Algebra.norm_eq_prod_automorphisms, Algebra.norm_eq_prod_automorphisms, map_prod]
  exact Finset.prod_congr rfl fun h _ ↦ (std_comm hM hU hdeg _ h x).symm

/-- Elements of the kernel of `Ψ` are norms from `M`. -/
theorem mem_normGroup_of_psi_eq_one (u : unitGroup p K) (h : psi hM hU hdeg s hs he u = 1) :
    (u : Kˣ) ∈ normGroup K M := by
  haveI := finiteDimensional_tower (p := p) K M
  haveI := finiteDimensional_tower (p := p) M F
  haveI := finiteDimensional_tower (p := p) U F
  haveI : IsGalois M F := IsGalois.tower_top_of_isGalois K M F
  haveI : IsGalois U F := IsGalois.tower_top_of_isGalois K U F
  set sU := stdGen hM hU hdeg s
  set φ := stdFrob hM hU hdeg
  set η := (exists_psiData hM hU hdeg s hs he u u.2).choose
  set y := psiY hM hU hdeg s hs he u
  have hdata : PsiData hM hU hdeg s u η y := psiY_spec hM hU hdeg s hs he u
  -- `e ∣ v y`
  have hdvd : (Module.finrank K M : ℤ) ∣ v p (y : F) := by
    rw [psi_eq_of_psiData hM hU hdeg s hs he hdata, zpow_eq_one_iff_modEq,
      orderOf_eq_card_of_forall_mem_zpowers hs, IsGalois.card_aut_eq_finrank] at h
    have h' := Int.ModEq.dvd h.symm
    rw [sub_zero] at h'
    exact (dvd_neg).1 h'
  obtain ⟨k, hk⟩ := hdvd
  -- normalise `y` to a unit
  have hπ := uniformizer_spec (p := p) (K := U)
  set πU : Uˣ := Units.mk0 _ hπ.ne_zero
  set y' : Fˣ := y / Units.map (algebraMap U F : U →* F) πU ^ k
  have hsU_U : ∀ a : Uˣ, uMap sU (Units.map (algebraMap U F : U →* F) a) =
      Units.map (algebraMap U F : U →* F) a := fun a ↦ Units.ext (sU.commutes _)
  have hy'data : PsiData hM hU hdeg s u η y' := by
    refine ⟨hdata.1, ?_⟩
    rw [hdata.2]
    simp only [y', map_div, map_zpow]
    rw [hsU_U πU, div_div_div_cancel_right]
  have hvy' : v p (y' : F) = 0 := by
    have hvπ := v_algebraMap (p := p) (K := U) (L := F) (uniformizer p U)
    rw [hπ, std_e_U hM hU hdeg, std_finrank_U hM hU hdeg, mul_one] at hvπ
    simp only [y', Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, Units.coe_map,
      MonoidHom.coe_coe, πU, Units.val_mk0]
    rw [v_div y.ne_zero (zpow_ne_zero _ ((map_ne_zero_iff _ (algebraMap U F).injective).2
      hπ.ne_zero)), v_zpow ((map_ne_zero_iff _ (algebraMap U F).injective).2 hπ.ne_zero), hvπ,
      hk]
    ring
  have hny' : nrm p F (y' : F) = 1 := (nrm_eq_one_iff_v_eq_zero y'.ne_zero).2 hvy'
  -- `b = N_{F/M}(y')` lies in `K`
  have hb : s (Algebra.norm M (y' : F)) = Algebra.norm M (y' : F) := by
    have e1 := congrArg (fun z : Fˣ ↦ Algebra.norm M (z : F)) hy'data.2
    simp only [Units.val_div_eq_div_val, coe_uMap, norm_div', norm_galois] at e1
    rw [div_self (Algebra.norm_ne_zero_iff.2 η.ne_zero), norm_stdGen hM hU hdeg s] at e1
    exact (div_eq_one_iff_eq (Algebra.norm_ne_zero_iff.2 y'.ne_zero)).1 e1.symm
  obtain ⟨b0, hb0⟩ := exists_algebraMap_eq_of_generator s hs hb
  have hb00 : b0 ≠ 0 := by
    rintro rfl; rw [map_zero] at hb0; exact Algebra.norm_ne_zero_iff.2 y'.ne_zero hb0.symm
  have hnb0 : nrm p K b0 = 1 := by
    rw [← nrm_algebraMap_tower (L := M), hb0]
    rw [nrm_norm, hny', one_pow]
  obtain ⟨a, ha1, ha⟩ := exists_norm_eq_of_isUnramified hU (Units.mk0 b0 hb00) hnb0
  -- Hilbert 90 for `F/M`
  set x' : Fˣ := y'⁻¹ * Units.map (algebraMap U F : U →* F) a
  have hx' : Algebra.norm M (x' : F) = 1 := by
    simp only [x', Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_coe,
      map_mul, Algebra.norm_inv]
    rw [std_norm_U hM hU hdeg, ha, ← hb0]
    exact inv_mul_cancel₀ ((map_ne_zero_iff _ (algebraMap K M).injective).2 hb00)
  obtain ⟨x, hx⟩ := hilbert90_norm (p := p) φ (stdFrob_generates hM hU hdeg) x' hx'
  set η₁ : Fˣ := η * (uMap sU x / x)
  have hcomm : ∀ z : Fˣ, uMap sU (uMap φ z) = uMap φ (uMap sU z) := fun z ↦
    Units.ext (std_comm hM hU hdeg sU φ z)
  have hfix : uMap φ η₁ = η₁ := by
    have h1 : uMap φ η₁ / η₁ = (uMap φ η / η) * (uMap sU (uMap φ x / x) / (uMap φ x / x)) := by
      simp only [η₁, map_mul, map_div, hcomm]
      apply Units.ext
      simp only [Units.val_mul, Units.val_div_eq_div_val]
      field_simp
    have h2 : uMap φ η₁ / η₁ = 1 := by
      rw [h1, hy'data.2]
      change uMap sU y' / y' * (uMap sU (Units.map (φ : F →* F) x / x) /
        (Units.map (φ : F →* F) x / x)) = 1
      rw [hx]
      simp only [x', map_mul, map_inv, hsU_U]
      apply Units.ext
      have h1 := (uMap sU y').ne_zero
      have h2 := y'.ne_zero
      have h3 := (Units.map (algebraMap U F : U →* F) a).ne_zero
      simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_inv_eq_inv_val,
        Units.val_one]
      field_simp
    exact div_eq_one.1 h2
  obtain ⟨m, hm⟩ := exists_algebraMap_eq_of_generator φ (stdFrob_generates hM hU hdeg)
    (congrArg Units.val hfix)
  have hm0 : m ≠ 0 := by
    rintro rfl; rw [map_zero] at hm; exact (Units.ne_zero _) hm.symm
  refine ⟨Units.mk0 m hm0, Units.ext ?_⟩
  change Algebra.norm K m = ((u : Kˣ) : K)
  apply (algebraMap K U).injective
  rw [← std_norm_M hM hU hdeg, hm]
  simp only [η₁, Units.val_mul, Units.val_div_eq_div_val, coe_uMap, map_mul, norm_div',
    norm_galois]
  rw [div_self (Algebra.norm_ne_zero_iff.2 x.ne_zero), mul_one]
  exact hdata.1


theorem psi_ker :
    (psi hM hU hdeg s hs he).ker = (normGroup K M ⊓ unitGroup p K).subgroupOf (unitGroup p K) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact ⟨mem_normGroup_of_psi_eq_one hM hU hdeg s hs he u h, u.2⟩
  · rintro ⟨⟨m, hm⟩, -⟩
    have hu : Units.map (Algebra.norm K : M →* K) m ∈ unitGroup p K := hm ▸ u.2
    have : u = ⟨_, hu⟩ := Subtype.ext hm.symm
    rw [this]
    exact psi_norm hM hU hdeg s hs he m hu

/-- **`Ψ` is surjective**, hence induces `𝒪ˣ_K / N(𝒪ˣ_M) ≃ Gal(M/K)`. -/
theorem psi_surjective : Function.Surjective (psi hM hU hdeg s hs he) := by
  haveI := finiteDimensional_tower (p := p) K M
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  have h1 := Subgroup.index_ker (psi hM hU hdeg s hs he)
  rw [psi_ker] at h1
  have h2 : ((normGroup K M ⊓ unitGroup p K).subgroupOf (unitGroup p K)).index =
      Module.finrank K M := relIndex_unitNorms hM
  rw [← h1, h2, IsGalois.card_aut_eq_finrank]

end Psi

end PadicField
