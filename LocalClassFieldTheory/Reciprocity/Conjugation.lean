/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.NormCompat

/-!
# Conjugation functoriality of the reciprocity map

* `PadicField.abRec_norm_frobLift`: Neukirch's formula for `abRec`;
* `PadicField.abRec_ext`: homomorphisms `Kˣ → G` trivial on `N_{L/K} Lˣ` that agree on the
  Neukirch values `N_{Σ/K} π` of all Frobenius lifts agree;
* `PadicField.abRec_conj`: for a finite Galois `K'/K`, a finite abelian `L/K'` that is Galois over
  `K`, `g ∈ Gal(L/K)` and `x ∈ K'ˣ`: `abRec_L (g x) = g abRec_L(x) g⁻¹`.
-/

set_option linter.unusedSectionVars false

open IntermediateField Polynomial

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

section Generic

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]

variable (p) in
/-- A common multiple of the unramified degrees `cycDeg E` of the cyclic subextensions `E` of
`L`. -/
noncomputable def abDeg : ℕ :=
  haveI := finite_cycSub (L := L)
  haveI := Fintype.ofFinite (CycSub L)
  ∏ E : CycSub L, cycDeg p E.1

theorem abDeg_pos : 0 < abDeg p L := by
  haveI := finite_cycSub (L := L)
  haveI := Fintype.ofFinite (CycSub L)
  exact Finset.prod_pos fun E _ ↦ cycDeg_pos (p := p) E.1

theorem cycDeg_dvd_abDeg (E : CycSub L) : cycDeg p E.1 ∣ abDeg p L := by
  haveI := finite_cycSub (L := L)
  unfold abDeg
  exact Finset.dvd_prod_of_mem _ (@Finset.mem_univ _ (Fintype.ofFinite _) E)

/-- **Neukirch's formula for `abRec`**: let `D ⊇ L ⊔ K_s` be finite Galois with `abDeg L ∣ s`, and
`τ ∈ Gal(D/K)` a Frobenius lift whose fixed field `Σ` has `f(Σ/K) = 1`. Then
`abRec L (N_{Σ/K} π) = τ|_L` for every uniformiser `π` of `Σ`. -/
theorem abRec_norm_frobLift {s : ℕ} (hs0 : 0 < s) (hs : abDeg p L ∣ s)
    (D : IntermediateField K Ω) [FiniteDimensional K D] [IsGalois K D] (hLD : L ≤ D)
    (hsD : unramifiedOfDegree p K Ω s ≤ D) (τ : D ≃ₐ[K] D) (hτ : resHom hsD τ = frobT p K Ω s)
    (hf : f p K (fixedField (Subgroup.zpowers τ)) = 1)
    (π : fixedField (Subgroup.zpowers τ)) (hπ : v p π = 1) (y : Kˣ)
    (hy : (y : K) = Algebra.norm K π) : abRec p L y = resHom hLD τ := by
  have hπ0 : Algebra.norm K π ≠ 0 := hy ▸ y.ne_zero
  have hy' : y = Units.mk0 _ hπ0 := Units.ext hy
  symm
  rw [eq_abRec_iff]
  intro E
  rw [resHom_trans, hy']
  exact (cycRec_norm_frobLift E.1 hs0 ((cycDeg_dvd_abDeg L E).trans hs) D (E.2.1.trans hLD)
    hsD τ hτ hf π hπ hπ0).symm

/-- **Uniqueness**: two homomorphisms `Kˣ → G` which agree on `N_{L/K} Lˣ` and on the values
`y` of `abRec L` at Frobenius lifts `τ ∈ Gal(D/K)` agree. -/
theorem abRec_ext_of_frobLift {G : Type*} [Group G] (φ ψ : Kˣ →* G)
    (hker : ∀ x ∈ normGroup K L, φ x = ψ x) (D : IntermediateField K Ω) [FiniteDimensional K D]
    [IsGalois K D] (hLD : L ≤ D) {s : ℕ} (hsD : unramifiedOfDegree p K Ω s ≤ D)
    (key : ∀ τ : D ≃ₐ[K] D, resHom hsD τ = frobT p K Ω s →
      ∃ y : Kˣ, abRec p L y = resHom hLD τ ∧ φ y = ψ y) : φ = ψ := by
  have hker' : (abRec p L).ker ≤ MonoidHom.eqLocus φ ψ := by
    intro z hz
    rw [ker_abRec] at hz
    exact hker z hz
  have hrange : ∀ σ : L ≃ₐ[K] L, ∃ h ∈ MonoidHom.eqLocus φ ψ, abRec p L h = σ := by
    intro σ
    obtain ⟨φ₀, hφ₀⟩ := resHom_surjective hsD (frobT p K Ω s)
    obtain ⟨g, rfl⟩ := resHom_surjective hLD σ
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
      ((zpowers_frob (isUnramified_unramifiedOfDegree p K Ω s)).symm ▸ Subgroup.mem_top
        (resHom hsD g))
    obtain ⟨a, ha⟩ : ∃ a, a = g * φ₀ ^ (-j) * φ₀ := ⟨_, rfl⟩
    have h1 : resHom hsD a = frobT p K Ω s := by
      rw [ha, map_mul, map_mul, map_zpow, hφ₀, ← hj, zpow_neg, mul_inv_cancel, one_mul]
    have hg : g = a * φ₀⁻¹ * φ₀ ^ j := by
      rw [ha, mul_inv_cancel_right, zpow_neg, inv_mul_cancel_right]
    obtain ⟨ya, hya, hya'⟩ := key a h1
    obtain ⟨yφ, hyφ, hyφ'⟩ := key φ₀ hφ₀
    refine ⟨ya * yφ⁻¹ * yφ ^ j, ?_, ?_⟩
    · exact mul_mem (mul_mem hya' (inv_mem hyφ')) (zpow_mem hyφ' j)
    · rw [map_mul, map_mul, map_inv, map_zpow, hya, hyφ, hg, map_mul, map_mul, map_inv, map_zpow]
  refine MonoidHom.ext fun z ↦ ?_
  obtain ⟨h, hH, hh⟩ := hrange (abRec p L z)
  have hzh : z * h⁻¹ ∈ (abRec p L).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hh, mul_inv_cancel]
  have := mul_mem (hker' hzh) hH
  rw [inv_mul_cancel_right] at this
  exact this

/-- `abRec_ext_of_frobLift` with the values given by Neukirch's formula: it suffices that `φ` and
`ψ` agree on the norms of uniformisers of fixed fields of Frobenius lifts. -/
theorem abRec_ext {G : Type*} [Group G] (φ ψ : Kˣ →* G)
    (hker : ∀ x ∈ normGroup K L, φ x = ψ x) (D : IntermediateField K Ω) [FiniteDimensional K D]
    [IsGalois K D] (hLD : L ≤ D) {s : ℕ} (hsdef : f p K D = s) (hs : abDeg p L ∣ s)
    (hsD : unramifiedOfDegree p K Ω s ≤ D)
    (key : ∀ τ : D ≃ₐ[K] D, resHom hsD τ = frobT p K Ω s →
      ∀ π : fixedField (Subgroup.zpowers τ), v p π = 1 → ∀ y : Kˣ,
        (y : K) = Algebra.norm K π → φ y = ψ y) : φ = ψ := by
  have hs0 : 0 < s := hsdef ▸ f_pos
  refine abRec_ext_of_frobLift L φ ψ hker D hLD hsD fun τ hτ ↦ ?_
  have hf := f_fixedField_frobLift hs0 hsdef hsD τ hτ
  set Fx := fixedField (Subgroup.zpowers τ)
  haveI : Module.Free K Fx := Module.Free.of_divisionRing _ _
  have hπ := uniformizer_spec (p := p) (K := Fx)
  have hπ0 : Algebra.norm K (uniformizer p Fx) ≠ 0 := Algebra.norm_ne_zero_iff.2 hπ.ne_zero
  exact ⟨Units.mk0 _ hπ0, abRec_norm_frobLift L hs0 hs D hLD hsD τ hτ hf _ hπ _ rfl,
    key τ hτ _ hπ _ rfl⟩

end Generic

section Conj

variable (K' : IntermediateField K Ω) [FiniteDimensional K K'] [IsGalois K K']

/-- A `K`-automorphism of `D ⊇ K'` fixing `K'` pointwise, as an automorphism over `K'`. -/
noncomputable def autExtend {D : IntermediateField K Ω} (h : K' ≤ D) (ρ : D ≃ₐ[K] D)
    (hρ : ∀ x : K', (ρ ⟨x, h x.2⟩ : Ω) = x) : extendScalars h ≃ₐ[K'] extendScalars h :=
  { (ρ : D ≃ₐ[K] D) with commutes' := fun x ↦ Subtype.ext (hρ x) }

theorem autRestrict_autExtend {D : IntermediateField K Ω} (h : K' ≤ D) (ρ : D ≃ₐ[K] D)
    (hρ : ∀ x : K', (ρ ⟨x, h x.2⟩ : Ω) = x) : autRestrict K' h (autExtend K' h ρ hρ) = ρ :=
  AlgEquiv.ext fun _ ↦ rfl

/-- `K`-automorphisms of `D ⊇ K'` map `K'` to itself. -/
theorem apply_mem_of_le {D : IntermediateField K Ω} (h : K' ≤ D) (g : D ≃ₐ[K] D) (x : K') :
    (g ⟨x, h x.2⟩ : Ω) ∈ K' := by
  have h1 : ((resHom h g x : K') : Ω) = (g ⟨x, h x.2⟩ : Ω) := resHom_apply h g x
  exact h1 ▸ (resHom h g x).2

/-- Conjugates of automorphisms over `K'` by automorphisms over `K` fix `K'`. -/
theorem conj_autRestrict_apply {D : IntermediateField K Ω} (h : K' ≤ D)
    (τ : extendScalars h ≃ₐ[K'] extendScalars h) (g : D ≃ₐ[K] D) (x : K') :
    ((g * autRestrict K' h τ * g⁻¹) ⟨x, h x.2⟩ : Ω) = x := by
  have hy := apply_mem_of_le K' h g⁻¹ x
  have h1 : autRestrict K' h τ (g⁻¹ ⟨x, h x.2⟩) = g⁻¹ ⟨x, h x.2⟩ := by
    have := τ.commutes ⟨_, hy⟩
    exact Subtype.ext (congrArg Subtype.val this)
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1, ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

/-- The conjugate `g τ g⁻¹` of `τ ∈ Gal(D/K')` by `g ∈ Gal(D/K)`. -/
noncomputable def conjAut {D : IntermediateField K Ω} (h : K' ≤ D)
    (τ : extendScalars h ≃ₐ[K'] extendScalars h) (g : D ≃ₐ[K] D) :
    extendScalars h ≃ₐ[K'] extendScalars h :=
  autExtend K' h (g * autRestrict K' h τ * g⁻¹) (conj_autRestrict_apply K' h τ g)

theorem autRestrict_conjAut {D : IntermediateField K Ω} (h : K' ≤ D)
    (τ : extendScalars h ≃ₐ[K'] extendScalars h) (g : D ≃ₐ[K] D) :
    autRestrict K' h (conjAut K' h τ g) = g * autRestrict K' h τ * g⁻¹ :=
  autRestrict_autExtend K' h _ _

/-- An automorphism over `K'` acting on the roots of `X^(q^(f' m)) - X` as `x ↦ x^(q^f')`
restricts to the Frobenius of `K'_m`. -/
theorem resHom_eq_frobT_of_pow {D : IntermediateField K Ω} (h : K' ≤ D) {m : ℕ} (hm : 0 < m)
    (hmD : unramifiedOfDegree p K' Ω m ≤ extendScalars h)
    (τ : extendScalars h ≃ₐ[K'] extendScalars h)
    (hτ : ∀ z : D, (z : Ω) ^ q p K ^ (f p K K' * m) = z →
      (autRestrict K' h τ z : Ω) = (z : Ω) ^ q p K ^ f p K K') :
    resHom hmD τ = frobT p K' Ω m := by
  rw [resHom_eq_iff]
  let φ₁ : unramifiedOfDegree p K' Ω m →ₐ[K'] Ω :=
    (extendScalars h).val.comp (τ.toAlgHom.comp (inclusion hmD))
  let φ₂ : unramifiedOfDegree p K' Ω m →ₐ[K'] Ω :=
    (unramifiedOfDegree p K' Ω m).val.comp (frobT p K' Ω m).toAlgHom
  have key : φ₁ = φ₂ := by
    refine algHom_ext_of_eq_adjoin K' (unramifiedOfDegree_def p K' Ω m) fun z hz ↦ ?_
    rw [mem_rootSet_X_pow_sub_X (one_lt_q_pow hm)] at hz
    have hzK' : z ∈ unramifiedOfDegree p K' Ω m := mem_unramifiedOfDegree_of_pow_eq hm hz
    rw [q_baseChange, ← pow_mul] at hz
    simp only [φ₁, φ₂, AlgHom.comp_apply, coe_val, AlgEquiv.coe_toAlgHom]
    rw [frob_baseChange_apply K' hm ⟨z, hzK'⟩ hz]
    exact hτ ⟨z, hmD hzK'⟩ hz
  intro x
  exact DFunLike.congr_fun key x

/-- Conversely, an automorphism restricting to the Frobenius of `K'_m` acts on the roots of
`X^(q^(f' m)) - X` as `x ↦ x^(q^f')`. -/
theorem pow_of_resHom_eq_frobT {D : IntermediateField K Ω} (h : K' ≤ D) {m : ℕ} (hm : 0 < m)
    (hmD : unramifiedOfDegree p K' Ω m ≤ extendScalars h)
    (τ : extendScalars h ≃ₐ[K'] extendScalars h) (hτ : resHom hmD τ = frobT p K' Ω m)
    (z : D) (hz : (z : Ω) ^ q p K ^ (f p K K' * m) = z) :
    (autRestrict K' h τ z : Ω) = (z : Ω) ^ q p K ^ f p K K' := by
  have hzK' : (z : Ω) ∈ unramifiedOfDegree p K' Ω m :=
    mem_unramifiedOfDegree_of_pow_eq hm (by rwa [q_baseChange, ← pow_mul])
  have h1 := resHom_apply hmD τ ⟨z, hzK'⟩
  rw [hτ, frob_baseChange_apply K' hm _ hz] at h1
  exact h1.symm

/-- Conjugates of Frobenius lifts over `K'` by automorphisms over `K` are Frobenius lifts. -/
theorem resHom_conjAut {D : IntermediateField K Ω} (h : K' ≤ D) {m : ℕ} (hm : 0 < m)
    (hmD : unramifiedOfDegree p K' Ω m ≤ extendScalars h)
    (τ : extendScalars h ≃ₐ[K'] extendScalars h) (hτ : resHom hmD τ = frobT p K' Ω m)
    (g : D ≃ₐ[K] D) : resHom hmD (conjAut K' h τ g) = frobT p K' Ω m := by
  refine resHom_eq_frobT_of_pow K' h hm hmD _ fun z hz ↦ ?_
  set N := q p K ^ (f p K K' * m)
  set Q := q p K ^ f p K K'
  have hzD : z ^ N = z := Subtype.ext (by rw [IntermediateField.coe_pow, hz])
  have hw : ((g⁻¹ z : D) : Ω) ^ N = (g⁻¹ z : D) := by
    rw [← IntermediateField.coe_pow, ← map_pow, hzD]
  have h1 : autRestrict K' h τ (g⁻¹ z) = (g⁻¹ z) ^ Q :=
    Subtype.ext ((pow_of_resHom_eq_frobT K' h hm hmD τ hτ _ hw).trans
      (IntermediateField.coe_pow _ _ _).symm)
  rw [autRestrict_conjAut, AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1, map_pow,
    ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, IntermediateField.coe_pow]

/-- Conjugation maps fixed fields to fixed fields: `x ↦ g x`, `Fix(ρ) ≃ Fix(g ρ g⁻¹)`. -/
noncomputable def fixedFieldConj {D : IntermediateField K Ω} (g ρ ρ' : D ≃ₐ[K] D)
    (hρ' : ρ' = g * ρ * g⁻¹) :
    fixedField (Subgroup.zpowers ρ) ≃ₐ[K] fixedField (Subgroup.zpowers ρ') :=
  AlgEquiv.ofBijective
    { toFun := fun a ↦ ⟨g a.1, by
        have ha : ρ a.1 = a.1 := a.2 ⟨ρ, Subgroup.mem_zpowers ρ⟩
        have ha' : ρ' (g a.1) = g a.1 := by
          rw [hρ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g⁻¹, inv_mul_cancel,
            AlgEquiv.one_apply, ha]
        rintro ⟨_, i, rfl⟩
        exact zpow_apply_eq_of_apply_eq ha' i⟩
      map_one' := Subtype.ext (map_one g)
      map_mul' := fun a b ↦ Subtype.ext (map_mul g a.1 b.1)
      map_zero' := Subtype.ext (map_zero g)
      map_add' := fun a b ↦ Subtype.ext (map_add g a.1 b.1)
      commutes' := fun c ↦ Subtype.ext (g.commutes c) }
    ⟨fun a b hab ↦ Subtype.ext (g.injective (congrArg Subtype.val hab)),
      fun b ↦ ⟨⟨g⁻¹ b.1, by
        have hb₀ : ρ' b.1 = b.1 := b.2 ⟨_, Subgroup.mem_zpowers _⟩
        have hb : (g * ρ * g⁻¹) b.1 = b.1 := hρ' ▸ hb₀
        have hb' : ρ (g⁻¹ b.1) = g⁻¹ b.1 := by
          conv_rhs => rw [← hb]
          rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g⁻¹, inv_mul_cancel,
            AlgEquiv.one_apply]
        rintro ⟨_, i, rfl⟩
        exact zpow_apply_eq_of_apply_eq hb' i⟩, Subtype.ext (by
          change g (g⁻¹ b.1) = b.1
          rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply])⟩⟩

theorem fixedFieldConj_apply {D : IntermediateField K Ω} (g ρ ρ' : D ≃ₐ[K] D)
    (hρ' : ρ' = g * ρ * g⁻¹) (a : fixedField (Subgroup.zpowers ρ)) :
    (fixedFieldConj g ρ ρ' hρ' a : D) = g a := rfl

theorem coe_fixedFieldEquiv_symm {D : IntermediateField K Ω} (h : K' ≤ D)
    (τ : extendScalars h ≃ₐ[K'] extendScalars h)
    (b : fixedField (Subgroup.zpowers (autRestrict K' h τ))) :
    ((((fixedFieldEquiv K' h τ).symm b : fixedField (Subgroup.zpowers τ)) :
      extendScalars h) : Ω) = ((b : D) : Ω) :=
  congrArg (fun z : fixedField (Subgroup.zpowers (autRestrict K' h τ)) ↦ ((z : D) : Ω))
    ((fixedFieldEquiv K' h τ).apply_symm_apply b)

/-- Uniformisers of `Fix(τ)` are transported to uniformisers of `Fix(g τ g⁻¹)`, compatibly with
the norms to `K'`. -/
theorem exists_conj_uniformizer {D : IntermediateField K Ω} [FiniteDimensional K D]
    (hK'D : K' ≤ D) [FiniteDimensional K' (extendScalars hK'D)]
    (τ : extendScalars hK'D ≃ₐ[K'] extendScalars hK'D) (ĝ : D ≃ₐ[K] D)
    (π : fixedField (Subgroup.zpowers τ)) (hπ : v p π = 1) :
    ∃ π' : fixedField (Subgroup.zpowers (conjAut K' hK'D τ ĝ)), v p π' = 1 ∧
      Algebra.norm K' π' = resHom hK'D ĝ (Algebra.norm K' π) := by
  obtain ⟨c, hc⟩ : ∃ c, c = fixedFieldConj ĝ (autRestrict K' hK'D τ)
      (autRestrict K' hK'D (conjAut K' hK'D τ ĝ)) (autRestrict_conjAut K' hK'D τ ĝ) :=
    ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e₂, e₂ = (fixedFieldEquiv K' hK'D τ).trans
      (c.trans (fixedFieldEquiv K' hK'D (conjAut K' hK'D τ ĝ)).symm) := ⟨_, rfl⟩
  have hπ' : v p (e₂ π) = 1 := by
    have h1 := v_fixedFieldEquiv (p := p) K' hK'D (conjAut K' hK'D τ ĝ) (e₂ π)
    rw [he₂, AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply] at h1
    rw [he₂, AlgEquiv.trans_apply, AlgEquiv.trans_apply, ← h1, v_algEquiv, v_fixedFieldEquiv, hπ]
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : K' ≃+* K', e₁ = (resHom hK'D ĝ).toRingEquiv := ⟨_, rfl⟩
  have he : (algebraMap K' _).comp e₁.toRingHom =
      e₂.toRingEquiv.toRingHom.comp (algebraMap K' (fixedField (Subgroup.zpowers τ))) := by
    ext k
    change (((e₁ k : K') : Ω)) = ((((e₂ (algebraMap K' _ k)) : fixedField _) :
      extendScalars hK'D) : Ω)
    rw [he₂, AlgEquiv.trans_apply, AlgEquiv.trans_apply, coe_fixedFieldEquiv_symm, hc,
      fixedFieldConj_apply, he₁]
    exact resHom_apply hK'D ĝ k
  refine ⟨e₂ π, hπ', ?_⟩
  have h1 := Algebra.norm_eq_of_equiv_equiv e₁ e₂.toRingEquiv he π
  have h2 : ∀ x, resHom hK'D ĝ x = e₁ x := fun x ↦ by rw [he₁]; rfl
  rw [h2, h1]
  exact (e₁.apply_symm_apply _).symm

end Conj

section ConjRec

variable (K' : IntermediateField K Ω) [FiniteDimensional K K'] [IsGalois K K']
variable (L : IntermediateField K' Ω) [FiniteDimensional K' L] [IsAbelianGalois K' L]

theorem le_restrictScalars : K' ≤ L.restrictScalars K := fun x hx ↦ L.algebraMap_mem ⟨x, hx⟩

/-- `Gal(L/K') → Gal(L/K)`. -/
noncomputable def toK : (L ≃ₐ[K'] L) →* (L.restrictScalars K ≃ₐ[K] L.restrictScalars K) where
  toFun σ := (σ.restrictScalars K : L.restrictScalars K ≃ₐ[K] L.restrictScalars K)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toK_apply (σ : L ≃ₐ[K'] L) (y : L.restrictScalars K) :
    ((toK K' L σ y : L.restrictScalars K) : Ω) = (σ y : Ω) := rfl

variable [Normal K (L.restrictScalars K)]

/-- `K`-automorphisms of `L` map norms from `L` to `K'` to norms. -/
theorem units_map_mem_normGroup (g : L.restrictScalars K ≃ₐ[K] L.restrictScalars K) (x : K'ˣ)
    (hx : x ∈ normGroup K' L) :
    Units.map (resHom (le_restrictScalars K' L) g : K' →* K') x ∈ normGroup K' L := by
  obtain ⟨z, hz⟩ := (mem_normGroup_iff).1 hx
  set e₁ : K' ≃+* K' := (resHom (le_restrictScalars K' L) g).toRingEquiv
  set e₂ : L ≃+* L := (g : L.restrictScalars K ≃ₐ[K] L.restrictScalars K).toRingEquiv
  have he : (algebraMap K' L).comp (e₁ : K' →+* K') = (e₂ : L →+* L).comp (algebraMap K' L) := by
    ext k
    exact resHom_apply (le_restrictScalars K' L) g k
  have h1 := Algebra.norm_eq_of_equiv_equiv e₁ e₂ he (z : L)
  refine (mem_normGroup_iff).2 ⟨Units.map (e₂ : L →* L) z, ?_⟩
  change Algebra.norm K' (e₂ (z : L)) = e₁ (x : K')
  rw [← hz, h1, RingEquiv.apply_symm_apply]

theorem toK_resHom {D : IntermediateField K Ω} (hK'D : K' ≤ D) (hLD : L ≤ extendScalars hK'D)
    (hLKD : L.restrictScalars K ≤ D) [Normal K' L]
    (τ : extendScalars hK'D ≃ₐ[K'] extendScalars hK'D) :
    toK K' L (resHom hLD τ) = resHom hLKD (autRestrict K' hK'D τ) := by
  ext z
  rw [toK_apply, resHom_apply, resHom_apply]
  rfl

theorem toK_resHom_conjAut {D : IntermediateField K Ω} (hK'D : K' ≤ D)
    (hLD : L ≤ extendScalars hK'D) (hLKD : L.restrictScalars K ≤ D)
    (τ : extendScalars hK'D ≃ₐ[K'] extendScalars hK'D) (ĝ : D ≃ₐ[K] D) :
    toK K' L (resHom hLD (conjAut K' hK'D τ ĝ)) =
      resHom hLKD ĝ * toK K' L (resHom hLD τ) * (resHom hLKD ĝ)⁻¹ := by
  rw [toK_resHom K' L hK'D hLD hLKD, toK_resHom K' L hK'D hLD hLKD, autRestrict_conjAut,
    map_mul, map_mul, map_inv]

set_option maxHeartbeats 600000 in
-- The proof works with reciprocity maps over `K'` and fields over both `K` and `K'`; instance
-- synthesis alone exceeds the default heartbeat limit.
/-- Conjugation functoriality, for an automorphism of a finite Galois `D ⊇ L`. -/
theorem abRec_conj_aux {D : IntermediateField K Ω} [FiniteDimensional K D] [IsGalois K D]
    (hK'D : K' ≤ D) (hLD : L ≤ extendScalars hK'D) (hLKD : L.restrictScalars K ≤ D)
    [FiniteDimensional K' (extendScalars hK'D)] [IsGalois K' (extendScalars hK'D)]
    (hs : abDeg p L ∣ f p K' (extendScalars hK'D)) (ĝ : D ≃ₐ[K] D) (w : K'ˣ) :
    toK K' L (abRec p L (Units.map (resHom hK'D ĝ : K' →* K') w)) =
      resHom hLKD ĝ * toK K' L (abRec p L w) * (resHom hLKD ĝ)⁻¹ := by
  obtain ⟨g, hg⟩ : ∃ g, g = resHom hLKD ĝ := ⟨_, rfl⟩
  have hσ : resHom (le_restrictScalars K' L) g = resHom hK'D ĝ := hg ▸ resHom_trans _ _ _
  obtain ⟨σU, hσU⟩ : ∃ σU : K'ˣ →* K'ˣ, σU = Units.map (resHom hK'D ĝ : K' →* K') := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : K'ˣ →* (L.restrictScalars K ≃ₐ[K] L.restrictScalars K),
      φ = (MulAut.conj g⁻¹).toMonoidHom.comp ((toK K' L).comp ((abRec p L).comp σU)) :=
    ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : K'ˣ →* (L.restrictScalars K ≃ₐ[K] L.restrictScalars K),
      ψ = (toK K' L).comp (abRec p L) := ⟨_, rfl⟩
  suffices hφψ : φ = ψ by
    have := DFunLike.congr_fun hφψ w
    rw [hφ, hψ] at this
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv] at this
    rw [← hσU, ← this, ← hg]
    group
  obtain ⟨s, hsdef⟩ : ∃ s, f p K' (extendScalars hK'D) = s := ⟨_, rfl⟩
  have hs0 : 0 < s := hsdef ▸ f_pos
  have hsD : unramifiedOfDegree p K' Ω s ≤ extendScalars hK'D :=
    unramifiedOfDegree_le_of_f_eq (extendScalars hK'D) hsdef
  refine abRec_ext L φ ψ ?_ (extendScalars hK'D) hLD hsdef (hsdef ▸ hs) hsD ?_
  · intro x hx
    have hx' : σU x ∈ normGroup K' L := by
      rw [hσU, ← hσ]; exact units_map_mem_normGroup K' L g x hx
    rw [hφ, hψ]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    rw [(MonoidHom.mem_ker.1 ((ker_abRec (p := p) L).symm ▸ hx' :
        σU x ∈ (abRec p L).ker)),
      (MonoidHom.mem_ker.1 ((ker_abRec (p := p) L).symm ▸ hx : x ∈ (abRec p L).ker))]
    simp
  intro τ hτ π hπ y hy
  have hψy : abRec p L y = resHom hLD τ := abRec_norm_frobLift L hs0 (hsdef ▸ hs)
    (extendScalars hK'D) hLD hsD τ hτ (f_fixedField_frobLift hs0 hsdef hsD τ hτ) π hπ y hy
  have hτ' : resHom hsD (conjAut K' hK'D τ ĝ) = frobT p K' Ω s :=
    resHom_conjAut K' hK'D hs0 hsD τ hτ ĝ
  have hf' := f_fixedField_frobLift hs0 hsdef hsD _ hτ'
  obtain ⟨π', hπ', hNπ'⟩ := exists_conj_uniformizer (p := p) K' hK'D τ ĝ π hπ
  have hy' : ((σU y : K'ˣ) : K') = Algebra.norm K' π' := by
    rw [hNπ', ← hy, hσU]
    rfl
  have hφy : abRec p L (σU y) = resHom hLD (conjAut K' hK'D τ ĝ) :=
    abRec_norm_frobLift L hs0 (hsdef ▸ hs) (extendScalars hK'D) hLD hsD _ hτ' hf' π' hπ'
      (σU y) hy'
  have hc := toK_resHom_conjAut K' L hK'D hLD hLKD τ ĝ
  rw [hφ, hψ]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]
  rw [hφy, hψy, hc, ← hg]
  group

include hp in
/-- **Conjugation functoriality of the reciprocity map**: let `K'/K` be finite Galois, `L/K'`
finite abelian with `L/K` Galois. For `g ∈ Gal(L/K)` and `w ∈ K'ˣ`,
`abRec_L (g w) = g abRec_L(w) g⁻¹` in `Gal(L/K)`. -/
theorem abRec_conj (g : L.restrictScalars K ≃ₐ[K] L.restrictScalars K) (w : K'ˣ) :
    toK K' L (abRec p L (Units.map (resHom (le_restrictScalars K' L) g : K' →* K') w)) =
      g * toK K' L (abRec p L w) * g⁻¹ := by
  haveI : FiniteDimensional K (L.restrictScalars K) :=
    (FiniteDimensional.trans K K' L : FiniteDimensional K L)
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  haveI : IsGalois K (L.restrictScalars K) := ⟨⟩
  obtain ⟨s₀, hs₀def⟩ : ∃ s₀, s₀ = abDeg p L := ⟨_, rfl⟩
  have hs₀ : 0 < s₀ := hs₀def ▸ abDeg_pos L
  obtain ⟨D, hDdef⟩ : ∃ D,
      D = L.restrictScalars K ⊔ unramifiedOfDegree p K Ω (f p K K' * s₀) := ⟨_, rfl⟩
  haveI : FiniteDimensional K D := hDdef ▸ inferInstance
  haveI : IsGalois K D := hDdef ▸ inferInstance
  have hLKD : L.restrictScalars K ≤ D := hDdef ▸ le_sup_left
  have hK'D : K' ≤ D := (le_restrictScalars K' L).trans hLKD
  have hLD : L ≤ extendScalars hK'D := fun x hx ↦ hLKD hx
  haveI : FiniteDimensional K (extendScalars hK'D) := (inferInstance : FiniteDimensional K D)
  haveI : FiniteDimensional K' (extendScalars hK'D) :=
    FiniteDimensional.right K K' (extendScalars hK'D)
  haveI : IsGalois K (extendScalars hK'D) := (inferInstance : IsGalois K D)
  haveI : IsGalois K' (extendScalars hK'D) :=
    IsGalois.tower_top_of_isGalois K K' (extendScalars hK'D)
  have hs : abDeg p L ∣ f p K' (extendScalars hK'D) := by
    have h1 : unramifiedOfDegree p K' Ω s₀ ≤ extendScalars hK'D := by
      intro y hy
      have : y ∈ (unramifiedOfDegree p K' Ω s₀).restrictScalars K := hy
      rw [restrictScalars_unramifiedOfDegree K' hs₀] at this
      change y ∈ D
      rw [hDdef]
      exact sup_le ((le_restrictScalars K' L).trans le_sup_left) le_sup_right this
    have := f_dvd_f_of_le (p := p) h1
    rwa [(isUnramified_unramifiedOfDegree p K' Ω s₀).f_eq,
      finrank_unramifiedOfDegree p K' Ω hs₀, hs₀def] at this
  obtain ⟨ĝ, hĝ⟩ := resHom_surjective hLKD g
  have hσ : resHom (le_restrictScalars K' L) g = resHom hK'D ĝ := by rw [← hĝ, resHom_trans]
  have := abRec_conj_aux K' L hK'D hLD hLKD hs ĝ w
  rw [hĝ] at this
  rw [hσ]
  exact this

end ConjRec

end PadicField
