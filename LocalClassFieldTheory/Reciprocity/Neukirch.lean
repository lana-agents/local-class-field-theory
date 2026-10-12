/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.LevelMap
import LocalClassFieldTheory.Galois.CosetNorm

/-!
# Neukirch's formula at a standard level

Let `F = M U` be a standard extension, `g ∈ Gal(F/U)`, `k ≥ 1` with `[M : K] k ∣ [U : K]`, and
`τ = (g, φ^k) ∈ Gal(F/K)` (a "Frobenius lift"). Let `Σ` be the fixed field of `τ`.

* `PadicField.orderOf_tau`: `τ` has order `[U : K] / k`;
* `PadicField.algebraMap_norm_tau`: for `y ∈ Σ`,
  `N_{Σ/K}(y) = ∏_{j<k} φ^j (N_{F/U} y)` (coset representatives `(g', φ^j)`, `j < k`).
-/

set_option linter.unusedSectionVars false

open IntermediateField Polynomial

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]

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

theorem orderOf_stdFrob : orderOf (stdFrob hM hU hdeg) = Module.finrank K U := by
  rw [stdFrob, orderOf_frob, std_finrank_M hM hU hdeg]

theorem orderOf_dvd_of_U (g : F ≃ₐ[U] F) : orderOf g ∣ Module.finrank K M := by
  haveI := finiteDimensional_tower (p := p) U F
  haveI : IsGalois U F := IsGalois.tower_top_of_isGalois K U F
  rw [← std_finrank_U hM hU hdeg, ← IsGalois.card_aut_eq_finrank]
  exact orderOf_dvd_natCard g

variable (g : F ≃ₐ[U] F) (k : ℕ) (hk : 0 < k)
  (hke : Module.finrank K M * k ∣ Module.finrank K U)

omit hk hke in
/-- The Frobenius lift `τ = (g, φ^k)`. -/
noncomputable def tau : F ≃ₐ[K] F := stdProd hM hU hdeg (g, stdFrob hM hU hdeg ^ k)

include hk hke

theorem orderOf_tau :
    orderOf (tau hM hU hdeg g k) = Module.finrank K U / k := by
  have hkt : k ∣ Module.finrank K U := (Dvd.intro_left _ rfl).trans hke
  rw [tau, MulEquiv.orderOf_eq, Prod.orderOf_mk,
    orderOf_pow_of_dvd hk.ne' (by rw [orderOf_stdFrob]; exact hkt), orderOf_stdFrob]
  apply Nat.lcm_eq_right
  refine (orderOf_dvd_of_U hM hU hdeg g).trans ?_
  obtain ⟨c, hc⟩ := hke
  rw [hc, mul_comm (Module.finrank K M) k, mul_assoc, Nat.mul_div_cancel_left _ hk]
  exact Dvd.intro _ rfl


theorem index_zpowers_tau :
    (Subgroup.zpowers (tau hM hU hdeg g k)).index = Module.finrank K M * k := by
  haveI := finiteDimensional_tower (p := p) K F
  have h1 := Subgroup.index_mul_card (Subgroup.zpowers (tau hM hU hdeg g k))
  rw [Nat.card_zpowers, orderOf_tau hM hU hdeg g k hk hke, IsGalois.card_aut_eq_finrank,
    hdeg] at h1
  have hkt : k ∣ Module.finrank K U := (Dvd.intro_left _ rfl).trans hke
  obtain ⟨c, hc⟩ := hkt
  have hc0 : 0 < c := by
    haveI := finiteDimensional_tower (p := p) K U
    have : 0 < Module.finrank K U := Module.finrank_pos
    rw [hc] at this
    exact Nat.pos_of_mul_pos_left this
  rw [hc, Nat.mul_div_cancel_left _ hk] at h1
  have : Module.finrank K M * (k * c) = (Module.finrank K M * k) * c := by ring
  rw [this] at h1
  exact Nat.eq_of_mul_eq_mul_right hc0 h1

omit hk hke in
/-- The parametrisation `(g', j) ↦ (g', φ^j)` of the coset representatives. -/
noncomputable def tauRep (gj : (F ≃ₐ[U] F) × ℕ) : F ≃ₐ[K] F :=
  stdProd hM hU hdeg (gj.1, stdFrob hM hU hdeg ^ gj.2)

variable [FiniteDimensional U F] [DecidableEq (F ≃ₐ[K] F)]

theorem tauRep_injOn :
    Set.InjOn (tauRep hM hU hdeg)
      (Set.univ ×ˢ Set.Iio k : Set ((F ≃ₐ[U] F) × ℕ)) := by
  rintro ⟨g₁, j₁⟩ h₁ ⟨g₂, j₂⟩ h₂ heq
  simp only [Set.mem_prod, Set.mem_univ, Set.mem_Iio, true_and] at h₁ h₂
  have := (stdProd hM hU hdeg).injective heq
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, hj⟩ := this
  have hkt : k ≤ Module.finrank K U :=
    Nat.le_of_dvd (by
      haveI := finiteDimensional_tower (p := p) K U
      exact Module.finrank_pos) ((Dvd.intro_left _ rfl).trans hke)
  have := pow_injOn_Iio_orderOf (x := stdFrob hM hU hdeg)
    (by rw [Set.mem_Iio, orderOf_stdFrob]; omega) (by rw [Set.mem_Iio, orderOf_stdFrob]; omega) hj
  rw [this]

theorem tauRep_injOn_quotient :
    Set.InjOn (QuotientGroup.mk : (F ≃ₐ[K] F) → _ ⧸ Subgroup.zpowers (tau hM hU hdeg g k))
      ((Finset.univ ×ˢ Finset.range k).image (tauRep hM hU hdeg) :
        Finset (F ≃ₐ[K] F)) := by
  intro a ha b hb hab
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
    Finset.mem_univ, Finset.mem_range, true_and] at ha hb
  obtain ⟨⟨g₁, j₁⟩, hj₁, rfl⟩ := ha
  obtain ⟨⟨g₂, j₂⟩, hj₂, rfl⟩ := hb
  rw [QuotientGroup.eq, Subgroup.mem_zpowers_iff] at hab
  obtain ⟨i, hi⟩ := hab
  simp only [tau, tauRep] at hi
  rw [← map_zpow, ← map_inv, ← map_mul] at hi
  have hi' := (stdProd hM hU hdeg).injective hi
  have hg := congrArg (MonoidHom.fst _ _) hi'
  have hφ := congrArg (MonoidHom.snd _ _) hi'
  rw [map_zpow, map_mul, map_inv] at hg hφ
  simp only [MonoidHom.coe_fst, MonoidHom.coe_snd] at hg hφ
  -- the Frobenius components
  replace hφ : stdFrob hM hU hdeg ^ ((k : ℤ) * i) = stdFrob hM hU hdeg ^ (-(j₁ : ℤ) + j₂) := by
    rw [zpow_mul, zpow_natCast, hφ, zpow_add, zpow_natCast, zpow_neg, zpow_natCast]
  rw [zpow_eq_zpow_iff_modEq, orderOf_stdFrob] at hφ
  have hkt : (k : ℤ) ∣ (Module.finrank K U : ℤ) := by
    exact_mod_cast (Dvd.intro_left _ rfl).trans hke
  have hdk : (k : ℤ) ∣ (j₂ : ℤ) - j₁ := by
    have h1 := (Int.ModEq.dvd hφ)
    have h2 : (k : ℤ) ∣ (-(j₁ : ℤ) + j₂) - (k : ℤ) * i := hkt.trans h1
    have h3 : (k : ℤ) ∣ (k : ℤ) * i := dvd_mul_right _ _
    have := dvd_add h2 h3
    rw [sub_add_cancel] at this
    rwa [show -(j₁ : ℤ) + j₂ = (j₂ : ℤ) - j₁ by ring] at this
  have hj : j₁ = j₂ := by
    obtain ⟨c, hc⟩ := hdk
    have hc0 : c = 0 := by
      by_contra hne
      have : (k : ℤ) ≤ |(k : ℤ) * c| := by
        rw [abs_mul, abs_of_pos (by exact_mod_cast hk)]
        exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hne)
      rw [← hc] at this
      have : |(j₂ : ℤ) - j₁| < k := by rw [abs_sub_lt_iff]; omega
      omega
    rw [hc0, mul_zero] at hc
    omega
  subst hj
  -- now `g^i = g₁⁻¹ g₂` and `t ∣ k i`
  have hti : (Module.finrank K U : ℤ) ∣ (k : ℤ) * i := by
    have := Int.ModEq.dvd hφ
    simpa using this
  have hgi : g ^ i = 1 := by
    obtain ⟨c, hc⟩ := hke
    rw [orderOf_dvd_iff_zpow_eq_one.symm]
    refine (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_U hM hU hdeg g)).trans ?_
    rw [hc] at hti
    push_cast at hti
    have : (Module.finrank K M : ℤ) * c ∣ i := by
      have hk0 : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
      obtain ⟨d, hd⟩ := hti
      refine ⟨d, ?_⟩
      have := hd
      rw [show (Module.finrank K M : ℤ) * k * c * d = k * ((Module.finrank K M : ℤ) * c * d) by
        ring] at this
      exact mul_left_cancel₀ hk0 this
    exact (dvd_mul_right _ _).trans this
  rw [hgi] at hg
  simp only [tauRep]
  congr 2
  exact (inv_mul_eq_one.1 hg.symm)


/-- **Norm from the fixed field of a Frobenius lift**:
`N_{Σ/K}(y) = ∏_{j<k} φ^j (N_{F/U} y)`. -/
theorem algebraMap_norm_tau (y : fixedField (Subgroup.zpowers (tau hM hU hdeg g k))) :
    algebraMap K F (Algebra.norm K y) = ∏ j ∈ Finset.range k,
      (stdFrob hM hU hdeg ^ j) (algebraMap U F (Algebra.norm U (y : F))) := by
  haveI := finiteDimensional_tower (p := p) K F
  haveI : IsGalois U F := IsGalois.tower_top_of_isGalois K U F
  have hinjOn : Set.InjOn (tauRep hM hU hdeg)
      ((Finset.univ ×ˢ Finset.range k : Finset ((F ≃ₐ[U] F) × ℕ)) :
        Set ((F ≃ₐ[U] F) × ℕ)) := by
    have := tauRep_injOn hM hU hdeg k hk hke
    simpa [Finset.coe_product] using this
  have hcard : ((Finset.univ ×ˢ Finset.range k).image (tauRep hM hU hdeg)).card =
      (Subgroup.zpowers (tau hM hU hdeg g k)).index := by
    rw [Finset.card_image_of_injOn hinjOn, Finset.card_product, Finset.card_univ,
      Finset.card_range, index_zpowers_tau hM hU hdeg g k hk hke, Fintype.card_eq_nat_card,
      IsGalois.card_aut_eq_finrank, std_finrank_U hM hU hdeg]
  rw [algebraMap_norm_eq_prod_of_injOn _ (tauRep_injOn_quotient hM hU hdeg g k hk hke) hcard y,
    Finset.prod_image fun a ha b hb h ↦ hinjOn ha hb h, Finset.prod_product, Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [Algebra.norm_eq_prod_automorphisms, map_prod]
  refine Finset.prod_congr rfl fun g' _ ↦ ?_
  change g' ((stdFrob hM hU hdeg ^ j) (y : F)) = _
  rw [std_comm hM hU hdeg]


omit hk hke [FiniteDimensional U F] [DecidableEq (F ≃ₐ[K] F)] hM hU hdeg in
/-- Telescoping: `a(∏_{j<k} a^j ξ) / ∏_{j<k} a^j ξ = a^k ξ / ξ`. -/
theorem uMap_prod_pow_div {R : Type*} [Field R] [Algebra R F] (a : F ≃ₐ[R] F) (ξ : Fˣ)
    (n : ℕ) : uMap a (∏ j ∈ Finset.range n, uMap (a ^ j) ξ) / ∏ j ∈ Finset.range n,
      uMap (a ^ j) ξ = uMap (a ^ n) ξ / ξ := by
  rw [map_prod, ← Finset.prod_div_distrib]
  have : ∀ j, uMap a (uMap (a ^ j) ξ) = uMap (a ^ (j + 1)) ξ := fun j ↦ by
    ext; simp [pow_succ', AlgEquiv.mul_apply]
  simp_rw [this]
  rw [Finset.prod_range_div (fun j ↦ uMap (a ^ j) ξ) n]
  congr 1


omit hk hke [FiniteDimensional U F] [DecidableEq (F ≃ₐ[K] F)] hM hU hdeg in
theorem v_galois {R : Type*} [Field R] [Algebra ℚ_[p] R] [Algebra R F]
    [IsScalarTower ℚ_[p] R F] (a : F ≃ₐ[R] F) (x : F) : v p (a x) = v p x := by
  by_cases hx : x = 0
  · simp [hx]
  exact (nrm_eq_iff_v_eq ((map_ne_zero_iff _ a.injective).2 hx) hx).1
    (nrm_algEquiv_tower (p := p) R F a x)

omit hk hke [FiniteDimensional U F] [DecidableEq (F ≃ₐ[K] F)] hM hU hdeg in
theorem v_prod {ι : Type*} (t : Finset ι) (f : ι → F) (hf : ∀ i, f i ≠ 0) :
    v p (∏ i ∈ t, f i) = ∑ i ∈ t, v p (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v_mul (hf a) (Finset.prod_ne_zero_iff.2 fun i _ ↦ hf i), ih]

omit hk hke [FiniteDimensional U F] [DecidableEq (F ≃ₐ[K] F)] in
theorem norm_U_galois_M (h : F ≃ₐ[M] F) (z : F) :
    algebraMap U F (Algebra.norm U (h z)) = h (algebraMap U F (Algebra.norm U z)) := by
  haveI := finiteDimensional_tower (p := p) U F
  haveI : IsGalois U F := IsGalois.tower_top_of_isGalois K U F
  rw [Algebra.norm_eq_prod_automorphisms, Algebra.norm_eq_prod_automorphisms, map_prod]
  exact Finset.prod_congr rfl fun g' _ ↦ std_comm hM hU hdeg g' h z


section Unram

omit hk hke [FiniteDimensional U F] [DecidableEq (F ≃ₐ[K] F)] in
/-- Elements of `Gal(F/U)` act trivially on residues. -/
theorem residue_U_smul (g : F ≃ₐ[U] F) (z : 𝒪 p F) :
    IsLocalRing.residue _ (g • z) = IsLocalRing.residue _ z := by
  haveI := finiteDimensional_tower (p := p) U F
  haveI : IsGalois U F := IsGalois.tower_top_of_isGalois K U F
  have hf : f p U F = 1 := by
    have h1 := e_mul_f (p := p) (K := U) (L := F)
    rw [std_e_U hM hU hdeg] at h1
    exact (Nat.mul_eq_left Module.finrank_pos.ne').1 h1
  have h1 : residueGal p U F g = 1 := by
    have hc : Nat.card (𝓴 p F ≃ₐ[𝓴 p U] 𝓴 p F) = 1 := by rw [card_gal_residue, hf]
    haveI := (Nat.card_eq_one_iff_unique.1 hc).1
    exact Subsingleton.elim _ _
  have h2 : g ∈ inertia p U F := by rw [← ker_residueGal]; exact h1
  rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← neg_mem_iff,
    neg_sub]
  exact (mem_inertia_iff g).1 h2 z

omit hk hke [FiniteDimensional U F] [DecidableEq (F ≃ₐ[K] F)] in
/-- Powers of the Frobenius act on residues by `x ↦ x ^ (q ^ j)`. -/
theorem residue_stdFrob_pow_smul (j : ℕ) (z : 𝒪 p F) :
    IsLocalRing.residue _ ((stdFrob hM hU hdeg ^ j) • z) =
      IsLocalRing.residue _ z ^ (q p K ^ j) := by
  have hqM : q p M = q p K := by
    have hf : f p K M = 1 := by
      have h1 := e_mul_f (p := p) (K := K) (L := M)
      rw [hM] at h1
      haveI := finiteDimensional_tower (p := p) K M
      exact (Nat.mul_eq_left Module.finrank_pos.ne').1 h1
    rw [q_eq_pow_f (K := K) (L := M), hf, pow_one]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_smul]
    have := frob_spec (std_isUnramified_top hM hU hdeg) ((stdFrob hM hU hdeg ^ j) • z)
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at this
    rw [show stdFrob hM hU hdeg = frob (std_isUnramified_top hM hU hdeg) from rfl] at ih this ⊢
    rw [this, map_pow, ih, hqM, ← pow_mul, ← pow_succ]

/-- The residue degree of the fixed field of `τ` is at most `k`. -/
theorem f_fixedField_tau_le : f p K (fixedField (Subgroup.zpowers (tau hM hU hdeg g k))) ≤ k := by
  classical
  set Sig := fixedField (Subgroup.zpowers (tau hM hU hdeg g k))
  set Q := q p K ^ k
  have hq := one_lt_q p K
  have hQ : 1 < Q := Nat.one_lt_pow hk.ne' hq
  let ι : 𝓴 p Sig →+* 𝓴 p F := algebraMap _ _
  have hroot : ∀ a : 𝓴 p Sig, ι a ^ Q = ι a := by
    intro a
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective a
    set xF := algebraMap (𝒪 p Sig) (𝒪 p F) x
    have hfix : (tau hM hU hdeg g k) (xF : F) = xF :=
      (x : Sig).2 ⟨tau hM hU hdeg g k, Subgroup.mem_zpowers _⟩
    have h1 : g • ((stdFrob hM hU hdeg ^ k) • xF) = xF := Integers.ext hfix
    change IsLocalRing.residue _ xF ^ Q = IsLocalRing.residue _ xF
    rw [← residue_stdFrob_pow_smul hM hU hdeg k xF, ← residue_U_smul hM hU hdeg g, h1]
  -- count
  haveI := Fintype.ofFinite (𝓴 p Sig)
  have hcard : Nat.card (𝓴 p Sig) ≤ Q := by
    set P : (𝓴 p F)[X] := X ^ Q - X
    have hP : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hQ
    have hdeg' : P.natDegree = Q := FiniteField.X_pow_card_sub_X_natDegree_eq _ hQ
    have hinj : Function.Injective ι := ι.injective
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ,
      ← Finset.card_image_of_injective _ hinj]
    calc (Finset.univ.image ι).card ≤ P.roots.toFinset.card := by
          refine Finset.card_le_card fun z hz ↦ ?_
          obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hz
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot,
            Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, hroot, sub_self]
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ Q := hdeg' ▸ Polynomial.card_roots' P
  have hqS : q p Sig = q p K ^ f p K Sig := q_eq_pow_f
  rw [q] at hqS
  rw [hqS] at hcard
  exact (Nat.pow_le_pow_iff_right hq).1 hcard

/-- `F` is unramified over the fixed field of `τ`: there is `y ∈ Σ` with `v_F(y) = 1`. -/
theorem exists_v_eq_one_tau :
    ∃ y : fixedField (Subgroup.zpowers (tau hM hU hdeg g k)), v p (y : F) = 1 := by
  set Sig := fixedField (Subgroup.zpowers (tau hM hU hdeg g k))
  haveI := finiteDimensional_tower (p := p) K F
  have hdegS : Module.finrank K Sig = Module.finrank K M * k := by
    have h1 := Module.finrank_mul_finrank K Sig F
    rw [IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers,
      orderOf_tau hM hU hdeg g k hk hke, hdeg] at h1
    have hkt : k ∣ Module.finrank K U := (Dvd.intro_left _ rfl).trans hke
    obtain ⟨c, hc⟩ := hkt
    have hc0 : 0 < c := by
      haveI := finiteDimensional_tower (p := p) K U
      have : 0 < Module.finrank K U := Module.finrank_pos
      rw [hc] at this
      exact Nat.pos_of_mul_pos_left this
    rw [hc, Nat.mul_div_cancel_left _ hk] at h1
    have : Module.finrank K M * (k * c) = (Module.finrank K M * k) * c := by ring
    rw [this] at h1
    exact Nat.eq_of_mul_eq_mul_right hc0 h1
  have hf : f p K Sig ≤ k := f_fixedField_tau_le hM hU hdeg g k hk hke
  have heS : e p K Sig ∣ Module.finrank K M := by
    rw [← (std_e hM hU hdeg).1]
    exact ⟨_, (e_mul_e (p := p) (K := K) (E := Sig) (L := F)).symm⟩
  have hef := e_mul_f (p := p) (K := K) (L := Sig)
  rw [hdegS] at hef
  have he : e p K Sig = Module.finrank K M := by
    have hle := Nat.le_of_dvd (by haveI := finiteDimensional_tower (p := p) K M
                                  exact Module.finrank_pos) heS
    by_contra hne
    have hlt := lt_of_le_of_ne hle hne
    have h2 := Nat.mul_lt_mul_of_lt_of_le hlt hf hk
    omega
  have heF : e p Sig F = 1 := by
    have h3 := e_mul_e (p := p) (K := K) (E := Sig) (L := F)
    rw [he, (std_e hM hU hdeg).1] at h3
    haveI := finiteDimensional_tower (p := p) K M
    exact (Nat.mul_eq_left Module.finrank_pos.ne').1 h3
  refine ⟨uniformizer p Sig, ?_⟩
  have := v_algebraMap (p := p) (K := Sig) (L := F) (uniformizer p Sig)
  rw [heF, uniformizer_spec] at this
  simpa using this

end Unram

variable (s : M ≃ₐ[K] M) (hs : ∀ g, g ∈ Subgroup.zpowers s)
  (he : Module.finrank K M ∣ Module.finrank K U)

/-- **Neukirch's formula**: if `y ∈ Σ = Fix(τ)` has `v_F(y) = 1` then `ρ_F(N_{Σ/K} y) = τ`. -/
theorem rhoF_norm_tau (y : fixedField (Subgroup.zpowers (tau hM hU hdeg g k)))
    (hy : v p (y : F) = 1) (hy0 : Algebra.norm K y ≠ 0) :
    rhoF hM hU hdeg s hs he (Units.mk0 _ hy0) = tau hM hU hdeg g k := by
  haveI := finiteDimensional_tower (p := p) K F
  haveI : IsGalois U F := IsGalois.tower_top_of_isGalois K U F
  set φ := stdFrob hM hU hdeg
  set sU := stdGen hM hU hdeg s
  have hyF : (y : F) ≠ 0 := by
    intro h; rw [h] at hy; simp [v, wval] at hy
  set Y : Fˣ := Units.mk0 _ hyF
  have hfFU : f p U F = 1 := by
    have h1 := e_mul_f (p := p) (K := U) (L := F)
    rw [std_e_U hM hU hdeg] at h1
    exact (Nat.mul_eq_left Module.finrank_pos.ne').1 h1
  have hNU0 : Algebra.norm U (y : F) ≠ 0 := Algebra.norm_ne_zero_iff.2 hyF
  have hnorm := algebraMap_norm_tau hM hU hdeg g k hk hke y
  -- `v_K (N y) = k`
  have hvN : v p (Algebra.norm K y) = k := by
    have h1 := v_algebraMap (p := p) (K := K) (L := F) (Algebra.norm K y)
    rw [hnorm, (std_e hM hU hdeg).1, v_prod _ _ fun j ↦ (map_ne_zero_iff _ (φ ^ j).injective).2
      ((map_ne_zero_iff _ (algebraMap U F).injective).2 hNU0)] at h1
    simp_rw [v_galois, v_algebraMap (p := p) (K := U) (L := F), std_e_U hM hU hdeg,
      std_finrank_U hM hU hdeg, v_norm hyF, hfFU, hy] at h1
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    have he0 : (Module.finrank K M : ℤ) ≠ 0 := by
      haveI := finiteDimensional_tower (p := p) K M
      exact_mod_cast Module.finrank_pos.ne'
    push_cast at h1
    have : (Module.finrank K M : ℤ) * (k : ℤ) = (Module.finrank K M : ℤ) * v p (Algebra.norm K y)
      := by linear_combination h1
    exact (mul_left_cancel₀ he0 this).symm
  set X : Kˣ := Units.mk0 _ hy0
  set ϖ : Kˣ := stdVarpi (p := p) (K := K) (M := M)
  have hπ := uniformizer_spec (p := p) (K := M)
  set πM : Fˣ := Units.map (algebraMap M F : M →* F) (Units.mk0 _ hπ.ne_zero)
  set ξ : Fˣ := Y / πM
  set η : Fˣ := ∏ j ∈ Finset.range k, uMap (φ ^ j) ξ
  obtain ⟨m, hm⟩ : ∃ m : ℕ, sU ^ m = g⁻¹ :=
    mem_powers_iff_mem_zpowers.2 (stdGen_generates hM hU hdeg s hs g⁻¹)
  set z : Fˣ := ∏ i ∈ Finset.range m, uMap (sU ^ i) Y
  -- `τ` fixes `y`
  have hτy : g ((φ ^ k) (y : F)) = (y : F) :=
    y.2 ⟨tau hM hU hdeg g k, Subgroup.mem_zpowers _⟩
  have hφky : (φ ^ k) (y : F) = g⁻¹ (y : F) := by
    have := congrArg g.symm hτy
    rw [AlgEquiv.symm_apply_apply] at this
    rw [AlgEquiv.aut_inv, this]
  have hφπ : ∀ j : ℕ, (φ ^ j) (πM : F) = πM := fun j ↦ (φ ^ j).commutes _
  have hφK : ∀ (j : ℕ) (c : K), (φ ^ j) (algebraMap K F c) = algebraMap K F c := fun j c ↦ by
    rw [IsScalarTower.algebraMap_apply K M F]; exact (φ ^ j).commutes _
  have hNπ : algebraMap U F (Algebra.norm U (πM : F)) = algebraMap K F (ϖ : K) := by
    rw [show (πM : F) = algebraMap M F (uniformizer p M) from rfl, std_norm_M hM hU hdeg,
      ← IsScalarTower.algebraMap_apply]
    rfl
  have hdata : PsiData hM hU hdeg s (unitPart hM X) η z := by
    refine ⟨?_, ?_⟩
    · apply (algebraMap U F).injective
      have hj : ∀ j ∈ Finset.range k, algebraMap U F (Algebra.norm U ((uMap (φ ^ j) ξ : Fˣ) : F))
          = (φ ^ j) (algebraMap U F (Algebra.norm U (y : F))) / algebraMap K F (ϖ : K) := by
        intro j _
        rw [coe_uMap, norm_U_galois_M hM hU hdeg, Units.val_div_eq_div_val, norm_div',
          map_div₀, map_div₀, hNπ, hφK]
        rfl
      rw [show (η : F) = ∏ j ∈ Finset.range k, ((uMap (φ ^ j) ξ : Fˣ) : F) from
        Units.coe_prod _ _, map_prod, map_prod, Finset.prod_congr rfl hj,
        Finset.prod_div_distrib, ← hnorm, Finset.prod_const, Finset.card_range,
        unitPart_apply, ← IsScalarTower.algebraMap_apply]
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, X, Units.val_mk0, hvN]
      rw [map_mul, map_zpow₀, zpow_neg, zpow_natCast, div_eq_mul_inv]
    · rw [uMap_prod_pow_div φ ξ k, uMap_prod_pow_div sU Y m, hm]
      ext
      simp only [Units.val_div_eq_div_val, coe_uMap, ξ, map_div₀, hφπ, Y, Units.val_mk0, hφky]
      have h1 := πM.ne_zero
      field_simp
  -- `v(z) = m`
  have hvz : v p (z : F) = m := by
    rw [show (z : F) = ∏ i ∈ Finset.range m, ((uMap (sU ^ i) Y : Fˣ) : F) from
      Units.coe_prod _ _, v_prod _ _ fun i ↦ Units.ne_zero _]
    simp only [coe_uMap, v_galois, Y, Units.val_mk0, hy, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  have hpsi := psi_eq_of_psiData hM hU hdeg s hs he hdata
  rw [hvz] at hpsi
  -- conclusion
  rw [rhoF_apply, hpsi]
  change stdProd hM hU hdeg (_, φ ^ v p (Algebra.norm K y)) = stdProd hM hU hdeg (g, φ ^ k)
  rw [hvN]
  congr 2
  · apply (MulEquiv.ofBijective _ (stdResM_bijective hM hU hdeg)).injective
    rw [MulEquiv.apply_symm_apply]
    change s ^ (-(m : ℤ)) = stdResM g
    have : stdResM (K := K) (sU ^ m) = s ^ m := by rw [map_pow, stdResM_stdGen]
    rw [hm, map_inv] at this
    rw [zpow_neg, zpow_natCast, ← this, inv_inv]

end PadicField
