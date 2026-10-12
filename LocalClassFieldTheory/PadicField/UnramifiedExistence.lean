/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.Galois

/-!
# Existence and uniqueness of unramified extensions

Let `K` be a field finite over `ℚ_[p]` and `Ω` an algebraically closed extension of `K`
(compatible with the `ℚ_[p]`-structures). Finite intermediate fields `K ⊆ E ⊆ Ω` are again finite
over `ℚ_[p]` (`PadicField.intermediateField_finiteDimensional_of_finiteDimensional`).

## Main definitions

* `PadicField.unramifiedOfDegree p K Ω n`: the subfield `K_n` of `Ω` generated over `K` by the
  roots of `X ^ (q ^ n) - X`, where `q = #𝓴 K`.

## Main results

* `PadicField.exists_isUnramified`: for each `n ≥ 1` there is an unramified extension of `K` of
  degree `n` inside `Ω`.
* `PadicField.finrank_unramifiedOfDegree`, `PadicField.isUnramified_unramifiedOfDegree`:
  `K_n / K` is unramified of degree `n`.
* `PadicField.eq_unramifiedOfDegree`: every finite unramified `E ⊆ Ω` equals `K_{[E : K]}`; in
  particular unramified intermediate fields of the same degree coincide
  (`PadicField.IsUnramified.eq_of_finrank_eq`).
* `PadicField.unramifiedOfDegree_le_iff`: `K_m ≤ K_n ↔ m ∣ n` (for `m, n ≥ 1`).
* `PadicField.IsUnramified.of_le`, `PadicField.IsUnramified.sup`: subextensions and composita of
  unramified extensions are unramified.
* `PadicField.unramifiedOfDegree_le_of_f_eq`: if `f(L/K) = n` then `K_n ≤ L`; conversely every
  unramified `E ≤ L` satisfies `E ≤ K_{f(L/K)}` (`PadicField.IsUnramified.le_unramifiedOfDegree_f`),
  so `K_{f(L/K)}` is the maximal unramified subextension of `L / K`.
-/

open Polynomial IsLocalRing

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]

section Card

variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L]

/-- `q_L = q_K ^ f(L/K)`. -/
theorem q_eq_pow_f : q p L = q p K ^ f p K L := by
  haveI := finiteDimensional_tower (p := p) K L
  exact Module.natCard_eq_pow_finrank

end Card

section Polynomial

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

theorem mem_rootSet_X_pow_sub_X {N : ℕ} (hN : 1 < N) {x : Ω} :
    x ∈ (X ^ N - X : K[X]).rootSet Ω ↔ x ^ N = x := by
  rw [mem_rootSet, aeval_sub, aeval_X_pow, aeval_X, sub_eq_zero]
  exact and_iff_right (FiniteField.X_pow_card_sub_X_ne_zero K hN)

theorem ncard_rootSet_X_pow_sub_X_le {N : ℕ} (hN : 1 < N) :
    ((X ^ N - X : K[X]).rootSet Ω).ncard ≤ N := by
  classical
  rw [rootSet_def, Set.ncard_coe_finset]
  refine (Multiset.toFinset_card_le _).trans ((card_roots' _).trans ?_)
  rw [Polynomial.map_sub, Polynomial.map_pow, map_X, natDegree_sub_eq_left_of_natDegree_lt]
  · simp
  · simpa using hN

end Polynomial

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]

/-- A finite intermediate field of `Ω / K` is finite over `ℚ_[p]`. -/
instance intermediateField_finiteDimensional_of_finiteDimensional (E : IntermediateField K Ω)
    [FiniteDimensional K E] : FiniteDimensional ℚ_[p] E :=
  Module.Finite.trans K E

/-- There is a monic polynomial over `𝒪 p K` of degree `n` whose reduction is irreducible. -/
theorem exists_monic_irreducible_residue (n : ℕ) (hn : 0 < n) :
    ∃ G : (𝒪 p K)[X], G.Monic ∧ G.natDegree = n ∧
      Irreducible (G.map (algebraMap (𝒪 p K) (𝓴 p K))) := by
  obtain ⟨r, hr⟩ := CharP.exists (𝓴 p K)
  haveI := Fact.mk (CharP.char_is_prime (𝓴 p K) r)
  haveI : NeZero n := ⟨hn.ne'⟩
  set F := FiniteField.Extension (𝓴 p K) r n
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (𝓴 p K) F
  have hdeg := (Field.primitive_element_iff_minpoly_natDegree_eq (𝓴 p K) α).1 hα
  rw [FiniteField.finrank_extension] at hdeg
  have hint : IsIntegral (𝓴 p K) α := .of_finite _ _
  have hlift : minpoly (𝓴 p K) α ∈ lifts (algebraMap (𝒪 p K) (𝓴 p K)) :=
    lifts_iff_coeff_lifts _ |>.2 fun _ ↦ residue_surjective _
  obtain ⟨G, hG, hGdeg, hGm⟩ := lifts_and_natDegree_eq_and_monic hlift (minpoly.monic hint)
  exact ⟨G, hGm, hGdeg.trans hdeg, hG ▸ minpoly.irreducible hint⟩

/-- Existence of unramified extensions of every degree `n ≥ 1` inside an algebraically closed
field. -/
theorem exists_isUnramified [IsAlgClosed Ω] (n : ℕ) (hn : 0 < n) :
    ∃ E : IntermediateField K Ω, ∃ _ : FiniteDimensional K E,
      Module.finrank K E = n ∧ IsUnramified p K E := by
  obtain ⟨G, hGm, hGdeg, hGirr⟩ := exists_monic_irreducible_residue (p := p) (K := K) n hn
  set G' := G.map (algebraMap (𝒪 p K) K)
  have hG'm : G'.Monic := hGm.map _
  have hG'deg : G'.natDegree = n := by rw [hGm.natDegree_map, hGdeg]
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_aeval_eq_zero Ω G'
    (by rw [degree_eq_natDegree hG'm.ne_zero, hG'deg]; exact_mod_cast hn.ne')
  have hint : IsIntegral K β := ⟨G', hG'm, by rwa [← aeval_def]⟩
  set E := IntermediateField.adjoin K {β}
  haveI : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hint
  have hle : Module.finrank K E ≤ n := by
    rw [IntermediateField.adjoin.finrank hint, ← hG'deg]
    exact natDegree_le_natDegree (minpoly.min K β hG'm hβ)
  set γ := IntermediateField.AdjoinSimple.gen K β
  have hγ : aeval γ G = 0 := by
    rw [← aeval_map_algebraMap K γ G]
    apply (algebraMap E Ω).injective
    rw [map_zero, ← aeval_algebraMap_apply, IntermediateField.AdjoinSimple.algebraMap_gen, hβ]
  have hγint : IsIntegral (𝒪 p K) γ := ⟨G, hGm, by rwa [← aeval_def]⟩
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝒪 p E)).1 hγint
  have hy0 : aeval y G = 0 := by
    apply Integers.coe_injective (p := p)
    rw [map_zero, ← aeval_algebraMap_apply, hy, hγ]
  set b := residue (𝒪 p E) y
  have hb : aeval b (G.map (algebraMap (𝒪 p K) (𝓴 p K))) = 0 := by
    rw [aeval_map_algebraMap]
    have : b = IsScalarTower.toAlgHom (𝒪 p K) (𝒪 p E) (𝓴 p E) y := rfl
    rw [this, aeval_algHom_apply, hy0, map_zero]
  have hmin := minpoly.eq_of_irreducible_of_monic hGirr hb (hGm.map _)
  have hf : n ≤ f p K E := by
    rw [f, ← hGdeg, ← hGm.natDegree_map (algebraMap (𝒪 p K) (𝓴 p K)), hmin]
    exact minpoly.natDegree_le b
  have hef := e_mul_f (p := p) (K := K) (L := E)
  have he := e_pos (p := p) (K := K) (L := E)
  refine ⟨E, inferInstance, ?_, ?_⟩
  · nlinarith
  · unfold IsUnramified; nlinarith

/-! ### The unramified extension of degree `n` -/

variable (p K Ω) in
/-- The unramified extension `K_n` of degree `n` of `K` inside `Ω`: the subfield generated by the
roots of `X ^ (q ^ n) - X`. (For `n = 0` this is `⊥`.) -/
irreducible_def unramifiedOfDegree (n : ℕ) : IntermediateField K Ω :=
  IntermediateField.adjoin K ((X ^ q p K ^ n - X : K[X]).rootSet Ω)

theorem one_lt_q_pow {n : ℕ} (hn : 0 < n) : 1 < q p K ^ n :=
  Nat.one_lt_pow hn.ne' (one_lt_q p K)

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] in
theorem mem_unramifiedOfDegree_of_pow_eq {n : ℕ} (hn : 0 < n) {x : Ω} (hx : x ^ q p K ^ n = x) :
    x ∈ unramifiedOfDegree p K Ω n := by
  rw [unramifiedOfDegree_def]
  exact IntermediateField.subset_adjoin _ _ ((mem_rootSet_X_pow_sub_X (one_lt_q_pow hn)).2 hx)

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] in
variable (p K Ω) in
theorem unramifiedOfDegree_zero : unramifiedOfDegree p K Ω 0 = ⊥ := by
  rw [unramifiedOfDegree_def, pow_zero, pow_one, sub_self, rootSet_zero,
    IntermediateField.adjoin_empty]

/-- Every finite unramified intermediate field `E` equals `K_{[E : K]}`. -/
theorem eq_unramifiedOfDegree (E : IntermediateField K Ω) [FiniteDimensional K E]
    (h : IsUnramified p K E) : E = unramifiedOfDegree p K Ω (Module.finrank K E) := by
  have hs := isSplittingField_of_isUnramified h
  rw [q_eq_pow_f (K := K), h.f_eq] at hs
  rw [unramifiedOfDegree_def]
  exact (IntermediateField.isSplittingField_iff.1 hs).2

theorem isUnramified_bot : IsUnramified p K (⊥ : IntermediateField K Ω) := by
  have h := e_mul_f (p := p) (K := K) (L := (⊥ : IntermediateField K Ω))
  rw [IntermediateField.finrank_bot] at h
  exact Nat.eq_one_of_mul_eq_one_right h

theorem IsUnramified.of_eq {E F : IntermediateField K Ω} [FiniteDimensional K E]
    [FiniteDimensional K F] (hE : IsUnramified p K E) (h : E = F) : IsUnramified p K F := by
  subst h; exact hE

variable [IsAlgClosed Ω]

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] in
variable (p K Ω) in
theorem isSplittingField_unramifiedOfDegree (n : ℕ) :
    IsSplittingField K (unramifiedOfDegree p K Ω n) (X ^ q p K ^ n - X) := by
  rw [unramifiedOfDegree_def]
  exact IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)

instance unramifiedOfDegree_finiteDimensional (n : ℕ) :
    FiniteDimensional K (unramifiedOfDegree p K Ω n) := by
  haveI := isSplittingField_unramifiedOfDegree p K Ω n
  exact IsSplittingField.finiteDimensional _ (X ^ q p K ^ n - X)

instance unramifiedOfDegree_normal (n : ℕ) : Normal K (unramifiedOfDegree p K Ω n) := by
  haveI := isSplittingField_unramifiedOfDegree p K Ω n
  exact Normal.of_isSplittingField (X ^ q p K ^ n - X)

variable (p K Ω) in
theorem finrank_unramifiedOfDegree {n : ℕ} (hn : 0 < n) :
    Module.finrank K (unramifiedOfDegree p K Ω n) = n := by
  obtain ⟨E, _, hE, hEu⟩ := exists_isUnramified (p := p) (K := K) (Ω := Ω) n hn
  have := eq_unramifiedOfDegree E hEu
  rw [hE] at this
  subst this
  exact hE

variable (p K Ω) in
theorem isUnramified_unramifiedOfDegree (n : ℕ) :
    IsUnramified p K (unramifiedOfDegree p K Ω n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact isUnramified_bot.of_eq (unramifiedOfDegree_zero p K Ω).symm
  obtain ⟨E, _, hE, hEu⟩ := exists_isUnramified (p := p) (K := K) (Ω := Ω) n hn
  have := eq_unramifiedOfDegree E hEu
  rw [hE] at this
  exact hEu.of_eq this

omit [IsAlgClosed Ω] in
/-- Uniqueness: an unramified intermediate field of degree `n` is `K_n`. -/
theorem IsUnramified.eq_unramifiedOfDegree {E : IntermediateField K Ω} [FiniteDimensional K E]
    (h : IsUnramified p K E) {n : ℕ} (hn : Module.finrank K E = n) :
    E = unramifiedOfDegree p K Ω n :=
  hn ▸ PadicField.eq_unramifiedOfDegree E h

omit [IsAlgClosed Ω] in
/-- Two unramified intermediate fields of the same degree coincide. -/
theorem IsUnramified.eq_of_finrank_eq {E F : IntermediateField K Ω} [FiniteDimensional K E]
    [FiniteDimensional K F] (hE : IsUnramified p K E) (hF : IsUnramified p K F)
    (h : Module.finrank K E = Module.finrank K F) : E = F :=
  (hE.eq_unramifiedOfDegree h).trans (hF.eq_unramifiedOfDegree rfl).symm

theorem pow_pow_mul_eq_self {M : Type*} [Monoid M] {x : M} {N m : ℕ} (hx : x ^ N ^ m = x)
    (k : ℕ) : x ^ N ^ (m * k) = x := by
  rw [pow_mul]
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, ih, hx]

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] in
theorem unramifiedOfDegree_le_of_dvd {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n) :
    unramifiedOfDegree p K Ω m ≤ unramifiedOfDegree p K Ω n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [unramifiedOfDegree_zero]; exact bot_le
  rw [unramifiedOfDegree_def p K Ω m]
  refine IntermediateField.adjoin_le_iff.2 fun x hx ↦ ?_
  rw [SetLike.mem_coe]
  rw [mem_rootSet_X_pow_sub_X (one_lt_q_pow hm)] at hx
  obtain ⟨k, rfl⟩ := h
  exact mem_unramifiedOfDegree_of_pow_eq (Nat.pos_of_ne_zero hn) (pow_pow_mul_eq_self hx k)

theorem unramifiedOfDegree_le_iff {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    unramifiedOfDegree p K Ω m ≤ unramifiedOfDegree p K Ω n ↔ m ∣ n := by
  refine ⟨fun h ↦ ?_, unramifiedOfDegree_le_of_dvd hn.ne'⟩
  have := IntermediateField.finrank_dvd_of_le_right h
  rwa [finrank_unramifiedOfDegree p K Ω hm, finrank_unramifiedOfDegree p K Ω hn] at this

omit [IsAlgClosed Ω] in
/-- An intermediate field of an unramified extension is unramified. -/
theorem IsUnramified.of_le {E F : IntermediateField K Ω} [FiniteDimensional K E]
    [FiniteDimensional K F] (hF : IsUnramified p K F) (h : E ≤ F) : IsUnramified p K E := by
  letI : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower ℚ_[p] E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have := e_mul_e (p := p) (K := K) (E := E) (L := F)
  unfold IsUnramified at hF ⊢
  rw [hF] at this
  exact Nat.eq_one_of_mul_eq_one_right this

omit [IsAlgClosed Ω] in
/-- Every unramified intermediate field is contained in `K_n` for any multiple `n` of its degree.
-/
theorem IsUnramified.le_unramifiedOfDegree {E : IntermediateField K Ω} [FiniteDimensional K E]
    (h : IsUnramified p K E) {n : ℕ} (hn : n ≠ 0) (hdvd : Module.finrank K E ∣ n) :
    E ≤ unramifiedOfDegree p K Ω n :=
  (PadicField.eq_unramifiedOfDegree E h).le.trans (unramifiedOfDegree_le_of_dvd hn hdvd)

/-- The compositum of two unramified extensions is unramified. -/
theorem IsUnramified.sup {E F : IntermediateField K Ω} [FiniteDimensional K E]
    [FiniteDimensional K F] (hE : IsUnramified p K E) (hF : IsUnramified p K F) :
    IsUnramified p K (E ⊔ F : IntermediateField K Ω) := by
  have h0 : Module.finrank K E * Module.finrank K F ≠ 0 :=
    mul_ne_zero Module.finrank_pos.ne' Module.finrank_pos.ne'
  refine (isUnramified_unramifiedOfDegree p K Ω
    (Module.finrank K E * Module.finrank K F)).of_le (sup_le ?_ ?_)
  · exact hE.le_unramifiedOfDegree h0 (dvd_mul_right _ _)
  · exact hF.le_unramifiedOfDegree h0 (dvd_mul_left _ _)

omit [IsAlgClosed Ω] in
/-- If the inertia degree of a finite `L / K` inside `Ω` is `n`, then `K_n ≤ L`. -/
theorem unramifiedOfDegree_le_of_f_eq (L : IntermediateField K Ω) [FiniteDimensional K L] {n : ℕ}
    (h : f p K L = n) : unramifiedOfDegree p K Ω n ≤ L := by
  have hn : 0 < n := h ▸ f_pos
  have hq : q p L = q p K ^ n := by rw [q_eq_pow_f (K := K), h]
  set T : Set Ω := (fun x : L ↦ (x : Ω)) '' teichmullerSet p L
  have hT : T ⊆ (X ^ q p K ^ n - X : K[X]).rootSet Ω := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_rootSet_X_pow_sub_X (one_lt_q_pow hn), ← hq]
    exact congrArg (fun y : L ↦ (y : Ω)) (teichmullerSet_pow_q hx)
  have hTcard : T.ncard = q p K ^ n := by
    rw [Set.ncard_image_of_injective _ Subtype.val_injective, teichmullerSet,
      Set.ncard_range_of_injective, ← hq, q]
    exact fun a b hab ↦ Teichmuller.teichmuller_injective (Integers.ext hab)
  have heq : T = (X ^ q p K ^ n - X : K[X]).rootSet Ω :=
    Set.eq_of_subset_of_ncard_le hT
      (by rw [hTcard]; exact ncard_rootSet_X_pow_sub_X_le (one_lt_q_pow hn))
      (rootSet_finite _ _)
  rw [unramifiedOfDegree_def]
  refine IntermediateField.adjoin_le_iff.2 (heq ▸ ?_)
  rintro _ ⟨x, -, rfl⟩
  exact x.2

omit [IsAlgClosed Ω] in
/-- The inertia degree is multiplicative along `K ⊆ E ⊆ F` for intermediate fields. -/
theorem f_dvd_f_of_le {E F : IntermediateField K Ω} [FiniteDimensional K E]
    [FiniteDimensional K F] (h : E ≤ F) : f p K E ∣ f p K F := by
  letI : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower ℚ_[p] E F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact ⟨_, (f_mul_f (p := p) (K := K) (E := E) (L := F)).symm⟩

omit [IsAlgClosed Ω] in
/-- `K_{f(L/K)}` is the maximal unramified subextension of a finite `L / K` inside `Ω`. -/
theorem IsUnramified.le_unramifiedOfDegree_f {E L : IntermediateField K Ω} [FiniteDimensional K E]
    [FiniteDimensional K L] (hE : IsUnramified p K E) (h : E ≤ L) :
    E ≤ unramifiedOfDegree p K Ω (f p K L) := by
  refine hE.le_unramifiedOfDegree f_pos.ne' ?_
  rw [← hE.f_eq]
  exact f_dvd_f_of_le h

end PadicField
