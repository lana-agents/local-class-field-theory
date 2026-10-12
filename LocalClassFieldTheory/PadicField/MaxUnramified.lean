/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.UnramifiedExistence

/-!
# The maximal unramified extension and its Frobenius

Let `K` be a field finite over `ℚ_[p]` and `Ω` an algebraically closed extension of `K`.

## Main definitions

* `PadicField.maxUnramified p K Ω`: the maximal unramified extension `K^ur = ⨆ n, K_n` of `K`
  inside `Ω`.
* `PadicField.frobUr p K Ω : Gal(K^ur / K)`: the arithmetic Frobenius of `K^ur`.

## Main results

* `PadicField.frob_unramifiedOfDegree_apply`: the Frobenius of `K_n` acts as `x ↦ x ^ q` on the
  roots of `X ^ (q ^ n) - X`.
* `PadicField.frob_unramifiedOfDegree_inclusion`: compatibility of the Frobenii of `K_m ⊆ K_n`.
* `PadicField.mem_maxUnramified_iff`: `x ∈ K^ur ↔ ∃ n > 0, x ∈ K_n`.
* `PadicField.isGalois_maxUnramified`: `K^ur / K` is Galois.
* `PadicField.IsUnramified.le_maxUnramified`: every finite unramified `E ⊆ Ω` lies in `K^ur`.
* `PadicField.frobUr_apply`: `frobUr` restricts to `frob` on each `K_n`.
* `PadicField.exists_eq_frobUr_pow`: every `σ ∈ Gal(K^ur / K)` agrees on `K_n` with a power of
  `frobUr`; hence `PadicField.dense_zpowers_frobUr`: the powers of `frobUr` are dense for the
  Krull topology.
* `PadicField.gal_maxUnramified_mul_comm`: `Gal(K^ur / K)` is abelian.
* `PadicField.exists_restrict_eq`: restriction `Gal(K^ur / K) → Gal(K_n / K)` is surjective.
-/

open Polynomial IsLocalRing IntermediateField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

section General

variable {L : Type*} [Field L] [Algebra ℚ_[p] L] [Algebra K L] [IsScalarTower ℚ_[p] K L]
  [FiniteDimensional ℚ_[p] L]

omit [IsAlgClosed Ω] in
/-- The Frobenius of an unramified `L / K` acts as `x ↦ x ^ q_K` on roots of `X ^ q_L - X`. -/
theorem frob_apply_of_pow_eq (h : IsUnramified p K L) {x : L} (hx : x ^ q p L = x) :
    frob h x = x ^ q p K := by
  have hnrm : nrm p L x ≤ 1 := by
    have h1 := congrArg (nrm p L) hx
    rw [nrm_pow] at h1
    by_contra! hlt
    have := lt_self_pow₀ hlt (one_lt_q p L)
    linarith
  have hy : Integers.mk x hnrm ^ Teichmuller.Q (𝒪 p L) = Integers.mk x hnrm := by
    ext; simp only [Integers.coe_pow, Integers.coe_mk]; exact hx
  have h1 : (frob h • Integers.mk x hnrm) ^ Teichmuller.Q (𝒪 p L) =
      frob h • Integers.mk x hnrm := by
    rw [← smul_pow', hy]
  have h2 : (Integers.mk x hnrm ^ q p K) ^ Teichmuller.Q (𝒪 p L) =
      Integers.mk x hnrm ^ q p K := by
    rw [← pow_mul, mul_comm, pow_mul, hy]
  have := Teichmuller.eq_of_pow_card_eq_self h1 h2
    (by rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact frob_spec h _)
  exact congrArg (fun z : 𝒪 p L ↦ (z : L)) this

end General

/-- The Frobenius of `K_n` acts as `x ↦ x ^ q` on roots of `X ^ (q ^ n) - X`. -/
theorem frob_unramifiedOfDegree_apply {n : ℕ} (hn : 0 < n) (x : unramifiedOfDegree p K Ω n)
    (hx : (x : Ω) ^ q p K ^ n = x) :
    frob (isUnramified_unramifiedOfDegree p K Ω n) x = x ^ q p K := by
  refine frob_apply_of_pow_eq _ (Subtype.ext ?_)
  rw [q_eq_pow_f (K := K), (isUnramified_unramifiedOfDegree p K Ω n).f_eq,
    finrank_unramifiedOfDegree p K Ω hn, IntermediateField.coe_pow]
  exact hx

/-- Compatibility of the Frobenii: the Frobenius of `K_n` restricts to that of `K_m ⊆ K_n`. -/
theorem frob_unramifiedOfDegree_inclusion {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : unramifiedOfDegree p K Ω m ≤ unramifiedOfDegree p K Ω n)
    (x : unramifiedOfDegree p K Ω m) :
    (frob (isUnramified_unramifiedOfDegree p K Ω n) (inclusion h x) : Ω) =
      frob (isUnramified_unramifiedOfDegree p K Ω m) x := by
  obtain ⟨k, rfl⟩ := (unramifiedOfDegree_le_iff hm hn).1 h
  let φ₁ : unramifiedOfDegree p K Ω m →ₐ[K] Ω := (unramifiedOfDegree p K Ω (m * k)).val.comp
    ((frob (isUnramified_unramifiedOfDegree p K Ω (m * k))).toAlgHom.comp (inclusion h))
  let φ₂ : unramifiedOfDegree p K Ω m →ₐ[K] Ω := (unramifiedOfDegree p K Ω m).val.comp
    (frob (isUnramified_unramifiedOfDegree p K Ω m)).toAlgHom
  have key : ∀ z : unramifiedOfDegree p K Ω m, (z : Ω) ^ q p K ^ m = z →
      (frob (isUnramified_unramifiedOfDegree p K Ω (m * k)) (inclusion h z) : Ω) =
        frob (isUnramified_unramifiedOfDegree p K Ω m) z := by
    intro z hz
    have hz' : ((inclusion h z : unramifiedOfDegree p K Ω (m * k)) : Ω) ^ q p K ^ (m * k) =
        (inclusion h z : unramifiedOfDegree p K Ω (m * k)) := by
      rw [coe_inclusion]; exact pow_pow_mul_eq_self hz k
    rw [frob_unramifiedOfDegree_apply hm _ hz, frob_unramifiedOfDegree_apply hn _ hz',
      IntermediateField.coe_pow, IntermediateField.coe_pow, coe_inclusion]
  have : φ₁ = φ₂ := by
    refine algHom_ext_of_eq_adjoin K (unramifiedOfDegree_def p K Ω m) fun y hy ↦ ?_
    simp only [φ₁, φ₂, AlgHom.comp_apply, coe_val, AlgEquiv.toAlgHom_apply]
    exact key _ ((mem_rootSet_X_pow_sub_X (one_lt_q_pow hm)).1 hy)
  have := DFunLike.congr_fun this x
  simpa only [φ₁, φ₂, AlgHom.comp_apply, coe_val, AlgEquiv.toAlgHom_apply] using this

/-! ### The maximal unramified extension -/

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] in
variable (p K Ω) in
/-- The maximal unramified extension `K^ur` of `K` inside `Ω`. -/
noncomputable def maxUnramified : IntermediateField K Ω := ⨆ n, unramifiedOfDegree p K Ω n

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] in
variable (p K Ω) in
theorem unramifiedOfDegree_le_maxUnramified (n : ℕ) :
    unramifiedOfDegree p K Ω n ≤ maxUnramified p K Ω :=
  le_iSup (fun n ↦ unramifiedOfDegree p K Ω n) n

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] in
variable (p K Ω) in
theorem directed_unramifiedOfDegree_succ :
    Directed (· ≤ ·) fun n : ℕ ↦ unramifiedOfDegree p K Ω (n + 1) := fun i j ↦
  ⟨i * j + i + j, unramifiedOfDegree_le_of_dvd (by omega) ⟨j + 1, by ring⟩,
    unramifiedOfDegree_le_of_dvd (by omega) ⟨i + 1, by ring⟩⟩

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] in
variable (p K Ω) in
theorem maxUnramified_eq_iSup_succ :
    maxUnramified p K Ω = ⨆ n : ℕ, unramifiedOfDegree p K Ω (n + 1) := by
  refine le_antisymm (iSup_le fun n ↦ ?_) (iSup_le fun n ↦ le_iSup _ (n + 1))
  rcases n with _ | n
  · rw [unramifiedOfDegree_zero]; exact bot_le
  · exact le_iSup (fun n : ℕ ↦ unramifiedOfDegree p K Ω (n + 1)) n

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] in
theorem mem_maxUnramified_iff {x : Ω} :
    x ∈ maxUnramified p K Ω ↔ ∃ n, 0 < n ∧ x ∈ unramifiedOfDegree p K Ω n := by
  rw [maxUnramified_eq_iSup_succ, ← SetLike.mem_coe,
    coe_iSup_of_directed (directed_unramifiedOfDegree_succ p K Ω), Set.mem_iUnion]
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨n + 1, n.succ_pos, hn⟩, fun ⟨n, hn, hx⟩ ↦ ⟨n - 1, ?_⟩⟩
  rwa [Nat.sub_add_cancel hn]

omit [IsAlgClosed Ω] in
/-- Every finite unramified subextension of `Ω / K` is contained in `K^ur`. -/
theorem IsUnramified.le_maxUnramified {E : IntermediateField K Ω} [FiniteDimensional K E]
    (h : IsUnramified p K E) : E ≤ maxUnramified p K Ω :=
  (PadicField.eq_unramifiedOfDegree E h).le.trans (unramifiedOfDegree_le_maxUnramified p K Ω _)

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] in
instance normal_maxUnramified : Normal K (maxUnramified p K Ω) :=
  IntermediateField.normal_iSup K Ω _

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] in
/-- `K^ur / K` is Galois. -/
instance isGalois_maxUnramified : IsGalois K (maxUnramified p K Ω) := by
  haveI := charZero p K
  exact ⟨⟩

/-! ### The Frobenius of `K^ur` -/

variable (p K Ω) in
/-- The Frobenius of `K_(n+1)`, viewed as a map into `K^ur` (auxiliary). -/
noncomputable def frobUrAux (n : ℕ) :
    (unramifiedOfDegree p K Ω (n + 1)).toSubalgebra →ₐ[K] maxUnramified p K Ω :=
  (inclusion (unramifiedOfDegree_le_maxUnramified p K Ω (n + 1))).comp
    (frob (isUnramified_unramifiedOfDegree p K Ω (n + 1))).toAlgHom

theorem frobUrAux_apply (n : ℕ) (x : unramifiedOfDegree p K Ω (n + 1)) :
    (frobUrAux p K Ω n x : Ω) = frob (isUnramified_unramifiedOfDegree p K Ω (n + 1)) x := by
  simp only [frobUrAux, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, coe_inclusion]

variable (p K Ω) in
/-- The Frobenius of `K^ur`, as an algebra homomorphism (auxiliary). -/
noncomputable def frobUrHom : maxUnramified p K Ω →ₐ[K] maxUnramified p K Ω :=
  Subalgebra.iSupLift (fun n : ℕ ↦ (unramifiedOfDegree p K Ω (n + 1)).toSubalgebra)
    (fun i j ↦ by
      obtain ⟨k, hi, hj⟩ := directed_unramifiedOfDegree_succ p K Ω i j
      exact ⟨k, hi, hj⟩)
    (frobUrAux p K Ω)
    (fun i j h ↦ by
      ext x
      simp only [AlgHom.comp_apply]
      rw [frobUrAux_apply, frobUrAux_apply]
      exact (frob_unramifiedOfDegree_inclusion i.succ_pos j.succ_pos h x).symm)
    (maxUnramified p K Ω).toSubalgebra
    (by
      rw [maxUnramified_eq_iSup_succ,
        toSubalgebra_iSup_of_directed (directed_unramifiedOfDegree_succ p K Ω)])

variable (p K Ω) in
/-- The arithmetic Frobenius `Frob ∈ Gal(K^ur / K)`. -/
noncomputable def frobUr : maxUnramified p K Ω ≃ₐ[K] maxUnramified p K Ω :=
  AlgEquiv.ofBijective (frobUrHom p K Ω) (Algebra.IsAlgebraic.algHom_bijective _)

/-- `frobUr` restricts to the Frobenius of `K_n` on `K_n`. -/
theorem frobUr_apply {n : ℕ} (hn : 0 < n) {x : Ω} (hx : x ∈ unramifiedOfDegree p K Ω n) :
    (frobUr p K Ω ⟨x, unramifiedOfDegree_le_maxUnramified p K Ω n hx⟩ : Ω) =
      frob (isUnramified_unramifiedOfDegree p K Ω n) ⟨x, hx⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [frobUr, AlgEquiv.ofBijective_apply, frobUrHom]
  exact (congrArg Subtype.val (Subalgebra.iSupLift_mk
    (K := fun n : ℕ ↦ (unramifiedOfDegree p K Ω (n + 1)).toSubalgebra) (f := frobUrAux p K Ω)
    (T := (maxUnramified p K Ω).toSubalgebra) (i := m)
    (x := (⟨x, hx⟩ : (unramifiedOfDegree p K Ω (m + 1)).toSubalgebra))
    (hx := unramifiedOfDegree_le_maxUnramified p K Ω _ hx))).trans
    (frobUrAux_apply m ⟨x, hx⟩)

/-- `frobUr ^ k` restricts to `frob ^ k` on `K_n`. -/
theorem frobUr_pow_apply {n : ℕ} (hn : 0 < n) (k : ℕ) (x : maxUnramified p K Ω)
    (hx : (x : Ω) ∈ unramifiedOfDegree p K Ω n) :
    ((frobUr p K Ω ^ k) x : Ω) =
      ((frob (isUnramified_unramifiedOfDegree p K Ω n) ^ k) ⟨x, hx⟩ : Ω) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    set w := (frob (isUnramified_unramifiedOfDegree p K Ω n) ^ k) ⟨x, hx⟩
    have hy : (frobUr p K Ω ^ k) x = ⟨w, unramifiedOfDegree_le_maxUnramified p K Ω n w.2⟩ :=
      Subtype.ext ih
    rw [pow_succ', AlgEquiv.mul_apply, hy, frobUr_apply hn, pow_succ', AlgEquiv.mul_apply]

/-- `frobUr ^ k` maps `K_n` into itself. -/
theorem frobUr_pow_mem {n : ℕ} (hn : 0 < n) (k : ℕ) {x : maxUnramified p K Ω}
    (hx : (x : Ω) ∈ unramifiedOfDegree p K Ω n) :
    ((frobUr p K Ω ^ k) x : Ω) ∈ unramifiedOfDegree p K Ω n := by
  rw [frobUr_pow_apply hn k x hx]
  exact Subtype.prop _

/-- Every element of `Gal(K^ur / K)` agrees on `K_n` with a power of `frobUr`. -/
theorem exists_eq_frobUr_pow (σ : maxUnramified p K Ω ≃ₐ[K] maxUnramified p K Ω) {n : ℕ}
    (hn : 0 < n) : ∃ k : ℕ, ∀ x : maxUnramified p K Ω,
      (x : Ω) ∈ unramifiedOfDegree p K Ω n → σ x = (frobUr p K Ω ^ k) x := by
  have h := isUnramified_unramifiedOfDegree p K Ω n
  let ρ : unramifiedOfDegree p K Ω n →ₐ[K] Ω := (maxUnramified p K Ω).val.comp
    (σ.toAlgHom.comp (inclusion (unramifiedOfDegree_le_maxUnramified p K Ω n)))
  have hρ : ∀ y, ρ y ∈ (unramifiedOfDegree p K Ω n).toSubalgebra := by
    intro y
    have hint : IsIntegral K (ρ y) := (Algebra.IsIntegral.isIntegral y).map ρ
    refine hint.mem_intermediateField_of_minpoly_splits ?_
    rw [minpoly.algHom_eq ρ ρ.injective y]
    exact Normal.splits inferInstance y
  let τ : unramifiedOfDegree p K Ω n →ₐ[K] unramifiedOfDegree p K Ω n :=
    ρ.codRestrict (unramifiedOfDegree p K Ω n).toSubalgebra hρ
  let τ' := AlgEquiv.ofBijective τ (Algebra.IsAlgebraic.algHom_bijective τ)
  have hmem : τ' ∈ Submonoid.powers (frob h) := by
    rw [mem_powers_iff_mem_zpowers, zpowers_frob]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := hmem
  have hk' : frob h ^ k = τ' := hk
  refine ⟨k, fun x hx ↦ Subtype.ext ?_⟩
  rw [frobUr_pow_apply hn k x hx, hk']
  rfl

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] in
/-- A finite subextension of `K^ur / K` is contained in some `K_n`. -/
theorem exists_le_unramifiedOfDegree (E : IntermediateField K (maxUnramified p K Ω))
    [FiniteDimensional K E] :
    ∃ n, 0 < n ∧ ∀ x ∈ E, ((x : maxUnramified p K Ω) : Ω) ∈ unramifiedOfDegree p K Ω n := by
  classical
  let b := Module.finBasis K E
  have h : ∀ i, ∃ n, 0 < n ∧
      (((b i : E) : maxUnramified p K Ω) : Ω) ∈ unramifiedOfDegree p K Ω n :=
    fun i ↦ mem_maxUnramified_iff.1 (b i : maxUnramified p K Ω).2
  choose N hN hmem using h
  have hpos : 0 < ∏ i, N i := Finset.prod_pos fun i _ ↦ hN i
  refine ⟨∏ i, N i, hpos, ?_⟩
  let ψ : E →ₗ[K] Ω := (maxUnramified p K Ω).val.toLinearMap.comp E.val.toLinearMap
  have hspan : (⊤ : Submodule K E) ≤
      (unramifiedOfDegree p K Ω (∏ i, N i)).toSubalgebra.toSubmodule.comap ψ := by
    rw [← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact unramifiedOfDegree_le_of_dvd hpos.ne' (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
      (hmem i)
  intro x hx
  exact hspan (Submodule.mem_top (x := ⟨x, hx⟩))

open scoped Topology in
/-- The powers of `frobUr` are dense in `Gal(K^ur / K)` for the Krull topology. -/
theorem dense_zpowers_frobUr :
    Dense (Subgroup.zpowers (frobUr p K Ω) :
      Set (maxUnramified p K Ω ≃ₐ[K] maxUnramified p K Ω)) := by
  intro σ
  rw [mem_closure_iff_nhds]
  intro t ht
  have h1 : (fun τ ↦ σ * τ) ⁻¹' t ∈ 𝓝 (1 : maxUnramified p K Ω ≃ₐ[K] maxUnramified p K Ω) := by
    apply (continuous_const_mul σ).continuousAt.preimage_mem_nhds
    rwa [mul_one]
  obtain ⟨E, hE, hEt⟩ := (krullTopology_mem_nhds_one_iff K _ _).1 h1
  obtain ⟨n, hn, hEn⟩ := exists_le_unramifiedOfDegree E
  obtain ⟨k, hk⟩ := exists_eq_frobUr_pow σ hn
  refine ⟨frobUr p K Ω ^ k, ?_, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k⟩
  have : σ⁻¹ * frobUr p K Ω ^ k ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [AlgEquiv.mul_apply, ← hk x (hEn x hx), AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  simpa using hEt this

/-- `Gal(K^ur / K)` is abelian. -/
theorem gal_maxUnramified_mul_comm (σ τ : maxUnramified p K Ω ≃ₐ[K] maxUnramified p K Ω) :
    σ * τ = τ * σ := by
  ext x
  obtain ⟨n, hn, hx⟩ := mem_maxUnramified_iff.1 x.2
  obtain ⟨a, ha⟩ := exists_eq_frobUr_pow σ hn
  obtain ⟨b, hb⟩ := exists_eq_frobUr_pow τ hn
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hb x hx, ha x hx, ha _ (frobUr_pow_mem hn b hx),
    hb _ (frobUr_pow_mem hn a hx), ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, ← pow_add,
    ← pow_add, add_comm]

/-- Restriction `Gal(K^ur / K) → Gal(K_n / K)` is surjective. -/
theorem exists_restrict_eq {n : ℕ} (hn : 0 < n)
    (τ : unramifiedOfDegree p K Ω n ≃ₐ[K] unramifiedOfDegree p K Ω n) :
    ∃ σ : maxUnramified p K Ω ≃ₐ[K] maxUnramified p K Ω, ∀ (x : maxUnramified p K Ω)
      (hx : (x : Ω) ∈ unramifiedOfDegree p K Ω n), (σ x : Ω) = τ ⟨x, hx⟩ := by
  have hmem : τ ∈ Submonoid.powers (frob (isUnramified_unramifiedOfDegree p K Ω n)) := by
    rw [mem_powers_iff_mem_zpowers, zpowers_frob]
    exact Subgroup.mem_top _
  obtain ⟨k, rfl⟩ := hmem
  exact ⟨frobUr p K Ω ^ k, frobUr_pow_apply hn k⟩

end PadicField
