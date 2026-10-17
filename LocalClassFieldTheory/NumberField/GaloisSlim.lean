/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.NumberField.KroneckerDensity.Bauer

/-!
# Absolute Galois groups of number fields are slim

Let `K` be a number field and `Ω` an algebraic closure of `K`. We prove that `G_K = Gal(Ω/K)`
is **slim**: the centralizer of every open subgroup is trivial
(`NumberField.centralizer_eq_bot_of_isOpen`), i.e. no nontrivial element of `G_K` commutes with
an open subgroup (`NumberField.eq_one_of_forall_mem_commute`). This is [AbsTopI], Theorem 1.7 (iii)
(slimness portion), which Mochizuki cites from [Mzk11] (*Global solvably closed anabelian
geometry*), Corollary 2.2 / Theorem 2.4; see also Neukirch–Schmidt–Wingberg, *Cohomology of
number fields*, Ch. XII §1. (Neither [Mzk11] nor [NSW] was available to us; the proof below is
self-contained.)

## Proof

Let `σ ∈ Gal(Ω/ℚ)` commute with `Gal(Ω/L)` for a finite extension `L/ℚ` inside `Ω`.

1. (`GaloisSlim.map_mem_of_commute`) `σ` maps every intermediate field `N ⊇ L` into itself: for
   `y ∈ N` and `τ ∈ Gal(Ω/N) ⊆ Gal(Ω/L)` we have `τ (σ y) = σ (τ y) = σ y`, so `σ y` lies in the
   fixed field of `Gal(Ω/N)`, which is `N` (infinite Galois theory).
2. (`GaloisSlim.exists_eq_sq_or_eq_mul_sq`, quadratic Kummer theory) If `x² = a ∈ M` and
   `y ∈ M(x)` with `y² = b ∈ M`, then `b = c²` or `b = a c²` for some `c ∈ M`.
3. (`GaloisSlim.smul_eq_self`) Let `M ⊇ L` be finite Galois over `ℚ` and `𝔭` a nonzero prime of
   `𝓞 M`. Then `σ|_M (𝔭) = 𝔭`. Otherwise `𝔮 = σ|_M (𝔭) ≠ 𝔭`; choose `a ∈ 𝓞 M` with `a ∈ 𝔭 \ 𝔭²`
   and `a ∉ 𝔮` (Chinese remainder theorem) and `x ∈ Ω` with `x² = a`. By 1, `σ x ∈ M(x)`, and
   `(σ x)² = σ a`, so by 2, `σ a ∈ M^{×2} ∪ a M^{×2}`. But `v_𝔮(σ a) = v_𝔭(a) = 1` and
   `v_𝔮(a) = 0`, so `v_𝔮(σ a)` would be even.
4. (`GaloisSlim.eq_one_of_commute`) For `y ∈ Ω`, let `M` be the Galois closure of `L(y)`. A
   rational prime `p` splitting completely in `M` exists
   (`NumberField.infinite_setOf_splitsCompletely`, from Kronecker's density theorem); the
   stabilizer in `Gal(M/ℚ)` of a prime of `𝓞 M` above `p`
   is trivial (`NumberField.SplitsCompletely.stabilizer_eq_bot`), and contains `σ|_M` by 3. Hence
   `σ|_M = 1` and `σ y = y`.

Finally, for a number field `K` an open subgroup of `Gal(Ω/K)` contains `Gal(Ω/E)` for a finite
`E/K`, and the `ℚ`-automorphisms of `Ω` fixing `E` are exactly the elements of `Gal(Ω/E)`.

No local class field theory and no local slimness is needed: the only arithmetic input beyond
Dedekind domain basics is the existence of a completely split prime.
-/

open IsDedekindDomain Ideal Pointwise

namespace NumberField

namespace GaloisSlim

variable {Ω : Type*} [Field Ω]

/-- **Quadratic Kummer theory.** If `x² ∈ M` and `y ∈ M(x)` has `y² ∈ M`, then `y² = c²` or
`y² = x² c²` for some `c ∈ M`. -/
theorem exists_eq_sq_or_eq_mul_sq [CharZero Ω] (M : IntermediateField ℚ Ω) {x y : Ω}
    (hx : x ^ 2 ∈ M) (hy : y ∈ IntermediateField.adjoin M {x}) (hy2 : y ^ 2 ∈ M) :
    ∃ c ∈ M, y ^ 2 = c ^ 2 ∨ y ^ 2 = x ^ 2 * c ^ 2 := by
  have hint : IsIntegral M x := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C ⟨x ^ 2, hx⟩, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub_C _ two_ne_zero
    · simp
  have hy' : y ∈ Algebra.adjoin M {x} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hy
  -- every element of `M[x]` has the form `u + v x` with `u, v ∈ M`
  have key : ∀ z ∈ Algebra.adjoin M {x}, ∃ u ∈ M, ∃ v ∈ M, z = u + v * x := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff] at hz
      exact ⟨0, M.zero_mem, 1, M.one_mem, by simp [hz]⟩
    | algebraMap r => exact ⟨r, r.2, 0, M.zero_mem, by simp⟩
    | add z w _ _ hz hw =>
      obtain ⟨u, hu, v, hv, rfl⟩ := hz
      obtain ⟨u', hu', v', hv', rfl⟩ := hw
      exact ⟨u + u', M.add_mem hu hu', v + v', M.add_mem hv hv', by ring⟩
    | mul z w _ _ hz hw =>
      obtain ⟨u, hu, v, hv, rfl⟩ := hz
      obtain ⟨u', hu', v', hv', rfl⟩ := hw
      refine ⟨u * u' + v * v' * x ^ 2, M.add_mem (M.mul_mem hu hu')
        (M.mul_mem (M.mul_mem hv hv') hx), u * v' + v * u',
        M.add_mem (M.mul_mem hu hv') (M.mul_mem hv hu'), by ring⟩
  obtain ⟨u, hu, v, hv, rfl⟩ := key y hy'
  by_cases hxM : x ∈ M
  · exact ⟨u + v * x, M.add_mem hu (M.mul_mem hv hxM), Or.inl rfl⟩
  by_cases hu0 : u = 0
  · exact ⟨v, hv, Or.inr (by rw [hu0]; ring)⟩
  by_cases hv0 : v = 0
  · exact ⟨u, hu, Or.inl (by rw [hv0]; ring)⟩
  exfalso
  apply hxM
  have h2 : u * v + u * v ≠ 0 := by
    rw [← two_mul]; simp [hu0, hv0]
  have : x = ((u + v * x) ^ 2 - u ^ 2 - v ^ 2 * x ^ 2) / (u * v + u * v) := by
    field_simp
    ring
  rw [this]
  exact M.div_mem (M.sub_mem (M.sub_mem hy2 (pow_mem hu 2)) (M.mul_mem (pow_mem hv 2) hx))
    (M.add_mem (M.mul_mem hu hv) (M.mul_mem hu hv))

/-- In `ℤᵐ⁰`, no square lies in `(exp (-2), exp (-1)]`. -/
theorem not_sq_mem_Ioc (w : WithZero (Multiplicative ℤ)) (h1 : w ^ 2 ≤ WithZero.exp (-1))
    (h2 : WithZero.exp (-2) < w ^ 2) : False := by
  induction w using WithZero.expRecOn with
  | zero => simp at h2
  | exp k =>
    rw [← WithZero.exp_nsmul, WithZero.exp_le_exp] at h1
    rw [← WithZero.exp_nsmul, WithZero.exp_lt_exp] at h2
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at h1 h2
    omega

/-- **Chinese remainder theorem**: for distinct maximal ideals `P ≠ Q` of a Dedekind domain with
`P ≠ ⊥`, some `a ∈ P \ P²` does not lie in `Q`. -/
theorem exists_mem_not_mem_sq_not_mem {R : Type*} [CommRing R] [IsDedekindDomain R]
    {P Q : Ideal R} [hP : P.IsMaximal] [hQ : Q.IsMaximal] (hP0 : P ≠ ⊥) (hPQ : P ≠ Q) :
    ∃ a ∈ P, a ∉ P ^ 2 ∧ a ∉ Q := by
  obtain ⟨π, hπP, hπP2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P hP0 hP.ne_top 2 le_rfl)
  have hcop : Q ⊔ P ^ 2 = ⊤ := by
    have : IsCoprime Q P := (Ideal.isCoprime_iff_sup_eq).mpr
      (hQ.coprime_of_ne hP (Ne.symm hPQ))
    exact (Ideal.isCoprime_iff_sup_eq).mp (this.pow_right (n := 2))
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp (hcop ▸ Submodule.mem_top : (1 : R) ∈ _)
  have htP : t ∈ P := Ideal.pow_le_self two_ne_zero ht
  refine ⟨π * s + t, P.add_mem (P.mul_mem_right s hπP) htP, fun h ↦ hπP2 ?_, fun h ↦ ?_⟩
  · have : π = (π * s + t) + (π * t - t) := by linear_combination -π * hst
    rw [this]
    exact (P ^ 2).add_mem h ((P ^ 2).sub_mem ((P ^ 2).mul_mem_left π ht) ht)
  · have : (1 : R) = (π * s + t) + (s - π * s) := by linear_combination -hst
    exact hQ.ne_top ((Q.eq_top_iff_one).mpr
      (this ▸ Q.add_mem h (Q.sub_mem hs (Q.mul_mem_left π hs))))

variable [CharZero Ω]

/-- **Step 1.** If `σ` commutes with `Gal(Ω/L)`, it maps every intermediate field `N ⊇ L` into
itself. -/
theorem map_mem_of_commute [IsGalois ℚ Ω] {σ : Ω ≃ₐ[ℚ] Ω} {L : IntermediateField ℚ Ω}
    (h : ∀ τ ∈ L.fixingSubgroup, σ * τ = τ * σ) {N : IntermediateField ℚ Ω} (hLN : L ≤ N)
    {y : Ω} (hy : y ∈ N) : σ y ∈ N := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup N, IntermediateField.mem_fixedField_iff]
  intro τ hτ
  have hc := DFunLike.congr_fun (h τ (IntermediateField.fixingSubgroup_antitone hLN hτ)) y
  have hτy : τ y = y := (mem_fixingSubgroup_iff _).mp hτ y hy
  simp only [AlgEquiv.mul_apply, hτy] at hc
  exact hc.symm

/-- **Step 3.** If `σ` commutes with `Gal(Ω/L)` and `M ⊇ L` is a number field normal over `ℚ`,
then `σ|_M` fixes every nonzero prime of `𝓞 M`. -/
theorem smul_eq_self [IsAlgClosed Ω] [IsGalois ℚ Ω] {σ : Ω ≃ₐ[ℚ] Ω} {L : IntermediateField ℚ Ω}
    (h : ∀ τ ∈ L.fixingSubgroup, σ * τ = τ * σ) (M : IntermediateField ℚ Ω) [NumberField M]
    [Normal ℚ M] (hLM : L ≤ M) (P : Ideal (𝓞 M)) [hPm : P.IsMaximal] (hP0 : P ≠ ⊥) :
    σ.restrictNormal M • P = P := by
  set g := σ.restrictNormal M
  by_contra hne
  have hQ0 : g • P ≠ ⊥ := fun h0 ↦ hP0 (by rw [← inv_smul_smul g P, h0, Ideal.smul_bot])
  have hQp : (g • P).IsPrime := by
    rw [Ideal.pointwise_smul_eq_comap]; exact Ideal.IsPrime.comap _
  have hQm : (g • P).IsMaximal := hQp.isMaximal hQ0
  obtain ⟨a, haP, haP2, haQ⟩ := exists_mem_not_mem_sq_not_mem hP0 (Ne.symm hne)
  -- a square root `x` of `a` in `Ω`
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (((a : M) : Ω)) two_pos
  have hxM : x ^ 2 ∈ M := hx ▸ (a : M).2
  -- `σ x ∈ M(x)`
  have hσx : σ x ∈ IntermediateField.adjoin M {x} := by
    have hle : L ≤ (IntermediateField.adjoin M {x}).restrictScalars ℚ := fun z hz ↦
      (IntermediateField.adjoin M {x}).algebraMap_mem ⟨z, hLM hz⟩
    exact map_mem_of_commute h hle (IntermediateField.subset_adjoin M {x} rfl)
  have hga : (((g • a : 𝓞 M) : M) : Ω) = σ ((a : M) : Ω) :=
    AlgEquiv.restrictNormal_commutes σ M a
  have hσx2 : (σ x) ^ 2 = (((g • a : 𝓞 M) : M) : Ω) := by rw [hga, ← map_pow, hx]
  obtain ⟨c, hcM, hc⟩ := exists_eq_sq_or_eq_mul_sq M hxM hσx (hσx2 ▸ ((g • a : 𝓞 M) : M).2)
  set c' : M := ⟨c, hcM⟩
  -- the valuation at `𝔮 = σ 𝔭`
  let v : HeightOneSpectrum (𝓞 M) := ⟨g • P, hQp, hQ0⟩
  have h1 : v.valuation M ((g • a : 𝓞 M) : M) ≤ WithZero.exp (-1) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_le_pow_iff_mem _ 1).mpr
      (by rw [pow_one]; exact Ideal.smul_mem_pointwise_smul_iff.mpr haP)
  have h2 : ¬ v.valuation M ((g • a : 𝓞 M) : M) ≤ WithZero.exp (-2) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    intro hle
    have := (v.intValuation_le_pow_iff_mem _ 2).mp hle
    change g • a ∈ (g • P) ^ 2 at this
    rw [← smul_pow', Ideal.smul_mem_pointwise_smul_iff] at this
    exact haP2 this
  have ha1 : v.valuation M (a : M) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.mpr haQ
  have hsq : v.valuation M ((g • a : 𝓞 M) : M) = v.valuation M c' ^ 2 := by
    rcases hc with hc | hc
    · rw [← map_pow]; congr 1; apply Subtype.ext; rw [← hσx2, hc]; rfl
    · rw [← one_mul (v.valuation M c' ^ 2), ← ha1, ← map_pow, ← map_mul]; congr 1
      apply Subtype.ext; rw [← hσx2, hc, hx]; rfl
  rw [hsq] at h1 h2
  exact not_sq_mem_Ioc _ h1 (lt_of_not_ge h2)

/-- **Step 4.** If `σ ∈ Gal(Ω/ℚ)` commutes with `Gal(Ω/L)` for a finite extension `L/ℚ` inside
the algebraic closure `Ω` of `ℚ`, then `σ = 1`. -/
theorem eq_one_of_commute [IsAlgClosed Ω] [Algebra.IsAlgebraic ℚ Ω] {σ : Ω ≃ₐ[ℚ] Ω}
    {L : IntermediateField ℚ Ω} [FiniteDimensional ℚ L]
    (h : ∀ τ ∈ L.fixingSubgroup, σ * τ = τ * σ) : σ = 1 := by
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  ext y
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {y}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  let M := IntermediateField.normalClosure ℚ (L ⊔ IntermediateField.adjoin ℚ {y} :
    IntermediateField ℚ Ω) Ω
  haveI hfin : FiniteDimensional ℚ M := normalClosure.is_finiteDimensional ℚ _ Ω
  haveI : NumberField M :=
    { to_finiteDimensional := (finiteDimensional_rat_iff _ _).mp hfin }
  haveI : Normal ℚ M := normalClosure.normal ℚ _ Ω
  haveI : IsGalois ℚ M := IsGalois.mk
  have hLM : L ≤ M := le_sup_left.trans (IntermediateField.le_normalClosure _)
  have hyM : y ∈ M := IntermediateField.le_normalClosure _
    ((le_sup_right : IntermediateField.adjoin ℚ {y} ≤ L ⊔ _)
      (IntermediateField.mem_adjoin_simple_self ℚ y))
  obtain ⟨p, hp, hsplit⟩ := (infinite_setOf_splitsCompletely M).nonempty
  haveI := isPrime_span_natCast hp
  obtain ⟨⟨P, hPp⟩⟩ := (Ideal.span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 M)
  haveI : P.IsMaximal := isMaximal_of_mem_primesOver hp hPp
  haveI := hPp.2
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (span_natCast_ne_bot hp) P
  have hg : σ.restrictNormal M ∈ MulAction.stabilizer Gal(M/ℚ) P := smul_eq_self h M hLM P hP0
  rw [hsplit.stabilizer_eq_bot P hPp, Subgroup.mem_bot] at hg
  have := AlgEquiv.restrictNormal_commutes σ M ⟨y, hyM⟩
  rw [hg] at this
  simpa using this.symm

end GaloisSlim

open GaloisSlim in
/-- **Absolute Galois groups of number fields are slim** (element form): if `σ ∈ Gal(Ω/K)`
commutes with every element of an open subgroup `H`, then `σ = 1`. -/
theorem eq_one_of_forall_mem_commute (K Ω : Type*) [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] {H : Subgroup Gal(Ω/K)} (hH : IsOpen (H : Set Gal(Ω/K)))
    {σ : Gal(Ω/K)} (hσ : ∀ τ ∈ H, τ * σ = σ * τ) : σ = 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ K Ω
  obtain ⟨E, hEfin, hEH⟩ := (krullTopology_mem_nhds_one_iff K Ω H).mp (hH.mem_nhds H.one_mem)
  haveI : FiniteDimensional ℚ E := Module.Finite.trans K E
  haveI : FiniteDimensional ℚ (E.restrictScalars ℚ) := this
  have key : σ.restrictScalars ℚ = 1 := by
    refine eq_one_of_commute (L := E.restrictScalars ℚ) fun τ hτ ↦ ?_
    have hτE : ∀ z ∈ E, τ z = z := fun z hz ↦ (mem_fixingSubgroup_iff _).mp hτ z hz
    let τK : Gal(Ω/K) := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv)
      fun k ↦ hτE _ (E.algebraMap_mem k)
    have hτK : τK ∈ H := hEH ((mem_fixingSubgroup_iff _).mpr fun z hz ↦ hτE z hz)
    ext z
    exact (DFunLike.congr_fun (hσ τK hτK) z).symm
  ext z
  simpa using DFunLike.congr_fun key z

/-- **Absolute Galois groups of number fields are slim** ([AbsTopI], Theorem 1.7 (iii)): the
centralizer of every open subgroup of `Gal(Ω/K)` is trivial. -/
theorem centralizer_eq_bot_of_isOpen (K Ω : Type*) [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] {H : Subgroup Gal(Ω/K)} (hH : IsOpen (H : Set Gal(Ω/K))) :
    Subgroup.centralizer (H : Set Gal(Ω/K)) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun _ hσ ↦
    eq_one_of_forall_mem_commute K Ω hH fun τ hτ ↦ Subgroup.mem_centralizer_iff.mp hσ τ hτ

end NumberField
