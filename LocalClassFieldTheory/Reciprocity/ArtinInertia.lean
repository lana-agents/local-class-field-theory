/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.ExistenceTheorem

/-!
# Injectivity of the Artin map; units and inertia

* `PadicField.eq_one_of_forall_pow`: `⋂ₙ (Kˣ)ⁿ = 1`;
* `PadicField.artin_injective`: the Artin map `Kˣ → Gal(K^ab/K)` is injective (by the existence
  theorem, its kernel lies in every `(Kˣ)ⁿ`);
* `PadicField.exists_unit_artin_eq`: every element of the inertia group `Gal(K^ab/K^ur)` is the
  image of a unit (compactness of the unit sphere of `K` and surjectivity at every finite level);
* `PadicField.unitsInertiaEquiv`: `𝒪ˣ ≃* Gal(K^ab/K^ur)` via the Artin map.
-/

set_option linter.unusedSectionVars false

open IntermediateField IsLocalRing Teichmuller

namespace PadicField

section LocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- `(1 + 𝔪ᵏ)^ℓ ⊆ 1 + 𝔪^(k+1)` for a prime `ℓ ∈ 𝔪` and `k ≥ 1`. -/
theorem one_add_pow_prime_sub_one_mem {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓR : (ℓ : R) ∈ maximalIdeal R)
    {k : ℕ} (hk : 1 ≤ k) {z : R} (hz : z ∈ maximalIdeal R ^ k) :
    (1 + z) ^ ℓ - 1 ∈ maximalIdeal R ^ (k + 1) := by
  rw [one_add_pow_sub_one]
  refine Ideal.sum_mem _ fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  have hzj : z ^ (j + 1) ∈ maximalIdeal R ^ (k * (j + 1)) := by
    rw [pow_mul]; exact Ideal.pow_mem_pow hz _
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hj) with h | h
  · obtain ⟨c, hc⟩ := hℓ.dvd_choose_self (Nat.succ_ne_zero j) h
    rw [hc, Nat.cast_mul, mul_assoc, pow_succ']
    refine Ideal.mul_mem_mul hℓR (Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right ?_ hzj))
    exact Nat.le_mul_of_pos_right k (Nat.succ_pos j)
  · refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right ?_ hzj)
    have h2 : 2 ≤ j + 1 := by have := hℓ.two_le; omega
    nlinarith

/-- `(1 + 𝔪)^(ℓ^k) ⊆ 1 + 𝔪^(k+1)` for a prime `ℓ ∈ 𝔪`. -/
theorem pow_prime_pow_sub_one_mem {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓR : (ℓ : R) ∈ maximalIdeal R)
    {u : R} (hu : u - 1 ∈ maximalIdeal R) (k : ℕ) :
    u ^ (ℓ ^ k) - 1 ∈ maximalIdeal R ^ (k + 1) := by
  induction k with
  | zero => simpa using hu
  | succ k ih =>
    have h := one_add_pow_prime_sub_one_mem hℓ hℓR (Nat.succ_pos k) ih
    rwa [add_sub_cancel, ← pow_mul, ← pow_succ] at h

/-- Units satisfy `y^(Q-1) ≡ 1 (mod 𝔪)`, `Q` the cardinality of the residue field. -/
theorem pow_Q_sub_one_sub_one_mem [Finite (ResidueField R)] {y : R} (hy : IsUnit y) :
    y ^ (Q R - 1) - 1 ∈ maximalIdeal R := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change residue R (y ^ (Q R - 1) - 1) = 0
  rw [map_sub, map_pow, map_one, sub_eq_zero]
  have h0 : residue R y ≠ 0 := (hy.map (residue R)).ne_zero
  have h1 : residue R y ^ (Q R - 1) * residue R y = 1 * residue R y := by
    rw [← pow_succ, Nat.sub_add_cancel one_lt_Q.le, pow_Q_residue, one_mul]
  exact mul_right_cancel₀ h0 h1

end LocalRing

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

open Integers

include hp in
theorem natCast_p_mem_maximalIdeal : ((p : ℕ) : 𝒪 p K) ∈ maximalIdeal (𝒪 p K) := by
  have h : (((p : ℕ) : 𝒪 p K) : K) = (p : K) := map_natCast (algebraMap (𝒪 p K) K) p
  rw [mem_maximalIdeal_iff, h, nrm_lt_one_iff_wval_pos natCast_p_ne_zero, wval_natCast_p]
  exact_mod_cast expo_pos p K

include hp in
/-- **`⋂ₙ (Kˣ)ⁿ = 1`**. -/
theorem eq_one_of_forall_pow (x : Kˣ) (h : ∀ n : ℕ, 0 < n → ∃ y : Kˣ, y ^ n = x) : x = 1 := by
  have hvx : v p (x : K) = 0 := by
    obtain ⟨n, hn⟩ : ∃ n, n = (v p (x : K)).natAbs + 1 := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ := h n (by omega)
    have h1 : v p (x : K) = (n : ℤ) * v p (y : K) := by
      rw [← hy, Units.val_pow_eq_pow_val, v_pow y.ne_zero]
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨_, h1⟩ (by rw [Int.natAbs_natCast]; omega)
  have hx1 : nrm p K (x : K) ≤ 1 := ((nrm_eq_one_iff_v_eq_zero x.ne_zero).2 hvx).le
  set x' : 𝒪 p K := mk (x : K) hx1
  have hmem : ∀ k : ℕ, x' - 1 ∈ maximalIdeal (𝒪 p K) ^ (k + 1) := by
    intro k
    obtain ⟨y, hy⟩ := h ((Q (𝒪 p K) - 1) * p ^ k)
      (Nat.mul_pos (Nat.sub_pos_of_lt one_lt_Q) (pow_pos hp.out.pos k))
    have hvy : v p (y : K) = 0 := by
      have h1 := congrArg (fun z : Kˣ ↦ v p (z : K)) hy
      simp only [Units.val_pow_eq_pow_val, v_pow y.ne_zero, hvx] at h1
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exfalso
        have : 0 < (Q (𝒪 p K) - 1) * p ^ k :=
          Nat.mul_pos (Nat.sub_pos_of_lt one_lt_Q) (pow_pos hp.out.pos k)
        exact this.ne' (by exact_mod_cast h2)
      · exact h2
    have hy1 : nrm p K (y : K) = 1 := (nrm_eq_one_iff_v_eq_zero y.ne_zero).2 hvy
    set y' : 𝒪 p K := mk (y : K) hy1.le
    have hy' : IsUnit y' := isUnit_iff_nrm_eq_one.2 hy1
    have hxy : x' = (y' ^ (Q (𝒪 p K) - 1)) ^ (p ^ k) := by
      apply Integers.ext
      rw [← pow_mul]
      change (x : K) = ((y' ^ ((Q (𝒪 p K) - 1) * p ^ k) : 𝒪 p K) : K)
      rw [coe_eq_algebraMap, map_pow, ← coe_eq_algebraMap, ← hy, Units.val_pow_eq_pow_val]
      rfl
    rw [hxy]
    exact pow_prime_pow_sub_one_mem hp.out natCast_p_mem_maximalIdeal
      (pow_Q_sub_one_sub_one_mem hy') k
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (𝒪 p K))
    (maximalIdeal.isMaximal (𝒪 p K)).ne_top
  have h0 : x' - 1 ∈ (⊥ : Ideal (𝒪 p K)) := by
    rw [← hbot, Submodule.mem_iInf]
    intro i
    exact Ideal.pow_le_pow_right (Nat.le_succ i) (hmem i)
  rw [Ideal.mem_bot, sub_eq_zero] at h0
  apply Units.ext
  have := congrArg (fun z : 𝒪 p K ↦ (z : K)) h0
  simpa [x'] using this

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

include hp in
/-- **The Artin map is injective.** -/
theorem artin_injective : Function.Injective (artin p K Ω) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  refine eq_one_of_forall_pow (p := p) (K := K) x fun n hn ↦ ?_
  obtain ⟨L, hL⟩ := exists_abFin_normGroup_le_pow' (p := p) (K := K) (Ω := Ω) hn
  exact hL x ((mem_ker_artin_iff x).1 hx L)

include hp in
/-- **Units map onto inertia**: every automorphism of `K^ab` fixing `K^ur` is `artin u` for a unit
`u`. Proof: the sets `{x ∈ K : ‖x‖ = 1, abRec_L x = σ|_L}` are nonempty
(`PadicField.exists_unit_abRec_eq`), closed (norm groups are open) and directed, inside the compact
unit sphere of `K`. -/
theorem exists_unit_artin_eq (σ : maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω)
    (hσ : ∀ y : maxAbelian K Ω, (y : Ω) ∈ maxUnramified p K Ω → σ y = y) :
    ∃ u : Kˣ, v p (u : K) = 0 ∧ artin p K Ω u = σ := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  letI : NormedField K := spectralNorm.normedField ℚ_[p] K
  letI : NormedSpace ℚ_[p] K := spectralNorm.normedSpace ℚ_[p] K
  haveI : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  have hn : ∀ x : K, ‖x‖ = nrm p K x := fun _ ↦ rfl
  let σL : ∀ L : AbFin K Ω, L.1 ≃ₐ[K] L.1 := fun L ↦ resHom (le_maxAbelian L) σ
  let T : AbFin K Ω → Set K := fun L ↦ Metric.sphere 0 1 ∩
    {x | ∀ hx : x ≠ 0, abRec p L.1 (Units.mk0 x hx) = σL L}
  have hclosed : ∀ L, IsClosed (T L) := by
    intro L
    refine Metric.isClosed_sphere.inter ?_
    rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨hx0, hxσ⟩ := hx
    set c := nrm p K (((Module.finrank K L.1 * (Module.finrank K L.1 * p)) : ℕ) : K)
    have hc : 0 < c := nrm_pos_iff.2 (Nat.cast_ne_zero.2 (Nat.mul_pos Module.finrank_pos
      (Nat.mul_pos Module.finrank_pos hp.out.pos)).ne')
    have hx0' : 0 < nrm p K x := nrm_pos_iff.2 hx0
    refine ⟨nrm p K x * min c 1, mul_pos hx0' (lt_min hc one_pos), fun y hy ↦ ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, hn] at hy
    have hy' : nrm p K (y - x) < nrm p K x * c :=
      hy.trans_le (mul_le_mul_of_nonneg_left (min_le_left _ _) hx0'.le)
    have hy0 : y ≠ 0 := by
      rintro rfl
      have := hy.trans_le (mul_le_mul_of_nonneg_left (min_le_right _ _) hx0'.le)
      rw [zero_sub, ← hn, norm_neg, hn, mul_one] at this
      exact lt_irrefl _ this
    have hq : nrm p K ((Units.mk0 (y / x) (div_ne_zero hy0 hx0) : K) - 1) < c := by
      rw [Units.val_mk0, div_sub_one hx0, nrm_div, div_lt_iff₀ hx0', mul_comm]
      exact hy'
    have hmem := mem_normGroup_of_nrm_sub_one_lt (p := p) (L := L.1) _ hq
    rw [← ker_abRec (p := p), MonoidHom.mem_ker] at hmem
    have hyx : Units.mk0 y hy0 = Units.mk0 (y / x) (div_ne_zero hy0 hx0) * Units.mk0 x hx0 :=
      Units.ext (by simp [div_mul_cancel₀ y hx0])
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall]
    refine ⟨hy0, ?_⟩
    rw [hyx, map_mul, hmem, one_mul]
    exact hxσ
  have hcompact : ∀ L, IsCompact (T L) := fun L ↦
    (isCompact_sphere 0 1).of_isClosed_subset (hclosed L) Set.inter_subset_left
  have hne : ∀ L, (T L).Nonempty := by
    intro L
    obtain ⟨u, hu0, hu⟩ := exists_unit_abRec_eq (p := p) L.1 (σL L) fun y hy ↦ by
      apply Subtype.ext
      rw [resHom_apply]
      exact congrArg Subtype.val (hσ _ hy)
    refine ⟨u, ?_, fun _ ↦ ?_⟩
    · rw [mem_sphere_zero_iff_norm, hn]
      exact (nrm_eq_one_iff_v_eq_zero u.ne_zero).2 hu0
    · rwa [Units.mk0_val]
  have hsub : ∀ L L' : AbFin K Ω, L.1 ≤ L'.1 → T L' ⊆ T L := by
    intro L L' hLL' x hx
    refine ⟨hx.1, fun hx0 ↦ ?_⟩
    rw [← resHom_abRec_of_le L'.1 L.1 hLL', hx.2 hx0]
    exact resHom_trans _ _ _
  have hdir : Directed (· ⊇ ·) T := by
    intro L₁ L₂
    haveI := isAbelianGalois_sup L₁.1 L₂.1
    exact ⟨⟨L₁.1 ⊔ L₂.1, inferInstance, inferInstance⟩, hsub _ _ le_sup_left,
      hsub _ _ le_sup_right⟩
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed T hdir hne hcompact hclosed
  rw [Set.mem_iInter] at hx
  have hx1 : nrm p K x = 1 := by
    have := (hx (Classical.arbitrary _)).1
    rwa [mem_sphere_zero_iff_norm, hn] at this
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [nrm_eq_zero_iff.2 rfl] at hx1; exact zero_ne_one hx1
  refine ⟨Units.mk0 x hx0, (nrm_eq_one_iff_v_eq_zero hx0).1 hx1, ?_⟩
  ext ⟨y, hy⟩
  obtain ⟨L, hyL⟩ := mem_maxAbelian_iff.1 hy
  rw [artin_apply _ L.1 y hyL, (hx L).2 hx0]
  exact resHom_apply _ _ _

variable (p K Ω) in
/-- The inertia subgroup `Gal(K^ab/K^ur)` of `Gal(K^ab/K)`. -/
def abInertia : Subgroup (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) where
  carrier := {σ | ∀ y : maxAbelian K Ω, (y : Ω) ∈ maxUnramified p K Ω → σ y = y}
  mul_mem' {σ τ} hσ hτ y hy := by rw [AlgEquiv.mul_apply, hτ y hy, hσ y hy]
  one_mem' _ _ := rfl
  inv_mem' {σ} hσ y hy := by
    rw [AlgEquiv.aut_inv]
    exact (AlgEquiv.symm_apply_eq σ).2 (hσ y hy).symm

theorem mem_abInertia {σ : maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω} :
    σ ∈ abInertia p K Ω ↔ ∀ y : maxAbelian K Ω, (y : Ω) ∈ maxUnramified p K Ω → σ y = y :=
  Iff.rfl

theorem artin_mem_abInertia (u : unitGroup p K) : artin p K Ω u ∈ abInertia p K Ω := by
  intro y hy
  have hv : v p ((u : Kˣ) : K) = 0 := (nrm_eq_one_iff_v_eq_zero (u : Kˣ).ne_zero).1 u.2
  exact Subtype.ext (artin_apply_maxUnramified_of_v_eq_zero (p := p) (Ω := Ω) (u : Kˣ) hv
    ⟨(y : Ω), hy⟩)

variable (p K Ω) in
/-- **Units and inertia**: the Artin map restricts to an isomorphism
`𝒪ˣ ≃* Gal(K^ab/K^ur)`. -/
noncomputable def unitsInertiaEquiv : unitGroup p K ≃* abInertia p K Ω :=
  MulEquiv.ofBijective
    (((artin p K Ω).comp (unitGroup p K).subtype).codRestrict (abInertia p K Ω)
      artin_mem_abInertia)
    ⟨fun u u' h ↦ Subtype.ext (artin_injective (p := p) (Ω := Ω)
        (congrArg Subtype.val h)),
      fun σ ↦ by
        obtain ⟨u, hu0, hu⟩ := exists_unit_artin_eq (p := p) σ.1 σ.2
        exact ⟨⟨u, (nrm_eq_one_iff_v_eq_zero u.ne_zero).2 hu0⟩, Subtype.ext hu⟩⟩

theorem unitsInertiaEquiv_apply (u : unitGroup p K) :
    (unitsInertiaEquiv p K Ω u : maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) = artin p K Ω u := rfl

include hp in
/-- **The Artin map has dense image** in `Gal(K^ab/K)` (Krull topology). -/
theorem denseRange_artin : DenseRange (artin p K Ω) := by
  intro σ
  rw [mem_closure_iff_nhds]
  intro U hU
  have h1 : (fun τ ↦ σ * τ) ⁻¹' U ∈ nhds (1 : maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) := by
    refine (continuous_const_mul σ).continuousAt.preimage_mem_nhds ?_
    rwa [mul_one]
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff K _ _).1 h1
  obtain ⟨L, hL⟩ := exists_abFin_le E
  obtain ⟨x, hx⟩ := abRec_surjective (p := p) L.1 (resHom (le_maxAbelian L) σ)
  refine ⟨artin p K Ω x, ?_, x, rfl⟩
  have h2 : σ⁻¹ * artin p K Ω x ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have h3 : artin p K Ω x y = σ y := by
      apply Subtype.ext
      rw [artin_apply x L.1 y (hL y hy), hx, resHom_apply]
      rfl
    rw [AlgEquiv.mul_apply, h3, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have := hEs h2
  simpa only [Set.mem_preimage, mul_inv_cancel_left] using this

end PadicField
