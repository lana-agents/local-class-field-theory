/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.Galois
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Structure of Galois groups of local fields

For a finite extension `L/K` of fields finite over `ℚ_[p]` we show that every non-trivial subgroup
`H ≤ Aut(L/K)` is cyclic or has a proper non-trivial normal subgroup
(`PadicField.isCyclic_or_exists_normal`). This is the solvability input for the bound
`|H²(Gal(L/K), Lˣ)| ≤ [L : K]`.

The filtration used is `H ⊇ H ∩ I ⊇ H ∩ I₁`:
* the inertia group `I` is the kernel of `Gal(L/K) → Gal(𝓴_L/𝓴_K)` (a cyclic group);
* on `I` the **tame character** `PadicField.tameChar : I →* (𝓴_L)ˣ`, `σ ↦ σ(π)/π mod 𝔪`, is a
  homomorphism into a cyclic group;
* its kernel, the wild inertia group, is a `p`-group (`PadicField.isPGroup_ker_tameChar`): an
  element `σ` of the kernel satisfies `‖σ x - x‖ ≤ ‖π‖ ‖x‖`, and if `σ^m = 1` with `p ∤ m` the
  binomial expansion of `(1 + (σ - 1))^m = 1` forces `σ = 1`;
* a non-trivial `p`-group is cyclic of order `p` or has a proper non-trivial normal subgroup
  (its centre, or a subgroup of order `p` of an abelian group).
-/

open IsLocalRing

set_option linter.unusedSectionVars false

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L]

section Tame

omit [FiniteDimensional ℚ_[p] K] in
variable (p) in
theorem nrm_ratio (σ : L ≃ₐ[K] L) : nrm p L (σ (uniformizer p L) / uniformizer p L) = 1 := by
  rw [nrm_div, nrm_algEquiv_tower, div_self]
  exact (nrm_pos_iff.2 (uniformizer_spec (p := p) (K := L)).ne_zero).ne'

/-- `σ(π)/π` as a unit of `𝒪_L`. -/
noncomputable def ratioUnit (σ : L ≃ₐ[K] L) : (𝒪 p L)ˣ :=
  (Integers.isUnit_iff_nrm_eq_one.2 (by
    rw [Integers.coe_mk]; exact nrm_ratio p σ) :
    IsUnit (Integers.mk (σ (uniformizer p L) / uniformizer p L) (nrm_ratio p σ).le)).unit

theorem coe_ratioUnit (σ : L ≃ₐ[K] L) :
    (((ratioUnit (p := p) σ : 𝒪 p L)) : L) = σ (uniformizer p L) / uniformizer p L := rfl

/-- The **tame character** `I → 𝓴_Lˣ`, `σ ↦ σ(π)/π mod 𝔪`. -/
noncomputable def tameChar : inertia p K L →* (𝓴 p L)ˣ where
  toFun σ := Units.map (residue (𝒪 p L) : 𝒪 p L →* 𝓴 p L) (ratioUnit (p := p) (σ : L ≃ₐ[K] L))
  map_one' := by
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_one]
    rw [← map_one (residue (𝒪 p L))]
    congr 1
    apply Integers.ext
    rw [coe_ratioUnit]
    simp [div_self (uniformizer_spec (p := p) (K := L)).ne_zero]
  map_mul' σ τ := by
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe, Units.val_mul]
    -- `στπ/π = σ(τπ/π) · σπ/π`, and `σ` acts trivially modulo `𝔪`
    have hσ := (mem_inertia_iff (σ : L ≃ₐ[K] L)).1 σ.2 (ratioUnit (p := p) (τ : L ≃ₐ[K] L))
    have h1 : ((ratioUnit (p := p) ((σ * τ : inertia p K L) : L ≃ₐ[K] L) : 𝒪 p L)) =
        (σ : L ≃ₐ[K] L) • (ratioUnit (p := p) (τ : L ≃ₐ[K] L) : 𝒪 p L) *
          (ratioUnit (p := p) (σ : L ≃ₐ[K] L) : 𝒪 p L) := by
      apply Integers.ext
      simp only [Integers.coe_mul, Integers.coe_smul, coe_ratioUnit, Subgroup.coe_mul,
        AlgEquiv.mul_apply, map_div₀]
      field_simp [(uniformizer_spec (p := p) (K := L)).ne_zero]
    rw [h1, map_mul, mul_comm]
    congr 1
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hσ

end Tame

section Wild

variable (p) in
theorem nrm_le_nrm_uniformizer_of_lt_one {y : L} (hy : nrm p L y < 1) :
    nrm p L y ≤ nrm p L (uniformizer p L) := by
  by_cases hy0 : y = 0
  · rw [hy0, (nrm_eq_zero_iff (p := p)).2 rfl]
    exact nrm_nonneg _
  have hπ := uniformizer_spec (p := p) (K := L)
  rw [nrm_le_iff_v_le hy0 hπ.ne_zero, hπ]
  have := (nrm_lt_one_iff_v_pos hy0).1 hy
  omega

theorem nrm_pow_sub_one_lt {w : L} (hw : nrm p L w = 1) (hw1 : nrm p L (w - 1) < 1) (k : ℤ) :
    nrm p L (w ^ k - 1) < 1 := by
  have hnat : ∀ n : ℕ, nrm p L (w ^ n - 1) < 1 := by
    intro n
    induction n with
    | zero => simp [(nrm_eq_zero_iff (p := p)).2 rfl]
    | succ n ih =>
      have : w ^ (n + 1) - 1 = w ^ n * (w - 1) + (w ^ n - 1) := by ring
      rw [this]
      refine lt_of_le_of_lt (nrm_add_le_max _ _) (max_lt ?_ ih)
      rw [nrm_mul, nrm_pow, hw, one_pow, one_mul]
      exact hw1
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp [(nrm_eq_zero_iff (p := p)).2 rfl] at hw
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]; exact hnat n
  · rw [zpow_neg, zpow_natCast]
    have : (w ^ n)⁻¹ - 1 = -((w ^ n - 1) / w ^ n) := by
      field_simp
      ring
    rw [this, nrm_neg, nrm_div, nrm_pow, hw, one_pow, div_one]
    exact hnat n

/-- Elements of the wild inertia group move every `x` by at most `‖π‖ ‖x‖`. -/
theorem nrm_sub_le_of_tameChar_eq_one (σ : inertia p K L) (hσ : tameChar σ = 1) (x : L) :
    nrm p L ((σ : L ≃ₐ[K] L) x - x) ≤ nrm p L (uniformizer p L) * nrm p L x := by
  by_cases hx : x = 0
  · simp [hx, (nrm_eq_zero_iff (p := p)).2 rfl]
  have hπ := uniformizer_spec (p := p) (K := L)
  obtain ⟨u, hu, hxu⟩ := eq_zpow_mul_unit hπ hx
  set π := uniformizer p L
  set k := v p x
  set w := (σ : L ≃ₐ[K] L) π / π with hwdef
  have hw : nrm p L w = 1 := nrm_ratio p _
  have hw1 : nrm p L (w - 1) < 1 := by
    have h := congrArg Units.val hσ
    simp only [tameChar, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map, MonoidHom.coe_coe,
      Units.val_one] at h
    rw [← map_one (residue (𝒪 p L)), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
      Integers.mem_maximalIdeal_iff] at h
    simpa [coe_ratioUnit] using h
  have hu1 : nrm p L ((σ : L ≃ₐ[K] L) u - u) < 1 := by
    have h := (mem_inertia_iff (σ : L ≃ₐ[K] L)).1 σ.2 (Integers.mk u hu.le)
    rw [Integers.mem_maximalIdeal_iff] at h
    simpa [Integers.coe_smul] using h
  have hσπ : (σ : L ≃ₐ[K] L) π = π * w := by
    rw [hwdef, mul_div_cancel₀ _ hπ.ne_zero]
  have hσx : (σ : L ≃ₐ[K] L) x - x = π ^ k * (w ^ k * ((σ : L ≃ₐ[K] L) u - u) + (w ^ k - 1) * u) := by
    rw [hxu, map_mul, map_zpow₀, hσπ, mul_zpow]
    ring
  rw [hσx, nrm_mul, hxu, nrm_mul, hu, mul_one, mul_comm]
  refine mul_le_mul_of_nonneg_right (nrm_le_nrm_uniformizer_of_lt_one p ?_) (nrm_nonneg _)
  refine lt_of_le_of_lt (nrm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [nrm_mul, nrm_zpow, hw, one_zpow, one_mul]
    exact hu1
  · rw [nrm_mul, hu, mul_one]
    exact nrm_pow_sub_one_lt hw hw1 k

/-- An element of the wild inertia group of order prime to `p` is trivial. -/
theorem eq_one_of_tameChar_eq_one {σ : inertia p K L} (hσ : tameChar σ = 1) {m : ℕ}
    (hm : ¬ p ∣ m) (hσm : σ ^ m = 1) : σ = 1 := by
  set c := nrm p L (uniformizer p L)
  have hc : c < 1 := (uniformizer_spec (p := p) (K := L)).nrm_lt_one
  have hc0 : 0 ≤ c := nrm_nonneg _
  let τ : L ≃ₐ[K] L := σ
  have h1 : ∀ y, nrm p L (τ y - y) ≤ c * nrm p L y := nrm_sub_le_of_tameChar_eq_one σ hσ
  have hpow : ∀ i : ℕ, ∀ y, nrm p L ((τ ^ i) y - y) ≤ c * nrm p L y := by
    intro i
    induction i with
    | zero =>
      intro y
      simp only [pow_zero, AlgEquiv.one_apply, sub_self, (nrm_eq_zero_iff (p := p)).2 rfl]
      exact mul_nonneg hc0 (nrm_nonneg _)
    | succ i ih =>
      intro y
      have : (τ ^ (i + 1)) y - y = (τ ^ i) (τ y - y) + ((τ ^ i) y - y) := by
        rw [map_sub, pow_succ, AlgEquiv.mul_apply]
        ring
      rw [this]
      refine le_trans (nrm_add_le_max _ _) (max_le ?_ (ih y))
      have e := ih (τ y - y)
      calc nrm p L ((τ ^ i) (τ y - y))
          = nrm p L (τ y - y) := nrm_algEquiv_tower (σ := τ ^ i) (x := τ y - y)
        _ ≤ c * nrm p L y := h1 y
  have hτm : τ ^ m = 1 := by
    have := congrArg Subtype.val hσm
    simpa [τ] using this
  have hmnrm : nrm p L (m : L) = 1 := by
    rw [show (m : L) = algebraMap ℚ_[p] L (m : ℚ_[p]) by simp, nrm_algebraMap,
      Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hm
  apply Subtype.ext
  ext x
  -- `0 = τ^m x - x = ∑_{i<m} τ^i d = m d + ∑_{i<m} (τ^i d - d)` with `d = τ x - x`
  set d := τ x - x
  have htel : (τ ^ m) x - x = ∑ i ∈ Finset.range m, (τ ^ i) d := by
    have := Finset.sum_range_sub (fun i => (τ ^ i) x) m
    simp only [pow_zero, AlgEquiv.one_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [d, map_sub, pow_succ, AlgEquiv.mul_apply]
  have hsum : ∑ i ∈ Finset.range m, (τ ^ i) d =
      (m : L) * d + ∑ i ∈ Finset.range m, ((τ ^ i) d - d) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hzero : (m : L) * d + ∑ i ∈ Finset.range m, ((τ ^ i) d - d) = 0 := by
    rw [← hsum, ← htel, hτm, AlgEquiv.one_apply, sub_self]
  have hbound : nrm p L (∑ i ∈ Finset.range m, ((τ ^ i) d - d)) ≤ c * nrm p L d :=
    nrm_sum_le _ _ (mul_nonneg hc0 (nrm_nonneg _)) fun i _ => hpow i d
  have hd : nrm p L d ≤ c * nrm p L d := by
    have e : (m : L) * d = -∑ i ∈ Finset.range m, ((τ ^ i) d - d) := eq_neg_of_add_eq_zero_left hzero
    have := congrArg (nrm p L) e
    rw [nrm_mul, hmnrm, one_mul, nrm_neg] at this
    exact this.trans_le hbound
  have hd0 : nrm p L d = 0 := by
    by_contra hne
    have hpos : 0 < nrm p L d := lt_of_le_of_ne (nrm_nonneg _) (Ne.symm hne)
    nlinarith
  rw [nrm_eq_zero_iff, sub_eq_zero] at hd0
  simpa [τ] using hd0

/-- The **wild inertia group** (kernel of the tame character) is a `p`-group. -/
theorem isPGroup_ker_tameChar : IsPGroup p (tameChar (p := p) (K := K) (L := L)).ker := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ_[p] K L
  intro σ
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos σ).ne' p
    hp.out.ne_one
  refine ⟨e, ?_⟩
  have h1 : ((σ ^ p ^ e : (tameChar (p := p) (K := K) (L := L)).ker) : inertia p K L) = 1 := by
    apply eq_one_of_tameChar_eq_one (m := m)
    · exact (σ ^ p ^ e).2
    · exact hm
    · rw [← Subgroup.coe_pow, ← pow_mul, ← he, pow_orderOf_eq_one]
      rfl
  exact Subtype.ext h1

end Wild

section Structure

/-- A non-trivial finite `p`-group is cyclic or has a proper non-trivial normal subgroup. -/
theorem IsPGroup.isCyclic_or_exists_normal {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (hG : IsPGroup p G) : IsCyclic G ∨ ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  haveI := hG.center_nontrivial
  by_cases hZ : Subgroup.center G = ⊤
  · -- `G` is abelian: take a subgroup of order `p`
    have hdvd : p ∣ Nat.card G := by
      rcases hG.card_eq_or_dvd with h | h
      · exact absurd h (Finite.one_lt_card).ne'
      · exact h
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
    by_cases hN : Subgroup.zpowers g = ⊤
    · left
      exact ⟨g, fun x => by rw [← Subgroup.mem_zpowers_iff, hN]; trivial⟩
    · right
      refine ⟨Subgroup.zpowers g, ⟨fun n _ c => ?_⟩, ?_, hN⟩
      · have hc : c ∈ Subgroup.center G := hZ ▸ Subgroup.mem_top c
        rw [Subgroup.mem_center_iff] at hc
        rwa [← hc n, mul_inv_cancel_right]
      · intro h
        have : g = 1 := by
          have := Subgroup.mem_zpowers g
          rw [h, Subgroup.mem_bot] at this
          exact this
        rw [this, orderOf_one] at hg
        exact hp.out.one_lt.ne hg
  · right
    exact ⟨Subgroup.center G, inferInstance,
      (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance, hZ⟩

theorem inertia_normal : (inertia p K L).Normal := by
  rw [← ker_residueGal]
  exact MonoidHom.normal_ker _


end Structure

section Main

omit [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L] in
/-- **Galois groups of local fields are solvable** (in the form needed here): every non-trivial
subgroup `H ≤ Aut(L/K)` is cyclic or has a proper non-trivial normal subgroup. -/
theorem isCyclic_or_exists_normal (p : ℕ) [hp : Fact p.Prime] [Algebra ℚ_[p] K]
    [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
    [FiniteDimensional ℚ_[p] L] (H : Subgroup (L ≃ₐ[K] L)) [Nontrivial H] :
    IsCyclic H ∨ ∃ N : Subgroup H, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ_[p] K L
  haveI := inertia_normal (p := p) (K := K) (L := L)
  set N₁ : Subgroup H := (inertia p K L).comap H.subtype with hN₁
  by_cases h1 : N₁ = ⊥
  · left
    refine isCyclic_of_injective ((residueGal p K L).comp H.subtype) ?_
    rw [← MonoidHom.ker_eq_bot_iff, ← h1, eq_comm, hN₁, ← ker_residueGal,
      MonoidHom.comap_ker]
  by_cases h2 : N₁ = ⊤
  · have hHI : ∀ h : H, (h : L ≃ₐ[K] L) ∈ inertia p K L := fun h => by
      have : h ∈ N₁ := h2 ▸ Subgroup.mem_top h
      exact this
    let ι : H →* inertia p K L :=
      { toFun := fun h => ⟨h, hHI h⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
    set θ : H →* (𝓴 p L)ˣ := (tameChar (p := p) (K := K) (L := L)).comp ι
    by_cases h3 : θ.ker = ⊥
    · left
      exact isCyclic_of_injective θ ((MonoidHom.ker_eq_bot_iff θ).1 h3)
    by_cases h4 : θ.ker = ⊤
    · -- `H` is a `p`-group
      have hP : IsPGroup p H := by
        intro h
        have hk : ι h ∈ (tameChar (p := p) (K := K) (L := L)).ker := by
          have : h ∈ θ.ker := h4 ▸ Subgroup.mem_top h
          exact this
        obtain ⟨k, hk'⟩ := isPGroup_ker_tameChar (p := p) ⟨ι h, hk⟩
        refine ⟨k, Subtype.ext ?_⟩
        have := congrArg (fun x : (tameChar (p := p) (K := K) (L := L)).ker =>
          ((x : inertia p K L) : L ≃ₐ[K] L)) hk'
        simpa [ι] using this
      exact IsPGroup.isCyclic_or_exists_normal hP
    · right
      exact ⟨θ.ker, θ.normal_ker, h3, h4⟩
  · right
    exact ⟨N₁, (inertia_normal (p := p)).comap H.subtype, h1, h2⟩

end Main

end PadicField
