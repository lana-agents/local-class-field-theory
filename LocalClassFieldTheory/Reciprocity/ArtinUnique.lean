/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.ArtinInertia

/-!
# Uniqueness of the Artin map

The Artin map `artin : Kˣ → Gal(K^ab/K)` is the **unique** homomorphism `r` such that

* (Frobenius) for every uniformiser `π` of `K`, `r π` acts on the roots `y` of `X^(q^n) - X`
  (`n > 0`) as `y ↦ y ^ q`, i.e. as the arithmetic Frobenius on `K^ur`;
* (norms) for every finite abelian `L ⊆ Ω`, `r x` fixes `L` whenever `x ∈ N_{L/K} Lˣ`.

Proof (`PadicField.eq_of_frob_of_norm`): by `monoidHom_ext_of_v_eq_one` it suffices to compare
`r π` and `r' π` for uniformisers `π`. Given `L` with `[L : K] = m`, the existence theorem gives a
finite abelian `E` with `N_E = ⟨π⟩ · N_{L K_m}` (`PadicField.exists_abFin_uniformizer`); then
`L ⊆ E K_m` (`N_E ∩ N_{K_m} ⊆ N_L`, as `π^k b ∈ N_{K_m}` forces `m ∣ k`), and `r π`, `r' π` agree
on `E` (both trivial) and on `K_m` (both Frobenius).

* `PadicField.artin_apply_of_pow_eq`, `PadicField.artin_apply_of_mem_normGroup`: the Artin map
  has both properties;
* **`PadicField.eq_artin_of_forall`**, `PadicField.eq_artin_iff`: the characterisation.
-/

set_option linter.unusedSectionVars false

open IntermediateField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

/-- Roots of `X^(q^n) - X` (`n > 0`) lie in `K^ab`. -/
theorem mem_maxAbelian_of_pow_eq {n : ℕ} (hn : 0 < n) {y : Ω} (hy : y ^ q p K ^ n = y) :
    y ∈ maxAbelian K Ω :=
  unramifiedOfDegree_le_maxAbelian n (mem_unramifiedOfDegree_of_pow_eq hn hy)

/-- **Uniformisers act as Frobenius**: on roots `y` of `X^(q^n) - X`, `artin π y = y ^ q`. -/
theorem artin_apply_of_pow_eq (x : Kˣ) (hx : v p (x : K) = 1) {n : ℕ} (hn : 0 < n) (y : Ω)
    (hy : y ^ q p K ^ n = y) :
    (artin p K Ω x ⟨y, mem_maxAbelian_of_pow_eq hn hy⟩ : Ω) = y ^ q p K := by
  have hyn : y ∈ unramifiedOfDegree p K Ω n := mem_unramifiedOfDegree_of_pow_eq hn hy
  rw [artin_apply_unramified hn x y hyn, hx, zpow_one]
  have := frobT_pow_apply_of_pow_eq hn 1 ⟨y, hyn⟩ hy
  rwa [pow_one, pow_one] at this

/-- Norms from `L` act trivially on `L`. -/
theorem artin_apply_of_mem_normGroup (L : AbFin K Ω) (x : Kˣ) (hx : x ∈ normGroup K L.1)
    (y : maxAbelian K Ω) (hy : (y : Ω) ∈ L.1) : artin p K Ω x y = y :=
  (artin_apply_eq_self_iff (p := p) x L.1).2 hx y hy

/-- Elements of the norm group of `K_m` have valuation divisible by `m`. -/
theorem dvd_v_of_mem_normGroup_unramifiedOfDegree {m : ℕ} (hm : 0 < m) {w : Kˣ}
    (hw : w ∈ normGroup K (unramifiedOfDegree p K Ω m)) : (m : ℤ) ∣ v p (w : K) := by
  obtain ⟨y, hy⟩ := mem_normGroup_iff.1 hw
  rw [← hy, v_norm (p := p) y.ne_zero, (isUnramified_unramifiedOfDegree p K Ω m).f_eq,
    finrank_unramifiedOfDegree p K Ω hm]
  exact dvd_mul_right _ _

include hp in
/-- For a uniformiser `π` and a finite abelian `L` of degree `m`, there is a finite abelian `E`
with `π ∈ N_E` and `L ⊆ E K_m`. -/
theorem exists_abFin_uniformizer (L : AbFin K Ω) (π : Kˣ) (hπ : v p (π : K) = 1) :
    ∃ E : AbFin K Ω, π ∈ normGroup K E.1 ∧
      L.1 ≤ E.1 ⊔ unramifiedOfDegree p K Ω (Module.finrank K L.1) := by
  obtain ⟨m, hmdef⟩ : ∃ m, m = Module.finrank K L.1 := ⟨_, rfl⟩
  rw [← hmdef]
  have hm : 0 < m := hmdef ▸ Module.finrank_pos
  haveI := isAbelianGalois_sup L.1 (unramifiedOfDegree p K Ω m)
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup Kˣ, H = Subgroup.zpowers π ⊔
      normGroup K (L.1 ⊔ unramifiedOfDegree p K Ω m : IntermediateField K Ω) := ⟨_, rfl⟩
  have hH : H.index ≠ 0 := by
    have h1 := index_normGroup_eq_finrank (p := p)
      (L.1 ⊔ unramifiedOfDegree p K Ω m : IntermediateField K Ω)
    have h2 : (normGroup K (L.1 ⊔ unramifiedOfDegree p K Ω m : IntermediateField K Ω)).index ≠
        0 := by
      rw [h1]; exact Module.finrank_pos.ne'
    exact ne_zero_of_dvd_ne_zero h2 (Subgroup.index_dvd_of_le (hHdef ▸ le_sup_right))
  obtain ⟨E, hE⟩ := existence (p := p) (Ω := Ω) H hH
  refine ⟨E, hE ▸ hHdef ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers π), ?_⟩
  haveI := isAbelianGalois_sup E.1 (unramifiedOfDegree p K Ω m)
  rw [le_iff_normGroup_le (p := p), normGroup_sup (p := p)]
  rintro z ⟨hzE, hzU⟩
  rw [hE, hHdef] at hzE
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hzE
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  rw [normGroup_sup (p := p)] at hb
  have h1 := dvd_v_of_mem_normGroup_unramifiedOfDegree hm hzU
  have h2 := dvd_v_of_mem_normGroup_unramifiedOfDegree hm hb.2
  rw [Units.val_mul, v_mul (Units.ne_zero _) (Units.ne_zero _), Units.val_zpow_eq_zpow_val,
    v_zpow π.ne_zero, hπ, mul_one] at h1
  have hk : (m : ℤ) ∣ k := by
    have := dvd_sub h1 h2
    rwa [add_sub_cancel_right] at this
  obtain ⟨j, rfl⟩ := hk
  refine mul_mem ?_ hb.1
  have hpow := pow_mem_of_index_ne_zero (normGroup K L.1) π
  rw [index_normGroup_eq_finrank (p := p), ← hmdef] at hpow
  rw [zpow_mul, zpow_natCast]
  exact zpow_mem hpow j

include hp in
/-- **Uniqueness of the Artin map**: two homomorphisms `Kˣ → Gal(K^ab/K)` sending uniformisers to
Frobenius elements (on the roots of `X^(q^n) - X`) and norms from each finite abelian `L` into
`Gal(K^ab/L)` agree. -/
theorem eq_of_frob_of_norm (r r' : Kˣ →* (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω))
    (hr : ∀ x : Kˣ, v p (x : K) = 1 → ∀ (n : ℕ) (hn : 0 < n) (y : Ω) (hy : y ^ q p K ^ n = y),
      (r x ⟨y, mem_maxAbelian_of_pow_eq hn hy⟩ : Ω) = y ^ q p K)
    (hr' : ∀ x : Kˣ, v p (x : K) = 1 → ∀ (n : ℕ) (hn : 0 < n) (y : Ω) (hy : y ^ q p K ^ n = y),
      (r' x ⟨y, mem_maxAbelian_of_pow_eq hn hy⟩ : Ω) = y ^ q p K)
    (hrN : ∀ L : AbFin K Ω, ∀ x ∈ normGroup K L.1, ∀ y : maxAbelian K Ω, (y : Ω) ∈ L.1 →
      r x y = y)
    (hrN' : ∀ L : AbFin K Ω, ∀ x ∈ normGroup K L.1, ∀ y : maxAbelian K Ω, (y : Ω) ∈ L.1 →
      r' x y = y) : r = r' := by
  refine monoidHom_ext_of_v_eq_one (p := p) fun π hπ ↦ ?_
  obtain ⟨g, hgdef⟩ : ∃ g, g = (r π)⁻¹ * r' π := ⟨_, rfl⟩
  have hg : ∀ y : maxAbelian K Ω, r π y = r' π y → g y = y := by
    intro y hy
    rw [hgdef, AlgEquiv.mul_apply, ← hy, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have hmem : ∀ y : maxAbelian K Ω, g y = y → (y : Ω) ∈ lift (fixedField (Subgroup.zpowers g)) :=
    fun y h ↦ (mem_lift y).2 (by rintro ⟨_, j, rfl⟩; exact zpow_apply_eq_of_apply_eq h j)
  have hfix : ∀ y : maxAbelian K Ω, g y = y := by
    intro y
    obtain ⟨L, hyL⟩ := mem_maxAbelian_iff.1 y.2
    obtain ⟨E, hπE, hLE⟩ := exists_abFin_uniformizer (p := p) L π hπ
    have hm : 0 < Module.finrank K L.1 := Module.finrank_pos
    have hE : E.1 ≤ lift (fixedField (Subgroup.zpowers g)) := fun z hz ↦
      hmem ⟨z, le_maxAbelian E hz⟩ (hg _ ((hrN E π hπE _ hz).trans (hrN' E π hπE _ hz).symm))
    have hU : unramifiedOfDegree p K Ω (Module.finrank K L.1) ≤
        lift (fixedField (Subgroup.zpowers g)) := by
      rw [unramifiedOfDegree_def p K Ω]
      refine adjoin_le_iff.2 fun z hz ↦ ?_
      rw [mem_rootSet_X_pow_sub_X (one_lt_q_pow hm)] at hz
      rw [SetLike.mem_coe]
      exact hmem ⟨z, mem_maxAbelian_of_pow_eq hm hz⟩
        (hg _ (Subtype.ext ((hr π hπ _ hm z hz).trans (hr' π hπ _ hm z hz).symm)))
    have := (mem_lift y).1 (sup_le hE hU (hLE hyL)) ⟨g, Subgroup.mem_zpowers g⟩
    exact this
  have h1 : g = 1 := AlgEquiv.ext hfix
  rw [hgdef, inv_mul_eq_one] at h1
  exact h1

include hp in
/-- **Characterisation of the Artin map**: a homomorphism `r : Kˣ → Gal(K^ab/K)` sending
uniformisers to Frobenius elements and norms from each finite abelian `L` into `Gal(K^ab/L)` is
the Artin map. -/
theorem eq_artin_of_forall (r : Kˣ →* (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω))
    (hr : ∀ x : Kˣ, v p (x : K) = 1 → ∀ (n : ℕ) (hn : 0 < n) (y : Ω) (hy : y ^ q p K ^ n = y),
      (r x ⟨y, mem_maxAbelian_of_pow_eq hn hy⟩ : Ω) = y ^ q p K)
    (hrN : ∀ L : AbFin K Ω, ∀ x ∈ normGroup K L.1, ∀ y : maxAbelian K Ω, (y : Ω) ∈ L.1 →
      r x y = y) : r = artin p K Ω :=
  eq_of_frob_of_norm r _ hr (fun x hx _ hn y hy ↦ artin_apply_of_pow_eq x hx hn y hy) hrN
    artin_apply_of_mem_normGroup

include hp in
theorem eq_artin_iff (r : Kˣ →* (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω)) :
    r = artin p K Ω ↔
      (∀ x : Kˣ, v p (x : K) = 1 → ∀ (n : ℕ) (hn : 0 < n) (y : Ω) (hy : y ^ q p K ^ n = y),
        (r x ⟨y, mem_maxAbelian_of_pow_eq hn hy⟩ : Ω) = y ^ q p K) ∧
      (∀ L : AbFin K Ω, ∀ x ∈ normGroup K L.1, ∀ y : maxAbelian K Ω, (y : Ω) ∈ L.1 →
        r x y = y) := by
  refine ⟨?_, fun h ↦ eq_artin_of_forall r h.1 h.2⟩
  rintro rfl
  exact ⟨fun x hx _ hn y hy ↦ artin_apply_of_pow_eq x hx hn y hy, artin_apply_of_mem_normGroup⟩

end PadicField
