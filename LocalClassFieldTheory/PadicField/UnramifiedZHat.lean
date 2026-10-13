/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.MaxUnramified
import LocalClassFieldTheory.Galois.ZHat

/-!
# `Gal(K^ur/K) ≅ Ẑ`

Let `K` be a field finite over `ℚ_[p]`, `Ω` an algebraically closed extension of `K` and
`K^ur ⊆ Ω` the maximal unramified extension, with its arithmetic Frobenius `frobUr`.

* `PadicField.urFix p K Ω n`: the open (normal) subgroup of `Gal(K^ur/K)` fixing `K_n`;
  `Frob ^ k` lies in it iff `n ∣ k` (`PadicField.frobUr_pow_mem_urFix_iff`).
* **`PadicField.galMaxUnramifiedEquiv : Gal(K^ur/K) ≃ₜ* Ẑ`**, an isomorphism of topological
  groups (Krull topology on the left, `Ẑ = lim ℤ/n` written multiplicatively on the right)
  sending the Frobenius to the topological generator `1 ∈ Ẑ`
  (`PadicField.galMaxUnramifiedEquiv_frobUr`). Its inverse is `a ↦ Frob ^ a`
  (`PadicField.galMaxUnramifiedEquiv_symm_apply`, with `Brauer.zhatPow`), and the image of `σ`
  is read off at finite level: if `σ` acts on `K_n` as `Frob ^ k`, then the `n`-th component of
  `galMaxUnramifiedEquiv σ` is `k mod n` (`PadicField.galMaxUnramifiedEquiv_apply_of_eq_pow`).
  Equivalently, `Frob ^ a` acts on `K_n` as `Frob ^ (a mod n)`
  (`PadicField.zhatPow_frobUr_apply`).
-/

set_option linter.unusedSectionVars false

open IntermediateField Brauer

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

variable (p K Ω) in
/-- The subgroup of `Gal(K^ur/K)` fixing `K_n`. -/
def urFix (n : ℕ) : Subgroup (maxUnramified p K Ω ≃ₐ[K] maxUnramified p K Ω) where
  carrier := {σ | ∀ x : maxUnramified p K Ω, (x : Ω) ∈ unramifiedOfDegree p K Ω n → σ x = x}
  mul_mem' {σ τ} hσ hτ x hx := by rw [AlgEquiv.mul_apply, hτ x hx, hσ x hx]
  one_mem' _ _ := rfl
  inv_mem' {σ} hσ x hx := by
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    exact (hσ x hx).symm

theorem mem_urFix {n : ℕ} {σ : maxUnramified p K Ω ≃ₐ[K] maxUnramified p K Ω} :
    σ ∈ urFix p K Ω n ↔
      ∀ x : maxUnramified p K Ω, (x : Ω) ∈ unramifiedOfDegree p K Ω n → σ x = x :=
  Iff.rfl

theorem isOpen_urFix (n : ℕ) :
    IsOpen (urFix p K Ω n : Set (maxUnramified p K Ω ≃ₐ[K] maxUnramified p K Ω)) := by
  have hle := unramifiedOfDegree_le_maxUnramified p K Ω n
  haveI : FiniteDimensional K (restrict hle) :=
    LinearEquiv.finiteDimensional (restrict_algEquiv hle).toLinearEquiv
  have h := (restrict hle).fixingSubgroup_isOpen
  convert h using 1
  ext g
  rw [SetLike.mem_coe, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h y hy ↦ h y ((mem_restrict _ y).1 hy), fun h y hy ↦ h y ((mem_restrict _ y).2 hy)⟩

instance urFix_normal (n : ℕ) : (urFix p K Ω n).Normal where
  conj_mem σ hσ τ := by
    rw [gal_maxUnramified_mul_comm τ σ, mul_inv_cancel_right]
    exact hσ

/-- `Frob ^ k` fixes `K_n` iff `n ∣ k`. -/
theorem frobUr_pow_mem_urFix_iff {n : ℕ} (hn : 0 < n) (k : ℕ) :
    frobUr p K Ω ^ k ∈ urFix p K Ω n ↔ n ∣ k := by
  have h := isUnramified_unramifiedOfDegree p K Ω n
  have ho : orderOf (frob h) = n := by rw [orderOf_frob, finrank_unramifiedOfDegree p K Ω hn]
  conv_rhs => rw [← ho, orderOf_dvd_iff_pow_eq_one]
  rw [mem_urFix]
  constructor
  · intro H
    ext y
    have := frobUr_pow_apply (p := p) (K := K) (Ω := Ω) hn k
      ⟨(y : Ω), unramifiedOfDegree_le_maxUnramified p K Ω n y.2⟩ y.2
    rw [H _ y.2] at this
    exact this.symm
  · intro H x hx
    apply Subtype.ext
    rw [frobUr_pow_apply hn k x hx, H]
    rfl

/-- `Frob ^ a` (`a ∈ Ẑ`) acts on `K_n` as `Frob ^ (a mod n)`. -/
theorem zhatPow_frobUr_apply (a : Multiplicative ZHat) {n : ℕ+} (x : maxUnramified p K Ω)
    (hx : (x : Ω) ∈ unramifiedOfDegree p K Ω n) :
    zhatPow (frobUr p K Ω) a x = (frobUr p K Ω ^ ((a.toAdd : ∀ n : ℕ+, ZMod n) n).val) x := by
  have h := zhatPow_pow_inv_mul_mem (frobUr p K Ω) (urFix p K Ω n) (isOpen_urFix n)
    (frobUr_pow_mem_urFix_iff n.pos) a x hx
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at h
  exact h

/-- `a ↦ Frob ^ a` is injective. -/
theorem zhatPow_frobUr_injective : Function.Injective (zhatPow (frobUr p K Ω)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h : ∀ n : ℕ+, (a.toAdd : ∀ n : ℕ+, ZMod n) n = 0 := fun n ↦
    (zhatPow_mem_iff (frobUr p K Ω) (urFix p K Ω n) (isOpen_urFix n)
      (frobUr_pow_mem_urFix_iff n.pos) a).1 (by rw [ha]; exact one_mem _)
  exact congrArg Multiplicative.ofAdd (ZHat.ext h)

/-- `a ↦ Frob ^ a` is surjective (the powers of `Frob` are dense). -/
theorem zhatPow_frobUr_surjective : Function.Surjective (zhatPow (frobUr p K Ω)) :=
  zhatPow_surjective _ dense_zpowers_frobUr

variable (p K Ω) in
/-- **`Gal(K^ur/K) ≅ Ẑ`**, as topological groups, with the Frobenius corresponding to `1`. -/
noncomputable def galMaxUnramifiedEquiv :
    (maxUnramified p K Ω ≃ₐ[K] maxUnramified p K Ω) ≃ₜ* Multiplicative ZHat :=
  let e := MulEquiv.ofBijective (zhatPow (frobUr p K Ω))
    ⟨zhatPow_frobUr_injective, zhatPow_frobUr_surjective⟩
  ContinuousMulEquiv.symm
    { e with
      continuous_toFun := (zhatPow (frobUr p K Ω)).continuous
      continuous_invFun :=
        (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv)
          (zhatPow (frobUr p K Ω)).continuous).symm.continuous }

theorem galMaxUnramifiedEquiv_symm_apply (a : Multiplicative ZHat) :
    (galMaxUnramifiedEquiv p K Ω).symm a = zhatPow (frobUr p K Ω) a := rfl

/-- The Frobenius corresponds to `1 ∈ Ẑ`. -/
theorem galMaxUnramifiedEquiv_frobUr :
    galMaxUnramifiedEquiv p K Ω (frobUr p K Ω) = Multiplicative.ofAdd (intToZHat 1) := by
  rw [ContinuousMulEquiv.apply_eq_iff_symm_apply, galMaxUnramifiedEquiv_symm_apply,
    zhatPow_one]

theorem galMaxUnramifiedEquiv_frobUr_zpow (k : ℤ) :
    galMaxUnramifiedEquiv p K Ω (frobUr p K Ω ^ k) = Multiplicative.ofAdd (intToZHat k) := by
  rw [ContinuousMulEquiv.apply_eq_iff_symm_apply, galMaxUnramifiedEquiv_symm_apply,
    zhatPow_intToZHat]

/-- If `σ` acts on `K_n` as `Frob ^ k`, the `n`-th component of `galMaxUnramifiedEquiv σ` is
`k mod n`. -/
theorem galMaxUnramifiedEquiv_apply_of_eq_pow
    (σ : maxUnramified p K Ω ≃ₐ[K] maxUnramified p K Ω) {n : ℕ+} {k : ℕ}
    (h : ∀ x : maxUnramified p K Ω, (x : Ω) ∈ unramifiedOfDegree p K Ω n →
      σ x = (frobUr p K Ω ^ k) x) :
    ((galMaxUnramifiedEquiv p K Ω σ).toAdd : ∀ n : ℕ+, ZMod n) n = k := by
  set a := galMaxUnramifiedEquiv p K Ω σ
  have hσ : σ = zhatPow (frobUr p K Ω) a := by
    rw [← galMaxUnramifiedEquiv_symm_apply, ContinuousMulEquiv.symm_apply_apply]
  have h2 : (frobUr p K Ω ^ k)⁻¹ * σ ∈ urFix p K Ω n := by
    intro x hx
    rw [AlgEquiv.mul_apply, h x hx, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  have h3 : (frobUr p K Ω ^ k)⁻¹ * σ =
      zhatPow (frobUr p K Ω) (Multiplicative.ofAdd (intToZHat (-(k : ℤ))) * a) := by
    rw [map_mul, zhatPow_intToZHat, ← hσ, zpow_neg, zpow_natCast]
  rw [h3, zhatPow_mem_iff (frobUr p K Ω) (urFix p K Ω n) (isOpen_urFix n)
    (frobUr_pow_mem_urFix_iff n.pos)] at h2
  change ((-(k : ℤ) : ℤ) : ZMod n) + (a.toAdd : ∀ n : ℕ+, ZMod n) n = 0 at h2
  rw [Int.cast_neg, Int.cast_natCast, neg_add_eq_zero] at h2
  exact h2.symm

end PadicField
