/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.CyclicRec

/-!
# Neukirch's formula for Frobenius lifts of higher degree

For `τ ∈ Gal(D/K)` acting on `K_s` as `Frob^k` and with fixed field `Σ` of inertia degree `k`,
`cycRec L (N_{Σ/K} π) = τ|_L` for every uniformiser `π` of `Σ`
(`PadicField.cycRec_norm_frobLift_pow`), provided `s` is divisible by the degree of the level
`(cycEmb L).level k`.
-/

set_option linter.unusedSectionVars false

open IntermediateField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

namespace StdLevel

variable (Λ : StdLevel p K Ω)

/-- **Neukirch's formula for Frobenius lifts of degree `k`** at an adapted level. -/
theorem rho_norm_frobLift_pow (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] {N : ℕ} (hΛ : Λ.Adapted L N) {k : ℕ} (hk : 0 < k)
    (hkM : Module.finrank K Λ.M * k ∣ Λ.t) (hkL : Module.finrank K L * k ∣ Λ.t)
    (D : IntermediateField K Ω) [FiniteDimensional K D] [IsGalois K D] (hLD : L ≤ D)
    (hUD : Λ.U ≤ D) (τ : D ≃ₐ[K] D) (hτ : resHom hUD τ = frob Λ.isUnramified_U ^ k)
    (hf : f p K (fixedField (Subgroup.zpowers τ)) = k)
    (π : fixedField (Subgroup.zpowers τ)) (hπ : v p π = 1) (hπ0 : Algebra.norm K π ≠ 0) :
    resHom hΛ.le_F (Λ.rho (Units.mk0 _ hπ0)) = resHom hLD τ := by
  obtain ⟨A, hA⟩ : ∃ A, A = L ⊔ Λ.U := ⟨_, rfl⟩
  haveI : FiniteDimensional K A := hA ▸ inferInstance
  haveI : IsGalois K A := hA ▸ inferInstance
  have hLA : L ≤ A := hA ▸ le_sup_left
  have hUA : Λ.U ≤ A := hA ▸ le_sup_right
  have hAD : A ≤ D := hA ▸ sup_le hLD hUD
  have hAF : A ≤ Λ.F := hA ▸ sup_le hΛ.le_F Λ.U_le
  have hkt : k ∣ Λ.t := (Dvd.intro_left _ rfl).trans hkM
  set τA := resHom hAD τ
  have hτA : resHom hUA τA = frob Λ.isUnramified_U ^ k := by
    rw [resHom_trans]; exact hτ
  -- the embedding `Fix(τ_A) → Fix(τ)`
  let j : fixedField (Subgroup.zpowers τA) →ₐ[K] fixedField (Subgroup.zpowers τ) :=
    { toFun := fun a ↦ ⟨inclusion hAD a.1, by
        rintro ⟨_, i, rfl⟩
        refine zpow_apply_eq_of_apply_eq ?_ i
        apply Subtype.ext
        rw [← resHom_apply hAD τ a.1]
        exact congrArg Subtype.val (a.2 ⟨τA, Subgroup.mem_zpowers _⟩)⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  -- `K_k ⊆ Fix(τ_A)`
  have hkS : k ∣ f p K (fixedField (Subgroup.zpowers τA)) := by
    have hkU : unramifiedOfDegree p K Ω k ≤ Λ.U := unramifiedOfDegree_le_of_dvd Λ.pos.ne' hkt
    let κ : unramifiedOfDegree p K Ω k →ₐ[K] fixedField (Subgroup.zpowers τA) :=
      { toFun := fun x ↦ ⟨inclusion hUA (inclusion hkU x), by
          rintro ⟨_, i, rfl⟩
          refine zpow_apply_eq_of_apply_eq ?_ i
          apply Subtype.ext
          have h2 := resHom_apply hUA τA (inclusion hkU x)
          have h3 : (frob Λ.isUnramified_U ^ k) (inclusion hkU x) = inclusion hkU x :=
            frob_pow_apply_of_mem hk hkt Λ.pos (inclusion hkU x) x.2
          rw [hτA, h3] at h2
          exact h2.symm⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl
        commutes' := fun _ ↦ rfl }
    have h := f_dvd_of_algHom (p := p) κ
    rwa [(isUnramified_unramifiedOfDegree p K Ω k).f_eq, finrank_unramifiedOfDegree p K Ω hk] at h
  have hfA : f p K (fixedField (Subgroup.zpowers τA)) = k := by
    have h1 := f_dvd_of_algHom (p := p) j
    rw [hf] at h1
    exact Nat.dvd_antisymm h1 hkS
  obtain ⟨πS, hπS, hNπS⟩ := exists_norm_eq_of_algHom j (hfA.trans hf.symm) π hπ
  have hπS0 : Algebra.norm K πS ≠ 0 := by rw [hNπS]; exact hπ0
  have hcore := rho_norm_fixedField Λ L hΛ.pos hΛ.dvd hΛ.le hΛ.le_F A hA hLA hUA hAF hk hkM hkL
    τA hτA πS hπS hπS0
  have hu : Units.mk0 _ hπS0 = Units.mk0 _ hπ0 := Units.ext hNπS
  rw [← hu, hcore, resHom_trans]

end StdLevel

variable (p) in
/-- The unramified degree of the level `(cycEmb L).level k`. -/
noncomputable def cycDegPow (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] (k : ℕ) (hk : 0 < k) : ℕ :=
  ((cycEmb p L).level k hk).t

/-- **Neukirch's formula for `cycRec` and Frobenius lifts of degree `k`**: let `D ⊇ L ⊔ K_s` be
finite Galois, `cycDegPow L k ∣ s`, `τ ∈ Gal(D/K)` acting on `K_s` as `Frob^k` with fixed field
`Σ` of inertia degree `k`. Then `cycRec L (N_{Σ/K} π) = τ|_L` for every uniformiser `π` of
`Σ`. -/
theorem cycRec_norm_frobLift_pow (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] {k : ℕ} (hk : 0 < k) {s : ℕ} (hs0 : 0 < s)
    (hs : cycDegPow p L k hk ∣ s) (D : IntermediateField K Ω) [FiniteDimensional K D]
    [IsGalois K D] (hLD : L ≤ D) (hsD : unramifiedOfDegree p K Ω s ≤ D) (τ : D ≃ₐ[K] D)
    (hτ : resHom hsD τ = frobT p K Ω s ^ k) (hf : f p K (fixedField (Subgroup.zpowers τ)) = k)
    (π : fixedField (Subgroup.zpowers τ)) (hπ : v p π = 1) (hπ0 : Algebra.norm K π ≠ 0) :
    cycRec p L (Units.mk0 _ hπ0) = resHom hLD τ := by
  set E := cycEmb p L
  set Λ := E.level k hk
  have hΛ := E.level_adapted k hk
  have hUs : Λ.U ≤ unramifiedOfDegree p K Ω s := unramifiedOfDegree_le_of_dvd hs0.ne' hs
  have hτU : resHom (hUs.trans hsD) τ = frob Λ.isUnramified_U ^ k := by
    rw [← resHom_trans hUs hsD, hτ, map_pow]
    congr 1
    exact resHom_frobT Λ.pos hs0 hUs
  have hkM : Module.finrank K Λ.M * k ∣ Λ.t := by
    change Module.finrank K E.M * k ∣ Module.finrank K E.M * (E.s * (E.s.factorial * k))
    exact Nat.mul_dvd_mul_left _ ((dvd_mul_left _ _).trans (dvd_mul_left _ _))
  rw [cycRec_eq_of_adapted L Λ hΛ ((dvd_mul_right _ _).trans (E.dvd_level_t k hk))]
  exact StdLevel.rho_norm_frobLift_pow Λ L hΛ hk hkM (E.dvd_level_t k hk) D hLD (hUs.trans hsD)
    τ hτU hf π hπ hπ0

end PadicField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

/-- `cycRec_norm_frobLift_pow` for an arbitrary unit `y` with `y = N_{Σ/K} π`. -/
theorem cycRec_norm_frobLift_pow' (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] {k : ℕ} (hk : 0 < k) {s : ℕ} (hs0 : 0 < s)
    (hs : cycDegPow p L k hk ∣ s) (D : IntermediateField K Ω) [FiniteDimensional K D]
    [IsGalois K D] (hLD : L ≤ D) (hsD : unramifiedOfDegree p K Ω s ≤ D) (τ : D ≃ₐ[K] D)
    (hτ : resHom hsD τ = frobT p K Ω s ^ k) (hf : f p K (fixedField (Subgroup.zpowers τ)) = k)
    (π : fixedField (Subgroup.zpowers τ)) (hπ : v p π = 1) (y : Kˣ)
    (hy : (y : K) = Algebra.norm K π) : cycRec p L y = resHom hLD τ := by
  have hπ0 : Algebra.norm K π ≠ 0 := hy ▸ y.ne_zero
  have : y = Units.mk0 _ hπ0 := Units.ext hy
  rw [this]
  exact cycRec_norm_frobLift_pow L hk hs0 hs D hLD hsD τ hτ hf π hπ hπ0

end PadicField
