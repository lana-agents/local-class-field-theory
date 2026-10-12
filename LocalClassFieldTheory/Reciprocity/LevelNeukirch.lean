/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.OmegaLevel

/-!
# Neukirch's formula for a cyclic subextension of a level

Let `Λ` be a standard level in `Ω` with field `F = M ⊔ K_t`, let `L ⊆ F` be cyclic with
`L ⊆ M ⊔ K_N` (`N` small), and `A = L ⊔ K_t`. For `τ ∈ Gal(A/K)` acting on `K_t` as `Frob^k`
(with `[M : K] k ∣ t` and `[L : K] k ∣ t`) and a uniformiser `π` of the fixed field `S` of `τ`
in `A`, `ρ_Λ(N_{S/K} π)|_L = τ|_L` (`PadicField.StdLevel.rho_norm_fixedField`).

The proof lifts `τ` to a Frobenius lift `(g, φ^k)` of `F`, compares the uniformiser `π` with the
norm of a uniformiser of the fixed field `Σ ⊇ S` of the lift (`f(Σ) = f(S) = k`), and uses that
`A/S` is unramified, so that units of `S` are norms from `A`, hence from `L`.
-/

set_option linter.unusedSectionVars false

open IntermediateField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

/-- The `t`-th Frobenius `Frob_{K_t}`. -/
noncomputable abbrev frobT (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω]
    [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] (t : ℕ) :
    unramifiedOfDegree p K Ω t ≃ₐ[K] unramifiedOfDegree p K Ω t :=
  frob (isUnramified_unramifiedOfDegree p K Ω t)

theorem frobT_pow_eq_one {t : ℕ} (ht : 0 < t) : frobT p K Ω t ^ t = 1 := by
  have := pow_orderOf_eq_one (frobT p K Ω t)
  rwa [orderOf_frob, finrank_unramifiedOfDegree p K Ω ht] at this

/-- An automorphism of `A = L ⊔ K_t` acting as `Frob^k` on `K_t` has order dividing `t / k` if
`[L : K] k ∣ t`. -/
theorem pow_div_eq_one {L U A : IntermediateField K Ω} [FiniteDimensional K L] [IsGalois K L]
    [Normal K U] (hA : A = L ⊔ U) (hLA : L ≤ A) (hUA : U ≤ A) (τ : A ≃ₐ[K] A) (n : ℕ)
    (hL : Module.finrank K L ∣ n) (hU : resHom hUA (τ ^ n) = 1) : τ ^ n = 1 := by
  have hLn : resHom hLA (τ ^ n) = 1 := by
    rw [map_pow]
    refine orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard _).trans ?_)
    rwa [IsGalois.card_aut_eq_finrank]
  have hfix : ∀ (E : IntermediateField K Ω) [Normal K E] (hEA : E ≤ A),
      resHom hEA (τ ^ n) = 1 → E ≤ lift (fixedField (Subgroup.zpowers (τ ^ n))) := by
    intro E _ hEA h x hx
    have h1 := resHom_apply hEA (τ ^ n) ⟨x, hx⟩
    rw [h, AlgEquiv.one_apply] at h1
    refine (mem_lift (⟨x, hEA hx⟩ : A)).2 ?_
    rintro ⟨_, j, rfl⟩
    exact zpow_apply_eq_of_apply_eq (Subtype.ext h1.symm) j
  have hle := sup_le (hfix L hLA hLn) (hfix U hUA hU)
  ext a
  have ha : (a : Ω) ∈ L ⊔ U := by rw [← hA]; exact a.2
  have := (mem_lift a).1 (hle ha) ⟨τ ^ n, Subgroup.mem_zpowers _⟩
  rw [AlgEquiv.one_apply]
  exact congrArg Subtype.val this

theorem aux_eq_one {e a b c k t : ℕ} (hk : 0 < k) (h1 : e * a ≤ c) (h3 : k * a = b)
    (h5 : t ≤ b) (h6 : c * k = t) (ha : 0 < a) (he : 0 < e) : e = 1 := by
  by_contra hne
  have he2 : 2 ≤ e := by omega
  have h7 : 2 * a ≤ c := le_trans (Nat.mul_le_mul_right a he2) h1
  have h8 : 2 * a * k ≤ c * k := Nat.mul_le_mul_right k h7
  nlinarith

/-- The fixed field of `τ`. -/
local notation "𝔽" τ:max => IntermediateField.fixedField (Subgroup.zpowers τ)

namespace StdLevel

variable (Λ : StdLevel p K Ω)

/-- **Neukirch's formula for a cyclic subextension `L` of a level**: if `τ ∈ Gal(A/K)`,
`A = L ⊔ K_t`, acts on `K_t` as `Frob^k`, and `π` is a uniformiser of the fixed field `S` of `τ`,
then `ρ_Λ(N_{S/K} π)|_L = τ|_L`. -/
theorem rho_norm_fixedField (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] {N : ℕ} (hN0 : 0 < N)
    (hNt : ∀ k, 0 < k → k ≤ N → Module.finrank K Λ.M * k ∣ Λ.t)
    (hL : L ≤ Λ.M ⊔ unramifiedOfDegree p K Ω N) (hLF : L ≤ Λ.F)
    (A : IntermediateField K Ω) [FiniteDimensional K A] [IsGalois K A] (hA : A = L ⊔ Λ.U)
    (hLA : L ≤ A) (hUA : Λ.U ≤ A) (hAF : A ≤ Λ.F)
    {k : ℕ} (hk : 0 < k) (hkM : Module.finrank K Λ.M * k ∣ Λ.t)
    (hkL : Module.finrank K L * k ∣ Λ.t)
    (τ : A ≃ₐ[K] A) (hτ : resHom hUA τ = frob Λ.isUnramified_U ^ k)
    (π : fixedField (Subgroup.zpowers τ)) (hπ : v p π = 1) (hπ0 : Algebra.norm K π ≠ 0) :
    resHom hLF (Λ.rho (Units.mk0 _ hπ0)) = resHom hLA τ := by
  classical
  have hke : Module.finrank K Λ.M * k ∣ Module.finrank K Λ.U := by rw [Λ.finrank_U]; exact hkM
  have hkt : k ∣ Λ.t := (Dvd.intro_left _ rfl).trans hkM
  -- lift `τ` to `F`
  obtain ⟨τF, hτF⟩ := resHom_surjective hAF τ
  have hτFA : ∀ a : A, (τF (inclusion hAF a) : Ω) = (τ a : Ω) := by
    intro a
    rw [← resHom_apply, hτF]
  have hτFU : ∀ u : Λ.U, τF (algebraMap Λ.U Λ.F u) =
      algebraMap Λ.U Λ.F ((frob Λ.isUnramified_U ^ k) u) := by
    intro u
    apply Subtype.ext
    have h2 := resHom_apply hUA τ u
    rw [hτ] at h2
    exact (hτFA (inclusion hUA u)).trans h2.symm
  set g := ((stdProd Λ.totRam Λ.isUnramified_U Λ.finrank_F).symm τF).1
  have hτg : τF = Λ.tauL g k := eq_tau_of_restrict _ _ _ τF k hτFU
  set Sig := fixedField (Subgroup.zpowers (Λ.tauL g k))
  have hfixA : ∀ a : A, τ a = a → Λ.tauL g k (inclusion hAF a) = inclusion hAF a := by
    intro a ha
    rw [← hτg]
    apply Subtype.ext
    rw [hτFA, ha]
    rfl
  -- the embedding `(𝔽 τ) → Σ`
  let ι : (𝔽 τ) →ₐ[K] Sig :=
    { toFun := fun x ↦ ⟨inclusion hAF x.1, by
        rintro ⟨_, j, rfl⟩
        exact zpow_apply_eq_of_apply_eq (hfixA _ (x.2 ⟨τ, Subgroup.mem_zpowers _⟩)) j⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  -- inertia degrees
  have hfSig : f p K Sig ≤ k := f_fixedField_tau_le Λ.totRam Λ.isUnramified_U Λ.finrank_F g k hk hke
  have hkS : k ∣ f p K (𝔽 τ) := by
    have hkU : unramifiedOfDegree p K Ω k ≤ Λ.U := unramifiedOfDegree_le_of_dvd Λ.pos.ne' hkt
    let κ : unramifiedOfDegree p K Ω k →ₐ[K] (𝔽 τ) :=
      { toFun := fun x ↦ ⟨inclusion hUA (inclusion hkU x), by
          rintro ⟨_, j, rfl⟩
          refine zpow_apply_eq_of_apply_eq ?_ j
          apply Subtype.ext
          have h2 := resHom_apply hUA τ (inclusion hkU x)
          have h3 : (frob Λ.isUnramified_U ^ k) (inclusion hkU x) = inclusion hkU x :=
            frob_pow_apply_of_mem hk hkt Λ.pos (inclusion hkU x) x.2
          rw [hτ, h3] at h2
          exact h2.symm⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl
        commutes' := fun _ ↦ rfl }
    have h := f_dvd_of_algHom (p := p) κ
    rwa [(isUnramified_unramifiedOfDegree p K Ω k).f_eq, finrank_unramifiedOfDegree p K Ω hk] at h
  have hSSig : f p K (𝔽 τ) ∣ f p K Sig := f_dvd_of_algHom (p := p) ι
  have hfS : f p K (𝔽 τ) = k := by
    have h1 := Nat.le_of_dvd f_pos hSSig
    have h2 := Nat.le_of_dvd f_pos hkS
    omega
  have hfSig' : f p K Sig = k := by
    have h1 := Nat.le_of_dvd f_pos hSSig
    omega
  -- a uniformiser of `Σ`
  obtain ⟨y, hy⟩ := exists_v_eq_one_tau Λ.totRam Λ.isUnramified_U Λ.finrank_F g k hk hke
  have hySig : v p y = 1 := (v_eq_one_of_v_algebraMap_eq_one (S := Sig) (T := Λ.F) hy).1
  have hy0' : y ≠ 0 := by rintro rfl; simp [v, wval] at hySig
  have hy0 : Algebra.norm K y ≠ 0 := Algebra.norm_ne_zero_iff.2 hy0'
  have hρy : Λ.rho (Units.mk0 _ hy0) = Λ.tauL g k :=
    rhoF_norm_tau Λ.totRam Λ.isUnramified_U Λ.finrank_F g k hk hke Λ.gen Λ.gen_spec Λ.dvd_U y
      hy hy0
  -- the tower `(𝔽 τ) → Σ`
  obtain ⟨π', hπ', hNπ'⟩ : ∃ π' : 𝔽 τ, v p π' = 1 ∧ Algebra.norm K π' = Algebra.norm K y := by
    letI : Algebra (𝔽 τ) Sig := ι.toRingHom.toAlgebra
    letI : SMul (𝔽 τ) Sig := Algebra.toSMul
    letI : Module (𝔽 τ) Sig := Algebra.toModule
    haveI : Module.Free (𝔽 τ) Sig := Module.Free.of_divisionRing _ _
    haveI : IsScalarTower K (𝔽 τ) Sig :=
      IsScalarTower.of_algebraMap_eq fun x ↦ (ι.commutes x).symm
    haveI : IsScalarTower ℚ_[p] (𝔽 τ) Sig := IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply ℚ_[p] K (𝔽 τ), IsScalarTower.algebraMap_apply ℚ_[p] K Sig]
      exact (ι.commutes _).symm
    haveI : FiniteDimensional (𝔽 τ) Sig := FiniteDimensional.right K (𝔽 τ) Sig
    exact ⟨Algebra.norm (𝔽 τ) y, v_norm_eq_one_of_f_eq (K := K) (by rw [hfS, hfSig']) hySig,
      Algebra.norm_norm⟩
  have hπ'0 : π' ≠ 0 := by rintro h; rw [h] at hπ'; simp [v, wval] at hπ'
  -- the unit `u = π / π'`
  obtain ⟨u, hu_def⟩ : ∃ u : 𝔽 τ, u = π / π' := ⟨_, rfl⟩
  have hπne : (π : (𝔽 τ)) ≠ 0 := by rintro h; rw [h] at hπ; simp [v, wval] at hπ
  have hu : nrm p (𝔽 τ) u = 1 := by
    rw [hu_def, nrm_eq_one_iff_v_eq_zero (div_ne_zero hπne hπ'0), v_div hπne hπ'0, hπ, hπ',
      sub_self]
  -- `A / (𝔽 τ)` is unramified
  have hpow : τ ^ (Λ.t / k) = 1 := by
    refine pow_div_eq_one hA hLA hUA τ (Λ.t / k) (Nat.dvd_div_of_mul_dvd (mul_comm k _ ▸ hkL)) ?_
    rw [map_pow, hτ, ← pow_mul, Nat.mul_div_cancel' hkt]
    have := pow_orderOf_eq_one (frob Λ.isUnramified_U)
    rwa [orderOf_frob, Λ.finrank_U] at this
  have heSA : e p (𝔽 τ) A = 1 := by
    have h1 := e_mul_f (p := p) (K := (𝔽 τ)) (L := A)
    rw [finrank_fixedField_eq_card, Nat.card_zpowers] at h1
    have h2 := Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd Λ.pos hkt) hk)
      (orderOf_dvd_of_pow_eq_one hpow)
    have h3 := f_mul_f (p := p) (K := K) (E := (𝔽 τ)) (L := A)
    have h4 : Λ.t ∣ f p K A := by
      have := f_dvd_of_algHom (p := p) (inclusion hUA)
      rwa [Λ.isUnramified_U.f_eq, Λ.finrank_U] at this
    rw [hfS] at h3
    have h5 : Λ.t ≤ f p K A := Nat.le_of_dvd f_pos h4
    have h6 : Λ.t / k * k = Λ.t := Nat.div_mul_cancel hkt
    have he := e_pos (p := p) (K := (𝔽 τ)) (L := A)
    have hf := f_pos (p := p) (K := (𝔽 τ)) (L := A)
    exact aux_eq_one hk (h1 ▸ h2) h3 h5 h6 hf he
  have hu0 : Algebra.norm K u ≠ 0 :=
    Algebra.norm_ne_zero_iff.2 (hu_def ▸ div_ne_zero hπne hπ'0)
  have hNu : Units.mk0 _ hu0 ∈ normGroup K L :=
    normGroup_le_of_algHom (inclusion hLA) (mk0_norm_mem_normGroup_of_e_eq_one heSA u hu hu0)
  have hρu : resHom hLF (Λ.rho (Units.mk0 _ hu0)) = 1 :=
    (Λ.rho_res_eq_one_iff L hN0 hNt hL hLF _).2 hNu
  have hsplit : Units.mk0 _ hπ0 = Units.mk0 _ hy0 * Units.mk0 _ hu0 := by
    ext
    simp only [Units.val_mk0, Units.val_mul]
    rw [← hNπ', ← map_mul]
    congr 1
    rw [hu_def]
    field_simp
  rw [hsplit, map_mul, map_mul, hρu, mul_one, hρy, ← hτg, ← hτF, resHom_trans]


end StdLevel

end PadicField
