/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.Embedding

/-!
# The reciprocity map of a cyclic extension

For a finite cyclic `L ⊆ Ω` we choose a standard level `Λ` adapted to `L` (`L ⊆ M ⊔ K_N`) and
define `PadicField.cycRec L : Kˣ →* Gal(L/K)` as `ρ_Λ` followed by restriction.

* `PadicField.StdLevel.rho_norm_frobLift`: Neukirch's formula for Frobenius lifts in an arbitrary
  finite Galois `D ⊇ L ⊔ K_t`;
* `PadicField.StdLevel.rho_res_eq_of_le`: independence of the level;
* `PadicField.cycRec_eq_one_iff`: the kernel of `cycRec L` is `N_{L/K} Lˣ`;
* `PadicField.cycRec_surjective`;
* `PadicField.cycRec_norm_frobLift`: Neukirch's formula for `cycRec`.
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

/-- `Λ` is adapted to `L` (with parameter `N`): `L ⊆ M ⊔ K_N` and `[M : K] k ∣ t` for
`1 ≤ k ≤ N`. -/
structure Adapted (L : IntermediateField K Ω) (N : ℕ) : Prop where
  pos : 0 < N
  dvd : ∀ k, 0 < k → k ≤ N → Module.finrank K Λ.M * k ∣ Λ.t
  le : L ≤ Λ.M ⊔ unramifiedOfDegree p K Ω N

variable {Λ}

theorem Adapted.le_F {L : IntermediateField K Ω} {N : ℕ} (h : Λ.Adapted L N) : L ≤ Λ.F := by
  refine h.le.trans (sup_le Λ.M_le ((unramifiedOfDegree_le_of_dvd Λ.pos.ne' ?_).trans Λ.U_le))
  exact (Dvd.intro_left _ rfl).trans (h.dvd N h.pos le_rfl)

variable (Λ)

/-- **Neukirch's formula for Frobenius lifts**: let `D ⊇ L ⊔ K_t` be finite Galois and
`τ ∈ Gal(D/K)` acting on `K_t` as the Frobenius, such that its fixed field `Σ` has
`f(Σ/K) = 1`. Then `ρ_Λ(N_{Σ/K} π)|_L = τ|_L` for every uniformiser `π` of `Σ`. -/
theorem rho_norm_frobLift (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] {N : ℕ} (hΛ : Λ.Adapted L N) (hLt : Module.finrank K L ∣ Λ.t)
    (D : IntermediateField K Ω) [FiniteDimensional K D] [IsGalois K D] (hLD : L ≤ D)
    (hUD : Λ.U ≤ D) (τ : D ≃ₐ[K] D) (hτ : resHom hUD τ = frob Λ.isUnramified_U)
    (hf : f p K (fixedField (Subgroup.zpowers τ)) = 1)
    (π : fixedField (Subgroup.zpowers τ)) (hπ : v p π = 1) (hπ0 : Algebra.norm K π ≠ 0) :
    resHom hΛ.le_F (Λ.rho (Units.mk0 _ hπ0)) = resHom hLD τ := by
  obtain ⟨A, hA⟩ : ∃ A, A = L ⊔ Λ.U := ⟨_, rfl⟩
  haveI : FiniteDimensional K A := hA ▸ inferInstance
  haveI : IsGalois K A := hA ▸ inferInstance
  have hLA : L ≤ A := hA ▸ le_sup_left
  have hUA : Λ.U ≤ A := hA ▸ le_sup_right
  have hAD : A ≤ D := hA ▸ sup_le hLD hUD
  have hAF : A ≤ Λ.F := hA ▸ sup_le hΛ.le_F Λ.U_le
  set τA := resHom hAD τ
  have hτA : resHom hUA τA = frob Λ.isUnramified_U ^ 1 := by
    rw [pow_one, resHom_trans]; exact hτ
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
  have hfA : f p K (fixedField (Subgroup.zpowers τA)) = 1 := by
    have := f_dvd_of_algHom (p := p) j
    rw [hf] at this
    exact Nat.eq_one_of_dvd_one this
  obtain ⟨πS, hπS, hNπS⟩ := exists_norm_eq_of_algHom j (hfA.trans hf.symm) π hπ
  have hπS0 : Algebra.norm K πS ≠ 0 := by rw [hNπS]; exact hπ0
  have hcore := rho_norm_fixedField Λ L hΛ.pos hΛ.dvd hΛ.le hΛ.le_F A hA hLA hUA hAF one_pos
    (by simpa using hΛ.dvd 1 one_pos hΛ.pos) (by rw [mul_one]; exact hLt) τA hτA πS hπS
    hπS0
  have hu : Units.mk0 _ hπS0 = Units.mk0 _ hπ0 := Units.ext hNπS
  rw [← hu, hcore, resHom_trans]

/-- Two elements of `Kˣ` of valuation one generate: homomorphisms agreeing on elements of
valuation one agree. -/
theorem _root_.PadicField.monoidHom_ext_of_v_eq_one {G : Type*} [Group G] {φ ψ : Kˣ →* G}
    (h : ∀ x : Kˣ, v p (x : K) = 1 → φ x = ψ x) : φ = ψ := by
  have hπ := uniformizer_spec (p := p) (K := K)
  set π : Kˣ := Units.mk0 _ hπ.ne_zero
  have hvπ : v p (π : K) = 1 := hπ
  ext x
  obtain ⟨y, hydef⟩ : ∃ y, y = x * π ^ (1 - v p (x : K)) := ⟨_, rfl⟩
  have hy : v p (y : K) = 1 := by
    simp only [hydef, Units.val_mul, Units.val_zpow_eq_zpow_val]
    rw [v_mul x.ne_zero (zpow_ne_zero _ π.ne_zero), v_zpow π.ne_zero, hvπ]
    ring
  have hx : x = y * π ^ (v p (x : K) - 1) := by
    simp only [hydef, mul_assoc, ← zpow_add]
    simp
  rw [hx, map_mul, map_mul, map_zpow, map_zpow, h y hy, h π hvπ]

/-- **Independence of the level**: if `Λ` is adapted to `L`, `[L : K] ∣ t` and `Λ'` is a level
with `L ⊆ F'` and `t ∣ t'`, then `ρ_Λ(x)|_L = ρ_Λ'(x)|_L`. -/
theorem rho_res_eq_of_le (Λ' : StdLevel p K Ω) (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] {N : ℕ} (hΛ : Λ.Adapted L N)
    (hLt : Module.finrank K L ∣ Λ.t) (hLF' : L ≤ Λ'.F) (htt' : Λ.t ∣ Λ'.t) (x : Kˣ) :
    resHom hΛ.le_F (Λ.rho x) = resHom hLF' (Λ'.rho x) := by
  suffices h : (resHom hΛ.le_F).comp Λ.rho = (resHom hLF').comp Λ'.rho from
    DFunLike.congr_fun h x
  refine monoidHom_ext_of_v_eq_one (p := p) fun x hx ↦ ?_
  simp only [MonoidHom.comp_apply]
  have hUU : Λ.U ≤ Λ'.U := unramifiedOfDegree_le_of_dvd Λ'.pos.ne' htt'
  have hUD : Λ.U ≤ Λ'.F := hUU.trans Λ'.U_le
  -- `ρ_Λ'(x) = (g, φ)` is a Frobenius lift
  obtain ⟨g, hρ'⟩ : ∃ g, Λ'.rho x = Λ'.tauL g 1 :=
    ⟨_, by rw [rho, rhoF_apply, hx, zpow_one, tauL, tau, pow_one]⟩
  have hke : Module.finrank K Λ'.M * 1 ∣ Module.finrank K Λ'.U := by
    rw [mul_one]; exact Λ'.dvd_U
  have hfSig : f p K (fixedField (Subgroup.zpowers (Λ'.tauL g 1))) = 1 :=
    le_antisymm (f_fixedField_tau_le Λ'.totRam Λ'.isUnramified_U Λ'.finrank_F g 1 one_pos hke)
      f_pos
  obtain ⟨y, hy⟩ := exists_v_eq_one_tau Λ'.totRam Λ'.isUnramified_U Λ'.finrank_F g 1 one_pos hke
  have hySig : v p y = 1 := (v_eq_one_of_v_algebraMap_eq_one (T := Λ'.F) hy).1
  have hy0' : y ≠ 0 := by rintro rfl; simp [v, wval] at hySig
  have hy0 : Algebra.norm K y ≠ 0 := Algebra.norm_ne_zero_iff.2 hy0'
  have hρy : Λ'.rho (Units.mk0 _ hy0) = Λ'.tauL g 1 :=
    rhoF_norm_tau Λ'.totRam Λ'.isUnramified_U Λ'.finrank_F g 1 one_pos hke Λ'.gen Λ'.gen_spec
      Λ'.dvd_U y hy hy0
  -- the Frobenius lift acts on `K_t` as the Frobenius
  have hτU : resHom hUD (Λ'.tauL g 1) = frob Λ.isUnramified_U := by
    rw [resHom_eq_iff]
    intro u
    have h1 : Λ'.tauL g 1 (inclusion hUD u) =
        algebraMap Λ'.U Λ'.F ((frob Λ'.isUnramified_U) (inclusion hUU u)) := by
      change stdProd _ _ _ (g, _) (algebraMap Λ'.U Λ'.F (inclusion hUU u)) = _
      rw [stdProd_apply, pow_one, ← stdResU_apply Λ'.isUnramified_U, stdResU_stdFrob,
        g.commutes]
    rw [h1, algebraMap_U]
    exact frob_unramifiedOfDegree_inclusion Λ.pos Λ'.pos hUU u
  have hN := rho_norm_frobLift Λ L hΛ hLt Λ'.F hLF' hUD (Λ'.tauL g 1) hτU hfSig y hySig hy0
  have hker : x * (Units.mk0 _ hy0)⁻¹ ∈ normGroup K L := by
    refine normGroup_le_of_algHom (inclusion hLF') (Λ'.mem_normGroup_of_rho_eq_one _ ?_)
    rw [map_mul, map_inv, hρy, hρ', mul_inv_cancel]
  have h1 := (Λ.rho_res_eq_one_iff L hΛ.pos hΛ.dvd hΛ.le hΛ.le_F _).2 hker
  rw [map_mul, map_mul, map_inv, map_inv, hN, mul_inv_eq_one] at h1
  rw [h1, hρ']

end StdLevel

section CycRec

variable (p) in
/-- An embedding datum for a cyclic `L`: `L ⊆ M ⊔ K_s` with `M` cyclic totally ramified Galois
and `[L : K] ∣ s`. -/
structure CycEmb (L : IntermediateField K Ω) where
  /-- The totally ramified field. -/
  M : IntermediateField K Ω
  /-- The unramified degree. -/
  s : ℕ
  finiteDimensional : FiniteDimensional K M
  isGalois : IsGalois K M
  isCyclic : IsCyclic (M ≃ₐ[K] M)
  totRam : e p K M = Module.finrank K M
  pos : 0 < s
  dvd : Module.finrank K L ∣ s
  le : L ≤ M ⊔ unramifiedOfDegree p K Ω s

attribute [instance] CycEmb.finiteDimensional CycEmb.isGalois CycEmb.isCyclic

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
  [IsCyclic (L ≃ₐ[K] L)]

theorem nonempty_cycEmb : Nonempty (CycEmb p L) := by
  obtain ⟨M, _, _, _, s, h1, h2, h3, h4⟩ := exists_totRam_le_sup (p := p) L
  exact ⟨⟨M, s, inferInstance, inferInstance, inferInstance, h1, h2, h3, h4⟩⟩

variable (p) in
/-- A chosen embedding datum. -/
noncomputable def cycEmb : CycEmb p L := Classical.choice (nonempty_cycEmb L)

/-- The standard level `(M, [M : K] s s! c)` attached to an embedding datum. -/
noncomputable def CycEmb.level {L : IntermediateField K Ω} (E : CycEmb p L) (c : ℕ) (hc : 0 < c) :
    StdLevel p K Ω where
  M := E.M
  t := Module.finrank K E.M * (E.s * (E.s.factorial * c))
  finiteDimensional := inferInstance
  isGalois := inferInstance
  isCyclic := inferInstance
  totRam := E.totRam
  dvd := dvd_mul_right _ _
  pos := Nat.mul_pos Module.finrank_pos (Nat.mul_pos E.pos (Nat.mul_pos E.s.factorial_pos hc))

theorem CycEmb.level_adapted {L : IntermediateField K Ω} (E : CycEmb p L) (c : ℕ) (hc : 0 < c) :
    (E.level c hc).Adapted L E.s where
  pos := E.pos
  dvd k hk hks := by
    change Module.finrank K E.M * k ∣ Module.finrank K E.M * (E.s * (E.s.factorial * c))
    refine Nat.mul_dvd_mul_left _ ((Nat.dvd_factorial hk hks).trans ?_)
    exact (dvd_mul_right _ c).trans (dvd_mul_left _ _)
  le := E.le

theorem CycEmb.dvd_level_t {L : IntermediateField K Ω} (E : CycEmb p L) (c : ℕ) (hc : 0 < c) :
    Module.finrank K L * c ∣ (E.level c hc).t := by
  change _ ∣ Module.finrank K E.M * (E.s * (E.s.factorial * c))
  exact (Nat.mul_dvd_mul E.dvd (dvd_mul_left c E.s.factorial)).trans (dvd_mul_left _ _)

theorem CycEmb.level_t_dvd {L : IntermediateField K Ω} (E : CycEmb p L) {c c' : ℕ} (hc : 0 < c)
    (hc' : 0 < c') (h : c ∣ c') : (E.level c hc).t ∣ (E.level c' hc').t := by
  change Module.finrank K E.M * (E.s * (E.s.factorial * c)) ∣
    Module.finrank K E.M * (E.s * (E.s.factorial * c'))
  exact Nat.mul_dvd_mul_left _ (Nat.mul_dvd_mul_left _ (Nat.mul_dvd_mul_left _ h))

variable (p) in
/-- **The reciprocity map of a cyclic extension** `L ⊆ Ω`: `Kˣ → Gal(L/K)`. -/
noncomputable def cycRec : Kˣ →* (L ≃ₐ[K] L) :=
  (resHom ((cycEmb p L).level_adapted 1 one_pos).le_F).comp ((cycEmb p L).level 1 one_pos).rho

/-- `cycRec` is computed by any adapted level `Λ` with `[L : K] ∣ t`. -/
theorem cycRec_eq_of_adapted (Λ : StdLevel p K Ω) {N : ℕ} (hΛ : Λ.Adapted L N)
    (hLt : Module.finrank K L ∣ Λ.t) (x : Kˣ) :
    cycRec p L x = resHom hΛ.le_F (Λ.rho x) := by
  set E := cycEmb p L
  have ht0 : 0 < Λ.t := Λ.pos
  set Λ₃ := E.level Λ.t ht0
  have hL3 : L ≤ Λ₃.F := (E.level_adapted Λ.t ht0).le_F
  have h1 := StdLevel.rho_res_eq_of_le (E.level 1 one_pos) Λ₃ L (E.level_adapted 1 one_pos)
    (by simpa using E.dvd_level_t 1 one_pos) hL3 (E.level_t_dvd one_pos ht0 (one_dvd _)) x
  have h2 := StdLevel.rho_res_eq_of_le Λ Λ₃ L hΛ hLt hL3
    ((dvd_mul_left _ _).trans (E.dvd_level_t Λ.t ht0)) x
  exact h1.trans h2.symm

/-- The kernel of `cycRec L` is the norm group `N_{L/K} Lˣ`. -/
theorem cycRec_eq_one_iff (x : Kˣ) : cycRec p L x = 1 ↔ x ∈ normGroup K L :=
  StdLevel.rho_res_eq_one_iff _ L (cycEmb p L).pos ((cycEmb p L).level_adapted 1 one_pos).dvd
    (cycEmb p L).le _ x

theorem ker_cycRec : (cycRec p L).ker = normGroup K L := by
  ext x; exact cycRec_eq_one_iff L x

theorem cycRec_surjective : Function.Surjective (cycRec p L) :=
  (resHom_surjective _).comp (StdLevel.rho_surjective _)

theorem resHom_frobT {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : unramifiedOfDegree p K Ω m ≤ unramifiedOfDegree p K Ω n) :
    resHom h (frobT p K Ω n) = frobT p K Ω m := by
  rw [resHom_eq_iff]
  intro x
  exact frob_unramifiedOfDegree_inclusion hm hn h x

variable (p) in
/-- The unramified degree of the chosen level of a cyclic `L`. -/
noncomputable def cycDeg : ℕ := ((cycEmb p L).level 1 one_pos).t

theorem cycDeg_pos : 0 < cycDeg p L := StdLevel.pos _

/-- **Neukirch's formula for `cycRec`**: let `D ⊇ L ⊔ K_s` be finite Galois with
`cycDeg L ∣ s`, and `τ ∈ Gal(D/K)` acting on `K_s` as the Frobenius, whose fixed field `Σ` has
`f(Σ/K) = 1`. Then `cycRec L (N_{Σ/K} π) = τ|_L` for every uniformiser `π` of `Σ`. -/
theorem cycRec_norm_frobLift {s : ℕ} (hs0 : 0 < s) (hs : cycDeg p L ∣ s)
    (D : IntermediateField K Ω) [FiniteDimensional K D] [IsGalois K D] (hLD : L ≤ D)
    (hsD : unramifiedOfDegree p K Ω s ≤ D) (τ : D ≃ₐ[K] D) (hτ : resHom hsD τ = frobT p K Ω s)
    (hf : f p K (fixedField (Subgroup.zpowers τ)) = 1)
    (π : fixedField (Subgroup.zpowers τ)) (hπ : v p π = 1) (hπ0 : Algebra.norm K π ≠ 0) :
    cycRec p L (Units.mk0 _ hπ0) = resHom hLD τ := by
  set Λ := (cycEmb p L).level 1 one_pos
  have hUs : Λ.U ≤ unramifiedOfDegree p K Ω s := unramifiedOfDegree_le_of_dvd hs0.ne' hs
  have hτU : resHom (hUs.trans hsD) τ = frob Λ.isUnramified_U := by
    rw [← resHom_trans hUs hsD, hτ]
    exact resHom_frobT Λ.pos hs0 hUs
  exact StdLevel.rho_norm_frobLift Λ L ((cycEmb p L).level_adapted 1 one_pos)
    (by simpa using (cycEmb p L).dvd_level_t 1 one_pos) D hLD (hUs.trans hsD) τ hτU hf π hπ hπ0

end CycRec

end PadicField
