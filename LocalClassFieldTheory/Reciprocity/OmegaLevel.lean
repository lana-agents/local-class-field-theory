/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.LevelFrob
import LocalClassFieldTheory.PadicField.MaxUnramified

/-!
# Standard levels inside an algebraic closure

Let `Ω` be an algebraically closed extension of `K`. A *standard level* `Λ` inside `Ω` consists of
a finite cyclic totally ramified Galois `M = Λ.M ⊆ Ω` and `t = Λ.t` with `[M : K] ∣ t`; its field
is `Λ.F = M ⊔ K_t`. We equip `Λ.M`, `Λ.U = K_t` and `Λ.F` with the algebra structures required
by the standard-level API and define the reciprocity map `PadicField.StdLevel.rho : Kˣ →* Gal(F/K)`.

* `PadicField.resHom`: restriction `Gal(E'/K) → Gal(E/K)` for `E ≤ E'` inside `Ω`;
* `PadicField.StdLevel.finrank_F`: `[F : K] = [M : K] t`;
* `PadicField.StdLevel.rho_mem_ker_iff`: for cyclic `L ⊆ M ⊔ K_N ⊆ F` (`N` small),
  `ρ(x)|_L = 1 ↔ x ∈ N_{L/K} Lˣ`.
-/

set_option linter.unusedSectionVars false

open IntermediateField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]

section Res

variable {E E' : IntermediateField K Ω} [Normal K E]

/-- Restriction `Gal(E'/K) → Gal(E/K)` for `E ≤ E'`. -/
noncomputable def resHom (h : E ≤ E') : (E' ≃ₐ[K] E') →* (E ≃ₐ[K] E) :=
  letI : Algebra E E' := (inclusion h).toAlgebra
  haveI : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  AlgEquiv.restrictNormalHom E

theorem resHom_apply (h : E ≤ E') (σ : E' ≃ₐ[K] E') (x : E) :
    ((resHom h σ x : E) : Ω) = (σ (inclusion h x) : Ω) := by
  letI : Algebra E E' := (inclusion h).toAlgebra
  haveI : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have := AlgEquiv.restrictNormal_commutes (σ : E' ≃ₐ[K] E') E x
  exact congrArg (fun y : E' ↦ (y : Ω)) this

theorem resHom_eq_iff (h : E ≤ E') (σ : E' ≃ₐ[K] E') (τ : E ≃ₐ[K] E) :
    resHom h σ = τ ↔ ∀ x : E, (σ (inclusion h x) : Ω) = (τ x : Ω) := by
  constructor
  · rintro rfl x; exact (resHom_apply h σ x).symm
  · intro H; ext x; rw [resHom_apply, H]

theorem resHom_surjective [Normal K E'] (h : E ≤ E') : Function.Surjective (resHom h) := by
  letI : Algebra E E' := (inclusion h).toAlgebra
  haveI : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact AlgEquiv.restrictNormalHom_surjective E'

theorem resHom_trans {E'' : IntermediateField K Ω} [Normal K E'] (h : E ≤ E') (h' : E' ≤ E'')
    (σ : E'' ≃ₐ[K] E'') : resHom h (resHom h' σ) = resHom (h.trans h') σ := by
  rw [resHom_eq_iff]
  intro x
  rw [resHom_apply, resHom_apply]
  rfl

/-- An automorphism of `A = L ⊔ U` trivial on `L` and on `U` is trivial. -/
theorem eq_one_of_resHom_eq_one {L U A : IntermediateField K Ω} [Normal K L] [Normal K U]
    (hA : A = L ⊔ U) (hLA : L ≤ A) (hUA : U ≤ A) (σ : A ≃ₐ[K] A) (hL : resHom hLA σ = 1)
    (hU : resHom hUA σ = 1) : σ = 1 := by
  have hfix : ∀ (E : IntermediateField K Ω) [Normal K E] (hEA : E ≤ A),
      resHom hEA σ = 1 → E ≤ lift (fixedField (Subgroup.zpowers σ)) := by
    intro E _ hEA h x hx
    have h1 := resHom_apply hEA σ ⟨x, hx⟩
    rw [h, AlgEquiv.one_apply] at h1
    refine (mem_lift (⟨x, hEA hx⟩ : A)).2 ?_
    rintro ⟨_, j, rfl⟩
    exact zpow_apply_eq_of_apply_eq (Subtype.ext h1.symm) j
  have hle := sup_le (hfix L hLA hL) (hfix U hUA hU)
  ext a
  have ha : (a : Ω) ∈ L ⊔ U := by rw [← hA]; exact a.2
  have := (mem_lift a).1 (hle ha) ⟨σ, Subgroup.mem_zpowers _⟩
  rw [AlgEquiv.one_apply]
  exact congrArg Subtype.val this

end Res

variable (p K Ω) in
/-- A standard level inside `Ω`: a cyclic totally ramified Galois `M/K` and `t` with
`[M : K] ∣ t`. -/
structure StdLevel where
  /-- The totally ramified part. -/
  M : IntermediateField K Ω
  /-- The degree of the unramified part. -/
  t : ℕ
  finiteDimensional : FiniteDimensional K M
  isGalois : IsGalois K M
  isCyclic : IsCyclic (M ≃ₐ[K] M)
  totRam : e p K M = Module.finrank K M
  dvd : Module.finrank K M ∣ t
  pos : 0 < t

namespace StdLevel

attribute [instance] StdLevel.finiteDimensional StdLevel.isGalois StdLevel.isCyclic

variable [IsAlgClosed Ω] (Λ : StdLevel p K Ω)

/-- The unramified part `K_t`. -/
noncomputable def U : IntermediateField K Ω := unramifiedOfDegree p K Ω Λ.t

/-- The field `F = M ⊔ K_t` of the level. -/
noncomputable def F : IntermediateField K Ω := Λ.M ⊔ Λ.U

theorem M_le : Λ.M ≤ Λ.F := le_sup_left
theorem U_le : Λ.U ≤ Λ.F := le_sup_right

instance : FiniteDimensional K Λ.U := unramifiedOfDegree_finiteDimensional _
instance : FiniteDimensional K Λ.F := by unfold F; infer_instance
theorem isUnramified_U : IsUnramified p K Λ.U := isUnramified_unramifiedOfDegree p K Ω _

instance : IsGalois K Λ.U := isGalois_of_isUnramified (K := K) (L := Λ.U) Λ.isUnramified_U
instance : IsGalois K Λ.F := by unfold F; infer_instance

noncomputable instance algM : Algebra Λ.M Λ.F := (inclusion Λ.M_le).toAlgebra
noncomputable instance algU : Algebra Λ.U Λ.F := (inclusion Λ.U_le).toAlgebra
instance : IsScalarTower K Λ.M Λ.F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
instance : IsScalarTower K Λ.U Λ.F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
instance : IsScalarTower ℚ_[p] Λ.M Λ.F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
instance : IsScalarTower ℚ_[p] Λ.U Λ.F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
instance : FiniteDimensional Λ.U Λ.F := FiniteDimensional.right K Λ.U Λ.F
instance : FiniteDimensional Λ.M Λ.F := FiniteDimensional.right K Λ.M Λ.F

theorem algebraMap_M (m : Λ.M) : ((algebraMap Λ.M Λ.F m : Λ.F) : Ω) = m := rfl
theorem algebraMap_U (u : Λ.U) : ((algebraMap Λ.U Λ.F u : Λ.F) : Ω) = u := rfl

theorem finrank_U : Module.finrank K Λ.U = Λ.t := finrank_unramifiedOfDegree p K Ω Λ.pos

theorem finrank_F : Module.finrank K Λ.F = Module.finrank K Λ.M * Module.finrank K Λ.U := by
  refine le_antisymm (IntermediateField.finrank_sup_le _ _) ?_
  have h1 := e_dvd_of_algHom (p := p) (inclusion Λ.M_le)
  have h2 := f_dvd_of_algHom (p := p) (inclusion Λ.U_le)
  rw [Λ.totRam] at h1
  rw [Λ.isUnramified_U.f_eq] at h2
  rw [← e_mul_f (p := p) (K := K) (L := Λ.F)]
  exact Nat.mul_le_mul (Nat.le_of_dvd e_pos h1) (Nat.le_of_dvd f_pos h2)

theorem dvd_U : Module.finrank K Λ.M ∣ Module.finrank K Λ.U := Λ.finrank_U ▸ Λ.dvd

/-- A generator of `Gal(M/K)`. -/
noncomputable def gen : Λ.M ≃ₐ[K] Λ.M := (IsCyclic.exists_generator (α := Λ.M ≃ₐ[K] Λ.M)).choose

theorem gen_spec : ∀ g, g ∈ Subgroup.zpowers Λ.gen :=
  (IsCyclic.exists_generator (α := Λ.M ≃ₐ[K] Λ.M)).choose_spec

/-- The reciprocity map of the level. -/
noncomputable def rho : Kˣ →* (Λ.F ≃ₐ[K] Λ.F) :=
  rhoF Λ.totRam Λ.isUnramified_U Λ.finrank_F Λ.gen Λ.gen_spec Λ.dvd_U

theorem rho_surjective : Function.Surjective Λ.rho := rhoF_surjective _ _ _ _ _ _

theorem mem_normGroup_of_rho_eq_one (x : Kˣ) (hx : Λ.rho x = 1) : x ∈ normGroup K Λ.F :=
  mem_normGroup_of_rhoF_eq_one _ _ _ _ _ _ x hx

/-- The Frobenius lift `τ = (g, φ^k)` of the level. -/
noncomputable abbrev tauL (g : Λ.F ≃ₐ[Λ.U] Λ.F) (k : ℕ) : Λ.F ≃ₐ[K] Λ.F :=
  tau (K := K) (M := Λ.M) (U := Λ.U) (F := Λ.F) Λ.totRam Λ.isUnramified_U Λ.finrank_F g k

theorem frob_pow_apply_of_mem {n N : ℕ} (hN : 0 < N) (hNn : N ∣ n) (hn : 0 < n)
    (u : unramifiedOfDegree p K Ω n) (hu : (u : Ω) ∈ unramifiedOfDegree p K Ω N) :
    (frob (isUnramified_unramifiedOfDegree p K Ω n) ^ N) u = u := by
  have h := unramifiedOfDegree_le_of_dvd (p := p) (K := K) (Ω := Ω) hn.ne' hNn
  set w : unramifiedOfDegree p K Ω N := ⟨u, hu⟩
  have hw : ∀ j : ℕ, ((frob (isUnramified_unramifiedOfDegree p K Ω n) ^ j) (inclusion h w) : Ω)
      = ((frob (isUnramified_unramifiedOfDegree p K Ω N) ^ j) w : Ω) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', AlgEquiv.mul_apply, pow_succ', AlgEquiv.mul_apply]
      have : (frob (isUnramified_unramifiedOfDegree p K Ω n) ^ j) (inclusion h w) =
          inclusion h ((frob (isUnramified_unramifiedOfDegree p K Ω N) ^ j) w) :=
        Subtype.ext ih
      rw [this, frob_unramifiedOfDegree_inclusion hN hn h]
  have h1 : frob (isUnramified_unramifiedOfDegree p K Ω N) ^ N = 1 := by
    have := pow_orderOf_eq_one (frob (isUnramified_unramifiedOfDegree p K Ω N))
    rwa [orderOf_frob, finrank_unramifiedOfDegree p K Ω hN] at this
  apply Subtype.ext
  have := hw N
  rw [h1, AlgEquiv.one_apply] at this
  exact this

/-- `τ = (1, φ^N)` fixes `M ⊔ K_N`. -/
theorem le_fixedField_tauL {N : ℕ} (hN : 0 < N) (hNt : N ∣ Λ.t) {L : IntermediateField K Ω}
    (hL : L ≤ Λ.M ⊔ unramifiedOfDegree p K Ω N) (hLF : L ≤ Λ.F) :
    L.restrict hLF ≤ fixedField (Subgroup.zpowers (Λ.tauL 1 N)) := by
  have hle : Λ.M ⊔ unramifiedOfDegree p K Ω N ≤
      lift (fixedField (Subgroup.zpowers (Λ.tauL 1 N))) := by
    have hfix : ∀ x : Λ.F, Λ.tauL 1 N x = x →
        (x : Ω) ∈ lift (fixedField (Subgroup.zpowers (Λ.tauL 1 N))) := by
      intro x hx
      rw [mem_lift]
      rintro ⟨_, j, rfl⟩
      exact zpow_apply_eq_of_apply_eq hx j
    refine sup_le (fun m hm ↦ hfix ⟨m, Λ.M_le hm⟩ ?_) (fun u hu ↦ ?_)
    · change stdProd Λ.totRam Λ.isUnramified_U Λ.finrank_F
        (1, stdFrob Λ.totRam Λ.isUnramified_U Λ.finrank_F ^ N) (algebraMap Λ.M Λ.F ⟨m, hm⟩) =
          algebraMap Λ.M Λ.F ⟨m, hm⟩
      rw [stdProd_apply, AlgEquiv.commutes, AlgEquiv.one_apply]
    · have huU : u ∈ Λ.U := unramifiedOfDegree_le_of_dvd Λ.pos.ne' hNt hu
      refine hfix ⟨u, Λ.U_le huU⟩ ?_
      change stdProd Λ.totRam Λ.isUnramified_U Λ.finrank_F
        (1, stdFrob Λ.totRam Λ.isUnramified_U Λ.finrank_F ^ N) (algebraMap Λ.U Λ.F ⟨u, huU⟩) =
          algebraMap Λ.U Λ.F ⟨u, huU⟩
      rw [stdProd_apply, AlgEquiv.one_apply, ← stdResU_apply Λ.isUnramified_U, map_pow,
        stdResU_stdFrob]
      congr 1
      exact frob_pow_apply_of_mem hN hNt Λ.pos ⟨u, huU⟩ hu
  intro x hx
  rw [mem_restrict] at hx
  exact (mem_lift x).1 (hle (hL hx))

/-- **Reciprocity for a cyclic subextension of a level**: `ρ(x)|_L = 1 ↔ x ∈ N_{L/K} Lˣ`. -/
theorem rho_res_eq_one_iff (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] {N : ℕ} (hN0 : 0 < N)
    (hNt : ∀ k, 0 < k → k ≤ N → Module.finrank K Λ.M * k ∣ Λ.t)
    (hL : L ≤ Λ.M ⊔ unramifiedOfDegree p K Ω N) (hLF : L ≤ Λ.F) (x : Kˣ) :
    resHom hLF (Λ.rho x) = 1 ↔ x ∈ normGroup K L := by
  set L' := L.restrict hLF
  let ε : L ≃ₐ[K] L' := restrict_algEquiv hLF
  haveI : IsGalois K L' := IsGalois.of_algEquiv ε
  haveI : IsCyclic (L' ≃ₐ[K] L') :=
    isCyclic_of_surjective (AlgEquiv.autCongr ε).toMonoidHom (AlgEquiv.autCongr ε).surjective
  have hNt' : ∀ k, 0 < k → k ≤ N → Module.finrank K Λ.M * k ∣ Module.finrank K Λ.U := by
    intro k hk hkN; rw [Λ.finrank_U]; exact hNt k hk hkN
  have hNdvd : N ∣ Λ.t := (Dvd.intro_left _ rfl).trans (hNt N hN0 le_rfl)
  have key := comap_rhoF_fixingSubgroup Λ.totRam Λ.isUnramified_U Λ.finrank_F Λ.gen Λ.gen_spec
    Λ.dvd_U N hN0 hNt' L' (Λ.le_fixedField_tauL hN0 hNdvd hL hLF)
  have hng : normGroup K L' = normGroup K L :=
    le_antisymm (normGroup_le_of_algHom ε.toAlgHom) (normGroup_le_of_algHom ε.symm.toAlgHom)
  rw [hng] at key
  rw [← key, Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]
  change _ ↔ ∀ y ∈ L', Λ.rho x y = y
  constructor
  · intro h y hy
    have := resHom_apply hLF (Λ.rho x) ⟨y, (mem_restrict hLF y).1 hy⟩
    rw [h, AlgEquiv.one_apply] at this
    exact Subtype.ext this.symm
  · intro h
    ext y
    rw [resHom_apply, AlgEquiv.one_apply]
    exact congrArg Subtype.val (h _ ((mem_restrict hLF _).2 y.2))

end StdLevel

end PadicField
