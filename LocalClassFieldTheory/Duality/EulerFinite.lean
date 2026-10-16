/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.ShapiroEuler
import LocalClassFieldTheory.Duality.TateH3Local
import LocalClassFieldTheory.Duality.TrivialModules

/-!
# Finiteness of `H¹(K, M)`, `H²(K, M)` and the Euler ratio

Let `K` be finite over `ℚ_p` and `M` a finite discrete `G_K`-module.

* **`PadicField.finite_h1`** : `H¹(K, M)` is finite. Let `K'/K` be finite with `G_{K'}` acting
  trivially on `M`. The kernel of the restriction `H¹(K, M) → H¹(K', M)` consists of classes of
  cocycles vanishing on `G_{K'}`, which factor through the finite set `G_K / G_{K'}`; and
  `H¹(K', M) = Hom(G_{K'}, M)` is finite (`PadicField.eulerCharacteristicFor_of_trivial_all`).
* **`PadicField.finite_h2`** : `H²(K, M)` is finite. In the exact sequence
  `H¹(K, Q) → H²(K, M) → H²(K, CoInd M)` of `0 → M → CoInd_{G_{K'}} M → Q → 0`, the left term is
  finite by `finite_h1` and the right one is `H²(K', M)` by Shapiro's lemma
  (`LocalClassFieldTheory.Duality.ShapiroEuler`), which is finite since `M` is trivial over `K'`.
* **`PadicField.eulerRatio`** : `ρ(M) = #H⁰ #H² p^{v_p(#M) [K : ℚ_p]} / #H¹ ∈ ℚ`; the Euler
  characteristic formula for `M` is `ρ(M) = 1` (`PadicField.eulerCharacteristicFor_iff_eulerRatio`)
  and `ρ` is multiplicative in short exact sequences (**`PadicField.eulerRatio_shortExact`**, from
  `cd(G_K) ≤ 2`, `PadicField.h2Hom_surjective`).

(Serre, *Galois cohomology*, II.5.2, Proposition 14 for the finiteness.)
-/

open groupCohomology Brauer ContH2 IntermediateField

universe v

set_option linter.unusedSectionVars false

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

section Finite

variable (M : Type*) [CommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  [IsTopologicalGroup M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]

/-- A finite discrete module is trivialised by `Gal(Ω/K')` for some finite `K'/K`. -/
theorem exists_trivializing :
    ∃ K' : IntermediateField K Ω, FiniteDimensional K K' ∧
      ∀ g ∈ K'.fixingSubgroup, ∀ m : M, g • m = m := by
  obtain ⟨K', hK', hU⟩ := exists_fixingSubgroup_eq _
    (isOpen_ker_toPermHom (G := Ω ≃ₐ[K] Ω) (A := M))
  exact ⟨K', hK', fun g hg m => smul_eq_of_mem_ker (hU ▸ hg) m⟩

variable (p) in
include hp in
/-- If `Gal(Ω/K')` acts trivially on `M`, the Euler characteristic formula holds over `K'`. -/
theorem eulerCharacteristicFor_res_of_trivial (K' : IntermediateField K Ω) [FiniteDimensional K K']
    (htriv : ∀ g ∈ K'.fixingSubgroup, ∀ m : M, g • m = m) :
    letI := resAction K' M
    EulerCharacteristicFor p K' Ω M := by
  letI := resAction K' M
  haveI := smoothAction_resAction K' M
  exact eulerCharacteristicFor_of_trivial_all M fun σ m =>
    htriv _ ((fixingSubgroupEquiv K').symm σ).2 m

/-- Restriction `H¹(G, M) → H¹(U, M)` to a subgroup. -/
noncomputable def resH1 (U : Subgroup (Ω ≃ₐ[K] Ω)) : ContH1 (Ω ≃ₐ[K] Ω) M →* ContH1 U M :=
  ContH1.map U.subtype continuous_subtype_val (MonoidHom.id M) continuous_id fun _ _ => rfl

/-- The kernel of restriction to a subgroup of finite index acting trivially is finite. -/
theorem finite_ker_resH1 (U : Subgroup (Ω ≃ₐ[K] Ω)) [Finite ((Ω ≃ₐ[K] Ω) ⧸ U)]
    (htriv : ∀ g ∈ U, ∀ m : M, g • m = m) :
    ((resH1 M U).ker : Set (ContH1 (Ω ≃ₐ[K] Ω) M)).Finite := by
  classical
  let S : Set (ContH1.cocycles (Ω ≃ₐ[K] Ω) M) := {f | ∀ u ∈ U, (f : _ → M) u = 1}
  have hS : S.Finite := by
    refine Set.Finite.of_finite_image (f := fun f q => (f : _ → M) (q : (Ω ≃ₐ[K] Ω) ⧸ U).out)
      (Set.toFinite _) ?_
    intro f hf f' hf' hff'
    apply Subtype.ext
    funext g
    set q : (Ω ≃ₐ[K] Ω) ⧸ U := QuotientGroup.mk g
    have hu : q.out⁻¹ * g ∈ U := QuotientGroup.eq.1 (QuotientGroup.out_eq' q)
    have hg : g = q.out * (q.out⁻¹ * g) := by group
    have e : ∀ f'' : ContH1.cocycles (Ω ≃ₐ[K] Ω) M, f'' ∈ S →
        (f'' : _ → M) g = (f'' : _ → M) q.out := by
      intro f'' hf''
      rw [hg, ContH1.isMulCocycle₁ f'', hf'' _ hu, smul_one, one_mul]
    rw [e f hf, e f' hf']
    exact congrFun hff' q
  refine (hS.image ContH1.mk).subset ?_
  intro x hx
  induction x using ContH1.induction_on with | h f => ?_
  refine ⟨f, ?_, rfl⟩
  intro u hu
  have hx' : resH1 M U (ContH1.mk f) = 1 := hx
  rw [resH1, ContH1.map_mk, ContH1.mk_eq_one_iff] at hx'
  obtain ⟨m, hm⟩ := hx'
  have := hm ⟨u, hu⟩
  simp only [ContH1.cocyclesMap_apply, Subgroup.coe_subtype, MonoidHom.id_apply] at this
  rw [← this, Subgroup.smul_def, htriv u hu, div_self']

include hp in
/-- **`H¹(K, M)` is finite** for every finite discrete `G_K`-module `M`. -/
theorem finite_h1 : Finite (ContH1 (Ω ≃ₐ[K] Ω) M) := by
  obtain ⟨K', hK', htriv⟩ := exists_trivializing (K := K) (Ω := Ω) M
  have hE := eulerCharacteristicFor_res_of_trivial p M K' htriv
  letI := resAction K' M
  have e := card_h1_of_equiv (fixingSubgroupEquiv K') (resCompat_resAction K' M)
    (continuous_fixingSubgroupEquiv K') (continuous_fixingSubgroupEquiv_symm K')
  haveI : Finite (ContH1 (Ω ≃ₐ[K'] Ω) M) := hE.1
  haveI : Finite (ContH1 K'.fixingSubgroup M) :=
    Nat.finite_of_card_ne_zero (by rw [e]; exact Nat.card_pos.ne')
  haveI : Finite ((resH1 M K'.fixingSubgroup).ker) :=
    (finite_ker_resH1 M K'.fixingSubgroup htriv).to_subtype
  refine Nat.finite_of_card_ne_zero ?_
  rw [card_eq_card_ker_mul_card_range (resH1 M K'.fixingSubgroup)]
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

/-- The diagonal embedding `M → CoInd_U M`. -/
def diag (U : Subgroup (Ω ≃ₐ[K] Ω)) : M →* CoInd U M where
  toFun m := (fun _ => m : (Ω ≃ₐ[K] Ω) ⧸ U → M)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem diag_smul (U : Subgroup (Ω ≃ₐ[K] Ω)) (g : Ω ≃ₐ[K] Ω) (m : M) :
    diag M U (g • m) = g • diag M U m := rfl

theorem diag_injective (U : Subgroup (Ω ≃ₐ[K] Ω)) : Function.Injective (diag M U) :=
  fun _ _ h => congrFun h (CoInd.base U)

include hp in
/-- **`H²(K, M)` is finite** for every finite discrete `G_K`-module `M`. -/
theorem finite_h2 : Finite (ContH2 (Ω ≃ₐ[K] Ω) M) := by
  obtain ⟨K', hK', htriv⟩ := exists_trivializing (K := K) (Ω := Ω) M
  have hE := eulerCharacteristicFor_res_of_trivial p M K' htriv
  set U := K'.fixingSubgroup
  have hUo : IsOpen (U : Set (Ω ≃ₐ[K] Ω)) := K'.fixingSubgroup_isOpen
  haveI := CoInd.smoothAction (A := M) hUo
  -- `H²(K, CoInd M) = H²(K', M)` is finite
  have hB : Finite (ContH2 (Ω ≃ₐ[K] Ω) (CoInd U M)) := by
    letI := resAction K' M
    haveI : Finite (ContH2 (Ω ≃ₐ[K'] Ω) M) := hE.2.1
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_h2_coInd (resCompat_resAction K' M)]
    exact Nat.card_pos.ne'
  -- the short exact sequence `0 → M → CoInd M → Q → 0`
  set B := (diag M U).range
  have hBs : IsGStable (G := Ω ≃ₐ[K] Ω) B := by
    rintro g _ ⟨m, rfl⟩
    exact ⟨g • m, diag_smul M U g m⟩
  letI := subAction B hBs
  letI := quotAction B hBs
  haveI := smoothAction_sub B hBs
  haveI := smoothAction_quot B hBs
  let S := subQuotSES B hBs
  letI : TopologicalSpace (CoInd U M ⧸ B) := ⊥
  haveI : DiscreteTopology (CoInd U M ⧸ B) := ⟨rfl⟩
  haveI : Finite (CoInd U M) := inferInstanceAs (Finite ((Ω ≃ₐ[K] Ω) ⧸ U → M))
  haveI : Finite (CoInd U M ⧸ B) := Finite.of_surjective _ (QuotientGroup.mk'_surjective B)
  haveI : Finite (ContH1 (Ω ≃ₐ[K] Ω) (CoInd U M ⧸ B)) :=
    finite_h1 (p := p) (K := K) (Ω := Ω) (CoInd U M ⧸ B)
  have hB2 : Finite (ContH2 (Ω ≃ₐ[K] Ω) B) := by
    haveI : Finite (h2Hom (G := Ω ≃ₐ[K] Ω) S.i S.map_smul_i).ker := by
      rw [S.exact_h2A]
      exact Finite.of_surjective _ (S.delta1.rangeRestrict_surjective)
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_eq_card_ker_mul_card_range (h2Hom (G := Ω ≃ₐ[K] Ω) S.i S.map_smul_i)]
    exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  let τ : M ≃* B := MonoidHom.ofInjective (diag_injective M U)
  have hτ : ∀ (g : Ω ≃ₐ[K] Ω) (m : M), τ (g • m) = g • τ m := fun g m => rfl
  exact Finite.of_injective _ (h2Map_bijective τ hτ).1

end Finite

section Ratio

variable (p K Ω) in
/-- The **Euler ratio** `ρ(M) = #H⁰(K, M) · #H²(K, M) · p^{v_p(#M) [K : ℚ_p]} / #H¹(K, M)`. -/
noncomputable def eulerRatio (M : Type*) [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] : ℚ :=
  ((Nat.card (H0 (Ω ≃ₐ[K] Ω) M) * Nat.card (ContH2 (Ω ≃ₐ[K] Ω) M) *
    p ^ (padicValNat p (Nat.card M) * Module.finrank ℚ_[p] K) : ℕ) : ℚ) /
    Nat.card (ContH1 (Ω ≃ₐ[K] Ω) M)

variable (M : Type*) [CommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  [IsTopologicalGroup M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]

include hp in
theorem eulerRatio_pos : 0 < eulerRatio p K Ω M := by
  haveI := finite_h1 (p := p) (K := K) (Ω := Ω) M
  haveI := finite_h2 (p := p) (K := K) (Ω := Ω) M
  unfold eulerRatio
  have h1 : (0 : ℚ) < Nat.card (ContH1 (Ω ≃ₐ[K] Ω) M) := by exact_mod_cast Nat.card_pos
  refine div_pos ?_ h1
  have : 0 < Nat.card (H0 (Ω ≃ₐ[K] Ω) M) * Nat.card (ContH2 (Ω ≃ₐ[K] Ω) M) *
      p ^ (padicValNat p (Nat.card M) * Module.finrank ℚ_[p] K) :=
    Nat.mul_pos (Nat.mul_pos Nat.card_pos Nat.card_pos) (pow_pos hp.out.pos _)
  exact_mod_cast this

include hp in
/-- **The Euler characteristic formula is `ρ(M) = 1`.** -/
theorem eulerCharacteristicFor_iff_eulerRatio :
    EulerCharacteristicFor p K Ω M ↔ eulerRatio p K Ω M = 1 := by
  haveI := finite_h1 (p := p) (K := K) (Ω := Ω) M
  haveI := finite_h2 (p := p) (K := K) (Ω := Ω) M
  have h1 : (Nat.card (ContH1 (Ω ≃ₐ[K] Ω) M) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold eulerRatio EulerCharacteristicFor
  rw [div_eq_one_iff_eq h1, Nat.cast_inj]
  constructor
  · rintro ⟨-, -, h⟩
    exact h.symm
  · intro h
    exact ⟨inferInstance, inferInstance, h.symm⟩

/-- `ρ` is invariant under equivariant isomorphisms. -/
theorem eulerRatio_congr {M' : Type*} [CommGroup M'] [TopologicalSpace M'] [DiscreteTopology M']
    [IsTopologicalGroup M'] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M'] [SmoothAction (Ω ≃ₐ[K] Ω) M']
    (τ : M ≃* M') (hτ : ∀ (g : Ω ≃ₐ[K] Ω) (x : M), τ (g • x) = g • τ x) :
    eulerRatio p K Ω M = eulerRatio p K Ω M' := by
  unfold eulerRatio
  rw [← Nat.card_congr (Equiv.ofBijective _ (h1Map_bijective τ hτ)),
    ← Nat.card_congr (Equiv.ofBijective _ (h0Map_bijective τ hτ)),
    ← Nat.card_congr (Equiv.ofBijective _ (h2Map_bijective τ hτ)), ← Nat.card_congr τ.toEquiv]

include hp in
theorem eulerRatio_of_subsingleton [Subsingleton M] : eulerRatio p K Ω M = 1 :=
  (eulerCharacteristicFor_iff_eulerRatio M).1 eulerCharacteristicFor_of_subsingleton

include hp in
/-- **`ρ` is multiplicative in short exact sequences** (`cd(G_K) ≤ 2`). -/
theorem eulerRatio_shortExact {A B C : Type v} [CommGroup A] [CommGroup B] [CommGroup C]
    [Finite A] [Finite B] [Finite C] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalGroup A] [TopologicalSpace B] [DiscreteTopology B] [IsTopologicalGroup B]
    [TopologicalSpace C] [DiscreteTopology C] [IsTopologicalGroup C]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) A] [MulDistribMulAction (Ω ≃ₐ[K] Ω) B]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) C] [SmoothAction (Ω ≃ₐ[K] Ω) A]
    [SmoothAction (Ω ≃ₐ[K] Ω) B] [SmoothAction (Ω ≃ₐ[K] Ω) C]
    (S : GShortExact (Ω ≃ₐ[K] Ω) A B C) :
    eulerRatio p K Ω B = eulerRatio p K Ω A * eulerRatio p K Ω C := by
  haveI := finite_h1 (p := p) (K := K) (Ω := Ω) A
  haveI := finite_h1 (p := p) (K := K) (Ω := Ω) B
  haveI := finite_h1 (p := p) (K := K) (Ω := Ω) C
  have key := S.card_identity (h2Hom_surjective (p := p) (K := K) (Ω := Ω) S)
  have hv : padicValNat p (Nat.card B) =
      padicValNat p (Nat.card A) + padicValNat p (Nat.card C) := by
    rw [S.card_eq_mul, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne']
  have hA1 : (Nat.card (ContH1 (Ω ≃ₐ[K] Ω) A) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hB1 : (Nat.card (ContH1 (Ω ≃ₐ[K] Ω) B) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hC1 : (Nat.card (ContH1 (Ω ≃ₐ[K] Ω) C) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold eulerRatio
  rw [div_mul_div_comm, div_eq_div_iff hB1 (mul_ne_zero hA1 hC1), hv, add_mul, pow_add]
  have key' : (Nat.card (ContH1 (Ω ≃ₐ[K] Ω) B) : ℚ) *
      (Nat.card (H0 (Ω ≃ₐ[K] Ω) A) * Nat.card (ContH2 (Ω ≃ₐ[K] Ω) A) *
        (Nat.card (H0 (Ω ≃ₐ[K] Ω) C) * Nat.card (ContH2 (Ω ≃ₐ[K] Ω) C))) =
      Nat.card (ContH1 (Ω ≃ₐ[K] Ω) A) * Nat.card (ContH1 (Ω ≃ₐ[K] Ω) C) *
        (Nat.card (H0 (Ω ≃ₐ[K] Ω) B) * Nat.card (ContH2 (Ω ≃ₐ[K] Ω) B)) := by
    exact_mod_cast key
  push_cast
  linear_combination (-1 : ℚ) * ((p : ℚ) ^ (padicValNat p (Nat.card A) * Module.finrank ℚ_[p] K) *
    (p : ℚ) ^ (padicValNat p (Nat.card C) * Module.finrank ℚ_[p] K)) * key'

end Ratio


end PadicField
