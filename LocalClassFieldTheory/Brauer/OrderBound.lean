/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.Relative
import LocalClassFieldTheory.Brauer.InfRes
import LocalClassFieldTheory.Brauer.LocalGalois

/-!
# The bound `|H²(H, Lˣ)| ≤ |H|`

Let `L/K` be a finite extension of fields finite over `ℚ_[p]` and `H ≤ Aut(L/K)` a subgroup.
Then `H²(H, Lˣ)` is finite of order at most `|H|` (`PadicField.card_contH2_le`); in particular
`|Br(L/K)| ≤ [L : K]` for Galois `L/K` (`PadicField.card_relBr_le`).

Proof: induction on `|H|`.
* If `H` is cyclic, `Aut(L/L^H) ≅ H` and `|Br(L/L^H)| = [L : L^H] = |H|` by periodicity and the
  class field axiom (`PadicField.card_contH2_of_isCyclic`).
* Otherwise `H` has a proper non-trivial normal subgroup `N`
  (`PadicField.isCyclic_or_exists_normal`: solvability of local Galois groups). With
  `F₂ = L^N`, `H` acts on `F₂` through `Q = H/N` and
  `0 → H²(Q, F₂ˣ) → H²(H, Lˣ) → H²(N, Lˣ)` is exact (`ContH2.map_injective`,
  `ContH2.exists_map_eq_of_res`, Hilbert 90 for `L/L^N`), so `|H²(H)| ≤ |Q| |N| = |H|`.
-/

open ContH2 IntermediateField groupCohomology

set_option linter.unusedSectionVars false

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]

section

variable {F E : Type*} [Field F] [Field E] [Algebra ℚ_[p] F] [Algebra ℚ_[p] E]
  [Algebra F E] [IsScalarTower ℚ_[p] F E] [FiniteDimensional ℚ_[p] F]
  [FiniteDimensional ℚ_[p] E]

/-- `Aut(E/E^H) ≃* H`. -/
noncomputable def fixedFieldGalEquiv [FiniteDimensional F E] (H : Subgroup (E ≃ₐ[F] E)) :
    (E ≃ₐ[fixedField H] E) ≃* H :=
  (fixingSubgroupEquiv (fixedField H)).symm.trans
    (MulEquiv.subgroupCongr (fixingSubgroup_fixedField H))

theorem fixedFieldGalEquiv_apply [FiniteDimensional F E] (H : Subgroup (E ≃ₐ[F] E))
    (σ : E ≃ₐ[fixedField H] E) (x : E) : ((fixedFieldGalEquiv H σ : E ≃ₐ[F] E)) x = σ x := rfl

include hp in
/-- **Cyclic case**: `|H²(H, Eˣ)| = |H|` for a cyclic group `H` of automorphisms. -/
theorem card_contH2_of_isCyclic (H : Subgroup (E ≃ₐ[F] E)) [IsCyclic H] :
    Nat.card (ContH2 H Eˣ) = Nat.card H := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ_[p] F E
  set F₁ := fixedField H
  have e := fixedFieldGalEquiv H
  haveI : IsCyclic (E ≃ₐ[F₁] E) := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  haveI : IsGalois F₁ E := by
    apply IsGalois.of_card_aut_eq_finrank
    rw [Nat.card_congr (fixedFieldGalEquiv H).toEquiv, finrank_fixedField_eq_card]
  rw [card_mapEquiv (G := E ≃ₐ[F₁] E) (fixedFieldGalEquiv H).symm continuous_of_discreteTopology
    continuous_of_discreteTopology (fun g m => rfl)]
  rw [card_rel_of_isCyclic (p := p), ← IsGalois.card_aut_eq_finrank,
    Nat.card_congr (fixedFieldGalEquiv H).toEquiv]

end

/-- Counting in an exact sequence `1 → X → Y → Z` of groups with `X`, `Z` finite. -/
theorem card_le_of_exact {X Y Z : Type*} [Group X] [Group Y] [Group Z] [Finite X] [Finite Z]
    (i : X →* Y) (r : Y →* Z) (hi : Function.Injective i) (hex : r.ker ≤ i.range) :
    Nat.card Y ≠ 0 ∧ Nat.card Y ≤ Nat.card X * Nat.card Z := by
  have h1 : Nat.card r.ker ≤ Nat.card X := by
    calc Nat.card r.ker ≤ Nat.card i.range := by
          haveI : Finite i.range := Set.finite_range i |>.to_subtype
          exact Subgroup.card_le_of_le hex
      _ = Nat.card X := Nat.card_range_of_injective hi
  have h2 : Nat.card (Y ⧸ r.ker) ≤ Nat.card Z := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange r).toEquiv]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  have hk : Nat.card r.ker ≠ 0 := by
    haveI : Finite r.ker := by
      haveI : Finite i.range := Set.finite_range i |>.to_subtype
      exact Finite.of_injective _ (Subgroup.inclusion_injective hex)
    exact Nat.card_pos.ne'
  have hq : Nat.card (Y ⧸ r.ker) ≠ 0 := by
    haveI : Finite (Y ⧸ r.ker) := by
      haveI : Finite r.range := inferInstance
      exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange r).toEquiv.symm
    exact Nat.card_ne_zero.2 ⟨inferInstance, this⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup r.ker]
  refine ⟨mul_ne_zero hq hk, ?_⟩
  rw [mul_comm]
  exact Nat.mul_le_mul h1 h2

section Normal

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable {H : Subgroup (E ≃ₐ[F] E)} (N : Subgroup H) [hN : N.Normal]

/-- `N` as a subgroup of `Aut(E/F)`. -/
abbrev normalAut : Subgroup (E ≃ₐ[F] E) := N.map H.subtype

/-- The fixed field `E^N`. -/
abbrev fixedN : IntermediateField F E := fixedField (normalAut N)

include hN in
theorem conj_mem_normalAut (h : H) {n : E ≃ₐ[F] E} (hn : n ∈ normalAut N) :
    (h : E ≃ₐ[F] E)⁻¹ * n * h ∈ normalAut N := by
  obtain ⟨n₀, hn₀, rfl⟩ := hn
  refine ⟨h⁻¹ * n₀ * h, ?_, rfl⟩
  have := hN.conj_mem n₀ hn₀ h⁻¹
  rwa [inv_inv] at this

include hN in
theorem apply_mem_fixedN (h : H) {x : E} (hx : x ∈ fixedN N) : (h : E ≃ₐ[F] E) x ∈ fixedN N := by
  rintro ⟨n, hn⟩
  have e : ((h : E ≃ₐ[F] E)⁻¹ * n * h) x = x := hx ⟨_, conj_mem_normalAut N h hn⟩
  change n ((h : E ≃ₐ[F] E) x) = (h : E ≃ₐ[F] E) x
  calc n ((h : E ≃ₐ[F] E) x) = (h : E ≃ₐ[F] E) (((h : E ≃ₐ[F] E)⁻¹ * n * h) x) := by
        simp [AlgEquiv.mul_apply]
    _ = (h : E ≃ₐ[F] E) x := by rw [e]

/-- The action of `H` on `E^N`. -/
noncomputable def resN : H →* (fixedN N ≃ₐ[F] fixedN N) where
  toFun h :=
    { toFun := fun x => ⟨(h : E ≃ₐ[F] E) x, apply_mem_fixedN N h x.2⟩
      invFun := fun x => ⟨((h⁻¹ : H) : E ≃ₐ[F] E) x, apply_mem_fixedN N h⁻¹ x.2⟩
      left_inv := fun x => by ext; simp
      right_inv := fun x => by ext; simp
      map_mul' := fun x y => by ext; simp
      map_add' := fun x y => by ext; simp
      commutes' := fun a => by ext; simp }
  map_one' := by ext; simp
  map_mul' h h' := by ext; simp

theorem coe_resN_apply (h : H) (x : fixedN N) :
    ((resN N h x : fixedN N) : E) = (h : E ≃ₐ[F] E) x := rfl

theorem mem_ker_resN_iff [FiniteDimensional F E] (h : H) : h ∈ (resN N).ker ↔ h ∈ N := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hh
    have : (h : E ≃ₐ[F] E) ∈ (fixedN N).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have := congrArg (fun σ : fixedN N ≃ₐ[F] fixedN N => ((σ ⟨x, hx⟩ : fixedN N) : E)) hh
      simpa [coe_resN_apply] using this
    rw [fixingSubgroup_fixedField] at this
    obtain ⟨n, hn, e⟩ := this
    rwa [← Subtype.ext e]
  · intro hh
    ext x
    rw [coe_resN_apply, AlgEquiv.one_apply]
    exact x.2 ⟨h, ⟨h, hh, rfl⟩⟩

end Normal

section NormalStep

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable {H : Subgroup (E ≃ₐ[F] E)} (N : Subgroup H) [hN : N.Normal]

/-- The quotient `H/N` as a group of automorphisms of `E^N`. -/
noncomputable abbrev quotAut : Subgroup (fixedN N ≃ₐ[F] fixedN N) := (resN N).range

set_option synthInstance.maxHeartbeats 200000 in
-- The action of `quotAut N` on `(E^N)ˣ` is slow to synthesize.
theorem units_map_val_resN_smul (h : H) (a : (fixedN N)ˣ) :
    Units.map ((fixedN N).val : fixedN N →* E) ((resN N).rangeRestrict h • a) =
      h • Units.map ((fixedN N).val : fixedN N →* E) a := by
  ext
  rfl

/-- Hilbert 90 for `N = Aut(E/E^N)`, on the kernel of `H → Aut(E^N)`. -/
theorem isMulCoboundary₁_ker_resN (c : ((resN N).rangeRestrict).ker → Eˣ)
    (hc : IsMulCocycle₁ c) : IsMulCoboundary₁ c := by
  have hker : ∀ k : H, k ∈ ((resN N).rangeRestrict).ker ↔ k ∈ N := by
    intro k
    rw [MonoidHom.ker_rangeRestrict, mem_ker_resN_iff]
  have hmemH : ∀ σ : E ≃ₐ[fixedN N] E, σ.restrictScalars F ∈ H := by
    intro σ
    have : σ.restrictScalars F ∈ (fixedN N).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact σ.commutes ⟨x, hx⟩
    rw [fixingSubgroup_fixedField] at this
    obtain ⟨n, -, e⟩ := this
    rw [← e]
    exact n.2
  have hmemK : ∀ σ : E ≃ₐ[fixedN N] E,
      (⟨σ.restrictScalars F, hmemH σ⟩ : H) ∈ ((resN N).rangeRestrict).ker := by
    intro σ
    rw [hker]
    have : σ.restrictScalars F ∈ (fixedN N).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      exact σ.commutes ⟨x, hx⟩
    rw [fixingSubgroup_fixedField] at this
    obtain ⟨n, hn, e⟩ := this
    have : n = ⟨σ.restrictScalars F, hmemH σ⟩ := Subtype.ext e
    rwa [← this]
  let κ : (E ≃ₐ[fixedN N] E) → ((resN N).rangeRestrict).ker := fun σ => ⟨_, hmemK σ⟩
  have hκ_mul : ∀ σ τ, κ (σ * τ) = κ σ * κ τ := fun _ _ => rfl
  have hκ_smul : ∀ σ (u : Eˣ), κ σ • u = σ • u := fun _ _ => rfl
  have hκ_surj : ∀ k, ∃ σ, κ σ = k := by
    rintro ⟨k, hk⟩
    rw [hker] at hk
    have hfix : ∀ x : fixedN N, (k : E ≃ₐ[F] E) x = x := fun x => x.2 ⟨k, ⟨k, hk, rfl⟩⟩
    exact ⟨{ (k : E ≃ₐ[F] E).toRingEquiv with commutes' := hfix }, rfl⟩
  obtain ⟨m, hm⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units (fun σ => c (κ σ))
    (fun σ τ => by simp only []; rw [hκ_mul, hc, hκ_smul])
  refine ⟨m, fun k => ?_⟩
  obtain ⟨σ, rfl⟩ := hκ_surj k
  rw [hκ_smul]
  exact hm σ

theorem ker_rangeRestrict_resN : ((resN N).rangeRestrict).ker = N := by
  ext k
  rw [MonoidHom.ker_rangeRestrict, mem_ker_resN_iff]

/-- `ker(H → Aut(E^N)) ≃* N ≤ Aut(E/F)`. -/
noncomputable def kerEquivNormalAut : ((resN N).rangeRestrict).ker ≃* normalAut N :=
  (MulEquiv.subgroupCongr (ker_rangeRestrict_resN N)).trans
    (N.equivMapOfInjective H.subtype H.subtype_injective)

theorem card_eq_card_quotAut_mul :
    Nat.card H = Nat.card (quotAut N) * Nat.card (normalAut N) := by
  have hk : (resN N).ker = N := by ext k; exact mem_ker_resN_iff N k
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (resN N).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (resN N)).toEquiv, hk,
    Nat.card_congr (N.equivMapOfInjective H.subtype H.subtype_injective).toEquiv]

set_option synthInstance.maxHeartbeats 200000 in
-- The action of `quotAut N` on `(E^N)ˣ` is slow to synthesize.
/-- **The normal step**: `|H²(H, Eˣ)| ≤ |H²(H/N, (E^N)ˣ)| · |H²(N, Eˣ)|`. -/
theorem card_contH2_le_of_normal
    (hQ : Nat.card (ContH2 (quotAut N) (fixedN N)ˣ) ≠ 0 ∧
      Nat.card (ContH2 (quotAut N) (fixedN N)ˣ) ≤ Nat.card (quotAut N))
    (hK : Nat.card (ContH2 (normalAut N) Eˣ) ≠ 0 ∧
      Nat.card (ContH2 (normalAut N) Eˣ) ≤ Nat.card (normalAut N)) :
    Nat.card (ContH2 H Eˣ) ≠ 0 ∧ Nat.card (ContH2 H Eˣ) ≤ Nat.card H := by
  set φ := (resN N).rangeRestrict
  have hφ : Continuous φ := continuous_of_discreteTopology
  let ψ : (fixedN N)ˣ →* Eˣ := Units.map ((fixedN N).val : fixedN N →* E)
  have hψ : Function.Injective ψ := Units.map_injective (fixedN N).val.injective
  let i := ContH2.map φ hφ ψ (units_map_val_resN_smul N)
  let r := ContH2.map φ.ker.subtype continuous_of_discreteTopology (MonoidHom.id Eˣ)
    (fun _ _ => rfl)
  have hfix : ∀ m : Eˣ, (∀ n ∈ φ.ker, n • m = m) → m ∈ ψ.range := by
    intro m hm
    have hmF : (m : E) ∈ fixedN N := by
      rintro ⟨n, hn⟩
      obtain ⟨n₀, hn₀, rfl⟩ := hn
      have := hm n₀ (by rw [ker_rangeRestrict_resN]; exact hn₀)
      exact congrArg Units.val this
    refine ⟨Units.mk0 ⟨m, hmF⟩ (by simp [Subtype.ext_iff]), ?_⟩
    ext
    rfl
  have hi : Function.Injective i :=
    ContH2.map_injective φ hφ (resN N).rangeRestrict_surjective ψ hψ _ hfix
      (fun _ => IsLocallyConstant.of_discrete _) (fun c _ hc => isMulCoboundary₁_ker_resN N c hc)
  have hex : r.ker ≤ i.range := by
    intro α hα
    induction α using ContH2.induction_on with | h f => ?_
    rw [MonoidHom.mem_ker] at hα
    obtain ⟨x, hx, hxf⟩ := (mk_eq_one_iff _).1 hα
    obtain ⟨β, hβ⟩ := exists_map_eq_of_res φ hφ (resN N).rangeRestrict_surjective ψ hψ _ hfix
      (fun _ => IsLocallyConstant.of_discrete _) (fun c _ hc => isMulCoboundary₁_ker_resN N c hc)
      f x hx (fun n n' => (congrFun hxf (n, n')).symm)
    exact ⟨β, hβ⟩
  have hKcard : Nat.card (ContH2 φ.ker Eˣ) = Nat.card (ContH2 (normalAut N) Eˣ) :=
    card_mapEquiv (kerEquivNormalAut N) continuous_of_discreteTopology
      continuous_of_discreteTopology (fun _ _ => rfl)
  haveI : Finite (ContH2 (quotAut N) (fixedN N)ˣ) := Nat.finite_of_card_ne_zero hQ.1
  haveI : Finite (ContH2 φ.ker Eˣ) := Nat.finite_of_card_ne_zero (hKcard ▸ hK.1)
  obtain ⟨h0, hle⟩ := card_le_of_exact i r hi hex
  refine ⟨h0, hle.trans ?_⟩
  rw [hKcard]
  rw [card_eq_card_quotAut_mul N]
  exact Nat.mul_le_mul hQ.2 hK.2

end NormalStep

universe u v in
theorem card_contH2_le_aux (n : ℕ) :
    ∀ {F : Type v} {E : Type u} [Field F] [Field E] [Algebra ℚ_[p] F] [Algebra ℚ_[p] E]
      [Algebra F E] [IsScalarTower ℚ_[p] F E] [FiniteDimensional ℚ_[p] F]
      [FiniteDimensional ℚ_[p] E] (H : Subgroup (E ≃ₐ[F] E)), Nat.card H = n →
      Nat.card (ContH2 H Eˣ) ≠ 0 ∧ Nat.card (ContH2 H Eˣ) ≤ Nat.card H := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F E _ _ _ _ _ _ _ _ H hn
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ_[p] F E
  have hH0 : Nat.card H ≠ 0 := Nat.card_pos.ne'
  by_cases hc : IsCyclic H
  · rw [card_contH2_of_isCyclic (p := p)]
    exact ⟨hH0, le_rfl⟩
  have hnt : Nontrivial H := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hc isCyclic_of_subsingleton
  obtain ⟨N, hNn, hNb, hNt⟩ := (isCyclic_or_exists_normal p H).resolve_left hc
  have hcard := card_eq_card_quotAut_mul N
  have hN1 : 1 < Nat.card (normalAut N) := by
    rw [← Nat.card_congr (N.equivMapOfInjective H.subtype H.subtype_injective).toEquiv]
    exact (Subgroup.one_lt_card_iff_ne_bot N).2 hNb
  have hNlt : Nat.card (normalAut N) < Nat.card H := by
    rw [← Nat.card_congr (N.equivMapOfInjective H.subtype H.subtype_injective).toEquiv]
    exact lt_of_le_of_ne (Subgroup.card_le_card_group N)
      (fun h => hNt ((Subgroup.card_eq_iff_eq_top N).1 h))
  have hQlt : Nat.card (quotAut N) < Nat.card H := by
    rw [hcard]
    have hQ0 : 0 < Nat.card (quotAut N) := Nat.card_pos
    exact lt_mul_of_one_lt_right hQ0 hN1
  exact card_contH2_le_of_normal N (ih _ (hn ▸ hQlt) (quotAut N) rfl)
    (ih _ (hn ▸ hNlt) (normalAut N) rfl)

/-- **`|H²(H, Eˣ)| ≤ |H|`** for every group `H` of automorphisms of a finite extension of local
fields (and `H²(H, Eˣ)` is finite). -/
theorem card_contH2_le {F E : Type*} [Field F] [Field E] [Algebra ℚ_[p] F] [Algebra ℚ_[p] E]
    [Algebra F E] [IsScalarTower ℚ_[p] F E] [FiniteDimensional ℚ_[p] F]
    [FiniteDimensional ℚ_[p] E] (H : Subgroup (E ≃ₐ[F] E)) :
    Nat.card (ContH2 H Eˣ) ≠ 0 ∧ Nat.card (ContH2 H Eˣ) ≤ Nat.card H :=
  card_contH2_le_aux (p := p) _ H rfl

/-- **`|Br(L/K)| ≤ [L : K]`** for a finite Galois extension of local fields. -/
theorem card_relBr_le {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
    [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
    [FiniteDimensional ℚ_[p] L] [FiniteDimensional K L] [IsGalois K L] :
    Nat.card (Brauer.RelBr K L) ≠ 0 ∧ Nat.card (Brauer.RelBr K L) ≤ Module.finrank K L := by
  have h := card_contH2_le (p := p) (⊤ : Subgroup (L ≃ₐ[K] L))
  rw [card_mapEquiv (G := L ≃ₐ[K] L) Subgroup.topEquiv continuous_of_discreteTopology
    continuous_of_discreteTopology (fun _ _ => rfl), Nat.card_congr Subgroup.topEquiv.toEquiv,
    IsGalois.card_aut_eq_finrank] at h
  exact h

end PadicField
