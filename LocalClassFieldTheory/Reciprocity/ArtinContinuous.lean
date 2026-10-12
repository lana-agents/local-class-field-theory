/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.Artin
import LocalClassFieldTheory.PadicField.Powers

/-!
# Continuity of the Artin map

* `PadicField.mem_normGroup_of_nrm_sub_one_lt`: norm groups of finite extensions contain a
  neighbourhood `{u | ‖u - 1‖ < ‖n² p‖}` of `1` (`n = [L : K]`), since they contain all `n`-th
  powers; in particular they are open.
* `PadicField.unitsTopology`: the topology on `Kˣ` induced by the absolute value.
* `PadicField.continuous_artin`: the Artin map `Kˣ → Gal(K^ab/K)` is continuous for the Krull
  topology.
-/

set_option linter.unusedSectionVars false

open IntermediateField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

section Open

variable {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]

include hp in
/-- **Norm groups are open**: they contain `{u | ‖u - 1‖ < ‖n² p‖}`, `n = [L : K]`. -/
theorem mem_normGroup_of_nrm_sub_one_lt (u : Kˣ)
    (hu : nrm p K ((u : K) - 1) <
      nrm p K ((Module.finrank K L * (Module.finrank K L * p) : ℕ) : K)) :
    u ∈ normGroup K L := by
  obtain ⟨x, hx⟩ := exists_pow_eq_of_nrm_sub_one_lt (p := p) _ Module.finrank_pos (u : K) hu
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [zero_pow Module.finrank_pos.ne'] at hx; exact u.ne_zero hx.symm
  refine (mem_normGroup_iff).2 ⟨Units.mk0 (algebraMap K L x) ((map_ne_zero _).2 hx0), ?_⟩
  rw [Units.val_mk0, Algebra.norm_algebraMap, hx]

end Open

variable (p K) in
/-- The topology on `Kˣ` induced by the absolute value of `K`. -/
@[reducible] noncomputable def unitsTopology : TopologicalSpace Kˣ :=
  letI : NormedField K := spectralNorm.normedField ℚ_[p] K
  inferInstance

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

/-- A finite subextension of `K^ab / K` lies in a finite abelian `L ⊆ Ω`. -/
theorem exists_abFin_le (E : IntermediateField K (maxAbelian K Ω)) [FiniteDimensional K E] :
    ∃ L : AbFin K Ω, ∀ x ∈ E, ((x : maxAbelian K Ω) : Ω) ∈ L.1 := by
  classical
  let b := Module.finBasis K E
  have h : ∀ i, ∃ L : AbFin K Ω, (((b i : E) : maxAbelian K Ω) : Ω) ∈ L.1 :=
    fun i ↦ mem_maxAbelian_iff.1 (b i : maxAbelian K Ω).2
  choose Li hLi using h
  obtain ⟨L, hL⟩ := directed_abFin.finset_le (Finset.univ.image Li)
  refine ⟨L, ?_⟩
  let ψ : E →ₗ[K] Ω := (maxAbelian K Ω).val.toLinearMap.comp E.val.toLinearMap
  have hspan : (⊤ : Submodule K E) ≤ L.1.toSubalgebra.toSubmodule.comap ψ := by
    rw [← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hL (Li i) (Finset.mem_image_of_mem _ (Finset.mem_univ i)) (hLi i)
  intro x hx
  exact hspan (Submodule.mem_top (x := ⟨x, hx⟩))

/-- **Continuity of the Artin map** for the topology of `Kˣ` given by the absolute value and the
Krull topology on `Gal(K^ab/K)`. -/
theorem continuous_artin :
    @Continuous _ _ (unitsTopology p K) _ (artin p K Ω) := by
  letI : NormedField K := spectralNorm.normedField ℚ_[p] K
  change Continuous (artin p K Ω)
  refine continuous_of_continuousAt_one _ ?_
  intro s hs
  rw [map_one] at hs
  obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff K _ _).1 hs
  obtain ⟨L, hL⟩ := exists_abFin_le E
  set n := Module.finrank K L.1
  set r := nrm p K ((n * (n * p) : ℕ) : K)
  have hr : 0 < r := by
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
    exact nrm_pos_iff.2 (Nat.cast_ne_zero.2
      (Nat.mul_pos Module.finrank_pos (Nat.mul_pos Module.finrank_pos hp.out.pos)).ne')
  have hopen : IsOpen ((Units.val : Kˣ → K) ⁻¹' Metric.ball 1 r) :=
    Units.continuous_val.isOpen_preimage _ Metric.isOpen_ball
  have h1 : (1 : Kˣ) ∈ (Units.val ⁻¹' Metric.ball (1 : K) r) := by simpa using hr
  refine Filter.mem_map.2 (Filter.mem_of_superset (hopen.mem_nhds h1) fun u hu ↦ ?_)
  have hu' : nrm p K ((u : K) - 1) < r := by
    have h := hu
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at h
    exact h
  have hN : u ∈ normGroup K L.1 := mem_normGroup_of_nrm_sub_one_lt u hu'
  show artin p K Ω u ∈ s
  apply hEs
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  exact (artin_apply_eq_self_iff (p := p) u L.1).2 hN y (hL y hy)

end PadicField
