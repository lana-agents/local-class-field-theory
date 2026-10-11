/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.Extension

/-!
# Residue fields, ramification index and inertia degree

For a field `K` finite over `ℚ_[p]` the residue field `𝓴 p K` of `𝒪 p K` is finite; its cardinality
is `q p K`. For an extension `L/K` we define the ramification index `e p K L` (the valuation in `L`
of a uniformiser of `K`) and the inertia degree `f p K L = [𝓴 p L : 𝓴 p K]`, and prove the
fundamental identity `e * f = [L : K]` (`PadicField.e_mul_f`), together with
`v_L (x) = e * v_K (x)` for `x ∈ K` (`PadicField.v_algebraMap`).
-/

open Polynomial IsLocalRing

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]

section Residue

variable (p) (K : Type*) [Field K] [Algebra ℚ_[p] K] [Algebra.IsAlgebraic ℚ_[p] K]

/-- The residue field of `K`. -/
abbrev Residue : Type _ := ResidueField (𝒪 p K)

@[inherit_doc] scoped notation "𝓴" => PadicField.Residue

/-- The unit ball of `ℚ_[p]` is `ℤ_[p]`. -/
noncomputable def integersQpEquiv : 𝒪 p ℚ_[p] ≃+* ℤ_[p] where
  toFun x := ⟨(x : ℚ_[p]), by
    have := Integers.nrm_coe_le_one x
    rwa [show ((x : ℚ_[p])) = algebraMap ℚ_[p] ℚ_[p] (x : ℚ_[p]) from rfl, nrm_algebraMap] at this⟩
  invFun y := Integers.mk (y : ℚ_[p]) (by
    rw [show ((y : ℚ_[p])) = algebraMap ℚ_[p] ℚ_[p] (y : ℚ_[p]) from rfl, nrm_algebraMap]
    exact y.2)
  left_inv x := rfl
  right_inv y := rfl
  map_mul' x y := rfl
  map_add' x y := rfl

instance finite_residue_Qp : Finite (𝓴 p ℚ_[p]) :=
  Finite.of_equiv _ ((ResidueField.mapEquiv (integersQpEquiv p)).trans
    (PadicInt.residueField (p := p))).symm.toEquiv

variable [FiniteDimensional ℚ_[p] K]

instance finite_residue : Finite (𝓴 p K) :=
  ResidueField.finite_of_finite (R := 𝒪 p ℚ_[p]) (finite_residue_Qp p)

/-- The cardinality of the residue field. -/
noncomputable def q : ℕ := Nat.card (𝓴 p K)

theorem one_lt_q : 1 < q p K := Finite.one_lt_card

end Residue

section Ramification

variable (p) (K L : Type*) [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L]

/-- The ramification index of `L/K`: the valuation in `L` of a uniformiser of `K`. -/
noncomputable def e : ℕ := (v p (algebraMap K L (uniformizer p K))).toNat

/-- The inertia degree `[𝓴 p L : 𝓴 p K]`. -/
noncomputable def f : ℕ := Module.finrank (𝓴 p K) (𝓴 p L)

variable {p K L}

theorem v_algebraMap_uniformizer :
    v p (algebraMap K L (uniformizer p K)) = e p K L := by
  have hπ := uniformizer_spec (p := p) (K := K)
  have h0 : algebraMap K L (uniformizer p K) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).2 hπ.ne_zero
  have : 0 < v p (algebraMap K L (uniformizer p K)) := by
    rw [← nrm_lt_one_iff_v_pos h0, nrm_algebraMap_tower]; exact hπ.nrm_lt_one
  rw [e, Int.toNat_of_nonneg this.le]

theorem e_pos : 0 < e p K L := by
  have hπ := uniformizer_spec (p := p) (K := K)
  have h0 : algebraMap K L (uniformizer p K) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).2 hπ.ne_zero
  have : 0 < v p (algebraMap K L (uniformizer p K)) := by
    rw [← nrm_lt_one_iff_v_pos h0, nrm_algebraMap_tower]; exact hπ.nrm_lt_one
  rw [v_algebraMap_uniformizer] at this
  exact_mod_cast this

/-- `v_L (x) = e(L/K) * v_K (x)` for `x ∈ K`. -/
theorem v_algebraMap (x : K) : v p (algebraMap K L x) = e p K L * v p x := by
  by_cases hx : x = 0
  · simp [hx, v, wval]
  have hπ := uniformizer_spec (p := p) (K := K)
  obtain ⟨u, hu, hxu⟩ := eq_zpow_mul_unit hπ hx
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hπ0 : algebraMap K L (uniformizer p K) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).2 hπ.ne_zero
  have hu0' : algebraMap K L u ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).2 hu0
  have hvu : v p (algebraMap K L u) = 0 := by
    rw [← nrm_eq_one_iff_v_eq_zero hu0', nrm_algebraMap_tower, hu]
  conv_lhs => rw [hxu, map_mul, map_zpow₀]
  rw [v_mul (zpow_ne_zero _ hπ0) hu0', v_zpow hπ0, hvu, v_algebraMap_uniformizer]
  ring

namespace Integers

theorem map_maximalIdeal :
    (maximalIdeal (𝒪 p K)).map (algebraMap (𝒪 p K) (𝒪 p L)) =
      Ideal.span {algebraMap (𝒪 p K) (𝒪 p L) (ϖ p K)} := by
  rw [maximalIdeal_eq_span, Ideal.map_span, Set.image_singleton]

theorem map_maximalIdeal_le_iff (n : ℕ) :
    (maximalIdeal (𝒪 p K)).map (algebraMap (𝒪 p K) (𝒪 p L)) ≤ maximalIdeal (𝒪 p L) ^ n ↔
      n ≤ e p K L := by
  rw [map_maximalIdeal, Ideal.span_singleton_le_iff_mem, mem_maximalIdeal_pow_iff]
  have h0 : algebraMap (𝒪 p K) (𝒪 p L) (ϖ p K) ≠ 0 := by
    intro h
    have := congrArg (fun z : 𝒪 p L ↦ (z : L)) h
    simp only [coe_algebraMap, coe_ϖ, coe_zero, map_eq_zero] at this
    exact uniformizer_spec.ne_zero this
  simp only [h0, false_or, coe_algebraMap, coe_ϖ, v_algebraMap_uniformizer]
  exact Nat.cast_le

theorem ramificationIdx'_eq :
    Ideal.ramificationIdx' (maximalIdeal (𝒪 p K)) (maximalIdeal (𝒪 p L)) = e p K L :=
  Ideal.ramificationIdx'_spec ((map_maximalIdeal_le_iff _).2 le_rfl)
    (by rw [map_maximalIdeal_le_iff]; omega)

theorem inertiaDeg'_eq :
    Ideal.inertiaDeg' (maximalIdeal (𝒪 p K)) (maximalIdeal (𝒪 p L)) = f p K L := by
  rw [Ideal.inertiaDeg', dif_pos comap_maximalIdeal]
  rfl

end Integers

/-- The fundamental identity `e f = [L : K]`. -/
theorem e_mul_f : e p K L * f p K L = Module.finrank K L := by
  haveI := finiteDimensional_tower (p := p) K L
  have h := Ideal.sum_ramification_inertia (R := 𝒪 p K) (S := 𝒪 p L) K L
    (p := maximalIdeal (𝒪 p K)) (Integers.maximalIdeal_ne_bot (p := p) K)
  rw [IsLocalRing.primesOverFinset_eq (𝒪 p L) (Integers.maximalIdeal_ne_bot (p := p) K),
    Finset.sum_singleton, Integers.ramificationIdx'_eq, Integers.inertiaDeg'_eq] at h
  exact h

theorem f_pos : 0 < f p K L := by
  haveI := finiteDimensional_tower (p := p) K L
  exact Module.finrank_pos

end Ramification

end PadicField
