/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.Uniformizer

/-!
# Rings of integers in an extension of finite extensions of `ℚ_[p]`

Let `L/K` be an extension of fields finite over `ℚ_[p]` (with compatible `ℚ_[p]`-structures).
We construct the algebra `𝒪 p K → 𝒪 p L` and show:

* `𝒪 p L` is the integral closure of `𝒪 p K` in `L` (`IsIntegralClosure`), hence a finite
  `𝒪 p K`-module;
* the algebra map is local, and the maximal ideal of `𝒪 p L` lies over that of `𝒪 p K`;
* `K`-automorphisms of `L` preserve the absolute value and act on `𝒪 p L`.
-/

open Polynomial

namespace PadicField

variable (p : ℕ) [hp : Fact p.Prime]

theorem charZero (K : Type*) [Field K] [Algebra ℚ_[p] K] : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective

variable {p}
variable (K L : Type*) [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L]

section Algebraic

variable [Algebra.IsAlgebraic ℚ_[p] K] [Algebra.IsAlgebraic ℚ_[p] L]

namespace Integers

/-- The ring homomorphism `𝒪 p K →+* 𝒪 p L` induced by `K → L`. -/
noncomputable def mapTower : 𝒪 p K →+* 𝒪 p L where
  toFun x := mk (algebraMap K L x) (by rw [nrm_algebraMap_tower]; exact nrm_coe_le_one x)
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := by ext; simp

noncomputable instance : Algebra (𝒪 p K) (𝒪 p L) := (mapTower K L).toAlgebra

variable {K L}

@[simp]
theorem coe_algebraMap (x : 𝒪 p K) :
    ((algebraMap (𝒪 p K) (𝒪 p L) x : 𝒪 p L) : L) = algebraMap K L (x : K) := rfl

instance : IsScalarTower (𝒪 p K) (𝒪 p L) L := .of_algebraMap_eq' rfl

instance : FaithfulSMul (𝒪 p K) (𝒪 p L) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y h
  have := congrArg (fun z : 𝒪 p L ↦ (z : L)) h
  simp only [coe_algebraMap] at this
  exact ext ((algebraMap K L).injective this)

variable (K L) in
/-- `𝒪 p L` is the integral closure of `𝒪 p K` in `L`. -/
instance isIntegralClosure : IsIntegralClosure (𝒪 p L) (𝒪 p K) L where
  algebraMap_injective := coe_injective
  isIntegral_iff {x} := by
    constructor
    · rintro ⟨f, hf, hroot⟩
      refine ⟨mk x ?_, rfl⟩
      refine nrm_le_one_of_monic_root (f.map (algebraMap (𝒪 p K) L)) (hf.map _) ?_ fun i ↦ ?_
      · rw [aeval_def, eval₂_map, Algebra.algebraMap_self, RingHom.id_comp]; exact hroot
      · rw [coeff_map, IsScalarTower.algebraMap_apply (𝒪 p K) K L, nrm_algebraMap_tower]
        exact nrm_coe_le_one _
    · rintro ⟨y, rfl⟩
      set x : L := (y : L)
      have hx : nrm p L x ≤ 1 := nrm_coe_le_one y
      have hcoeff := (nrm_le_one_iff_coeff x).1 hx
      set P : L[X] := (minpoly ℚ_[p] x).map (algebraMap ℚ_[p] L)
      have hlift : P ∈ lifts (algebraMap (𝒪 p K) L) := by
        rw [lifts_iff_coeff_lifts]
        intro n
        refine ⟨mk (algebraMap ℚ_[p] K ((minpoly ℚ_[p] x).coeff n)) ?_, ?_⟩
        · rw [nrm_algebraMap]; exact hcoeff n
        · simp only [P, coeff_map, IsScalarTower.algebraMap_apply (𝒪 p K) K L]
          exact (IsScalarTower.algebraMap_apply ℚ_[p] K L _).symm
      have hmonic : P.Monic := (minpoly.monic (Algebra.IsIntegral.isIntegral x)).map _
      obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift hmonic
      refine ⟨q, hqm, ?_⟩
      rw [eval₂_eq_eval_map, hq, eval_map, ← aeval_def, minpoly.aeval]

end Integers

omit [Algebra.IsAlgebraic ℚ_[p] K] in
/-- `K`-automorphisms of `L` preserve the absolute value. -/
theorem nrm_algEquiv_tower (σ : L ≃ₐ[K] L) (x : L) : nrm p L (σ x) = nrm p L x :=
  nrm_map ((σ.restrictScalars ℚ_[p]).toAlgHom) x

omit [Algebra.IsAlgebraic ℚ_[p] K] in
/-- `K`-algebra maps between extensions preserve the absolute value. -/
theorem nrm_algHom_tower {M : Type*} [Field M] [Algebra ℚ_[p] M] [Algebra.IsAlgebraic ℚ_[p] M]
    [Algebra K M] [IsScalarTower ℚ_[p] K M] (σ : L →ₐ[K] M) (x : L) :
    nrm p M (σ x) = nrm p L x :=
  nrm_map (σ.restrictScalars ℚ_[p]) x

namespace Integers

/-- The action of `Gal(L/K)` on `𝒪 p L`. -/
noncomputable instance : MulSemiringAction (L ≃ₐ[K] L) (𝒪 p L) where
  smul σ x := mk (σ (x : L)) (by rw [nrm_algEquiv_tower]; exact nrm_coe_le_one x)
  one_smul x := by ext; rfl
  mul_smul σ τ x := by ext; rfl
  smul_zero σ := by ext; change σ 0 = 0; simp
  smul_add σ x y := by ext; change σ (x + y : L) = σ x + σ y; simp
  smul_one σ := by ext; change σ 1 = 1; simp
  smul_mul σ x y := by ext; change σ (x * y : L) = σ x * σ y; simp

variable {K L}

omit [Algebra.IsAlgebraic ℚ_[p] K] in
@[simp]
theorem coe_smul (σ : L ≃ₐ[K] L) (x : 𝒪 p L) : ((σ • x : 𝒪 p L) : L) = σ (x : L) := rfl

instance : SMulCommClass (L ≃ₐ[K] L) (𝒪 p K) (𝒪 p L) where
  smul_comm σ a x := by
    ext
    change σ (algebraMap K L (a : K) * (x : L)) = algebraMap K L (a : K) * σ (x : L)
    simp

theorem algebraMap_mem_maximalIdeal_iff {x : 𝒪 p K} :
    algebraMap (𝒪 p K) (𝒪 p L) x ∈ IsLocalRing.maximalIdeal (𝒪 p L) ↔
      x ∈ IsLocalRing.maximalIdeal (𝒪 p K) := by
  rw [mem_maximalIdeal_iff, mem_maximalIdeal_iff, coe_algebraMap, nrm_algebraMap_tower]

instance : IsLocalHom (algebraMap (𝒪 p K) (𝒪 p L)) where
  map_nonunit x hx := by
    rw [isUnit_iff_nrm_eq_one] at hx ⊢
    rwa [coe_algebraMap, nrm_algebraMap_tower] at hx

theorem comap_maximalIdeal :
    (IsLocalRing.maximalIdeal (𝒪 p L)).comap (algebraMap (𝒪 p K) (𝒪 p L)) =
      IsLocalRing.maximalIdeal (𝒪 p K) := by
  ext x; simp only [Ideal.mem_comap, algebraMap_mem_maximalIdeal_iff]

instance : (IsLocalRing.maximalIdeal (𝒪 p L)).LiesOver (IsLocalRing.maximalIdeal (𝒪 p K)) :=
  ⟨comap_maximalIdeal.symm⟩

end Integers

end Algebraic

section Finite

variable [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] L]

omit [FiniteDimensional ℚ_[p] K] in
include p in
theorem finiteDimensional_tower : FiniteDimensional K L :=
  FiniteDimensional.right ℚ_[p] K L

namespace Integers

/-- `𝒪 p L` is a finite `𝒪 p K`-module. -/
instance moduleFinite : Module.Finite (𝒪 p K) (𝒪 p L) := by
  haveI := finiteDimensional_tower (p := p) K L
  haveI := charZero p K
  exact IsIntegralClosure.finite (𝒪 p K) K L (𝒪 p L)

theorem maximalIdeal_ne_bot : IsLocalRing.maximalIdeal (𝒪 p K) ≠ ⊥ :=
  IsDiscreteValuationRing.not_a_field _

end Integers

end Finite

end PadicField
