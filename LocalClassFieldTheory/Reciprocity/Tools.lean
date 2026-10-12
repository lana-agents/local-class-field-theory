/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.CyclicLevel

/-!
# Auxiliary facts on towers `K ⊆ S ⊆ T`

* `PadicField.v_eq_one_of_v_algebraMap_eq_one`: if `v_T(y) = 1` for `y ∈ S` then `v_S(y) = 1`
  and `T/S` is unramified;
* `PadicField.v_norm_eq_one_of_f_eq`: if `f(S/K) = f(T/K)`, norms of uniformisers of `T` are
  uniformisers of `S`;
* `PadicField.exists_norm_eq_of_e_eq_one`: units are norms from unramified extensions;
* `PadicField.normGroup_le_of_algHom`: norm groups are antitone along `K`-embeddings;
* `PadicField.e_eq_of_algEquiv`, `PadicField.f_eq_of_algEquiv`: invariance under
  `K`-isomorphisms.
-/

set_option linter.unusedSectionVars false

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]

section Tower

variable {K S T : Type*} [Field K] [Field S] [Field T] [Algebra ℚ_[p] K] [Algebra ℚ_[p] S]
  [Algebra ℚ_[p] T] [Algebra K S] [Algebra K T] [Algebra S T] [IsScalarTower ℚ_[p] K S]
  [IsScalarTower ℚ_[p] K T] [IsScalarTower ℚ_[p] S T] [IsScalarTower K S T]
  [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] S] [FiniteDimensional ℚ_[p] T]

include hp in
theorem v_eq_one_of_v_algebraMap_eq_one {y : S} (hy : v p (algebraMap S T y) = 1) :
    v p y = 1 ∧ e p S T = 1 := by
  rw [v_algebraMap] at hy
  have he := e_pos (p := p) (K := S) (L := T)
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hy with h | h
  · refine ⟨?_, by exact_mod_cast h⟩
    rw [h, one_mul] at hy; exact hy
  · have : (0 : ℤ) < e p S T := by exact_mod_cast he
    omega

include hp in
theorem f_eq_one_of_f_eq (hf : f p K S = f p K T) : f p S T = 1 := by
  have h := f_mul_f (p := p) (K := K) (E := S) (L := T)
  rw [← hf] at h
  exact (Nat.mul_eq_left (f_pos (p := p) (K := K) (L := S)).ne').1 h

include hp in
theorem e_eq_one_of_e_eq (he : e p K S = e p K T) : e p S T = 1 := by
  have h := e_mul_e (p := p) (K := K) (E := S) (L := T)
  rw [← he] at h
  exact (Nat.mul_eq_left (e_pos (p := p) (K := K) (L := S)).ne').1 h

include hp in
theorem v_norm_eq_one_of_f_eq (hf : f p K S = f p K T) {y : T} (hy : v p y = 1) :
    v p (Algebra.norm S y) = 1 := by
  have hy0 : y ≠ 0 := by rintro rfl; simp [v, wval] at hy
  rw [v_norm hy0, f_eq_one_of_f_eq (K := K) hf, hy]; rfl

include hp in
/-- In an unramified extension `T/S` every unit of `S` is a norm. -/
theorem exists_norm_eq_of_e_eq_one (he : e p S T = 1) (u : S) (hu : nrm p S u = 1) :
    ∃ w : Tˣ, Algebra.norm S (w : T) = u := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  obtain ⟨w, -, hw⟩ := exists_norm_eq_of_isUnramified (K := S) (L := T) he (Units.mk0 u hu0) hu
  exact ⟨w, hw⟩

include hp in
/-- Units of `S` are norms from an unramified extension `T / S`, hence their norms to `K` lie in
`N_{T/K} Tˣ`. -/
theorem mk0_norm_mem_normGroup_of_e_eq_one (he : e p S T = 1) (u : S) (hu : nrm p S u = 1)
    (hu0 : Algebra.norm K u ≠ 0) : Units.mk0 _ hu0 ∈ normGroup K T := by
  haveI := finiteDimensional_tower (p := p) K S
  haveI := finiteDimensional_tower (p := p) S T
  obtain ⟨w, hw⟩ := exists_norm_eq_of_e_eq_one (p := p) he u hu
  refine ⟨w, Units.ext ?_⟩
  change Algebra.norm K (w : T) = Algebra.norm K u
  rw [← hw, Algebra.norm_norm]

end Tower

section NormGroup

variable {K E E' : Type*} [Field K] [Field E] [Field E'] [Algebra K E] [Algebra K E']
  [FiniteDimensional K E] [FiniteDimensional K E']

theorem mem_normGroup_iff {a : Kˣ} : a ∈ normGroup K E ↔ ∃ y : Eˣ, Algebra.norm K (y : E) = a := by
  simp only [normGroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩; exact ⟨y, Units.ext hy⟩

/-- Norm groups are antitone along `K`-embeddings. -/
theorem normGroup_le_of_algHom (φ : E →ₐ[K] E') : normGroup K E' ≤ normGroup K E := by
  letI : Algebra E E' := φ.toAlgebra
  haveI : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  haveI : FiniteDimensional E E' := FiniteDimensional.right K E E'
  rw [normGroup_tower (E := E)]
  rintro _ ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

theorem norm_mem_normGroup_of_algHom (φ : E →ₐ[K] E') (y : E'ˣ) :
    Units.map (Algebra.norm K : E' →* K) y ∈ normGroup K E :=
  normGroup_le_of_algHom φ ⟨y, rfl⟩

end NormGroup

section Equiv

variable {K E E' : Type*} [Field K] [Field E] [Field E'] [Algebra ℚ_[p] K] [Algebra ℚ_[p] E]
  [Algebra ℚ_[p] E'] [Algebra K E] [Algebra K E'] [IsScalarTower ℚ_[p] K E]
  [IsScalarTower ℚ_[p] K E'] [FiniteDimensional ℚ_[p] K] [FiniteDimensional ℚ_[p] E]
  [FiniteDimensional ℚ_[p] E']

include hp in
/-- `K`-isomorphisms preserve the ramification index. -/
theorem e_eq_of_algEquiv (σ : E ≃ₐ[K] E') : e p K E = e p K E' := by
  have h1 := e_dvd_of_algHom (p := p) σ.toAlgHom
  have h2 := e_dvd_of_algHom (p := p) σ.symm.toAlgHom
  exact Nat.dvd_antisymm h1 h2

include hp in
/-- `K`-isomorphisms preserve the inertia degree. -/
theorem f_eq_of_algEquiv (σ : E ≃ₐ[K] E') : f p K E = f p K E' :=
  Nat.dvd_antisymm (f_dvd_of_algHom (p := p) σ.toAlgHom) (f_dvd_of_algHom (p := p) σ.symm.toAlgHom)

include hp in
theorem isUnramified_of_algEquiv (σ : E ≃ₐ[K] E') (h : IsUnramified p K E) :
    IsUnramified p K E' := by
  unfold IsUnramified at *
  rw [← e_eq_of_algEquiv σ, h]

end Equiv

end PadicField
