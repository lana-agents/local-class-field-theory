/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.ArtinUnique

/-!
# Independence of the algebraic closure

Let `σ : Ω ≃ₐ[K] Ω'` be a `K`-isomorphism of algebraically closed fields. It maps finite abelian
subextensions to finite abelian subextensions, hence restricts to `K^ab_Ω ≃ₐ[K] K^ab_Ω'`
(`PadicField.maxAbelianEquiv`) and induces `Gal(K^ab_Ω/K) ≃* Gal(K^ab_Ω'/K)`, `g ↦ σ g σ⁻¹`
(`PadicField.galMaxAbelianEquiv`). The Artin maps correspond:

* **`PadicField.galMaxAbelianEquiv_artin`**: `σ ∘ artin_Ω(x) ∘ σ⁻¹ = artin_Ω'(x)`;
* `PadicField.abRec_map`: for finite abelian `L ⊆ Ω`, `abRec_{σ L}(x) = σ abRec_L(x) σ⁻¹`.

Proof: the transported map satisfies the characterising properties of `artin_Ω'`
(`PadicField.eq_artin_of_forall`), since `σ` commutes with `y ↦ y ^ q` and preserves norm groups.
-/

set_option linter.unusedSectionVars false

open IntermediateField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]
variable {Ω' : Type*} [Field Ω'] [Algebra K Ω'] [Algebra ℚ_[p] Ω'] [IsScalarTower ℚ_[p] K Ω']
  [IsAlgClosed Ω']

section Map

variable {Ω₁ Ω₂ : Type*} [Field Ω₁] [Algebra K Ω₁] [Field Ω₂] [Algebra K Ω₂]

/-- The image of a finite abelian subextension under a `K`-isomorphism. -/
noncomputable def AbFin.map (σ : Ω₁ ≃ₐ[K] Ω₂) (L : AbFin K Ω₁) : AbFin K Ω₂ :=
  ⟨L.1.map σ.toAlgHom,
    LinearEquiv.finiteDimensional (equivMap L.1 σ.toAlgHom).toLinearEquiv,
    .of_algHom (equivMap L.1 σ.toAlgHom).symm.toAlgHom⟩

theorem AbFin.mem_map (σ : Ω₁ ≃ₐ[K] Ω₂) (L : AbFin K Ω₁) {y : Ω₁} (hy : y ∈ L.1) :
    σ y ∈ (L.map σ).1 :=
  (IntermediateField.mem_map _).2 ⟨y, hy, rfl⟩

theorem map_mem_maxAbelian (σ : Ω₁ ≃ₐ[K] Ω₂) {y : Ω₁} (hy : y ∈ maxAbelian K Ω₁) :
    σ y ∈ maxAbelian K Ω₂ := by
  obtain ⟨L, hyL⟩ := mem_maxAbelian_iff.1 hy
  exact le_maxAbelian (L.map σ) (L.mem_map σ hyL)

variable (K) in
/-- A `K`-isomorphism `Ω₁ ≃ Ω₂` restricts to `K^ab_{Ω₁} ≃ K^ab_{Ω₂}`. -/
noncomputable def maxAbelianEquiv (σ : Ω₁ ≃ₐ[K] Ω₂) : maxAbelian K Ω₁ ≃ₐ[K] maxAbelian K Ω₂ where
  toFun y := ⟨σ (y : Ω₁), map_mem_maxAbelian σ y.2⟩
  invFun y := ⟨σ.symm (y : Ω₂), map_mem_maxAbelian σ.symm y.2⟩
  left_inv y := Subtype.ext (σ.symm_apply_apply (y : Ω₁))
  right_inv y := Subtype.ext (σ.apply_symm_apply (y : Ω₂))
  map_mul' x y := Subtype.ext (map_mul σ (x : Ω₁) y)
  map_add' x y := Subtype.ext (map_add σ (x : Ω₁) y)
  commutes' c := Subtype.ext (σ.commutes c)

theorem maxAbelianEquiv_apply (σ : Ω₁ ≃ₐ[K] Ω₂) (y : maxAbelian K Ω₁) :
    (maxAbelianEquiv K σ y : Ω₂) = σ (y : Ω₁) := rfl

theorem maxAbelianEquiv_symm_apply (σ : Ω₁ ≃ₐ[K] Ω₂) (y : maxAbelian K Ω₂) :
    ((maxAbelianEquiv K σ).symm y : Ω₁) = σ.symm (y : Ω₂) := rfl

variable (K) in
/-- The isomorphism `Gal(K^ab_{Ω₁}/K) ≃* Gal(K^ab_{Ω₂}/K)`, `g ↦ σ g σ⁻¹`. -/
noncomputable def galMaxAbelianEquiv (σ : Ω₁ ≃ₐ[K] Ω₂) :
    (maxAbelian K Ω₁ ≃ₐ[K] maxAbelian K Ω₁) ≃* (maxAbelian K Ω₂ ≃ₐ[K] maxAbelian K Ω₂) :=
  AlgEquiv.autCongr (maxAbelianEquiv K σ)

theorem galMaxAbelianEquiv_apply (σ : Ω₁ ≃ₐ[K] Ω₂) (g : maxAbelian K Ω₁ ≃ₐ[K] maxAbelian K Ω₁)
    (y : maxAbelian K Ω₂) :
    (galMaxAbelianEquiv K σ g y : Ω₂) = σ (g ((maxAbelianEquiv K σ).symm y)) := rfl

end Map

include hp in
/-- **Independence of `Ω`**: under a `K`-isomorphism `σ : Ω ≃ Ω'`, the Artin maps correspond,
`σ ∘ artin_Ω(x) ∘ σ⁻¹ = artin_Ω'(x)`. -/
theorem galMaxAbelianEquiv_artin (σ : Ω ≃ₐ[K] Ω') (x : Kˣ) :
    galMaxAbelianEquiv K σ (artin p K Ω x) = artin p K Ω' x := by
  have h := eq_artin_of_forall (p := p) (Ω := Ω')
    ((galMaxAbelianEquiv K σ).toMonoidHom.comp (artin p K Ω)) ?_ ?_
  · exact DFunLike.congr_fun h x
  · intro x hx n hn y hy
    have hy' : (σ.symm y) ^ q p K ^ n = σ.symm y := by rw [← map_pow, hy]
    change σ (artin p K Ω x ⟨σ.symm y, _⟩ : Ω) = _
    rw [artin_apply_of_pow_eq x hx hn _ hy', map_pow, AlgEquiv.apply_symm_apply]
  · intro L x hx y hy
    apply Subtype.ext
    change σ (artin p K Ω x ((maxAbelianEquiv K σ).symm y) : Ω) = y
    have hN : x ∈ normGroup K (L.map σ.symm).1 :=
      let φ : (L.map σ.symm).1 →ₐ[K] L.1 := (equivMap L.1 σ.symm.toAlgHom).symm.toAlgHom
      normGroup_le_of_algHom φ hx
    rw [artin_apply_of_mem_normGroup (p := p) (L.map σ.symm) x hN _ (L.mem_map σ.symm hy),
      maxAbelianEquiv_symm_apply, AlgEquiv.apply_symm_apply]

include hp in
/-- Independence of `Ω` at finite level: for finite abelian `L ⊆ Ω`,
`abRec_{σ L}(x) = σ abRec_L(x) σ⁻¹`. -/
theorem abRec_map (σ : Ω ≃ₐ[K] Ω') (L : AbFin K Ω) (x : Kˣ) :
    abRec p (L.map σ).1 x = AlgEquiv.autCongr (equivMap L.1 σ.toAlgHom) (abRec p L.1 x) := by
  ext ⟨y, hy⟩
  obtain ⟨z, hz, rfl⟩ := (IntermediateField.mem_map _).1 hy
  have h1 := artin_apply (p := p) x (L.map σ).1 _ hy
  rw [← galMaxAbelianEquiv_artin (p := p) σ x, galMaxAbelianEquiv_apply] at h1
  rw [← h1]
  have h2 := artin_apply (p := p) (Ω := Ω) x L.1 z hz
  have h3 : (maxAbelianEquiv K σ).symm ⟨σ.toAlgHom z, le_maxAbelian (L.map σ) hy⟩ =
      ⟨z, le_maxAbelian L hz⟩ :=
    Subtype.ext (σ.symm_apply_apply z)
  rw [h3, h2]
  have h4 : (equivMap L.1 σ.toAlgHom).symm ⟨σ.toAlgHom z, hy⟩ = ⟨z, hz⟩ :=
    (AlgEquiv.symm_apply_eq _).2 rfl
  rw [AlgEquiv.autCongr_apply]
  change _ = ((equivMap L.1 σ.toAlgHom)
    (abRec p L.1 x ((equivMap L.1 σ.toAlgHom).symm ⟨σ.toAlgHom z, hy⟩)) : Ω')
  rw [h4]
  rfl

end PadicField
