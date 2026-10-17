/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.OmegaIndependence

/-!
# Naturality of the Artin map under isomorphisms of the base field

Let `τ : K ≃ₐ[ℚ_p] K'` be an isomorphism of finite extensions of `ℚ_p` and `σ : Ω ≃+* Ω'` an
isomorphism of algebraically closed fields compatible with the embeddings,
`σ ∘ (K → Ω) = (K' → Ω') ∘ τ`. Then `σ` maps `K^ab` onto `K'^ab` (`PadicField.maxAbelianRingEquiv`)
and the Artin maps correspond (**`PadicField.artin_naturality`**):

`artin_{K'}(τ x) (σ y) = σ (artin_K(x) y)`   for `x ∈ Kˣ`, `y ∈ K^ab`,

i.e. `artin_{K'}(τ x) = σ ∘ artin_K(x) ∘ σ⁻¹`. For `K = E ⊆ Ω`, `K' = σ(E)` and `σ ∈ Aut(Ω)` this
is the Galois equivariance `artin_{σE}(σ a) = σ · artin_E(a) · σ⁻¹`.

Proof: the transported map satisfies the characterising properties of `artin_{K'}`
(`PadicField.eq_artin_of_forall`): `τ` preserves `v` and `q` (`PadicField.v_algEquiv'`,
`PadicField.q_algEquiv`), and maps norm groups to norm groups (`Algebra.norm_eq_of_equiv_equiv`);
finite abelian subextensions are transported by `σ` (`PadicField.mapField`).
-/

set_option linter.unusedSectionVars false

open IntermediateField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Invariance of `v` and `q` -/

section Invariants

variable {K K' : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  [Field K'] [Algebra ℚ_[p] K'] [FiniteDimensional ℚ_[p] K'] (τ : K ≃ₐ[ℚ_[p]] K')

theorem nrm_algEquiv' (x : K) : nrm p K' (τ x) = nrm p K x := nrm_map τ.toAlgHom x

include τ in
theorem expo_algEquiv : expo p K' = expo p K := by
  rw [expo, expo, ← LinearEquiv.finrank_eq τ.toLinearEquiv]

theorem wval_algEquiv (x : K) : wval p (τ x) = wval p x := by
  by_cases hx : x = 0
  · subst hx
    simp [wval]
  have hx' : τ x ≠ 0 := (map_ne_zero_iff _ τ.injective).2 hx
  rw [wval_eq_iff hx', nrm_algEquiv', expo_algEquiv τ, nrm_pow_expo hx]

include τ in
theorem valGen_algEquiv : valGen p K' = valGen p K := by
  classical
  unfold valGen
  congr 1
  ext k
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨x, hx, hk⟩
    refine ⟨τ.symm x, (map_ne_zero_iff _ τ.symm.injective).2 hx, ?_⟩
    rw [← wval_algEquiv τ, AlgEquiv.apply_symm_apply, hk]
  · rintro ⟨x, hx, hk⟩
    exact ⟨τ x, (map_ne_zero_iff _ τ.injective).2 hx, by rw [wval_algEquiv, hk]⟩

theorem v_algEquiv' (x : K) : v p (τ x) = v p x := by
  rw [v, v, wval_algEquiv, valGen_algEquiv τ]

/-- The isomorphism of the rings of integers induced by `τ`. -/
noncomputable def integersEquiv : 𝒪 p K ≃+* 𝒪 p K' where
  toFun x := Integers.mk (τ x) (by rw [nrm_algEquiv']; exact Integers.nrm_coe_le_one x)
  invFun y := Integers.mk (τ.symm y) (by
    rw [← nrm_algEquiv' τ, AlgEquiv.apply_symm_apply]; exact Integers.nrm_coe_le_one y)
  left_inv x := Integers.ext (by simp [Integers.coe_mk])
  right_inv y := Integers.ext (by simp [Integers.coe_mk])
  map_mul' x y := Integers.ext (by simp [Integers.coe_mk])
  map_add' x y := Integers.ext (by simp [Integers.coe_mk])

include τ in
theorem q_algEquiv : q p K' = q p K :=
  (Nat.card_congr (IsLocalRing.ResidueField.mapEquiv (integersEquiv τ)).toEquiv).symm

end Invariants

/-! ### Transport of subextensions -/

section Transport

variable {K K' : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  [Field K'] [Algebra ℚ_[p] K'] [FiniteDimensional ℚ_[p] K']
variable {Ω Ω' : Type*} [Field Ω] [Algebra K Ω] [Field Ω'] [Algebra K' Ω']
variable (τ : K ≃ₐ[ℚ_[p]] K') (σ : Ω ≃+* Ω')
  (hσ : ∀ c : K, σ (algebraMap K Ω c) = algebraMap K' Ω' (τ c))

include hσ in
theorem symm_compat (c : K') : σ.symm (algebraMap K' Ω' c) = algebraMap K Ω (τ.symm c) := by
  apply σ.injective
  rw [RingEquiv.apply_symm_apply, hσ, AlgEquiv.apply_symm_apply]

/-- The image `σ(L)` of an intermediate field, as an intermediate field over `K'`. -/
def mapField (L : IntermediateField K Ω) : IntermediateField K' Ω' :=
  { L.toSubfield.map σ.toRingHom with
    algebraMap_mem' := fun c => ⟨algebraMap K Ω (τ.symm c), L.algebraMap_mem _, by
      change σ _ = _
      rw [hσ, AlgEquiv.apply_symm_apply]⟩ }

theorem mem_mapField {L : IntermediateField K Ω} {y : Ω'} :
    y ∈ mapField τ σ hσ L ↔ ∃ x ∈ L, σ x = y := Iff.rfl

theorem map_mem_mapField {L : IntermediateField K Ω} {x : Ω} (hx : x ∈ L) :
    σ x ∈ mapField τ σ hσ L := ⟨x, hx, rfl⟩

/-- `σ : L ≃ σ(L)`. -/
def mapFieldEquiv (L : IntermediateField K Ω) : L ≃+* mapField τ σ hσ L where
  toFun x := ⟨σ (x : Ω), map_mem_mapField τ σ hσ x.2⟩
  invFun y := ⟨σ.symm y, by
    obtain ⟨x, hx, hxy⟩ := (mem_mapField τ σ hσ).1 y.2
    rw [← hxy, RingEquiv.symm_apply_apply]; exact hx⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply (x : Ω))
  right_inv y := Subtype.ext (σ.apply_symm_apply (y : Ω'))
  map_mul' x y := Subtype.ext (map_mul σ (x : Ω) y)
  map_add' x y := Subtype.ext (map_add σ (x : Ω) y)

theorem coe_mapFieldEquiv (L : IntermediateField K Ω) (x : L) :
    (mapFieldEquiv τ σ hσ L x : Ω') = σ (x : Ω) := rfl

theorem mapFieldEquiv_algebraMap (L : IntermediateField K Ω) (c : K) :
    mapFieldEquiv τ σ hσ L (algebraMap K L c) = algebraMap K' (mapField τ σ hσ L) (τ c) :=
  Subtype.ext (hσ c)

/-- Finite abelian subextensions are transported to finite abelian subextensions. -/
theorem mapField_abFin (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    FiniteDimensional K' (mapField τ σ hσ L) ∧ IsAbelianGalois K' (mapField τ σ hσ L) := by
  set M := mapField τ σ hσ L
  letI : Algebra K K' := τ.toRingEquiv.toRingHom.toAlgebra
  letI : Algebra K M := ((algebraMap K' M).comp (algebraMap K K')).toAlgebra
  haveI : IsScalarTower K K' M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let φ : L ≃ₐ[K] M :=
    { mapFieldEquiv τ σ hσ L with
      commutes' := fun c => mapFieldEquiv_algebraMap τ σ hσ L c }
  haveI : FiniteDimensional K M := LinearEquiv.finiteDimensional φ.toLinearEquiv
  haveI : IsAbelianGalois K M := IsAbelianGalois.of_algHom φ.symm.toAlgHom
  exact ⟨Module.Finite.of_restrictScalars_finite K K' M, IsAbelianGalois.tower_top K K' M⟩

/-- The transport of a finite abelian subextension. -/
def AbFin.mapBase (L : AbFin K Ω) : AbFin K' Ω' :=
  ⟨mapField τ σ hσ L.1, mapField_abFin τ σ hσ L.1⟩

theorem mapField_mapField_symm (L : IntermediateField K' Ω') :
    mapField τ σ hσ (mapField τ.symm σ.symm (symm_compat τ σ hσ) L) = L := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    change σ (σ.symm z) ∈ L
    rwa [RingEquiv.apply_symm_apply]
  · intro hy
    exact ⟨σ.symm y, ⟨y, hy, rfl⟩, σ.apply_symm_apply y⟩

/-- Norms are transported: `τ(N_{L/K}(x)) = N_{σL/K'}(σ x)`. -/
theorem norm_mapFieldEquiv (L : IntermediateField K Ω) (x : L) :
    τ (Algebra.norm K x) = Algebra.norm K' (mapFieldEquiv τ σ hσ L x) := by
  rw [Algebra.norm_eq_of_equiv_equiv (τ : K ≃+* K') (mapFieldEquiv τ σ hσ L)
    (RingHom.ext fun c => (mapFieldEquiv_algebraMap τ σ hσ L c).symm) x]
  exact τ.toRingEquiv.apply_symm_apply _

end Transport

/-! ### The maximal abelian extensions and the Artin map -/

section Artin

variable {K K' : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
  [Field K'] [Algebra ℚ_[p] K'] [FiniteDimensional ℚ_[p] K']
variable {Ω Ω' : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [Field Ω'] [Algebra K' Ω'] [Algebra ℚ_[p] Ω'] [IsScalarTower ℚ_[p] K' Ω']
  [IsAlgClosed Ω']
variable (τ : K ≃ₐ[ℚ_[p]] K') (σ : Ω ≃+* Ω')
  (hσ : ∀ c : K, σ (algebraMap K Ω c) = algebraMap K' Ω' (τ c))

include τ hσ in
theorem map_mem_maxAbelian_base {y : Ω} (hy : y ∈ maxAbelian K Ω) :
    σ y ∈ maxAbelian K' Ω' := by
  obtain ⟨L, hyL⟩ := mem_maxAbelian_iff.1 hy
  exact le_maxAbelian (L.mapBase τ σ hσ) (map_mem_mapField τ σ hσ hyL)

/-- `σ : K^ab ≃ K'^ab`. -/
def maxAbelianRingEquiv : maxAbelian K Ω ≃+* maxAbelian K' Ω' where
  toFun y := ⟨σ (y : Ω), map_mem_maxAbelian_base τ σ hσ y.2⟩
  invFun y := ⟨σ.symm (y : Ω'), map_mem_maxAbelian_base τ.symm σ.symm (symm_compat τ σ hσ) y.2⟩
  left_inv y := Subtype.ext (σ.symm_apply_apply y)
  right_inv y := Subtype.ext (σ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul σ (x : Ω) y)
  map_add' x y := Subtype.ext (map_add σ (x : Ω) y)

theorem coe_maxAbelianRingEquiv (y : maxAbelian K Ω) :
    (maxAbelianRingEquiv τ σ hσ y : Ω') = σ (y : Ω) := rfl

theorem coe_maxAbelianRingEquiv_symm (y : maxAbelian K' Ω') :
    ((maxAbelianRingEquiv τ σ hσ).symm y : Ω) = σ.symm (y : Ω') := rfl

/-- `g ↦ σ g σ⁻¹ : Gal(K^ab/K) ≃* Gal(K'^ab/K')`. -/
noncomputable def galConjBase :
    (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) →* (maxAbelian K' Ω' ≃ₐ[K'] maxAbelian K' Ω') where
  toFun g :=
    { (maxAbelianRingEquiv τ σ hσ).symm.trans (g.toRingEquiv.trans (maxAbelianRingEquiv τ σ hσ))
      with
      commutes' := fun c => by
        apply Subtype.ext
        change σ (g ((maxAbelianRingEquiv τ σ hσ).symm (algebraMap K' _ c)) : Ω) =
          algebraMap K' Ω' c
        have h1 : (maxAbelianRingEquiv τ σ hσ).symm (algebraMap K' (maxAbelian K' Ω') c) =
            algebraMap K (maxAbelian K Ω) (τ.symm c) :=
          Subtype.ext (symm_compat τ σ hσ c)
        rw [h1, g.commutes]
        change σ (algebraMap K Ω (τ.symm c)) = _
        rw [hσ, AlgEquiv.apply_symm_apply] }
  map_one' := by ext y; simp
  map_mul' g h := by ext y; simp

theorem galConjBase_apply (g : maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) (y : maxAbelian K' Ω') :
    (galConjBase τ σ hσ g y : Ω') = σ (g ((maxAbelianRingEquiv τ σ hσ).symm y) : Ω) := rfl

include hσ in
/-- **Naturality of the Artin map under isomorphisms of the base field**:
`artin_{K'}(τ x) (σ y) = σ (artin_K(x) y)`. -/
theorem artin_naturality (x : Kˣ) (y : maxAbelian K Ω) :
    (artin p K' Ω' (Units.map (τ : K →* K') x) (maxAbelianRingEquiv τ σ hσ y) : Ω') =
      σ (artin p K Ω x y : Ω) := by
  set r : K'ˣ →* (maxAbelian K' Ω' ≃ₐ[K'] maxAbelian K' Ω') :=
    (galConjBase τ σ hσ).comp ((artin p K Ω).comp (Units.map (τ.symm : K' →* K)))
  have hr : r = artin p K' Ω' := by
    refine eq_artin_of_forall r ?_ ?_
    · intro x' hx' n hn y' hy'
      have hv : v p ((Units.map (τ.symm : K' →* K) x' : Kˣ) : K) = 1 := by
        rw [Units.coe_map]
        change v p (τ.symm (x' : K')) = 1
        rw [v_algEquiv']; exact hx'
      have hq := q_algEquiv τ
      have hy : (σ.symm y') ^ q p K ^ n = σ.symm y' := by
        rw [← map_pow, ← hq, hy']
      change σ (artin p K Ω _ ((maxAbelianRingEquiv τ σ hσ).symm ⟨y', _⟩) : Ω) = _
      have := artin_apply_of_pow_eq (Ω := Ω) _ hv hn _ hy
      have he : (maxAbelianRingEquiv τ σ hσ).symm ⟨y', mem_maxAbelian_of_pow_eq hn hy'⟩ =
          ⟨σ.symm y', mem_maxAbelian_of_pow_eq hn hy⟩ := Subtype.ext rfl
      rw [he, this, map_pow, RingEquiv.apply_symm_apply, hq]
    · intro L' x' hx' y' hy'
      apply Subtype.ext
      -- pull back `L'`
      set L₀ : AbFin K Ω := ⟨mapField τ.symm σ.symm (symm_compat τ σ hσ) L'.1,
        mapField_abFin τ.symm σ.symm (symm_compat τ σ hσ) L'.1⟩
      have hN : (Units.map (τ.symm : K' →* K) x') ∈ normGroup K L₀.1 := by
        obtain ⟨w', hw'⟩ := hx'
        set φ := mapFieldEquiv τ.symm σ.symm (symm_compat τ σ hσ) L'.1
        refine ⟨Units.map (φ : L'.1 →* L₀.1) w', ?_⟩
        apply Units.ext
        rw [Units.coe_map, Units.coe_map, Units.coe_map]
        change Algebra.norm K (φ (w' : L'.1)) = τ.symm (x' : K')
        rw [← norm_mapFieldEquiv τ.symm σ.symm (symm_compat τ σ hσ) L'.1, ← hw']
        rfl
      have hy0 : σ.symm y' ∈ L₀.1 := ⟨y', hy', rfl⟩
      change σ (artin p K Ω _ ((maxAbelianRingEquiv τ σ hσ).symm y') : Ω) = _
      rw [artin_apply_of_mem_normGroup L₀ _ hN _ hy0]
      exact σ.apply_symm_apply _
  have h := DFunLike.congr_fun (DFunLike.congr_fun hr.symm (Units.map (τ : K →* K') x))
    (maxAbelianRingEquiv τ σ hσ y)
  rw [h]
  change σ (artin p K Ω (Units.map (τ.symm : K' →* K) (Units.map (τ : K →* K') x))
    ((maxAbelianRingEquiv τ σ hσ).symm (maxAbelianRingEquiv τ σ hσ y)) : Ω) = _
  have hx : Units.map (τ.symm : K' →* K) (Units.map (τ : K →* K') x) = x := by
    ext
    simp
  rw [RingEquiv.symm_apply_apply, hx]

end Artin

end PadicField
