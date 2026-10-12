/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.Abelian
import LocalClassFieldTheory.PadicField.AbsoluteInertia

/-!
# The Artin map `Kˣ → Gal(K^ab/K)`

`K^ab ⊆ Ω` (`PadicField.maxAbelian`) is the union of the finite abelian subextensions of `Ω/K`.
The local reciprocity maps `abRec L` are compatible with restriction, hence glue to the
**Artin map** `PadicField.artin : Kˣ →* Gal(K^ab/K)`.

* `PadicField.artin_apply`: on a finite abelian `L`, `artin x` acts as `abRec L x`;
* `PadicField.artin_apply_eq_self_iff`: `artin x` fixes `L` iff `x ∈ N_{L/K} Lˣ`;
* `PadicField.ker_artin`: the kernel is the intersection of all norm groups;
* `PadicField.artin_uniformizer_apply`, `PadicField.mk_eq_arithFrob_of_artin`: uniformisers act
  on `K^ur` as the arithmetic Frobenius, i.e. map to `arithFrob` modulo inertia;
* `PadicField.artin_unit_mem_absInertia`: units act trivially on `K^ur` (they map into inertia),
  and `PadicField.exists_unit_abRec_eq`: at every finite abelian level, units map onto the
  inertia subgroup `Gal(L / L ∩ K^ur)`.
-/

set_option linter.unusedSectionVars false

open IntermediateField
open scoped IsMulCommutative

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

omit [IsAlgClosed Ω] in
/-- The compositum of two abelian extensions is abelian. -/
theorem isAbelianGalois_sup (L₁ L₂ : IntermediateField K Ω) [FiniteDimensional K L₁]
    [FiniteDimensional K L₂] [IsAbelianGalois K L₁] [IsAbelianGalois K L₂] :
    IsAbelianGalois K (L₁ ⊔ L₂ : IntermediateField K Ω) where
  is_comm := ⟨fun σ τ ↦ by
    have h := eq_one_of_resHom_eq_one rfl (le_sup_left : L₁ ≤ L₁ ⊔ L₂)
      (le_sup_right : L₂ ≤ L₁ ⊔ L₂) (σ * τ * (τ * σ)⁻¹)
      (by rw [map_mul, map_inv, map_mul, map_mul, mul_comm (resHom _ σ), mul_inv_cancel])
      (by rw [map_mul, map_inv, map_mul, map_mul, mul_comm (resHom _ σ), mul_inv_cancel])
    exact mul_inv_eq_one.1 h⟩

variable (K Ω) in
/-- The finite abelian subextensions of `Ω / K`. -/
def AbFin : Type _ :=
  {L : IntermediateField K Ω // FiniteDimensional K L ∧ IsAbelianGalois K L}

instance AbFin.finiteDimensional (L : AbFin K Ω) : FiniteDimensional K L.1 := L.2.1
instance AbFin.isAbelianGalois (L : AbFin K Ω) : IsAbelianGalois K L.1 := L.2.2

instance : Nonempty (AbFin K Ω) :=
  ⟨⟨⊥, inferInstance, .of_algHom (IntermediateField.botEquiv K Ω).toAlgHom⟩⟩

omit [IsAlgClosed Ω] in
theorem directed_abFin : Directed (· ≤ ·) fun L : AbFin K Ω ↦ L.1 := fun L₁ L₂ ↦
  ⟨⟨L₁.1 ⊔ L₂.1, inferInstance, isAbelianGalois_sup L₁.1 L₂.1⟩, le_sup_left, le_sup_right⟩

variable (K Ω) in
/-- The maximal abelian extension `K^ab` of `K` inside `Ω`. -/
noncomputable def maxAbelian : IntermediateField K Ω := ⨆ L : AbFin K Ω, L.1

omit [IsAlgClosed Ω] in
theorem le_maxAbelian (L : AbFin K Ω) : L.1 ≤ maxAbelian K Ω :=
  le_iSup (fun L : AbFin K Ω ↦ L.1) L

omit [IsAlgClosed Ω] in
theorem mem_maxAbelian_iff {x : Ω} : x ∈ maxAbelian K Ω ↔ ∃ L : AbFin K Ω, x ∈ L.1 := by
  rw [maxAbelian, ← SetLike.mem_coe, coe_iSup_of_directed directed_abFin, Set.mem_iUnion]
  rfl

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] in
instance normal_maxAbelian : Normal K (maxAbelian K Ω) :=
  IntermediateField.normal_iSup K Ω _

include hp in
/-- `K^ab / K` is Galois. -/
theorem isGalois_maxAbelian : IsGalois K (maxAbelian K Ω) := by
  haveI := charZero p K
  exact ⟨⟩

variable (p) in
/-- The local reciprocity map of `L`, viewed as a map into `K^ab` (auxiliary). -/
noncomputable def artinAux (x : Kˣ) (L : AbFin K Ω) :
    L.1.toSubalgebra →ₐ[K] maxAbelian K Ω :=
  (inclusion (le_maxAbelian L)).comp (abRec p L.1 x).toAlgHom

theorem artinAux_apply (x : Kˣ) (L : AbFin K Ω) (y : L.1) :
    (artinAux p x L y : Ω) = abRec p L.1 x y := rfl

variable (p) in
/-- The Artin map as an algebra homomorphism (auxiliary). -/
noncomputable def artinHom (x : Kˣ) : maxAbelian K Ω →ₐ[K] maxAbelian K Ω :=
  Subalgebra.iSupLift (fun L : AbFin K Ω ↦ L.1.toSubalgebra)
    (fun L₁ L₂ ↦ by
      obtain ⟨L, h1, h2⟩ := directed_abFin L₁ L₂
      exact ⟨L, h1, h2⟩)
    (artinAux p x)
    (fun L₁ L₂ h ↦ by
      ext y
      simp only [AlgHom.comp_apply]
      rw [artinAux_apply, artinAux_apply, ← resHom_abRec_of_le L₂.1 L₁.1 h x, resHom_apply]
      rfl)
    (maxAbelian K Ω).toSubalgebra
    (by rw [maxAbelian, toSubalgebra_iSup_of_directed directed_abFin])

theorem artinHom_apply (x : Kˣ) (L : AbFin K Ω) (y : Ω) (hy : y ∈ L.1) :
    (artinHom p x ⟨y, le_maxAbelian L hy⟩ : Ω) = abRec p L.1 x ⟨y, hy⟩ := by
  simp only [artinHom]
  exact (congrArg Subtype.val (Subalgebra.iSupLift_mk
    (K := fun L : AbFin K Ω ↦ L.1.toSubalgebra) (f := artinAux p x)
    (T := (maxAbelian K Ω).toSubalgebra) (i := L)
    (x := (⟨y, hy⟩ : L.1.toSubalgebra)) (hx := le_maxAbelian L hy))).trans
    (artinAux_apply x L ⟨y, hy⟩)

variable (p) in
/-- The Artin map on elements. -/
noncomputable def artinEquiv (x : Kˣ) : maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω :=
  AlgEquiv.ofBijective (artinHom p x) (Algebra.IsAlgebraic.algHom_bijective _)

theorem artinEquiv_apply (x : Kˣ) (L : AbFin K Ω) (y : Ω) (hy : y ∈ L.1) :
    (artinEquiv p x ⟨y, le_maxAbelian L hy⟩ : Ω) = abRec p L.1 x ⟨y, hy⟩ :=
  artinHom_apply x L y hy

variable (p K Ω) in
/-- **The Artin map** `Kˣ → Gal(K^ab / K)`. -/
noncomputable def artin : Kˣ →* (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) where
  toFun := artinEquiv p
  map_one' := by
    ext ⟨y, hy⟩
    obtain ⟨L, hyL⟩ := mem_maxAbelian_iff.1 hy
    rw [artinEquiv_apply 1 L y hyL, map_one]
    rfl
  map_mul' x x' := by
    ext ⟨y, hy⟩
    obtain ⟨L, hyL⟩ := mem_maxAbelian_iff.1 hy
    rw [artinEquiv_apply _ L y hyL, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    set z := abRec p L.1 x' ⟨y, hyL⟩
    have h1 : artinEquiv p x' ⟨y, hy⟩ = ⟨z, le_maxAbelian L z.2⟩ :=
      Subtype.ext (artinEquiv_apply x' L y hyL)
    rw [h1, artinEquiv_apply x L z z.2]

/-- On a finite abelian `L`, the Artin map acts as `abRec L`. -/
theorem artin_apply (x : Kˣ) (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] (y : Ω) (hy : y ∈ L) :
    (artin p K Ω x ⟨y, le_maxAbelian ⟨L, inferInstance, inferInstance⟩ hy⟩ : Ω) =
      abRec p L x ⟨y, hy⟩ :=
  artinEquiv_apply x ⟨L, inferInstance, inferInstance⟩ y hy

/-- `artin x` fixes a finite abelian `L` iff `x` is a norm from `L`. -/
theorem artin_apply_eq_self_iff (x : Kˣ) (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] :
    (∀ y : maxAbelian K Ω, (y : Ω) ∈ L → artin p K Ω x y = y) ↔ x ∈ normGroup K L := by
  rw [← ker_abRec (p := p) L, MonoidHom.mem_ker]
  constructor
  · intro h
    ext ⟨y, hy⟩
    have := congrArg Subtype.val (h ⟨y, le_maxAbelian ⟨L, inferInstance, inferInstance⟩ hy⟩ hy)
    rw [artin_apply x L y hy] at this
    exact this
  · intro h ⟨y, hy'⟩ hy
    apply Subtype.ext
    rw [artin_apply x L y hy, h]
    rfl

/-- The kernel of the Artin map is the intersection of all norm groups of finite abelian
extensions. -/
theorem mem_ker_artin_iff (x : Kˣ) :
    x ∈ (artin p K Ω).ker ↔ ∀ L : AbFin K Ω, x ∈ normGroup K L.1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h L
    rw [← artin_apply_eq_self_iff (p := p)]
    intro y _
    rw [h]; rfl
  · intro h
    ext ⟨y, hy⟩
    obtain ⟨L, hyL⟩ := mem_maxAbelian_iff.1 hy
    have := (artin_apply_eq_self_iff (p := p) x L.1).2 (h L) ⟨y, hy⟩ hyL
    rw [this]
    rfl

end PadicField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] in
theorem resHom_self {E : IntermediateField K Ω} [Normal K E] (σ : E ≃ₐ[K] E) :
    resHom (le_refl E) σ = σ := by
  rw [resHom_eq_iff]; intro x; rfl

instance isGalois_unramifiedOfDegree (n : ℕ) : IsGalois K (unramifiedOfDegree p K Ω n) :=
  isGalois_of_isUnramified (isUnramified_unramifiedOfDegree p K Ω n)

instance isCyclic_unramifiedOfDegree (n : ℕ) :
    IsCyclic (unramifiedOfDegree p K Ω n ≃ₐ[K] unramifiedOfDegree p K Ω n) :=
  isCyclic_gal (isUnramified_unramifiedOfDegree p K Ω n)

instance isAbelianGalois_unramifiedOfDegree (n : ℕ) :
    IsAbelianGalois K (unramifiedOfDegree p K Ω n) := .of_isCyclic K _

/-- Uniformisers act on `K_n` as the Frobenius. -/
theorem cycRec_unramified_of_v_eq_one {n : ℕ} (hn : 0 < n) (x : Kˣ) (hx : v p (x : K) = 1) :
    cycRec p (unramifiedOfDegree p K Ω n) x = frobT p K Ω n := by
  set s := n * cycDeg p (unramifiedOfDegree p K Ω n)
  have hs : 0 < s := Nat.mul_pos hn (cycDeg_pos _)
  have hns : unramifiedOfDegree p K Ω n ≤ unramifiedOfDegree p K Ω s :=
    unramifiedOfDegree_le_of_dvd hs.ne' (dvd_mul_right _ _)
  set D := unramifiedOfDegree p K Ω s
  set τ := frobT p K Ω s
  have hfD : f p K D = s := by
    rw [(isUnramified_unramifiedOfDegree p K Ω s).f_eq, finrank_unramifiedOfDegree p K Ω hs]
  have hf := f_fixedField_frobLift hs hfD le_rfl τ (resHom_self τ)
  set Fx := fixedField (Subgroup.zpowers τ)
  -- `Fix τ = K`
  have hdeg : Module.finrank K Fx = 1 := by
    have h1 := Module.finrank_mul_finrank K Fx D
    rw [finrank_fixedField_eq_card, Nat.card_zpowers, orderOf_frob,
      finrank_unramifiedOfDegree p K Ω hs] at h1
    exact (Nat.mul_eq_right hs.ne').1 h1
  have he : e p K Fx = 1 := by
    have := e_mul_f (p := p) (K := K) (L := Fx)
    rw [hdeg] at this
    exact Nat.eq_one_of_mul_eq_one_right this
  set π : Fx := algebraMap K Fx x
  have hπ : v p π = 1 := by rw [v_algebraMap, he, hx]; rfl
  have hNπ : Algebra.norm K π = x := by
    rw [Algebra.norm_algebraMap, hdeg, pow_one]
  have hπ0 : Algebra.norm K π ≠ 0 := by rw [hNπ]; exact x.ne_zero
  have h := cycRec_norm_frobLift (unramifiedOfDegree p K Ω n) hs (dvd_mul_left _ _) D hns le_rfl τ
    (resHom_self τ) hf π hπ hπ0
  have hu : Units.mk0 _ hπ0 = x := Units.ext hNπ
  rw [hu] at h
  rw [h]
  exact resHom_frobT hn hs hns

/-- The reciprocity map of `K_n` is `x ↦ Frob ^ v(x)`. -/
theorem cycRec_unramified {n : ℕ} (hn : 0 < n) (x : Kˣ) :
    cycRec p (unramifiedOfDegree p K Ω n) x = frobT p K Ω n ^ v p (x : K) := by
  have := monoidHom_ext_of_v_eq_one (p := p) (φ := cycRec p (unramifiedOfDegree p K Ω n))
    (ψ := (zpowersHom _ (frobT p K Ω n)).comp (vMul p K)) fun x hx ↦ by
      rw [cycRec_unramified_of_v_eq_one hn x hx]
      simp [vMul, hx]
  exact DFunLike.congr_fun this x

theorem unramifiedOfDegree_le_maxAbelian (n : ℕ) :
    unramifiedOfDegree p K Ω n ≤ maxAbelian K Ω :=
  le_maxAbelian ⟨_, inferInstance, inferInstance⟩

/-- `K^ur ⊆ K^ab`. -/
theorem maxUnramified_le_maxAbelian : maxUnramified p K Ω ≤ maxAbelian K Ω :=
  iSup_le fun n ↦ unramifiedOfDegree_le_maxAbelian n

/-- The Artin map acts on `K_n` as `Frob ^ v(x)`. -/
theorem artin_apply_unramified {n : ℕ} (hn : 0 < n) (x : Kˣ) (y : Ω)
    (hy : y ∈ unramifiedOfDegree p K Ω n) :
    (artin p K Ω x ⟨y, unramifiedOfDegree_le_maxAbelian n hy⟩ : Ω) =
      ((frobT p K Ω n ^ v p (x : K)) ⟨y, hy⟩ : Ω) := by
  rw [artin_apply x _ y hy, abRec_eq_cycRec, cycRec_unramified hn]

/-- **Uniformisers act on `K^ur` as the arithmetic Frobenius.** -/
theorem artin_apply_maxUnramified_of_v_eq_one (x : Kˣ) (hx : v p (x : K) = 1)
    (y : maxUnramified p K Ω) :
    (artin p K Ω x ⟨y, maxUnramified_le_maxAbelian y.2⟩ : Ω) = frobUr p K Ω y := by
  obtain ⟨n, hn, hyn⟩ := (mem_maxUnramified_iff (p := p) (K := K) (Ω := Ω)).1 y.2
  rw [artin_apply_unramified hn x (y : Ω) hyn, hx, zpow_one]
  exact (frobUr_apply hn hyn).symm

/-- **Units act trivially on `K^ur`.** -/
theorem artin_apply_maxUnramified_of_v_eq_zero (x : Kˣ) (hx : v p (x : K) = 0)
    (y : maxUnramified p K Ω) :
    (artin p K Ω x ⟨y, maxUnramified_le_maxAbelian y.2⟩ : Ω) = y := by
  obtain ⟨n, hn, hyn⟩ := (mem_maxUnramified_iff (p := p) (K := K) (Ω := Ω)).1 y.2
  rw [artin_apply_unramified hn x (y : Ω) hyn, hx, zpow_zero]
  rfl

/-- **Uniformisers map to the arithmetic Frobenius modulo inertia**: every extension `σ` of
`artin x` (`v(x) = 1`) to `Ω` satisfies `σ ≡ Frob (mod I_K)`. -/
theorem mk_eq_arithFrob_of_artin [Algebra.IsAlgebraic ℚ_[p] Ω] (x : Kˣ) (hx : v p (x : K) = 1) (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ y : maxAbelian K Ω, σ y = artin p K Ω x y) :
    (QuotientGroup.mk σ : (Ω ≃ₐ[K] Ω) ⧸ absInertia p K Ω) = arithFrob p K Ω := by
  apply (unramifiedQuotientEquiv p K Ω).injective
  rw [unramifiedQuotientEquiv_arithFrob]
  ext y
  rw [unramifiedQuotientEquiv_mk, ← artin_apply_maxUnramified_of_v_eq_one x hx y]
  exact hσ ⟨y, maxUnramified_le_maxAbelian y.2⟩

/-- **Units map into inertia**: every extension `σ` of `artin u` (`u` a unit) to `Ω` lies in the
absolute inertia group. -/
theorem mem_absInertia_of_artin [Algebra.IsAlgebraic ℚ_[p] Ω] (x : Kˣ) (hx : v p (x : K) = 0) (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ y : maxAbelian K Ω, σ y = artin p K Ω x y) : σ ∈ absInertia p K Ω := by
  rw [absInertia_eq, IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  rw [hσ ⟨y, maxUnramified_le_maxAbelian hy⟩]
  exact artin_apply_maxUnramified_of_v_eq_zero x hx ⟨y, hy⟩

/-- **Units map onto inertia at every finite abelian level**: an element of `Gal(L/K)` fixing
`L ∩ K^ur` is `abRec L u` for a unit `u`. -/
theorem exists_unit_abRec_eq (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] (σ : L ≃ₐ[K] L) (hσ : ∀ y : L, (y : Ω) ∈ maxUnramified p K Ω → σ y = y) :
    ∃ u : Kˣ, v p (u : K) = 0 ∧ abRec p L u = σ := by
  obtain ⟨x, rfl⟩ := abRec_surjective (p := p) L σ
  set n := f p K L
  have hn : 0 < n := f_pos
  have hnL : unramifiedOfDegree p K Ω n ≤ L := unramifiedOfDegree_le_of_f_eq L rfl
  have h1 : resHom hnL (abRec p L x) = 1 := by
    rw [resHom_eq_iff]
    intro y
    have := hσ (inclusion hnL y) (unramifiedOfDegree_le_maxUnramified p K Ω n y.2)
    rw [this]; rfl
  rw [resHom_abRec_of_le L _ hnL, abRec_eq_cycRec, cycRec_unramified hn,
    ← orderOf_dvd_iff_zpow_eq_one, orderOf_frob, finrank_unramifiedOfDegree p K Ω hn] at h1
  obtain ⟨k, hk⟩ := h1
  have hπ := uniformizer_spec (p := p) (K := L)
  set y : Kˣ := Units.map (Algebra.norm K : L →* K) (Units.mk0 _ hπ.ne_zero)
  have hy : v p (y : K) = n := by
    change v p (Algebra.norm K (uniformizer p L)) = n
    rw [v_norm hπ.ne_zero, hπ, mul_one]
  have hyN : abRec p L y = 1 := by
    rw [← MonoidHom.mem_ker, ker_abRec]
    exact ⟨_, rfl⟩
  refine ⟨x * y ^ (-k), ?_, ?_⟩
  · rw [Units.val_mul, Units.val_zpow_eq_zpow_val, v_mul x.ne_zero (zpow_ne_zero _ y.ne_zero),
      v_zpow y.ne_zero, hy, hk]
    ring
  · rw [map_mul, map_zpow, hyN, one_zpow, mul_one]

end PadicField
