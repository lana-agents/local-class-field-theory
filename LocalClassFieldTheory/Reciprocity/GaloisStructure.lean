/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Reciprocity.ArtinInertia
import LocalClassFieldTheory.Reciprocity.ArtinContinuous
import LocalClassFieldTheory.PadicField.UnramifiedZHat

/-!
# `Gal(K^ab/K) ≅ 𝒪ˣ × Ẑ`

Fix a uniformiser `π` of `K` (`v(π) = 1`). The Artin map identifies the units `𝒪ˣ` with the
inertia group, and `π` with a Frobenius lift; extending `k ↦ artin(π)^k` continuously to `Ẑ`
(`PadicField.artinZHat`, via `Brauer.zhatPow`) we get a continuous homomorphism
`𝒪ˣ × Ẑ → Gal(K^ab/K)`, `(u, a) ↦ artin(u) · artin(π)^a`, which is

* injective: on `K_n` it acts as `Frob^(a mod n)`, so it determines `a`, and then `u` by
  injectivity of the Artin map;
* surjective: its image is compact, hence closed, and contains the dense image of the Artin map
  (`x = u π^{v(x)}`).

Since `𝒪ˣ × Ẑ` is compact (`PadicField.unitGroup.compactSpace`, for the topology of the absolute
value, `PadicField.unitGroup.topologicalSpace`), this is an isomorphism of topological groups:

* **`PadicField.galAbEquiv π hπ : Gal(K^ab/K) ≃ₜ* 𝒪ˣ × Ẑ`**, with
  `galAbEquiv (artin (u * π ^ k)) = (u, k)` (`PadicField.galAbEquiv_artin`), i.e. on
  `Kˣ = 𝒪ˣ × π^ℤ` the Artin map becomes `id × (ℤ → Ẑ)` (`PadicField.galAbEquiv_artin'`, with
  `PadicField.unitComponent`);
* the `Ẑ`-component is the restriction to `K^ur` followed by `Gal(K^ur/K) ≅ Ẑ`
  (`PadicField.galAbEquiv_snd`), so the inertia group `Gal(K^ab/K^ur)` corresponds to `𝒪ˣ × 1`
  (`PadicField.galAbEquiv_snd_eq_one_iff`);
* `PadicField.gal_maxAbelian_mul_comm`: `Gal(K^ab/K)` is abelian.
-/

set_option linter.unusedSectionVars false

open IntermediateField Brauer

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

/-! ### The units -/

/-- The units `𝒪ˣ = {u ∈ Kˣ | ‖u‖ = 1}` with the topology induced by the absolute value. -/
noncomputable instance unitGroup.topologicalSpace : TopologicalSpace (unitGroup p K) :=
  @instTopologicalSpaceSubtype _ _ (unitsTopology p K)

/-- `𝒪ˣ` is compact. -/
instance unitGroup.compactSpace : CompactSpace (unitGroup p K) := by
  letI : NormedField K := spectralNorm.normedField ℚ_[p] K
  letI : NormedSpace ℚ_[p] K := spectralNorm.normedSpace ℚ_[p] K
  haveI : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  change CompactSpace (unitGroup p K : Set Kˣ)
  rw [← isCompact_iff_compactSpace, Units.isEmbedding_val₀.isCompact_iff]
  have h : (Units.val '' (unitGroup p K : Set Kˣ)) = Metric.sphere (0 : K) 1 := by
    ext x
    rw [mem_sphere_zero_iff_norm]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [norm_zero] at hx
        exact zero_ne_one hx
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  rw [h]
  exact isCompact_sphere 0 1

theorem continuous_artin_unitGroup :
    Continuous fun u : unitGroup p K ↦ artin p K Ω u := by
  letI := unitsTopology p K
  exact (continuous_artin (p := p) (K := K) (Ω := Ω)).comp continuous_subtype_val

/-! ### `Gal(K^ab/K)` -/

open scoped IsMulCommutative in
/-- `Gal(K^ab/K)` is abelian. -/
theorem gal_maxAbelian_mul_comm (σ τ : maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) :
    σ * τ = τ * σ := by
  ext ⟨y, hy⟩
  obtain ⟨L, hyL⟩ := mem_maxAbelian_iff.1 hy
  have h : resHom (le_maxAbelian L) (σ * τ) = resHom (le_maxAbelian L) (τ * σ) := by
    rw [map_mul, map_mul, mul_comm]
  have := congrArg (fun ρ : L.1 ≃ₐ[K] L.1 ↦ ((ρ ⟨y, hyL⟩ : L.1) : Ω)) h
  simp only [resHom_apply] at this
  exact this

variable (p K Ω) in
/-- The subgroup of `Gal(K^ab/K)` fixing `K_n`. -/
def abFix (n : ℕ) : Subgroup (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) where
  carrier := {σ | ∀ y : maxAbelian K Ω, (y : Ω) ∈ unramifiedOfDegree p K Ω n → σ y = y}
  mul_mem' {σ τ} hσ hτ y hy := by rw [AlgEquiv.mul_apply, hτ y hy, hσ y hy]
  one_mem' _ _ := rfl
  inv_mem' {σ} hσ y hy := by
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    exact (hσ y hy).symm

theorem isOpen_abFix (n : ℕ) :
    IsOpen (abFix p K Ω n : Set (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω)) := by
  have hle := unramifiedOfDegree_le_maxAbelian (p := p) (K := K) (Ω := Ω) n
  haveI : FiniteDimensional K (restrict hle) :=
    LinearEquiv.finiteDimensional (restrict_algEquiv hle).toLinearEquiv
  have h := (restrict hle).fixingSubgroup_isOpen
  convert h using 1
  ext g
  rw [SetLike.mem_coe, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  exact ⟨fun h y hy ↦ h y ((mem_restrict _ y).1 hy), fun h y hy ↦ h y ((mem_restrict _ y).2 hy)⟩

instance abFix_normal (n : ℕ) : (abFix p K Ω n).Normal where
  conj_mem σ hσ τ := by
    rw [gal_maxAbelian_mul_comm τ σ, mul_inv_cancel_right]
    exact hσ

variable (p K Ω) in
/-- Restriction `Gal(K^ab/K) → Gal(K^ur/K)`. -/
noncomputable def resUr :
    (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) →* (maxUnramified p K Ω ≃ₐ[K] maxUnramified p K Ω) :=
  resHom maxUnramified_le_maxAbelian

theorem resUr_apply (σ : maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) (y : maxUnramified p K Ω) :
    ((resUr p K Ω σ y : maxUnramified p K Ω) : Ω) =
      (σ ⟨y, maxUnramified_le_maxAbelian y.2⟩ : Ω) :=
  resHom_apply _ σ y

theorem mem_abFix_iff_resUr {n : ℕ} (σ : maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) :
    σ ∈ abFix p K Ω n ↔ resUr p K Ω σ ∈ urFix p K Ω n := by
  constructor
  · intro h x hx
    apply Subtype.ext
    rw [resUr_apply]
    exact congrArg Subtype.val (h _ hx)
  · intro h y hy
    have hy' : (y : Ω) ∈ maxUnramified p K Ω := unramifiedOfDegree_le_maxUnramified p K Ω n hy
    have := congrArg Subtype.val (h ⟨y, hy'⟩ hy)
    rw [resUr_apply] at this
    exact Subtype.ext this

/-- The Artin symbol of a uniformiser restricts to the Frobenius of `K^ur`. -/
theorem resUr_artin_uniformizer {π : Kˣ} (hπ : v p (π : K) = 1) :
    resUr p K Ω (artin p K Ω π) = frobUr p K Ω := by
  ext y
  rw [resUr_apply]
  exact artin_apply_maxUnramified_of_v_eq_one π hπ y

theorem artin_pow_mem_abFix_iff {π : Kˣ} (hπ : v p (π : K) = 1) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    artin p K Ω π ^ k ∈ abFix p K Ω n ↔ n ∣ k := by
  rw [mem_abFix_iff_resUr, map_pow, resUr_artin_uniformizer hπ]
  exact frobUr_pow_mem_urFix_iff hn k

theorem artin_unit_mem_abFix (u : unitGroup p K) (n : ℕ) :
    artin p K Ω u ∈ abFix p K Ω n := fun y hy ↦
  artin_mem_abInertia u y (unramifiedOfDegree_le_maxUnramified p K Ω n hy)

/-! ### `artin(π) ^ a` for `a ∈ Ẑ` -/

variable (p K Ω) in
/-- `a ↦ artin(π) ^ a`, the continuous extension of `k ↦ artin(π ^ k)` to `Ẑ`. -/
noncomputable def artinZHat (π : Kˣ) :
    Multiplicative ZHat →ₜ* (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) :=
  haveI := isGalois_maxAbelian (p := p) (K := K) (Ω := Ω)
  zhatPow (artin p K Ω π)

theorem artinZHat_intToZHat (π : Kˣ) (k : ℤ) :
    artinZHat p K Ω π (Multiplicative.ofAdd (intToZHat k)) = artin p K Ω (π ^ k) := by
  haveI := isGalois_maxAbelian (p := p) (K := K) (Ω := Ω)
  rw [map_zpow]
  exact zhatPow_intToZHat _ k

theorem artinZHat_mem_abFix_iff {π : Kˣ} (hπ : v p (π : K) = 1) (a : Multiplicative ZHat)
    (n : ℕ+) :
    artinZHat p K Ω π a ∈ abFix p K Ω n ↔ (a.toAdd : ∀ n : ℕ+, ZMod n) n = 0 := by
  haveI := isGalois_maxAbelian (p := p) (K := K) (Ω := Ω)
  exact zhatPow_mem_iff _ _ (isOpen_abFix n) (artin_pow_mem_abFix_iff hπ n.pos) a

/-- On `K^ur`, `artin(π) ^ a` acts as `Frob ^ a`. -/
theorem resUr_artinZHat {π : Kˣ} (hπ : v p (π : K) = 1) (a : Multiplicative ZHat) :
    resUr p K Ω (artinZHat p K Ω π a) = zhatPow (frobUr p K Ω) a := by
  ext y
  obtain ⟨n, hn, hyn⟩ := (mem_maxUnramified_iff (p := p) (K := K) (Ω := Ω)).1 y.2
  set m : ℕ+ := ⟨n, hn⟩
  set j := ((a.toAdd : ∀ n : ℕ+, ZMod n) m).val
  haveI := isGalois_maxAbelian (p := p) (K := K) (Ω := Ω)
  have h1 : (artin p K Ω π ^ j)⁻¹ * artinZHat p K Ω π a ∈ abFix p K Ω m :=
    zhatPow_pow_inv_mul_mem _ _ (isOpen_abFix m) (artin_pow_mem_abFix_iff hπ m.pos) a
  rw [mem_abFix_iff_resUr, map_mul, map_inv, map_pow, resUr_artin_uniformizer hπ] at h1
  have h2 := h1 y hyn
  rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at h2
  rw [h2, zhatPow_frobUr_apply a (n := m) y hyn]

/-! ### The decomposition -/

variable (p K Ω) in
/-- The homomorphism `𝒪ˣ × Ẑ → Gal(K^ab/K)`, `(u, a) ↦ artin(u) · artin(π)^a`. -/
noncomputable def galAbHom (π : Kˣ) :
    unitGroup p K × Multiplicative ZHat →* (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) where
  toFun x := artin p K Ω x.1 * artinZHat p K Ω π x.2
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul]
    rw [mul_assoc, mul_assoc]
    congr 1
    rw [← mul_assoc, gal_maxAbelian_mul_comm (artin p K Ω y.1), mul_assoc]

theorem galAbHom_apply (π : Kˣ) (x : unitGroup p K × Multiplicative ZHat) :
    galAbHom p K Ω π x = artin p K Ω x.1 * artinZHat p K Ω π x.2 := rfl

theorem continuous_galAbHom (π : Kˣ) : Continuous (galAbHom p K Ω π) :=
  (continuous_artin_unitGroup.comp continuous_fst).mul
    ((artinZHat p K Ω π).continuous.comp continuous_snd)

theorem galAbHom_injective {π : Kˣ} (hπ : v p (π : K) = 1) :
    Function.Injective (galAbHom p K Ω π) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨u, a⟩ h
  rw [galAbHom_apply, mul_eq_one_iff_eq_inv] at h
  have ha : a = 1 := by
    refine congrArg Multiplicative.ofAdd (ZHat.ext fun n ↦ ?_)
    refine (artinZHat_mem_abFix_iff (Ω := Ω) hπ a n).1 ?_
    rw [← inv_inv (artinZHat p K Ω π a), ← h]
    exact inv_mem (artin_unit_mem_abFix u n)
  rw [ha, map_one, inv_one] at h
  change artin p K Ω u = 1 at h
  have hu : u = 1 := Subtype.ext (artin_injective (p := p) (Ω := Ω)
    (by rw [h, Subgroup.coe_one, map_one]))
  rw [hu, ha]
  rfl

variable (p) in
/-- The unit part `x π ^ (-v(x))` of `x ∈ Kˣ`. -/
noncomputable def unitComponent (π : Kˣ) (hπ : v p (π : K) = 1) (x : Kˣ) : unitGroup p K :=
  ⟨x * π ^ (-v p (x : K)), by
    rw [mem_unitGroup, nrm_eq_one_iff_v_eq_zero (Units.ne_zero _), Units.val_mul,
      Units.val_zpow_eq_zpow_val, v_mul x.ne_zero (zpow_ne_zero _ π.ne_zero),
      v_zpow π.ne_zero, hπ]
    ring⟩

theorem unitComponent_mul_zpow {π : Kˣ} (hπ : v p (π : K) = 1) (x : Kˣ) :
    (unitComponent p π hπ x : Kˣ) * π ^ v p (x : K) = x := by
  change x * π ^ (-v p (x : K)) * π ^ v p (x : K) = x
  rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]

theorem galAbHom_artin (π : Kˣ) (u : unitGroup p K) (k : ℤ) :
    galAbHom p K Ω π (u, Multiplicative.ofAdd (intToZHat k)) = artin p K Ω (u * π ^ k) := by
  rw [galAbHom_apply, artinZHat_intToZHat, map_mul]

theorem galAbHom_surjective {π : Kˣ} (hπ : v p (π : K) = 1) :
    Function.Surjective (galAbHom p K Ω π) := by
  haveI := isGalois_maxAbelian (p := p) (K := K) (Ω := Ω)
  have hcl : IsClosed (Set.range (galAbHom p K Ω π)) :=
    (isCompact_range (continuous_galAbHom π)).isClosed
  have hsub : Set.range (artin p K Ω) ⊆ Set.range (galAbHom p K Ω π) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, (galAbHom_artin π (unitComponent p π hπ x) (v p (x : K))).trans
      (by rw [unitComponent_mul_zpow hπ x])⟩
  intro σ
  have h := closure_mono hsub (denseRange_artin (p := p) (K := K) (Ω := Ω) σ)
  rwa [hcl.closure_eq] at h

variable (p K Ω) in
/-- **`Gal(K^ab/K) ≅ 𝒪ˣ × Ẑ`** as topological groups, after the choice of a uniformiser `π`:
the inverse is `(u, a) ↦ artin(u) · artin(π)^a`. -/
noncomputable def galAbEquiv {π : Kˣ} (hπ : v p (π : K) = 1) :
    (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) ≃ₜ* unitGroup p K × Multiplicative ZHat :=
  haveI := isGalois_maxAbelian (p := p) (K := K) (Ω := Ω)
  let e := MulEquiv.ofBijective (galAbHom p K Ω π)
    ⟨galAbHom_injective hπ, galAbHom_surjective hπ⟩
  ContinuousMulEquiv.symm
    { e with
      continuous_toFun := continuous_galAbHom π
      continuous_invFun :=
        (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv)
          (continuous_galAbHom π)).symm.continuous }

theorem galAbEquiv_symm_apply {π : Kˣ} (hπ : v p (π : K) = 1)
    (x : unitGroup p K × Multiplicative ZHat) :
    (galAbEquiv p K Ω hπ).symm x = artin p K Ω x.1 * artinZHat p K Ω π x.2 := rfl

/-- `galAbEquiv (artin (u π ^ k)) = (u, k)`. -/
theorem galAbEquiv_artin {π : Kˣ} (hπ : v p (π : K) = 1) (u : unitGroup p K) (k : ℤ) :
    galAbEquiv p K Ω hπ (artin p K Ω (u * π ^ k)) = (u, Multiplicative.ofAdd (intToZHat k)) := by
  rw [ContinuousMulEquiv.apply_eq_iff_symm_apply]
  exact (galAbHom_artin π u k).symm

/-- On `Kˣ = 𝒪ˣ × π^ℤ`, `galAbEquiv ∘ artin` is `x ↦ (x π^(-v(x)), v(x))`. -/
theorem galAbEquiv_artin' {π : Kˣ} (hπ : v p (π : K) = 1) (x : Kˣ) :
    galAbEquiv p K Ω hπ (artin p K Ω x) =
      (unitComponent p π hπ x, Multiplicative.ofAdd (intToZHat (v p (x : K)))) := by
  conv_lhs => rw [← unitComponent_mul_zpow hπ x]
  exact galAbEquiv_artin hπ _ _

/-- Units correspond to `𝒪ˣ × 1`. -/
theorem galAbEquiv_artin_unit {π : Kˣ} (hπ : v p (π : K) = 1) (u : unitGroup p K) :
    galAbEquiv p K Ω hπ (artin p K Ω u) = (u, 1) := by
  simpa using galAbEquiv_artin (Ω := Ω) hπ u 0

/-- The uniformiser corresponds to `(1, 1)`, `1 ∈ Ẑ` the topological generator. -/
theorem galAbEquiv_artin_uniformizer {π : Kˣ} (hπ : v p (π : K) = 1) :
    galAbEquiv p K Ω hπ (artin p K Ω π) = (1, Multiplicative.ofAdd (intToZHat 1)) := by
  simpa using galAbEquiv_artin (Ω := Ω) hπ 1 1

/-- The `Ẑ`-component of `galAbEquiv σ` is the image of `σ|_{K^ur}` under
`Gal(K^ur/K) ≅ Ẑ`. -/
theorem galAbEquiv_snd {π : Kˣ} (hπ : v p (π : K) = 1)
    (σ : maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) :
    (galAbEquiv p K Ω hπ σ).2 = galMaxUnramifiedEquiv p K Ω (resUr p K Ω σ) := by
  set x := galAbEquiv p K Ω hπ σ
  have hσ : σ = artin p K Ω x.1 * artinZHat p K Ω π x.2 := by
    rw [← galAbEquiv_symm_apply hπ, ContinuousMulEquiv.symm_apply_apply]
  have h1 : resUr p K Ω (artin p K Ω x.1) = 1 := by
    ext y
    rw [resUr_apply]
    exact congrArg Subtype.val (artin_mem_abInertia x.1 _ y.2)
  rw [hσ, map_mul, h1, one_mul, resUr_artinZHat hπ, ← galMaxUnramifiedEquiv_symm_apply,
    ContinuousMulEquiv.apply_symm_apply]

theorem resUr_eq_one_iff (σ : maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) :
    resUr p K Ω σ = 1 ↔ σ ∈ abInertia p K Ω := by
  rw [mem_abInertia]
  constructor
  · intro h y hy
    have h1 := DFunLike.congr_fun h ⟨y, hy⟩
    rw [AlgEquiv.one_apply] at h1
    have h2 := congrArg Subtype.val h1
    rw [resUr_apply] at h2
    exact Subtype.ext h2
  · intro h
    refine AlgEquiv.ext fun y ↦ ?_
    rw [AlgEquiv.one_apply]
    apply Subtype.ext
    rw [resUr_apply]
    exact congrArg Subtype.val (h _ y.2)

/-- The inertia group `Gal(K^ab/K^ur)` corresponds to `𝒪ˣ × 1`. -/
theorem galAbEquiv_snd_eq_one_iff {π : Kˣ} (hπ : v p (π : K) = 1)
    (σ : maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) :
    (galAbEquiv p K Ω hπ σ).2 = 1 ↔ σ ∈ abInertia p K Ω := by
  rw [galAbEquiv_snd, EmbeddingLike.map_eq_one_iff, resUr_eq_one_iff]

end PadicField
