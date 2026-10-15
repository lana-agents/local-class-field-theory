/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.ArtinPairing
import LocalClassFieldTheory.Brauer.CorBr
import LocalClassFieldTheory.Reciprocity.GaloisStructure

/-!
# The Artin map and the transfer (Verlagerung)

For a finite extension `K' ⊆ Ω` of `K` let `H = Gal(Ω/K') ≤ G = Gal(Ω/K)`. The **transfer**
`Ver : G → H^ab` is `g ↦ ∏_{c ∈ G/H} κ(c, g)` with `κ(c, g) = c.out⁻¹ g (g⁻¹ c).out ∈ H`
(`ContH2.transfer_eq_prod_kappa`: this is Mathlib's `MonoidHom.transfer`). We prove

* **`PadicField.artin_transfer`**: `artin_{K'}(a) = Ver(g)` in `Gal(K'^ab/K')` for every `a ∈ Kˣ`
  and every lift `g ∈ Gal(Ω/K)` of `artin_K(a)`, i.e. the square
  `Kˣ → Gal(K^ab/K)`, `K'ˣ → Gal(K'^ab/K')` with the inclusion `Kˣ ⊆ K'ˣ` and the transfer
  commutes (the transfer property of the reciprocity map).

Proof: for a character `χ'` of `Gal(Ω/K')` its corestriction `cor χ' = χ' ∘ Ver`
(`PadicField.corChar`) satisfies the projection formula
`cor(χ' ∪ κ(a)) = (cor χ') ∪ κ(a)` in `Br(K)`, at the level of carry cocycles
(`PadicField.corBr_carryClass`: the corestriction of the carry cocycle of `χ'` differs from the
carry cocycle of `cor χ'` by the coboundary of `g ↦ a^{⌊u(g)/n⌋}`, `u(g) = ∑_c χ̃'(κ(c, g))`).
With `inv_K ∘ cor = inv_{K'}` this gives `⟨cor χ', a⟩_K = ⟨χ', a⟩_{K'}`
(`PadicField.pairing_corChar`), and `⟨χ, a⟩ = χ(artin a)` (`PadicField.pairing_eq_artinChar`)
turns it into `χ'(artin_{K'} a) = χ'(Ver(g))` for all characters; characters of the finite
abelian quotients `Gal(E/K')` separate points.
-/

open ContH2 Brauer IntermediateField Finset

set_option linter.unusedSectionVars false

namespace ContH2

variable {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] {A : Type*} [CommGroup A]

/-- **The transfer as a product over cosets**: `Ver_ϕ(g) = ∏_c ϕ(κ(c, g))`. -/
theorem transfer_eq_prod_kappa [Fintype (G ⧸ H)] (ϕ : H →* A) (g : G) :
    ϕ.transfer g = ∏ c : G ⧸ H, ϕ (kappa H c g) := by
  classical
  let T : H.LeftTransversal :=
    ⟨Set.range Quotient.out, Subgroup.isComplement_range_left QuotientGroup.out_eq'⟩
  rw [MonoidHom.transfer_def ϕ T g, Subgroup.leftTransversals.diff]
  refine Finset.prod_congr (by congr; exact Subsingleton.elim _ _) fun c _ => congrArg ϕ ?_
  apply Subtype.ext
  have h1 := Subgroup.IsComplement.leftQuotientEquiv_apply (H := H) QuotientGroup.out_eq'
  simp only [Subgroup.smul_apply_eq_smul_apply_inv_smul, coe_kappa, smul_eq_mul, mul_assoc]
  change (T.2.leftQuotientEquiv c : G)⁻¹ * (g * (T.2.leftQuotientEquiv (g⁻¹ • c) : G)) = _
  rw [h1, h1]

end ContH2

namespace PadicField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
variable (K' : IntermediateField K Ω) [FiniteDimensional K K'] (n : ℕ) [NeZero n]

/-- The corestriction `H¹(K', ℤ/n) → H¹(K, ℤ/n)` of a character: `χ ∘ Ver`. -/
noncomputable def corChar (χ : (Ω ≃ₐ[K'] Ω) →* Multiplicative (ZMod n)) :
    (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n) :=
  (χ.comp (fixingSubgroupEquiv K').toMonoidHom).transfer

theorem corChar_apply (χ : (Ω ≃ₐ[K'] Ω) →* Multiplicative (ZMod n)) (g : Ω ≃ₐ[K] Ω) :
    corChar K' n χ g =
      ∏ c : (Ω ≃ₐ[K] Ω) ⧸ K'.fixingSubgroup,
        χ (fixingSubgroupEquiv K' (kappa K'.fixingSubgroup c g)) :=
  transfer_eq_prod_kappa _ _ g

/-- `u(g) = ∑_c χ̃(κ(c, g)) ∈ ℕ`, the integral lift of `(cor χ)(g)`. -/
noncomputable def uSum (χ : (Ω ≃ₐ[K'] Ω) →* Multiplicative (ZMod n)) (g : Ω ≃ₐ[K] Ω) : ℕ :=
  ∑ c : (Ω ≃ₐ[K] Ω) ⧸ K'.fixingSubgroup,
    chiExp n χ (fixingSubgroupEquiv K' (kappa K'.fixingSubgroup c g))

theorem chiExp_corChar (χ : (Ω ≃ₐ[K'] Ω) →* Multiplicative (ZMod n)) (g : Ω ≃ₐ[K] Ω) :
    chiExp n (corChar K' n χ) g = uSum K' n χ g % n := by
  rw [chiExp, corChar_apply, uSum, toAdd_prod, ← ZMod.val_natCast]
  congr 1
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [chiExp, ZMod.natCast_zmod_val]

theorem uSum_add (χ : (Ω ≃ₐ[K'] Ω) →* Multiplicative (ZMod n)) (g h : Ω ≃ₐ[K] Ω) :
    uSum K' n χ g + uSum K' n χ h =
      n * ∑ c : (Ω ≃ₐ[K] Ω) ⧸ K'.fixingSubgroup,
        (chiExp n χ (fixingSubgroupEquiv K' (kappa K'.fixingSubgroup c g)) +
          chiExp n χ (fixingSubgroupEquiv K' (kappa K'.fixingSubgroup (g⁻¹ • c) h))) / n +
      uSum K' n χ (g * h) := by
  have hre : uSum K' n χ h = ∑ c : (Ω ≃ₐ[K] Ω) ⧸ K'.fixingSubgroup,
      chiExp n χ (fixingSubgroupEquiv K' (kappa K'.fixingSubgroup (g⁻¹ • c) h)) :=
    (Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun _ => rfl).symm
  rw [hre, uSum, uSum, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [kappa_mul, map_mul, chiExp_mul]
  exact (Nat.div_add_mod _ _).symm

theorem isLocallyConstant_uSum {χ : (Ω ≃ₐ[K'] Ω) →* Multiplicative (ZMod n)}
    (hχ : IsLocallyConstant χ) : IsLocallyConstant (uSum K' n χ) := by
  have h : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω =>
      ∏ c : (Ω ≃ₐ[K] Ω) ⧸ K'.fixingSubgroup,
        Multiplicative.ofAdd (chiExp n χ (fixingSubgroupEquiv K' (kappa K'.fixingSubgroup c g))) :=
    isLocallyConstant_prod _ _ fun c _ =>
      ((isLocallyConstant_chiExp n hχ).comp_continuous ((continuous_fixingSubgroupEquiv K').comp
        (continuous_kappa K'.fixingSubgroup_isOpen c))).comp _
  convert h.comp Multiplicative.toAdd using 1
  funext g
  simp only [Function.comp_apply, toAdd_prod, toAdd_ofAdd, uSum]

theorem isLocallyConstant_corChar {χ : (Ω ≃ₐ[K'] Ω) →* Multiplicative (ZMod n)}
    (hχ : IsLocallyConstant χ) : IsLocallyConstant (corChar K' n χ) := by
  have h : IsLocallyConstant fun g : Ω ≃ₐ[K] Ω =>
      ∏ c : (Ω ≃ₐ[K] Ω) ⧸ K'.fixingSubgroup,
        χ (fixingSubgroupEquiv K' (kappa K'.fixingSubgroup c g)) :=
    isLocallyConstant_prod _ _ fun c _ =>
      hχ.comp_continuous ((continuous_fixingSubgroupEquiv K').comp
        (continuous_kappa K'.fixingSubgroup_isOpen c))
  convert h using 1
  funext g
  exact corChar_apply K' n χ g

/-- The integer identity behind the projection formula. -/
theorem carry_exponent_eq (χ : (Ω ≃ₐ[K'] Ω) →* Multiplicative (ZMod n)) (g h : Ω ≃ₐ[K] Ω) :
    (∑ c : (Ω ≃ₐ[K] Ω) ⧸ K'.fixingSubgroup,
        (chiExp n χ (fixingSubgroupEquiv K' (kappa K'.fixingSubgroup c g)) +
          chiExp n χ (fixingSubgroupEquiv K' (kappa K'.fixingSubgroup (g⁻¹ • c) h))) / n) +
      uSum K' n χ (g * h) / n =
    (chiExp n (corChar K' n χ) g + chiExp n (corChar K' n χ) h) / n +
      uSum K' n χ h / n + uSum K' n χ g / n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have e1 := uSum_add K' n χ g h
  have e2 : ∀ x, uSum K' n χ x = n * (uSum K' n χ x / n) + chiExp n (corChar K' n χ) x :=
    fun x => by rw [chiExp_corChar]; exact (Nat.div_add_mod _ _).symm
  have e3 := Nat.div_add_mod (chiExp n (corChar K' n χ) g + chiExp n (corChar K' n χ) h) n
  rw [← chiExp_mul] at e3
  apply Nat.eq_of_mul_eq_mul_left hn
  rw [e2 g, e2 h, e2 (g * h)] at e1
  simp only [mul_add]
  linarith

variable [Algebra.IsIntegral K Ω]

/-- **The projection formula for carry cocycles**: the corestriction of the carry cocycle of `χ`
is the carry cocycle of `cor χ` times the coboundary of `g ↦ A^{⌊u(g)/n⌋}`. -/
theorem corFun_carryFun (χ : (Ω ≃ₐ[K'] Ω) →* Multiplicative (ZMod n)) (A : Ωˣ)
    (hA : ∀ σ : Ω ≃ₐ[K] Ω, σ • A = A) (g h : Ω ≃ₐ[K] Ω) :
    corFun K'.fixingSubgroup
        (fun x => carryFun n χ A (fixingSubgroupEquiv K' x.1, fixingSubgroupEquiv K' x.2)) (g, h) =
      carryFun n (corChar K' n χ) A (g, h) *
        dx _ _ (fun x => A ^ (uSum K' n χ x / n)) (g, h) := by
  have hAp : ∀ (σ : Ω ≃ₐ[K] Ω) (k : ℕ), σ • A ^ k = A ^ k := fun σ k => by
    rw [smul_pow', hA]
  simp only [corFun_apply, dx_apply, carryFun, hAp, Finset.prod_pow_eq_pow_sum]
  apply mul_right_cancel (b := A ^ (uSum K' n χ (g * h) / n))
  rw [← pow_add, carry_exponent_eq, pow_add, pow_add]
  mul_abel

/-- **The projection formula** `cor(χ ∪ κ(a)) = (cor χ) ∪ κ(a)` for `a ∈ Kˣ`, in the form of
carry classes: `cor_{K'/K}` of the carry class of `χ` and `αⁿ = a` is the carry class of `cor χ`
and `αⁿ`. -/
theorem corBr_carryClass (χ : (Ω ≃ₐ[K'] Ω) →* Multiplicative (ZMod n))
    (hχ : IsLocallyConstant χ) (α : Ωˣ) (hα' : ∀ σ : Ω ≃ₐ[K'] Ω, σ • α ^ n = α ^ n)
    (hα : ∀ σ : Ω ≃ₐ[K] Ω, σ • α ^ n = α ^ n) :
    corBr K' (carryClass n χ hχ α hα') =
      carryClass n (corChar K' n χ) (isLocallyConstant_corChar K' n hχ) α hα := by
  rw [corBr, MonoidHom.comp_apply, carryClass, carryClass]
  change cor K'.fixingSubgroup K'.fixingSubgroup_isOpen (mk _) = _
  rw [cor_mk, mk_eq_mk_iff]
  refine ⟨fun x => (α ^ n) ^ (uSum K' n χ x / n),
    (isLocallyConstant_uSum K' n hχ).comp fun k => (α ^ n) ^ (k / n), ?_⟩
  funext ⟨g, h⟩
  rw [Pi.div_apply]
  change _ = corFun K'.fixingSubgroup
      (fun x => carryFun n χ (α ^ n) (fixingSubgroupEquiv K' x.1, fixingSubgroupEquiv K' x.2))
      (g, h) / carryFun n (corChar K' n χ) (α ^ n) (g, h)
  rw [corFun_carryFun K' n χ (α ^ n) hα, mul_div_cancel_left]

section Padic

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
variable (K' : IntermediateField K Ω) [FiniteDimensional K K'] (n : ℕ) [NeZero n]

/-- The corestriction of a locally constant character. -/
noncomputable def corLocChar (χ : LocChar K' Ω n) : LocChar K Ω n :=
  ⟨corChar K' n χ.1, isLocallyConstant_corChar K' n χ.2⟩

/-- **`⟨cor χ, a⟩_K = ⟨χ, a⟩_{K'}`** for `a ∈ Kˣ` (projection formula and `inv ∘ cor = inv`). -/
theorem pairing_corLocChar (χ : LocChar K' Ω n) (a : Kˣ) :
    pairing (p := p) n (corLocChar K' n χ) a =
      pairing (p := p) n χ (Units.map (algebraMap K K' : K →* K') a) := by
  apply zmodToQZ_injective (Nat.pos_of_ne_zero (NeZero.ne n))
  apply Multiplicative.ofAdd.injective
  rw [← invEquiv_toBr_cupKummerClass, ← invEquiv_toBr_cupKummerClass, toBr_cupKummerClass,
    toBr_cupKummerClass]
  set a' : K'ˣ := Units.map (algebraMap K K' : K →* K') a
  have hroot : rootK (Ω := Ω) n a' ^ n = Units.map (algebraMap K Ω : K →* Ω) a := by
    rw [rootK_pow]
    ext
    simp [a', ← IsScalarTower.algebraMap_apply]
  rw [← invEquiv_corBr K', corBr_carryClass K' n χ.1 χ.2 _ _ (pow_smul_eq_of_pow_eq n hroot)]
  congr 1

/-- A product of images in a commutative group is the image of an ordered product. -/
theorem prod_comp_eq_map_prod {ι G B : Type*} [Fintype ι] [Group G] [CommGroup B] (f : G →* B)
    (σ : ι → G) : ∏ c, f (σ c) = f ((Finset.univ.toList.map σ).prod) := by
  rw [← Finset.prod_map_toList, show (fun c => f (σ c)) = f ∘ σ from rfl, ← List.map_map,
    ← map_list_prod]

/-- Characters `X → ℤ/m` separate the points of a finite abelian group. -/
theorem eq_of_forall_char {X : Type*} [CommGroup X] [Finite X] {x y : X}
    (h : ∀ (m : ℕ) [NeZero m] (ψ : X →* Multiplicative (ZMod m)), ψ x = ψ y) : x = y := by
  by_contra hxy
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite X
  obtain ⟨i, hi⟩ : ∃ i, e x i ≠ e y i := by
    by_contra hall
    push Not at hall
    exact hxy (e.injective (funext hall))
  haveI : NeZero (n i) := ⟨(zero_lt_one.trans (hn i)).ne'⟩
  exact hi (h (n i) ((Pi.evalMonoidHom (fun i => Multiplicative (ZMod (n i))) i).comp
    e.toMonoidHom))

variable (p) in
/-- `Gal(K^ab/K)` as a commutative group. -/
noncomputable abbrev galAbCommGroup (K : Type*) [Field K] [Algebra ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] (Ω : Type*) [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω]
    [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] [IsGalois K Ω] :
    CommGroup (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) :=
  { (inferInstance : Group (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω)) with
    mul_comm := gal_maxAbelian_mul_comm }

variable (p) in
/-- **The transfer** `Ver : Gal(Ω/K) → Gal(K'^ab/K')`, the transfer to `Gal(Ω/K') ≤ Gal(Ω/K)`
followed by restriction to `K'^ab`. -/
noncomputable def ver : (Ω ≃ₐ[K] Ω) →* (maxAbelian K' Ω ≃ₐ[K'] maxAbelian K' Ω) :=
  letI := galAbCommGroup p K' Ω
  ((AlgEquiv.restrictNormalHom (maxAbelian K' Ω)).comp
    (fixingSubgroupEquiv K').toMonoidHom).transfer

/-- **The Artin map commutes with the transfer**: for `a ∈ Kˣ` and any lift `g ∈ Gal(Ω/K)` of
`artin_K(a) ∈ Gal(K^ab/K)`, `artin_{K'}(a) = Ver(g)` in `Gal(K'^ab/K')`. -/
theorem artin_transfer (a : Kˣ) (g : Ω ≃ₐ[K] Ω)
    (hg : AlgEquiv.restrictNormalHom (maxAbelian K Ω) g = artin p K Ω a) :
    artin p K' Ω (Units.map (algebraMap K K' : K →* K') a) = ver p K' g := by
  set a' : K'ˣ := Units.map (algebraMap K K' : K →* K') a
  obtain ⟨g', hg'⟩ := exists_lift_artin (p := p) (Ω := Ω) a'
  set σ : (Ω ≃ₐ[K] Ω) ⧸ K'.fixingSubgroup → (Ω ≃ₐ[K'] Ω) :=
    fun c => fixingSubgroupEquiv K' (kappa K'.fixingSubgroup c g)
  -- the character identity `χ(g') = (cor χ)(g)`
  have key : ∀ (m : ℕ) [NeZero m] (χ : LocChar K' Ω m), χ.1 g' = ∏ c, χ.1 (σ c) := by
    intro m _ χ
    apply Multiplicative.toAdd.injective
    rw [← artinChar_eq m χ a' g' hg', ← pairing_eq_artinChar, ← pairing_corLocChar,
      pairing_eq_artinChar, artinChar_eq m _ a g hg]
    exact congrArg Multiplicative.toAdd (corChar_apply K' m χ.1 g)
  -- products of restrictions are restrictions of an ordered product
  let τ : Ω ≃ₐ[K'] Ω := ((Finset.univ : Finset ((Ω ≃ₐ[K] Ω) ⧸ K'.fixingSubgroup)).toList.map σ).prod
  letI := galAbCommGroup p K' Ω
  have hver : ver p K' g = AlgEquiv.restrictNormalHom (maxAbelian K' Ω) τ := by
    rw [ver, transfer_eq_prod_kappa]
    exact prod_comp_eq_map_prod (AlgEquiv.restrictNormalHom (maxAbelian K' Ω)) σ
  rw [← hg', hver]
  ext z
  obtain ⟨E, hzE⟩ := mem_maxAbelian_iff.1 z.2
  -- on the finite abelian `E`, the restrictions of `g'` and `τ` agree
  letI : CommGroup (E.1 ≃ₐ[K'] E.1) :=
    { (inferInstance : Group (E.1 ≃ₐ[K'] E.1)) with mul_comm := mul_comm' }
  have hE : AlgEquiv.restrictNormalHom E.1 g' = AlgEquiv.restrictNormalHom E.1 τ := by
    refine eq_of_forall_char fun m _ ψ => ?_
    let χ : LocChar K' Ω m := ⟨ψ.comp (AlgEquiv.restrictNormalHom E.1),
      (IsLocallyConstant.of_discrete ψ).comp_continuous
        (InfiniteGalois.restrictNormalHom_continuous E.1)⟩
    have := key m χ
    rw [prod_comp_eq_map_prod χ.1 σ] at this
    exact this
  have h1 := congrArg (fun φ : E.1 ≃ₐ[K'] E.1 => (φ ⟨z, hzE⟩ : Ω)) hE
  simp only [AlgEquiv.restrictNormalHom_apply] at h1 ⊢
  exact h1

end Padic

end PadicField
