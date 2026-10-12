/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.Duality

/-!
# The duality pairing and the Artin map

We prove that the cup product pairing of local duality computes the Artin map:

`⟨χ, a⟩ = χ(artin a)` for every character `χ : Gal(Ω/K) → ℤ/n` and `a ∈ Kˣ`
(`PadicField.pairing_eq_artinChar`),

where `χ(artin a)` is computed on the cyclic field `L_χ` cut out by `χ`
(`PadicField.artinChar χ a = χ̄(abRec_{L_χ} a)`). This is the "cup product description of the
reciprocity map" (Tate–Nakayama compatibility in degree two).

Proof: both sides are bilinear. For characters with unramified `L_χ` the identity follows from the
explicit unramified computation (`inv(cupClass(Frob, a)) = v(a)/d`) and the change of generator
formula `cupClass(σ, a) = cupClass(τ, a^{idx_σ τ})` (`Brauer.cupClass_eq_of_gen`). For a uniformiser
`π` and an arbitrary `χ`, subtract the unramified character `φ` with `φ(Frob) = χ(artin π)`: then
`π` is a norm from `L_{χ - φ}`, so `⟨χ - φ, π⟩ = 0 = (χ - φ)(artin π)`. Uniformisers generate `Kˣ`.
-/

open ContH2 Finset

set_option linter.unusedSectionVars false

namespace ContH2

/-- `∑_{j < d} ⌊(j + w)/d⌋ = w` for `w < d`. -/
theorem sum_range_add_div {d w : ℕ} (hw : w < d) : ∑ j ∈ range d, (j + w) / d = w := by
  have h : ∀ j ∈ range d, (j + w) / d = if d ≤ j + w then 1 else 0 := by
    intro j hj
    rw [mem_range] at hj
    split_ifs with h
    · exact Nat.div_eq_of_lt_le (by omega) (by omega)
    · exact Nat.div_eq_of_lt (by omega)
  rw [sum_congr rfl h, sum_boole]
  have : (range d).filter (fun j => d ≤ j + w) = Ico (d - w) d := by
    ext j
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [this, Nat.card_Ico]
  push_cast
  omega

variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]

omit [MulDistribMulAction G M] in
/-- **Change of generator**: `Φ_τ(cup_σ(a)) = a^{idx_σ τ}`. -/
theorem phiFun_cupFun_of_gen (σ τ : G) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (hτ : ∀ g, g ∈ Subgroup.zpowers τ) (a : M) :
    phiFun τ (cupFun σ hσ a) = a ^ idx σ hσ τ := by
  have hστ : orderOf τ = orderOf σ := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, orderOf_eq_card_of_forall_mem_zpowers hτ]
  simp only [phiFun, cupFun]
  rw [prod_range_pow τ hτ (fun g => a ^ ((idx σ hσ g + idx σ hσ τ) / orderOf σ)),
    ← prod_range_pow σ hσ (fun g => a ^ ((idx σ hσ g + idx σ hσ τ) / orderOf σ))]
  rw [prod_congr rfl fun j hj => by rw [idx_pow σ hσ (mem_range.1 hj)], prod_pow_eq_pow_sum,
    sum_range_add_div (idx_lt σ hσ τ)]

end ContH2



namespace Brauer

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Change of generator for carry classes: `cup_σ(a) = cup_τ(a^{idx_σ τ})`. -/
theorem cupClass_eq_of_gen (σ τ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (hτ : ∀ g, g ∈ Subgroup.zpowers τ) (hn : 1 < orderOf τ) (a : Kˣ) :
    cupClass σ hσ a = cupClass τ hτ (a ^ idx σ hσ τ) := by
  apply (relCyclicEquiv τ hτ).injective
  rw [relCyclicEquiv_cupClass τ hτ hn, cupClass, relCyclicEquiv_mk]
  congr 1
  apply Units.ext
  apply (algebraMap K L).injective
  rw [algebraMap_phiUnits]
  change ((phiFun τ (cupFun σ hσ (fixedUnitsEquiv K L a : Lˣ)) : Lˣ) : L) = _
  rw [phiFun_cupFun_of_gen σ τ hσ hτ, Units.val_pow_eq_pow_val, coe_fixedUnitsEquiv,
    Units.val_pow_eq_pow_val, map_pow]

end Brauer

namespace PadicField

open Brauer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

/-- The invariant of the inflated class of `a` for any unramified `L ⊆ Ω`. -/
theorem invEquiv_infl_unrClass (L : IntermediateField K Ω) [FiniteDimensional K L] [IsGalois K L]
    (h : IsUnramified p K L) (a : Kˣ) :
    invEquiv p K Ω (infl L (unrClass h a)) = vQZ p K (Module.finrank K L) a := by
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank K L = d := ⟨_, rfl⟩
  have hd0 : 0 < d := hd ▸ Module.finrank_pos
  have hL := h.eq_unramifiedOfDegree hd
  subst hL
  rw [invEquiv_infl hd0]
  exact invUnr_unrClass _ a

/-- The reciprocity map of an unramified `L ⊆ Ω` is `a ↦ Frob^{v(a)}`. -/
theorem abRec_unramified (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] (h : IsUnramified p K L) (a : Kˣ) :
    abRec p L a = frob h ^ v p (a : K) := by
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank K L = d := ⟨_, rfl⟩
  have hd0 : 0 < d := hd ▸ Module.finrank_pos
  have hL := h.eq_unramifiedOfDegree hd
  subst hL
  haveI : IsCyclic (unramifiedOfDegree p K Ω d ≃ₐ[K] unramifiedOfDegree p K Ω d) :=
    isCyclic_gal h
  rw [abRec_eq_cycRec, cycRec_unramified hd0]

section ArtinChar

variable (n : ℕ) [NeZero n]

instance (χ : LocChar K Ω n) : IsCyclic (charField n χ ≃ₐ[K] charField n χ) :=
  isCyclic_of_injective (charBar n χ) (charBar_injective n χ)

instance (χ : LocChar K Ω n) : IsAbelianGalois K (charField n χ) := .of_isCyclic K _

/-- `χ(artin a)`, computed on the cyclic field of `χ`. -/
noncomputable def artinChar (χ : LocChar K Ω n) (a : Kˣ) : ZMod n :=
  Multiplicative.toAdd (charBar n χ (abRec p (charField n χ) a))

theorem charField_le_maxAbelian (χ : LocChar K Ω n) : charField n χ ≤ maxAbelian K Ω :=
  le_maxAbelian ⟨charField n χ, inferInstance, inferInstance⟩

/-- A lift of `artin a` restricts to `abRec_E a` on every finite abelian `E ⊆ Ω`. -/
theorem restrictNormalHom_eq_abRec (E : IntermediateField K Ω) [FiniteDimensional K E]
    [IsAbelianGalois K E] (a : Kˣ) (g : Ω ≃ₐ[K] Ω)
    (hg : AlgEquiv.restrictNormalHom (maxAbelian K Ω) g = artin p K Ω a) :
    AlgEquiv.restrictNormalHom E g = abRec p E a := by
  ext y
  rw [AlgEquiv.restrictNormalHom_apply, ← artin_apply (p := p) a E y y.2, ← hg,
    AlgEquiv.restrictNormalHom_apply]

/-- `artinChar χ a = χ(g)` for any lift `g` of `artin a`. -/
theorem artinChar_eq (χ : LocChar K Ω n) (a : Kˣ) (g : Ω ≃ₐ[K] Ω)
    (hg : AlgEquiv.restrictNormalHom (maxAbelian K Ω) g = artin p K Ω a) :
    artinChar (p := p) n χ a = Multiplicative.toAdd (χ.1 g) := by
  rw [artinChar, ← charBar_restrict, restrictNormalHom_eq_abRec _ a g hg]

theorem exists_lift_artin (a : Kˣ) :
    ∃ g : Ω ≃ₐ[K] Ω, AlgEquiv.restrictNormalHom (maxAbelian K Ω) g = artin p K Ω a :=
  AlgEquiv.restrictNormalHom_surjective Ω _

theorem artinChar_mul_left (χ χ' : LocChar K Ω n) (a : Kˣ) :
    artinChar (p := p) n (χ * χ') a = artinChar (p := p) n χ a + artinChar (p := p) n χ' a := by
  obtain ⟨g, hg⟩ := exists_lift_artin (p := p) (Ω := Ω) a
  rw [artinChar_eq n _ a g hg, artinChar_eq n _ a g hg, artinChar_eq n _ a g hg,
    Subgroup.coe_mul, MonoidHom.mul_apply, toAdd_mul]

theorem artinChar_mul_right (χ : LocChar K Ω n) (a b : Kˣ) :
    artinChar (p := p) n χ (a * b) = artinChar (p := p) n χ a + artinChar (p := p) n χ b := by
  simp only [artinChar, map_mul, toAdd_mul]

/-- **Unramified case**: `⟨χ, a⟩ = χ(artin a)` when `L_χ` is unramified. -/
theorem pairing_eq_artinChar_of_isUnramified (χ : LocChar K Ω n)
    (h : IsUnramified p K (charField n χ)) (a : Kˣ) :
    pairing (p := p) n χ a = artinChar (p := p) n χ a := by
  set L := charField n χ
  set σ₀ := charGen n χ
  have hσ₀ := mem_zpowers_charGen n χ
  have hcard : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hdvd := (exists_charBar_eq n χ).1
  by_cases hd : 1 < orderOf σ₀
  · set Fr := frob h
    have hFr := mem_zpowers_frob h
    have hFr1 : 1 < orderOf Fr := by
      rw [orderOf_frob, ← hcard, ← orderOf_charGen]; exact hd
    set w := idx σ₀ hσ₀ Fr
    have e1 : Multiplicative.ofAdd (zmodToQZ n (pairing (p := p) n χ a)) =
        vQZ p K (Module.finrank K L) (a ^ w) := by
      rw [← invEquiv_toBr_cupKummerClass, toBr_cupKummerClass,
        carryClass_eq_infl n χ (rootK n a) a (rootK_pow n a),
        cupClass_eq_of_gen σ₀ Fr hσ₀ hFr hFr1,
        ← unrClass_eq_cupClass h (by rw [← orderOf_frob h]; exact hFr1),
        invEquiv_infl_unrClass L h]
    have hcb : charBar n χ Fr = Multiplicative.ofAdd (((w * (n / Nat.card (L ≃ₐ[K] L)) : ℕ) :
        ZMod n)) := by
      rw [← pow_idx σ₀ hσ₀ Fr, map_pow, charBar_charGen, ← ofAdd_nsmul, nsmul_eq_mul,
        Nat.cast_mul]
    have e2 : artinChar (p := p) n χ a =
        ((v p (a : K) * w * (n / Nat.card (L ≃ₐ[K] L) : ℕ) : ℤ) : ZMod n) := by
      rw [artinChar, abRec_unramified L h, map_zpow, hcb, ← ofAdd_zsmul, toAdd_ofAdd,
        zsmul_eq_mul]
      simp only [Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
      ring
    apply zmodToQZ_injective (Nat.pos_of_ne_zero (NeZero.ne n))
    rw [e2, zmodToQZ_intCast]
    have := congrArg Multiplicative.toAdd e1
    rw [toAdd_ofAdd] at this
    rw [this, vQZ_apply, toAdd_ofAdd, Units.val_pow_eq_pow_val, v_pow (Units.ne_zero a)]
    congr 1
    have hd0 : (Nat.card (L ≃ₐ[K] L) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
    have hnd : ((n / Nat.card (L ≃ₐ[K] L) : ℕ) : ℚ) = n / Nat.card (L ≃ₐ[K] L) := by
      rw [Nat.cast_div hdvd hd0]
    simp only [Int.cast_mul, Int.cast_natCast]
    rw [hnd, ← hcard]
    field_simp
  · have h1 : orderOf σ₀ = 1 := by
      have := orderOf_pos σ₀
      omega
    have hsub : ∀ g : L ≃ₐ[K] L, g = 1 := by
      intro g
      obtain ⟨k, -, rfl⟩ := exists_pow_eq_lt σ₀ hσ₀ g
      rw [orderOf_eq_one_iff.1 h1, one_pow]
    have hN : normGroup K L = ⊤ := by
      have := index_normGroup_charField p n χ
      rw [← orderOf_charGen, h1, Subgroup.index_eq_one] at this
      exact this
    rw [(pairing_eq_zero_iff n χ a).2 (hN ▸ Subgroup.mem_top a), artinChar,
      hsub (abRec p L a), map_one, toAdd_one]

theorem artinChar_one (a : Kˣ) : artinChar (p := p) n (1 : LocChar K Ω n) a = 0 := by
  have := artinChar_mul_left (p := p) n (1 : LocChar K Ω n) 1 a
  rw [mul_one] at this
  exact left_eq_add.1 this |>.symm ▸ rfl

theorem artinChar_inv (χ : LocChar K Ω n) (a : Kˣ) :
    artinChar (p := p) n χ⁻¹ a = -artinChar (p := p) n χ a := by
  have := artinChar_mul_left (p := p) n χ χ⁻¹ a
  rw [mul_inv_cancel, artinChar_one] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

theorem pairing_one (χ : LocChar K Ω n) : pairing (p := p) n χ 1 = 0 := by
  have := pairing_mul_right (p := p) n χ 1 1
  rw [mul_one] at this
  exact (left_eq_add.1 this)

/-- The character `Frob^k ↦ c · k` of `Gal(K_n/K)`. -/
noncomputable def unrHom (c : ZMod n) :
    (unramifiedOfDegree p K Ω n ≃ₐ[K] unramifiedOfDegree p K Ω n) →* Multiplicative (ZMod n) :=
  monoidHomOfForallMemZpowers (mem_zpowers_frob (isUnramified_unramifiedOfDegree p K Ω n))
    (g' := Multiplicative.ofAdd c) (by
      rw [orderOf_frob, finrank_unramifiedOfDegree p K Ω (Nat.pos_of_ne_zero (NeZero.ne n))]
      apply orderOf_dvd_of_pow_eq_one
      rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero])

theorem unrHom_frob (c : ZMod n) :
    unrHom (p := p) (K := K) (Ω := Ω) n c (frob (isUnramified_unramifiedOfDegree p K Ω n)) =
      Multiplicative.ofAdd c :=
  monoidHomOfForallMemZpowers_apply_gen _ _

/-- The unramified character `g ↦ c · k` where `g` acts on `K_n` as `Frob^k`. -/
noncomputable def unrChar (c : ZMod n) : LocChar K Ω n :=
  ⟨(unrHom (p := p) n c).comp (AlgEquiv.restrictNormalHom (unramifiedOfDegree p K Ω n)),
    show IsLocallyConstant ((unrHom (p := p) n c) ∘
      (AlgEquiv.restrictNormalHom (unramifiedOfDegree p K Ω n))) from
    ((IsLocallyConstant.iff_continuous _).2
      (InfiniteGalois.restrictNormalHom_continuous _)).comp _⟩

theorem unrChar_apply (c : ZMod n) (g : Ω ≃ₐ[K] Ω) :
    (unrChar (p := p) n c).1 g =
      unrHom (p := p) n c (AlgEquiv.restrictNormalHom (unramifiedOfDegree p K Ω n) g) := rfl

theorem charField_le_of_ker_le (χ : LocChar K Ω n) (E : IntermediateField K Ω) [Normal K E]
    (h : ∀ g : Ω ≃ₐ[K] Ω, AlgEquiv.restrictNormalHom E g = 1 → χ.1 g = 1) :
    charField n χ ≤ E := by
  intro y hy
  rw [← InfiniteGalois.fixedField_fixingSubgroup E]
  rintro ⟨σ, hσ⟩
  have hσ' : σ ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) E).ker := by
    rw [IntermediateField.restrictNormalHom_ker]; exact hσ
  exact hy ⟨σ, h σ hσ'⟩

theorem isUnramified_charField_unrChar (c : ZMod n) :
    IsUnramified p K (charField n (unrChar (p := p) (K := K) (Ω := Ω) n c)) := by
  refine (isUnramified_unramifiedOfDegree p K Ω n).of_le (charField_le_of_ker_le n _ _ ?_)
  intro g hg
  rw [unrChar_apply, hg, map_one]

theorem artinChar_unrChar {π : Kˣ} (hπ : v p (π : K) = 1) (c : ZMod n) :
    artinChar (p := p) n (unrChar (p := p) (Ω := Ω) n c) π = c := by
  obtain ⟨g, hg⟩ := exists_lift_artin (p := p) (Ω := Ω) π
  rw [artinChar_eq n _ π g hg, unrChar_apply, restrictNormalHom_eq_abRec _ π g hg,
    abRec_unramified _ (isUnramified_unramifiedOfDegree p K Ω n), hπ, zpow_one,
    unrHom_frob, toAdd_ofAdd]

/-- **Uniformisers**: `⟨χ, π⟩ = χ(artin π)`. -/
theorem pairing_eq_artinChar_of_v_eq_one (χ : LocChar K Ω n) {π : Kˣ}
    (hπ : v p (π : K) = 1) : pairing (p := p) n χ π = artinChar (p := p) n χ π := by
  set c := artinChar (p := p) n χ π
  set φ := unrChar (p := p) (K := K) (Ω := Ω) n c
  set χ' := χ * φ⁻¹
  have h1 : artinChar (p := p) n χ' π = 0 := by
    change artinChar (p := p) n (χ * φ⁻¹) π = 0
    rw [artinChar_mul_left, artinChar_inv, artinChar_unrChar n hπ, add_neg_cancel]
  have h2 : pairing (p := p) n χ' π = 0 := by
    rw [pairing_eq_zero_iff, ← ker_abRec (p := p), MonoidHom.mem_ker]
    apply charBar_injective n χ'
    rw [map_one]
    exact (ofAdd_toAdd _).symm.trans ((congrArg Multiplicative.ofAdd h1).trans ofAdd_zero)
  have hχ : χ = χ' * φ := by simp [χ']
  rw [hχ, pairing_mul_left, h2, zero_add,
    pairing_eq_artinChar_of_isUnramified n φ (isUnramified_charField_unrChar n c),
    artinChar_unrChar n hπ]

/-- **The cup product pairing computes the Artin map**: `⟨χ, a⟩ = χ(artin a)` for every
character `χ : Gal(Ω/K) → ℤ/n` and every `a ∈ Kˣ`. -/
theorem pairing_eq_artinChar (χ : LocChar K Ω n) (a : Kˣ) :
    pairing (p := p) n χ a = artinChar (p := p) n χ a := by
  let f₁ : Kˣ →* Multiplicative (ZMod n) :=
    { toFun := fun a => Multiplicative.ofAdd (pairing (p := p) n χ a)
      map_one' := by rw [pairing_one, ofAdd_zero]
      map_mul' := fun a b => by rw [pairing_mul_right, ofAdd_add] }
  let f₂ : Kˣ →* Multiplicative (ZMod n) :=
    { toFun := fun a => Multiplicative.ofAdd (artinChar (p := p) n χ a)
      map_one' := by rw [artinChar, map_one, map_one, toAdd_one, ofAdd_zero]
      map_mul' := fun a b => by rw [artinChar_mul_right, ofAdd_add] }
  have := monoidHom_ext_of_v_eq_one (p := p) (φ := f₁) (ψ := f₂) fun x hx => by
    simp only [f₁, f₂, MonoidHom.coe_mk, OneHom.coe_mk,
      pairing_eq_artinChar_of_v_eq_one n χ hx]
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun this a)

end ArtinChar

end PadicField
