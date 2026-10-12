/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.KummerH2

/-!
# The cup product pairing `H¹(K, ℤ/n) × H¹(K, μ_n) → H²(K, μ_n)`

For a locally constant character `χ : Gal(Ω/K) → ℤ/n` and a `μ_n`-valued 1-cocycle `ζ` we define
the cup product cocycle `(χ ∪ ζ)(g, h) = (g • ζ(h))^{χ(g)}` (`Brauer.cupKummerFun`). For the Kummer
cocycle `ζ(h) = hα/α` of `a = αⁿ ∈ Kˣ` we show (`Brauer.toBr_mk_cupKummer`) that in `Br(K)`

`χ ∪ κ(a) = [(g, h) ↦ a^{⌊(χ̃(g) + χ̃(h))/n⌋}]` (`Brauer.carryFun`),

where `χ̃(g) ∈ [0, n)` lifts `χ(g)`: indeed `χ ∪ dα` differs from the carry cocycle by the
coboundary of `g ↦ (gα)^{-χ̃(g)}`.
-/

open ContH2 groupCohomology KummerTheory

set_option linter.unusedSectionVars false

namespace Brauer

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (n : ℕ)

/-- The exponent `χ̃(g) ∈ [0, n)` of a character `χ : G → ℤ/n`. -/
def chiExp (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)) (g : Ω ≃ₐ[K] Ω) : ℕ :=
  (Multiplicative.toAdd (χ g)).val

theorem chiExp_mul [NeZero n] (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)) (g h : Ω ≃ₐ[K] Ω) :
    chiExp n χ (g * h) = (chiExp n χ g + chiExp n χ h) % n := by
  simp only [chiExp, map_mul, toAdd_mul, ZMod.val_add]

theorem mu_pow_mod (x : Mu n Ω) (m : ℕ) : x ^ (m % n) = x ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul]
  apply Mu.ext
  simp only [map_mul, map_pow, Mu.val_pow_n, one_pow, one_mul]

/-- The cup product `(χ ∪ ζ)(g, h) = (g • ζ(h))^{χ(g)}`. -/
def cupKummerFun (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)) (ζ : (Ω ≃ₐ[K] Ω) → Mu n Ω) :
    (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → Mu n Ω :=
  fun gh => (gh.1 • ζ gh.2) ^ chiExp n χ gh.1

theorem isMulCocycle₂_cupKummerFun [NeZero n] (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n))
    {ζ : (Ω ≃ₐ[K] Ω) → Mu n Ω} (hζ : IsMulCocycle₁ ζ) : IsMulCocycle₂ (cupKummerFun n χ ζ) := by
  intro g h k
  simp only [cupKummerFun]
  rw [chiExp_mul, mu_pow_mod, hζ h k, smul_mul', smul_pow', mul_smul, mul_pow, pow_add]
  ac_rfl

/-- The algebraic identity behind `χ ∪ dα = carry · dy`. -/
theorem carry_identity {M : Type*} [CommGroup M] (w u A : M) {n cg ch cgh q : ℕ}
    (hA : A = w ^ n) (hsum : cg + ch = n * q + cgh) :
    (w / u) ^ cg = A ^ q * (w ^ (-(ch : ℤ)) / w ^ (-(cgh : ℤ)) * u ^ (-(cg : ℤ))) := by
  subst hA
  have h : (cg : ℤ) = n * q + cgh - ch := by omega
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_zpow]
  module

/-- The carry cocycle `(g, h) ↦ A^{⌊(χ̃(g) + χ̃(h))/n⌋}`. -/
def carryFun (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)) (A : Ωˣ) :
    (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → Ωˣ :=
  fun gh => A ^ ((chiExp n χ gh.1 + chiExp n χ gh.2) / n)

/-- The cochain `g ↦ (gα)^{-χ̃(g)}`. -/
def yFun (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)) (α : Ωˣ) : (Ω ≃ₐ[K] Ω) → Ωˣ :=
  fun g => (g • α) ^ (-(chiExp n χ g : ℤ))

theorem val_cupKummerFun_kummer [NeZero n] (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n))
    (α : Ωˣ) (hα : ∀ σ : Ω ≃ₐ[K] Ω, σ • α ^ n = α ^ n) (g h : Ω ≃ₐ[K] Ω) :
    Mu.val (cupKummerFun n χ (kummerFun α hα) (g, h)) =
      carryFun n χ (α ^ n) (g, h) * dx _ _ (yFun n χ α) (g, h) := by
  simp only [cupKummerFun, carryFun, yFun, dx_apply, map_pow, Mu.val_smul, val_kummerFun,
    smul_div', smul_zpow', ← mul_smul]
  refine carry_identity (n := n) _ _ _ ?_ ?_
  · rw [← smul_pow', hα]
  · rw [chiExp_mul, Nat.div_add_mod]

variable (K Ω) in
/-- Locally constant characters `Gal(Ω/K) → ℤ/n`, i.e. `H¹(K, ℤ/n)`. -/
def LocChar : Subgroup ((Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)) where
  carrier := {χ | IsLocallyConstant χ}
  mul_mem' ha hb := ha.mul hb
  one_mem' := IsLocallyConstant.const 1
  inv_mem' ha := ha.inv

theorem isLocallyConstant_chiExp {χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)}
    (hχ : IsLocallyConstant χ) : IsLocallyConstant (chiExp n χ) :=
  hχ.comp _

theorem isLocallyConstant_carryFun {χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)}
    (hχ : IsLocallyConstant χ) (A : Ωˣ) : IsLocallyConstant (carryFun n χ A) := by
  have h1 := (isLocallyConstant_chiExp n hχ).comp_continuous
    (continuous_fst (X := Ω ≃ₐ[K] Ω) (Y := Ω ≃ₐ[K] Ω))
  have h2 := (isLocallyConstant_chiExp n hχ).comp_continuous
    (continuous_snd (X := Ω ≃ₐ[K] Ω) (Y := Ω ≃ₐ[K] Ω))
  exact ((h1.prodMk h2).comp fun c => A ^ ((c.1 + c.2) / n))

variable [Algebra.IsIntegral K Ω]

theorem isLocallyConstant_yFun {χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)}
    (hχ : IsLocallyConstant χ) (α : Ωˣ) : IsLocallyConstant (yFun n χ α) :=
  ((isLocallyConstant_smul_units α).prodMk (isLocallyConstant_chiExp n hχ)).comp
    fun c => c.1 ^ (-(c.2 : ℤ))

theorem isLocallyConstant_smul_mu (m : Mu n Ω) :
    IsLocallyConstant fun g : Ω ≃ₐ[K] Ω => g • m :=
  isLocallyConstant_mu n (isLocallyConstant_smul_units (Mu.val m))

theorem isLocallyConstant_cupKummerFun {χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)}
    (hχ : IsLocallyConstant χ) {ζ : (Ω ≃ₐ[K] Ω) → Mu n Ω} (hζ : IsLocallyConstant ζ) :
    IsLocallyConstant (cupKummerFun n χ ζ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨g, h⟩
  have e1 : ∀ᶠ q : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) in nhds (g, h), ζ q.2 = ζ h :=
    (continuous_snd.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq ζ).1 hζ h)
  have e2 : ∀ᶠ q : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) in nhds (g, h), chiExp n χ q.1 = chiExp n χ g :=
    (continuous_fst.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq _).1 (isLocallyConstant_chiExp n hχ) g)
  have e3 : ∀ᶠ q : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) in nhds (g, h), q.1 • ζ h = g • ζ h :=
    (continuous_fst.continuousAt (x := (g, h))).eventually
      ((IsLocallyConstant.iff_eventually_eq _).1 (isLocallyConstant_smul_mu n (ζ h)) g)
  filter_upwards [e1, e2, e3] with q h1 h2 h3
  simp only [cupKummerFun, h1, h2, h3]

/-- The cup product of a character and a locally constant `μ_n`-valued 1-cocycle. -/
def cupKummer [NeZero n] (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)) (hχ : IsLocallyConstant χ)
    (ζ : (Ω ≃ₐ[K] Ω) → Mu n Ω) (hζ : IsLocallyConstant ζ) (hζc : IsMulCocycle₁ ζ) :
    cocycles (Ω ≃ₐ[K] Ω) (Mu n Ω) :=
  mkCocycle (cupKummerFun n χ ζ) (isLocallyConstant_cupKummerFun n hχ hζ)
    (isMulCocycle₂_cupKummerFun n χ hζc)

theorem isLocallyConstant_kummerFun (α : Ωˣ) (hα : ∀ σ : Ω ≃ₐ[K] Ω, σ • α ^ n = α ^ n) :
    IsLocallyConstant (kummerFun α hα) :=
  (IsLocallyConstant.iff_continuous _).2 (continuous_kummerFun α hα)

omit [Algebra.IsIntegral K Ω] in
theorem carryFun_eq [NeZero n] (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)) (α : Ωˣ)
    (hα : ∀ σ : Ω ≃ₐ[K] Ω, σ • α ^ n = α ^ n) :
    carryFun n χ (α ^ n) = (fun gh => Mu.val (cupKummerFun n χ (kummerFun α hα) gh)) *
      dx _ _ (yFun n χ α)⁻¹ := by
  funext gh
  obtain ⟨g, h⟩ := gh
  rw [Pi.mul_apply, val_cupKummerFun_kummer, dx_inv, Pi.inv_apply, mul_inv_cancel_right]

omit [Algebra.IsIntegral K Ω] in
/-- The carry function is a cocycle (it is cohomologous to `χ ∪ κ`). -/
theorem isMulCocycle₂_carryFun [NeZero n] (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n))
    (α : Ωˣ) (hα : ∀ σ : Ω ≃ₐ[K] Ω, σ • α ^ n = α ^ n) :
    IsMulCocycle₂ (carryFun n χ (α ^ n)) := by
  rw [carryFun_eq n χ α hα]
  refine isMulCocycle₂_mul ?_ (isMulCocycle₂_dx _)
  exact isMulCocycle₂_mapFun (MonoidHom.id (Ω ≃ₐ[K] Ω)) Mu.val (fun _ _ => rfl)
    (isMulCocycle₂_cupKummerFun n χ (isMulCocycle₁_kummerFun α hα))

/-- The carry class in `Br(K)`. -/
def carryClass [NeZero n] (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n))
    (hχ : IsLocallyConstant χ) (α : Ωˣ) (hα : ∀ σ : Ω ≃ₐ[K] Ω, σ • α ^ n = α ^ n) : Br K Ω :=
  mk (mkCocycle (carryFun n χ (α ^ n)) (isLocallyConstant_carryFun n hχ _)
    (isMulCocycle₂_carryFun n χ α hα))

/-- **The cup product with a Kummer class is the carry class**:
`χ ∪ κ(αⁿ) = [(g, h) ↦ (αⁿ)^{⌊(χ̃ g + χ̃ h)/n⌋}]` in `Br(K)`. -/
theorem toBr_mk_cupKummer [NeZero n] (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n))
    (hχ : IsLocallyConstant χ) (α : Ωˣ) (hα : ∀ σ : Ω ≃ₐ[K] Ω, σ • α ^ n = α ^ n) :
    toBr n (mk (cupKummer n χ hχ (kummerFun α hα) (isLocallyConstant_kummerFun n α hα)
      (isMulCocycle₁_kummerFun α hα))) = carryClass n χ hχ α hα := by
  rw [toBr_mk, carryClass, mk_eq_mk_iff]
  refine ⟨yFun n χ α, isLocallyConstant_yFun n hχ α, funext fun gh => ?_⟩
  obtain ⟨g, h⟩ := gh
  rw [Pi.div_apply, cocyclesMap_apply, coe_mkCocycle, MonoidHom.id_apply, MonoidHom.id_apply]
  change _ = Mu.val (cupKummerFun n χ (kummerFun α hα) (g, h)) / _
  rw [val_cupKummerFun_kummer, mul_div_cancel_left]

/-- An injective character `C → ℤ/n` of a finite group of order `d` hits `n/d`. -/
theorem exists_eq_div_of_injective {C : Type*} [Group C] [Finite C] {n : ℕ} [NeZero n]
    (ψ : C →* Multiplicative (ZMod n)) (hψ : Function.Injective ψ) :
    Nat.card C ∣ n ∧ ∃ σ : C, ψ σ = Multiplicative.ofAdd ((n / Nat.card C : ℕ) : ZMod n) := by
  classical
  set d := Nat.card C with hd
  have hcard : Nat.card ψ.range = d := by
    rw [hd]; exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  have hdvd : d ∣ n := by
    have := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [hcard, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at this
  refine ⟨hdvd, ?_⟩
  have hd0 : 0 < d := Nat.card_pos
  set x : Multiplicative (ZMod n) := Multiplicative.ofAdd ((n / d : ℕ) : ZMod n)
  have hx : x ^ d = 1 := by
    rw [← ofAdd_nsmul, nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hdvd, ZMod.natCast_self,
      ofAdd_zero]
  let T : Finset (Multiplicative (ZMod n)) := Finset.univ.filter fun y => y ^ d = 1
  have hT : T.card ≤ d := IsCyclic.card_pow_eq_one_le hd0
  have hST : (ψ.range : Set (Multiplicative (ZMod n))).toFinset ⊆ T := by
    intro y hy
    rw [Set.mem_toFinset, SetLike.mem_coe] at hy
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    have := pow_card_eq_one' (G := ψ.range) (x := ⟨y, hy⟩)
    rw [hcard] at this
    exact congrArg Subtype.val this
  have hSc : (ψ.range : Set (Multiplicative (ZMod n))).toFinset.card = d := by
    rw [← hcard, Nat.card_eq_fintype_card, Set.toFinset_card]
    rfl
  have heq := Finset.eq_of_subset_of_card_le hST (hSc ▸ hT)
  have hxT : x ∈ T := by simp [T, hx]
  rw [← heq, Set.mem_toFinset, SetLike.mem_coe] at hxT
  obtain ⟨σ, hσ⟩ := hxT
  exact ⟨σ, hσ⟩

theorem nat_mul_div_div {d m : ℕ} (hdvd : d ∣ m) (hm : 0 < m) (hd : 0 < d) (x : ℕ) :
    x * (m / d) / m = x / d := by
  have hpos : 0 < m / d := Nat.div_pos (Nat.le_of_dvd hm hdvd) hd
  calc x * (m / d) / m = x * (m / d) / (d * (m / d)) := by rw [Nat.mul_div_cancel' hdvd]
    _ = x / d := Nat.mul_div_mul_right _ _ hpos

section CharField

variable [IsGalois K Ω] [NeZero n] (χ : LocChar K Ω n)

omit [Algebra.IsIntegral K Ω] [IsGalois K Ω] [NeZero n] in
theorem isOpen_ker : IsOpen ((χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)).ker :
    Set (Ω ≃ₐ[K] Ω)) := by
  have : ((χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)).ker : Set (Ω ≃ₐ[K] Ω)) =
      (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)) ⁻¹' {1} := by ext; simp
  rw [this]
  exact IsLocallyConstant.isOpen_fiber χ.2 1

/-- `ker χ` as a closed subgroup. -/
def kerClosed : ClosedSubgroup (Ω ≃ₐ[K] Ω) where
  toSubgroup := (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)).ker
  isClosed' := Subgroup.isClosed_of_isOpen _ (isOpen_ker n χ)

instance : (kerClosed n χ).Normal := MonoidHom.normal_ker _

/-- The cyclic extension `L_χ = Ω^{ker χ}` cut out by `χ`. -/
def charField : IntermediateField K Ω :=
  IntermediateField.fixedField (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)).ker

omit [NeZero n] in
theorem fixingSubgroup_charField :
    (charField n χ).fixingSubgroup = (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)).ker :=
  InfiniteGalois.fixingSubgroup_fixedField (kerClosed n χ)

omit [NeZero n] in
instance finiteDimensional_charField : FiniteDimensional K (charField n χ) := by
  rw [← InfiniteGalois.isOpen_iff_finite]
  change IsOpen ((charField n χ).fixingSubgroup : Set (Ω ≃ₐ[K] Ω))
  rw [fixingSubgroup_charField n χ]
  exact isOpen_ker n χ

omit [NeZero n] in
instance isGalois_charField : IsGalois K (charField n χ) := by
  rw [← InfiniteGalois.normal_iff_isGalois, fixingSubgroup_charField n χ]
  exact MonoidHom.normal_ker _

/-- The injective character `Gal(L_χ/K) → ℤ/n` induced by `χ`. -/
noncomputable def charBar : (charField n χ ≃ₐ[K] charField n χ) →* Multiplicative (ZMod n) :=
  (QuotientGroup.kerLift (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n))).comp
    (InfiniteGalois.normalAutEquivQuotient (kerClosed n χ)).symm.toMonoidHom

omit [NeZero n] in
theorem charBar_restrict (g : Ω ≃ₐ[K] Ω) :
    charBar n χ (AlgEquiv.restrictNormalHom (charField n χ) g) = χ.1 g := by
  change QuotientGroup.kerLift _ ((InfiniteGalois.normalAutEquivQuotient (kerClosed n χ)).symm
    (InfiniteGalois.normalAutEquivQuotient (kerClosed n χ) g)) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

omit [NeZero n] in
theorem charBar_injective : Function.Injective (charBar n χ) :=
  (QuotientGroup.kerLift_injective _).comp (MulEquiv.injective _)

omit [NeZero n] in
theorem exists_charBar_eq [NeZero n] :
    Nat.card (charField n χ ≃ₐ[K] charField n χ) ∣ n ∧
      ∃ σ, charBar n χ σ = Multiplicative.ofAdd
        ((n / Nat.card (charField n χ ≃ₐ[K] charField n χ) : ℕ) : ZMod n) :=
  exists_eq_div_of_injective _ (charBar_injective n χ)

/-- The generator `σ₀` of `Gal(L_χ/K)` with `χ(σ₀) = n/d`. -/
noncomputable def charGen : charField n χ ≃ₐ[K] charField n χ :=
  (exists_charBar_eq n χ).2.choose

theorem charBar_charGen : charBar n χ (charGen n χ) = Multiplicative.ofAdd
    ((n / Nat.card (charField n χ ≃ₐ[K] charField n χ) : ℕ) : ZMod n) :=
  (exists_charBar_eq n χ).2.choose_spec

theorem orderOf_charGen :
    orderOf (charGen n χ) = Nat.card (charField n χ ≃ₐ[K] charField n χ) := by
  have hdvd := (exists_charBar_eq n χ).1
  have hn : n ≠ 0 := NeZero.ne n
  rw [← orderOf_injective _ (charBar_injective n χ), charBar_charGen,
    orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_coe _ hn,
    Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdvd), Nat.div_div_self hdvd hn]

theorem mem_zpowers_charGen (g : charField n χ ≃ₐ[K] charField n χ) :
    g ∈ Subgroup.zpowers (charGen n χ) := by
  rw [Subgroup.eq_top_of_card_eq (Subgroup.zpowers (charGen n χ))
    (by rw [Nat.card_zpowers, orderOf_charGen])]
  trivial

theorem chiExp_eq (g : Ω ≃ₐ[K] Ω) :
    chiExp n χ g = idx (charGen n χ) (mem_zpowers_charGen n χ)
      (AlgEquiv.restrictNormalHom (charField n χ) g) *
        (n / Nat.card (charField n χ ≃ₐ[K] charField n χ)) := by
  set d := Nat.card (charField n χ ≃ₐ[K] charField n χ)
  set i := idx (charGen n χ) (mem_zpowers_charGen n χ)
    (AlgEquiv.restrictNormalHom (charField n χ) g)
  have hdvd := (exists_charBar_eq n χ).1
  have hi : i < d := by
    have := idx_lt (charGen n χ) (mem_zpowers_charGen n χ)
      (AlgEquiv.restrictNormalHom (charField n χ) g)
    rwa [orderOf_charGen] at this
  have hχg : χ.1 g = Multiplicative.ofAdd ((i * (n / d) : ℕ) : ZMod n) := by
    rw [← charBar_restrict, ← pow_idx (charGen n χ) (mem_zpowers_charGen n χ)
      (AlgEquiv.restrictNormalHom (charField n χ) g), map_pow, charBar_charGen,
      ← ofAdd_nsmul, nsmul_eq_mul, Nat.cast_mul]
  rw [chiExp, hχg, toAdd_ofAdd, ZMod.val_natCast, Nat.mod_eq_of_lt]
  calc i * (n / d) < d * (n / d) := Nat.mul_lt_mul_of_pos_right hi
        (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) hdvd)
          Nat.card_pos)
    _ = n := Nat.mul_div_cancel' hdvd

theorem pow_smul_eq_of_pow_eq {α : Ωˣ} {a : Kˣ} (hαa : α ^ n = Units.map (algebraMap K Ω : K →* Ω) a)
    (σ : Ω ≃ₐ[K] Ω) : σ • α ^ n = α ^ n := by
  rw [hαa]
  ext
  simp [AlgEquiv.smul_units_def]

/-- The carry class of `χ` and `a` is the inflation of the carry class of `a` on the cyclic
extension `L_χ` (generator `σ₀`, `χ(σ₀) = n/d`). -/
theorem carryClass_eq_infl (α : Ωˣ) (a : Kˣ)
    (hαa : α ^ n = Units.map (algebraMap K Ω : K →* Ω) a) :
    carryClass n χ.1 χ.2 α (pow_smul_eq_of_pow_eq n hαa) =
      infl (charField n χ) (cupClass (charGen n χ) (mem_zpowers_charGen n χ) a) := by
  rw [carryClass, cupClass, infl_mk]
  refine congrArg mk (cocycles_ext fun g h => ?_)
  rw [cocyclesMap_apply, cupCocycle_apply, coe_mkCocycle]
  simp only [carryFun, cupFun]
  rw [chiExp_eq, chiExp_eq, ← add_mul, orderOf_charGen, hαa, map_pow]
  have hdvd := (exists_charBar_eq n χ).1
  rw [nat_mul_div_div hdvd (Nat.pos_of_ne_zero (NeZero.ne n)) Nat.card_pos]
  congr 1

/-- **The carry class of `χ` and `a` is trivial iff `a` is a norm from `L_χ`.** -/
theorem carryClass_eq_one_iff (α : Ωˣ) (a : Kˣ)
    (hαa : α ^ n = Units.map (algebraMap K Ω : K →* Ω) a) :
    carryClass n χ.1 χ.2 α (pow_smul_eq_of_pow_eq n hαa) = 1 ↔
      a ∈ PadicField.normGroup K (charField n χ) := by
  rw [carryClass_eq_infl n χ α a hαa, ← map_one (infl (Ω := Ω) (charField n χ)),
    (infl_injective _).eq_iff]
  by_cases hd : 1 < orderOf (charGen n χ)
  · rw [← (relCyclicEquiv (charGen n χ) (mem_zpowers_charGen n χ)).injective.eq_iff,
      relCyclicEquiv_cupClass _ _ hd, map_one, QuotientGroup.eq_one_iff]
  · have h1 : orderOf (charGen n χ) = 1 := by
      have := orderOf_pos (charGen n χ)
      omega
    have hfin : Module.finrank K (charField n χ) = 1 := by
      rw [← IsGalois.card_aut_eq_finrank, ← orderOf_charGen, h1]
    constructor
    · intro _
      rw [PadicField.mem_normGroup]
      refine ⟨Units.map (algebraMap K (charField n χ) : K →* charField n χ) a, ?_⟩
      simp [Algebra.norm_algebraMap, hfin]
    · intro _
      rw [cupClass]
      convert map_one (mk (G := charField n χ ≃ₐ[K] charField n χ) (M := (charField n χ)ˣ))
      refine cocycles_ext fun g h => ?_
      rw [cupCocycle_apply, coe_one_apply]
      simp only [cupFun, h1]
      have hg := idx_lt (charGen n χ) (mem_zpowers_charGen n χ) g
      have hh := idx_lt (charGen n χ) (mem_zpowers_charGen n χ) h
      rw [h1] at hg hh
      rw [Nat.lt_one_iff.1 hg, Nat.lt_one_iff.1 hh, pow_zero]

end CharField

/-- The embedding `ℤ/m → ℤ/n`, `k ↦ k n/m`, for `m ∣ n`. -/
noncomputable def zmodEmbed (m n : ℕ) (h : m ∣ n) : ZMod m →+ ZMod n :=
  ZMod.lift m ⟨zmultiplesHom (ZMod n) ((n / m : ℕ) : ZMod n), by
    simp only [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul, ← Nat.cast_mul,
      Nat.mul_div_cancel' h, ZMod.natCast_self]⟩

theorem zmodEmbed_apply_val (m n : ℕ) (h : m ∣ n) [NeZero m] (k : ZMod m) :
    zmodEmbed m n h k = ((k.val * (n / m) : ℕ) : ZMod n) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val k, ← Int.cast_natCast]
  rw [zmodEmbed, ZMod.lift_coe]
  simp [zmultiplesHom_apply]

theorem zmodEmbed_eq_zero {m n : ℕ} (h : m ∣ n) [NeZero m] [NeZero n] {k : ZMod m}
    (hk : zmodEmbed m n h k = 0) : k = 0 := by
  rw [zmodEmbed_apply_val, ZMod.natCast_eq_zero_iff] at hk
  have hpos : 0 < n / m := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne n)) h)
    (Nat.pos_of_ne_zero (NeZero.ne m))
  conv_lhs at hk => rw [show n = m * (n / m) from (Nat.mul_div_cancel' h).symm]
  have hdvd : m ∣ k.val := (Nat.mul_dvd_mul_iff_right hpos).1 hk
  have hlt := ZMod.val_lt k
  have : k.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
  exact (ZMod.val_eq_zero k).1 this

/-- **Characters separate points**: in a finite abelian group of exponent dividing `n`, every
`x ≠ 1` is detected by a character to `ℤ/n`. -/
theorem exists_hom_zmod_ne_one {A : Type*} [CommGroup A] [Finite A] {n : ℕ} [NeZero n]
    (hexp : ∀ x : A, x ^ n = 1) {x : A} (hx : x ≠ 1) :
    ∃ ψ : A →* Multiplicative (ZMod n), ψ x ≠ 1 := by
  obtain ⟨ι, _, m, hm, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  obtain ⟨i, hi⟩ : ∃ i, e x i ≠ 1 := by
    by_contra h
    push Not at h
    exact hx (e.injective (by rw [map_one]; exact funext h))
  haveI : NeZero (m i) := ⟨by have := hm i; omega⟩
  have hmi : m i ∣ n := by
    classical
    have h1 := hexp (e.symm (Pi.mulSingle i (Multiplicative.ofAdd 1)))
    have h2 := congrArg (fun y => e y i) h1
    simp only [map_pow, MulEquiv.apply_symm_apply, Pi.pow_apply, Pi.mulSingle_eq_same,
      map_one, Pi.one_apply, ← ofAdd_nsmul, nsmul_eq_mul, mul_one] at h2
    rwa [← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq, ZMod.natCast_eq_zero_iff] at h2
  refine ⟨(AddMonoidHom.toMultiplicative (zmodEmbed (m i) n hmi)).comp
    ((Pi.evalMonoidHom (fun i => Multiplicative (ZMod (m i))) i).comp e.toMonoidHom), ?_⟩
  intro h
  apply hi
  have h' : zmodEmbed (m i) n hmi (Multiplicative.toAdd (e x i)) = 0 := by
    simpa [AddMonoidHom.toMultiplicative] using h
  have := zmodEmbed_eq_zero hmi h'
  rw [← ofAdd_toAdd (e x i), this, ofAdd_zero]

end Brauer
