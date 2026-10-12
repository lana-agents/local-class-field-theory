/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.FundamentalClass
import LocalClassFieldTheory.Reciprocity.NormCompat

/-!
# The fundamental class inverts reciprocity for finite abelian extensions

For a finite group `G` acting on a commutative group `M`, a 2-cocycle `f` and `g ∈ G`, the element

`nak_g(f) = ∏_{τ ∈ G} f(τ, g) ∈ M^G`

is well defined modulo norms on cohomology classes (`ContH2.nakHom g : H²(G, M) →* Ĥ⁰(G, M)`).
This is the explicit cocycle formula for the cup product `Ĥ⁻²(G, ℤ) × H²(G, M) → Ĥ⁰(G, M)`
with the class of `g` under `G^ab ≅ Ĥ⁻²(G, ℤ)` (the identification of `Ĥ⁻²` and of the cup
product in negative degrees are *not* formalised; we work with the explicit formula). For a
generator `σ` of a cyclic `G` it is the periodicity isomorphism (`ContH2.nakHom_eq_cyclicHom`).

Main result (`PadicField.relNak_fundClass`): for a finite **abelian** `L ⊆ Ω` over `K` and
`g ∈ Gal(L/K)`,

`[∏_{τ ∈ Gal(L/K)} u(τ, g)] = (abRecEquiv L)⁻¹ g ∈ Kˣ / N_{L/K} Lˣ`

for any cocycle `u` representing the fundamental class `u_{L/K}`: cup product with `u_{L/K}`
(in degree `-2 → 0`) is the inverse of the reciprocity map — the Tate–Nakayama statement in
degree `-2` for abelian `L/K`.

Proof (reduction to the cyclic case `PadicField.relCyclicEquiv_fundClass`): let `H = ⟨g⟩` and
`M = L^H`, so that `L/M` is cyclic with generator `g`.
* coset decomposition (`ContH2.nakFun_eq_prod_quotient`):
  `∏_{τ ∈ G} u(τ, g) = ∏_{c ∈ G/H} c • ∏_{h ∈ H} u(h, g) = N_{M/K}(∏_{h ∈ H} u(h, g))`;
* the restriction of `u_{L/K}` to `Gal(L/M)` is `u_{L/M}` (invariants: `inv_M ∘ res = [M:K] inv_K`),
  so `∏_{h ∈ H} u(h, g)` is the periodicity invariant of `u_{L/M}`, i.e. `(rec_{L/M})⁻¹ g`;
* norm compatibility of reciprocity `PadicField.abRec_baseChange`.
-/

open ContH2 groupCohomology Finset

set_option linter.unusedSectionVars false

namespace ContH2

noncomputable section Nak

variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]

/-- `nak_g(f) = ∏_{τ ∈ G} f(τ, g)`. -/
def nakFun (g : G) (f : G × G → M) : M := ∏ τ : G, f (τ, g)

theorem nakFun_mul (g : G) (f f' : G × G → M) : nakFun g (f * f') = nakFun g f * nakFun g f' := by
  simp [nakFun, prod_mul_distrib]

theorem nakFun_dx (g : G) (x : G → M) : nakFun g (dx G M x) = normMap G M (x g) := by
  simp only [nakFun, dx_apply]
  rw [prod_mul_distrib, prod_div_distrib, normMap_apply]
  have h : ∏ τ : G, x (τ * g) = ∏ τ : G, x τ :=
    Fintype.prod_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)
  rw [h, div_mul_cancel]

theorem nakFun_mem_fixedSubgroup {f : G × G → M} (hf : IsMulCocycle₂ f) (g : G) :
    nakFun g f ∈ fixedSubgroup G M := by
  intro σ
  have key : ∀ τ, σ • f (τ, g) = f (σ * τ, g) * f (σ, τ) / f (σ, τ * g) := by
    intro τ
    rw [eq_div_iff_mul_eq', ← hf σ τ g]
  simp only [nakFun, smul_prod', key, prod_div_distrib, prod_mul_distrib]
  rw [Fintype.prod_equiv (Equiv.mulLeft σ) (fun τ => f (σ * τ, g)) (fun τ => f (τ, g))
      (fun _ => rfl),
    Fintype.prod_equiv (Equiv.mulRight g) (fun τ => f (σ, τ * g)) (fun τ => f (σ, τ))
      (fun _ => rfl), mul_div_cancel_right]

/-- `nak_g` on cocycles. -/
def cocyclesNak [TopologicalSpace G] (g : G) : cocycles G M →* Hhat0 G M where
  toFun f := QuotientGroup.mk ⟨nakFun g f, nakFun_mem_fixedSubgroup (isMulCocycle₂ f) g⟩
  map_one' := by
    rw [← QuotientGroup.mk_one]
    congr 1
    ext
    simp [nakFun]
  map_mul' f f' := by
    rw [← QuotientGroup.mk_mul]
    congr 1
    ext
    exact nakFun_mul g f f'

/-- **The cup product with `g ∈ G` (`≅ Ĥ⁻²(G, ℤ)` for abelian `G`)**, `H²(G, M) → Ĥ⁰(G, M)`,
`[f] ↦ [∏_τ f(τ, g)]`. -/
def nakHom [TopologicalSpace G] (g : G) : ContH2 G M →* Hhat0 G M :=
  QuotientGroup.lift _ (cocyclesNak g) (by
    rintro f ⟨x, -, hxf⟩
    rw [MonoidHom.mem_ker, cocyclesNak, MonoidHom.coe_mk, OneHom.coe_mk, Hhat0.mk_eq_one_iff]
    refine ⟨x g, ?_⟩
    rw [← nakFun_dx g, hxf])

theorem nakHom_mk [TopologicalSpace G] (g : G) (f : cocycles G M) :
    nakHom g (mk f) =
      QuotientGroup.mk ⟨nakFun g f, nakFun_mem_fixedSubgroup (isMulCocycle₂ f) g⟩ := rfl

theorem nakFun_eq_phiFun (σ : G) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (f : G × G → M) :
    nakFun σ f = phiFun σ f :=
  (prod_range_pow σ hσ (fun τ => f (τ, σ))).symm

/-- For a generator `σ` of a cyclic group, `nak_σ` is the periodicity isomorphism. -/
theorem nakHom_eq_cyclicHom [TopologicalSpace G] (σ : G) (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    nakHom (M := M) σ = cyclicHom σ hσ := by
  ext x
  induction x using induction_on with | h f => ?_
  rw [nakHom_mk, cyclicHom_mk]
  congr 2
  exact nakFun_eq_phiFun σ hσ f

/-- **Coset decomposition**: for a subgroup `S ∋ g`,
`∏_{τ ∈ G} f(τ, g) = ∏_{c ∈ G/S} c • ∏_{s ∈ S} f(s, g)`. -/
theorem nakFun_eq_prod_quotient {f : G × G → M} (hf : IsMulCocycle₂ f) (S : Subgroup G)
    [Fintype (G ⧸ S)] [Fintype S] {g : G} (hg : g ∈ S) :
    nakFun g f = ∏ c : G ⧸ S, c.out • ∏ s : S, f ((s : G), g) := by
  have hbij : Function.Bijective (fun cs : (G ⧸ S) × S => cs.1.out * (cs.2 : G)) := by
    constructor
    · rintro ⟨c, s⟩ ⟨c', s'⟩ h
      simp only at h
      have hc : c = c' := by
        have e1 : (QuotientGroup.mk (c.out * (s : G)) : G ⧸ S) = c := by
          rw [QuotientGroup.mk_mul_of_mem _ s.2, QuotientGroup.out_eq']
        have e2 : (QuotientGroup.mk (c'.out * (s' : G)) : G ⧸ S) = c' := by
          rw [QuotientGroup.mk_mul_of_mem _ s'.2, QuotientGroup.out_eq']
        rw [← e1, ← e2, h]
      subst hc
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel h))
    · intro τ
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul S τ
      refine ⟨(QuotientGroup.mk τ, h⁻¹), ?_⟩
      simp only [hh, Subgroup.coe_inv, mul_inv_cancel_right]
  rw [nakFun, ← Fintype.prod_bijective _ hbij (fun cs => f (cs.1.out * (cs.2 : G), g))
    (fun τ => f (τ, g)) (fun _ => rfl), Fintype.prod_prod_type]
  refine Fintype.prod_congr _ _ fun c => ?_
  have key : ∀ s : S, f (c.out * (s : G), g) =
      c.out • f ((s : G), g) * (f (c.out, (s : G) * g) / f (c.out, (s : G))) := by
    intro s
    rw [mul_div_assoc', eq_div_iff_mul_eq', hf]
  simp only [key, prod_mul_distrib, prod_div_distrib, smul_prod']
  have h2 : ∏ s : S, f (c.out, (s : G) * g) = ∏ s : S, f (c.out, (s : G)) :=
    Fintype.prod_equiv (Equiv.mulRight (⟨g, hg⟩ : S)) _ _ (fun _ => rfl)
  rw [h2, div_self', mul_one]

end Nak

end ContH2

namespace Brauer

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The element `∏_τ f(τ, g)` of `Kˣ`. -/
noncomputable def nakUnits (g : L ≃ₐ[K] L) (f : cocycles (L ≃ₐ[K] L) Lˣ) : Kˣ :=
  (fixedUnitsEquiv K L).symm ⟨nakFun g f, nakFun_mem_fixedSubgroup (isMulCocycle₂ f) g⟩

theorem algebraMap_nakUnits (g : L ≃ₐ[K] L) (f : cocycles (L ≃ₐ[K] L) Lˣ) :
    algebraMap K L (nakUnits g f) = ((nakFun g f : Lˣ) : L) := by
  rw [← coe_fixedUnitsEquiv, nakUnits, MulEquiv.apply_symm_apply]

/-- **Cup product with `g`** on the relative Brauer group, `Br(L/K) → Kˣ / N_{L/K} Lˣ`,
`[f] ↦ [∏_τ f(τ, g)]`. -/
noncomputable def relNak (g : L ≃ₐ[K] L) : RelBr K L →* Kˣ ⧸ PadicField.normGroup K L :=
  (hhat0Equiv K L).toMonoidHom.comp (nakHom g)

theorem relNak_mk (g : L ≃ₐ[K] L) (f : cocycles (L ≃ₐ[K] L) Lˣ) :
    relNak g (mk f) = QuotientGroup.mk (nakUnits g f) := by
  rw [relNak, MonoidHom.comp_apply, nakHom_mk, MulEquiv.coe_toMonoidHom, ← hhat0Equiv_mk,
    nakUnits, MulEquiv.apply_symm_apply]

/-- For a generator `σ` of a cyclic `Gal(L/K)`, `relNak σ` is the periodicity isomorphism. -/
theorem relNak_eq_relCyclicEquiv (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)
    (x : RelBr K L) : relNak σ x = relCyclicEquiv σ hσ x := by
  rw [relNak, relCyclicEquiv, MonoidHom.comp_apply, nakHom_eq_cyclicHom σ hσ]
  rfl

end Brauer

open Brauer IntermediateField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
  (g : L ≃ₐ[K] L)

/-- The fixed field `L^{⟨g⟩}`, as a subfield of `Ω`. -/
noncomputable abbrev fixG : IntermediateField K Ω := lift (fixedField (Subgroup.zpowers g))

theorem fixG_le : fixG L g ≤ L := lift_le _

instance : FiniteDimensional K (fixG L g) :=
  FiniteDimensional.of_injective (IntermediateField.inclusion (fixG_le L g)).toLinearMap
    (IntermediateField.inclusion (fixG_le L g)).injective

instance : IsAbelianGalois K (fixG L g) :=
  IsAbelianGalois.of_algHom (IntermediateField.inclusion (fixG_le L g))

theorem mem_baseChange_fixG {x : Ω} : x ∈ baseChange (fixG L g) L ↔ x ∈ L := by
  rw [mem_baseChange, sup_eq_left.2 (fixG_le L g)]

theorem apply_eq_of_mem_fixG (y : L) (hy : (y : Ω) ∈ fixG L g) : g y = y := by
  have h := (mem_lift y).1 hy
  exact (mem_fixedField_iff _ _).1 h g (Subgroup.mem_zpowers g)

/-- `g` as an automorphism of `L / L^{⟨g⟩}`. -/
noncomputable def genBC : baseChange (fixG L g) L ≃ₐ[fixG L g] baseChange (fixG L g) L where
  toFun x := ⟨(g ⟨x, (mem_baseChange_fixG L g).1 x.2⟩ : Ω), (mem_baseChange_fixG L g).2 (g _).2⟩
  invFun x := ⟨(g.symm ⟨x, (mem_baseChange_fixG L g).1 x.2⟩ : Ω),
    (mem_baseChange_fixG L g).2 (g.symm _).2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)
  map_mul' x y := by
    refine SetLike.coe_eq_coe.1 ?_
    have h := congrArg Subtype.val (map_mul g
      ⟨(x : Ω), (mem_baseChange_fixG L g).1 x.2⟩ ⟨(y : Ω), (mem_baseChange_fixG L g).1 y.2⟩)
    exact h
  map_add' x y := by
    refine SetLike.coe_eq_coe.1 ?_
    have h := congrArg Subtype.val (map_add g
      ⟨(x : Ω), (mem_baseChange_fixG L g).1 x.2⟩ ⟨(y : Ω), (mem_baseChange_fixG L g).1 y.2⟩)
    exact h
  commutes' m := by
    refine SetLike.coe_eq_coe.1 ?_
    have h := congrArg Subtype.val (apply_eq_of_mem_fixG L g ⟨(m : Ω), fixG_le L g m.2⟩ m.2)
    exact h

theorem coe_genBC (x : baseChange (fixG L g) L) :
    (genBC L g x : Ω) = g ⟨x, (mem_baseChange_fixG L g).1 x.2⟩ := by
  rfl

theorem resBaseChange_genBC : resBaseChange (fixG L g) L (genBC L g) = g := by
  ext y
  rw [resBaseChange_apply, coe_genBC]

theorem resBaseChange_mem_zpowers
    (τ : baseChange (fixG L g) L ≃ₐ[fixG L g] baseChange (fixG L g) L) :
    resBaseChange (fixG L g) L τ ∈ Subgroup.zpowers g := by
  rw [← fixingSubgroup_fixedField (Subgroup.zpowers g), IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have hyM : (y : Ω) ∈ fixG L g := (mem_lift y).2 hy
  apply Subtype.ext
  rw [resBaseChange_apply]
  have e : (⟨(y : Ω), le_baseChange (fixG L g) L y.2⟩ : baseChange (fixG L g) L) =
      algebraMap (fixG L g) (baseChange (fixG L g) L) ⟨y, hyM⟩ := rfl
  rw [e, AlgEquiv.commutes]
  rfl

theorem mem_zpowers_genBC (τ : baseChange (fixG L g) L ≃ₐ[fixG L g] baseChange (fixG L g) L) :
    τ ∈ Subgroup.zpowers (genBC L g) := by
  obtain ⟨k, hk⟩ := resBaseChange_mem_zpowers L g τ
  refine ⟨k, resBaseChange_injective (fixG L g) L ?_⟩
  simp only [map_zpow, resBaseChange_genBC]
  exact hk

section ResBC

variable (K' : IntermediateField K Ω) [FiniteDimensional K K']

/-- `L → L K'` on units. -/
noncomputable def unitsBC : Lˣ →* (baseChange K' L)ˣ :=
  Units.map
    { toFun := fun y => ⟨(y : Ω), le_baseChange K' L y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem coe_unitsBC (u : Lˣ) : (((unitsBC L K' u : (baseChange K' L)ˣ) : baseChange K' L) : Ω) =
    ((u : L) : Ω) := rfl

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
theorem unitsBC_smul (a : baseChange K' L ≃ₐ[K'] baseChange K' L) (u : Lˣ) :
    unitsBC L K' (resBaseChange K' L a • u) = a • unitsBC L K' u := by
  apply Units.ext
  apply Subtype.ext
  rw [smul_units_coe, coe_unitsBC, smul_units_coe, resBaseChange_apply]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
/-- Restriction `Br(L/K) → Br(L K'/K')` along `Gal(L K'/K') ↪ Gal(L/K)`. -/
noncomputable def resBC : RelBr K L →* RelBr K' (baseChange K' L) :=
  ContH2.map (resBaseChange K' L) continuous_of_discreteTopology (unitsBC L K')
    (unitsBC_smul L K')

theorem resBaseChange_restrictNormalHom (a : Ω ≃ₐ[K'] Ω) :
    resBaseChange K' L (AlgEquiv.restrictNormalHom (baseChange K' L) a) =
      AlgEquiv.restrictNormalHom L (resScalars K' a) := by
  ext y
  rw [resBaseChange_apply, AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
theorem infl_resBC (x : RelBr K L) :
    infl (baseChange K' L) (resBC L K' x) = res K' (infl L x) := by
  induction x using induction_on with | h f => ?_
  rw [resBC, map_mk, infl_mk, infl_mk, res_mk]
  refine congrArg mk (cocycles_ext fun a b => ?_)
  simp only [cocyclesMap_apply, resBaseChange_restrictNormalHom, MonoidHom.id_apply]
  rfl

theorem finrank_baseChange_of_le (h : K' ≤ L) :
    Module.finrank K K' * Module.finrank K' (baseChange K' L) = Module.finrank K L := by
  have e : (baseChange K' L).restrictScalars K = L := by
    rw [restrictScalars_baseChange, sup_eq_left.2 h]
  haveI : Module.Free K' (baseChange K' L) := Module.Free.of_divisionRing _ _
  rw [Module.finrank_mul_finrank K K' (baseChange K' L)]
  exact (IntermediateField.equivOfEq e).toLinearEquiv.finrank_eq

/-- For `K' ⊆ L`, the restriction of `u_{L/K}` is `u_{L/K'}`. -/
theorem resBC_fundClass (h : K' ≤ L) :
    resBC L K' (fundClass (p := p) (Ω := Ω) L) = fundClass (p := p) (Ω := Ω) (baseChange K' L) := by
  apply infl_injective (baseChange K' L)
  apply (invEquiv p K' Ω).injective
  rw [infl_resBC, invEquiv_res, invEquiv_infl_fundClass, invEquiv_infl_fundClass, ← ofAdd_nsmul]
  congr 1
  rw [← finrank_baseChange_of_le L K' h, ← QuotientAddGroup.mk_nsmul]
  congr 1
  have h1 : (Module.finrank K K' : ℚ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have h2 : (Module.finrank K' (baseChange K' L) : ℚ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  rw [nsmul_eq_mul]
  push_cast
  field_simp

end ResBC

theorem mem_fixG_iff (y : L) : (y : Ω) ∈ fixG L g ↔ ∀ τ ∈ Subgroup.zpowers g, τ y = y := by
  rw [mem_lift, mem_fixedField_iff]

theorem ker_resHom_fixG : (resHom (fixG_le L g)).ker = Subgroup.zpowers g := by
  rw [← fixingSubgroup_fixedField (Subgroup.zpowers g)]
  ext τ
  rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff, resHom_eq_iff]
  constructor
  · intro h y hy
    have hyM : (y : Ω) ∈ fixG L g := (mem_lift y).2 hy
    exact Subtype.ext (h ⟨y, hyM⟩)
  · intro h x
    have hx : (inclusion (fixG_le L g) x : Ω) ∈ fixG L g := x.2
    have := h (inclusion (fixG_le L g) x) ((mem_lift _).1 hx)
    rw [this]
    rfl

/-- `Gal(L/K)/⟨g⟩ ≃ Gal(L^{⟨g⟩}/K)`. -/
noncomputable def quotEquivFixG : (L ≃ₐ[K] L) ⧸ Subgroup.zpowers g ≃* (fixG L g ≃ₐ[K] fixG L g) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_resHom_fixG L g).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (resHom_surjective (fixG_le L g)))

theorem quotEquivFixG_apply (c : (L ≃ₐ[K] L) ⧸ Subgroup.zpowers g) :
    quotEquivFixG L g c = resHom (fixG_le L g) c.out := by
  conv_lhs => rw [← QuotientGroup.out_eq' c]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
-- `SMul Gal(L/K) Lˣ` for intermediate fields `L` is slow to synthesize.
/-- **Cup product with the fundamental class inverts reciprocity**, cocycle form: for any cocycle
`f` representing `u_{L/K}` and `g ∈ Gal(L/K)`, `abRec_L(∏_τ f(τ, g)) = g`. -/
theorem abRec_nakUnits (f : cocycles (L ≃ₐ[K] L) Lˣ) (hf : mk f = fundClass (p := p) (Ω := Ω) L) :
    abRec p L (nakUnits g f) = g := by
  classical
  have hML : fixG L g ≤ L := fixG_le L g
  have hg' := mem_zpowers_genBC L g
  set f' := cocyclesMap (resBaseChange (fixG L g) L) continuous_of_discreteTopology
    (unitsBC L (fixG L g))
    (unitsBC_smul L (fixG L g)) f
  -- the cyclic case over `M`
  have hcyc := relCyclicEquiv_fundClass (p := p) (K := fixG L g) (Ω := Ω)
    (baseChange (fixG L g) L) (genBC L g) hg'
  rw [← resBC_fundClass L (fixG L g) hML, ← hf, resBC, map_mk, relCyclicEquiv_mk] at hcyc
  set P := phiUnits (genBC L g) hg' f'
  have hP : abRec p (baseChange (fixG L g) L) P = genBC L g := (MulEquiv.eq_symm_apply _).1 hcyc
  have hN : abRec p L (normU (fixG L g) P) = g := by
    rw [← abRec_baseChange (p := p) (fixG L g) L P, hP, resBaseChange_genBC]
  suffices hsuff : nakUnits g f = normU (fixG L g) P by rw [hsuff, hN]
  -- `∏_τ f(τ, g) = N_{M/K} P`
  set Q : Lˣ := ∏ s : Subgroup.zpowers g, f ((s : L ≃ₐ[K] L), g)
  have hQ : unitsBC L (fixG L g) Q = phiFun (genBC L g) f' := by
    rw [← nakFun_eq_phiFun (genBC L g) hg', nakFun, map_prod]
    refine (Fintype.prod_bijective (fun τ => (⟨resBaseChange (fixG L g) L τ,
      resBaseChange_mem_zpowers L g τ⟩ : Subgroup.zpowers g))
      ⟨fun τ τ' h => resBaseChange_injective (fixG L g) L (congrArg Subtype.val h),
      fun s => ?_⟩ _ _ fun τ => ?_).symm
    · obtain ⟨k, hk⟩ := s.2
      exact ⟨genBC L g ^ k, Subtype.ext (by
        change resBaseChange (fixG L g) L (genBC L g ^ k) = _
        rw [map_zpow, resBaseChange_genBC]; exact hk)⟩
    · rw [cocyclesMap_apply, resBaseChange_genBC]
  have hPQ : ((P : fixG L g) : Ω) = ((Q : L) : Ω) := by
    have := congrArg (fun x : baseChange (fixG L g) L => (x : Ω))
      (algebraMap_phiUnits (genBC L g) hg' f')
    rw [← hQ, coe_unitsBC] at this
    exact this
  apply Units.ext
  apply (algebraMap K Ω).injective
  have hL : ∀ a : K, algebraMap K Ω a = ((algebraMap K L a : L) : Ω) := fun _ => rfl
  have hM : ∀ a : K, algebraMap K Ω a = ((algebraMap K (fixG L g) a : fixG L g) : Ω) :=
    fun _ => rfl
  have hinc : inclusion hML (P : fixG L g) = (Q : L) := Subtype.ext hPQ
  rw [hL, algebraMap_nakUnits, hM, normU, Units.coe_map,
    Algebra.norm_eq_prod_automorphisms,
    nakFun_eq_prod_quotient (isMulCocycle₂ f) (Subgroup.zpowers g) (Subgroup.mem_zpowers g),
    ← Fintype.prod_equiv (quotEquivFixG L g).toEquiv
      (fun c => (quotEquivFixG L g c) (P : fixG L g)) _ (fun _ => rfl)]
  simp only [Units.coe_prod, IntermediateField.coe_prod]
  refine Fintype.prod_congr _ _ fun c => ?_
  rw [quotEquivFixG_apply, resHom_apply, hinc, smul_units_coe]

/-- **The fundamental class inverts reciprocity** for finite abelian `L/K`: for every
`g ∈ Gal(L/K)`, cup product of `u_{L/K}` with `g` (`[f] ↦ [∏_τ f(τ, g)]`) is
`(abRecEquiv L)⁻¹ g`. -/
theorem relNak_fundClass :
    relNak g (fundClass (p := p) (Ω := Ω) L) = (abRecEquiv p L).symm g := by
  obtain ⟨f, hf⟩ := mk_surjective (fundClass (p := p) (Ω := Ω) L)
  rw [← hf, relNak_mk, MulEquiv.eq_symm_apply]
  exact abRec_nakUnits L g f hf

/-- In particular `g ↦ relNak g u_{L/K}` is a group isomorphism `Gal(L/K) ≃ Kˣ / N_{L/K} Lˣ`. -/
theorem relNak_fundClass_mul (g g' : L ≃ₐ[K] L) :
    relNak (g * g') (fundClass (p := p) (Ω := Ω) L) =
      relNak g (fundClass (p := p) (Ω := Ω) L) * relNak g' (fundClass (p := p) (Ω := Ω) L) := by
  rw [relNak_fundClass, relNak_fundClass, relNak_fundClass, map_mul]

end PadicField
