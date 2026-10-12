/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.ArtinPairing

/-!
# The fundamental class of a cyclic extension and the reciprocity map

Let `L ⊆ Ω` be a cyclic extension of `K` of degree `d` with generator `σ`. We prove

`inv (infl cup_σ(a)) = k/d` where `abRec_L(a) = σ^k` (`PadicField.invEquiv_infl_cupClass`),

i.e. the periodicity isomorphism `Br(L/K) ≃ Kˣ/N_{L/K}` with respect to `σ`, followed by `inv`,
is `a ↦ (reciprocity exponent of a)/d`. Consequently the fundamental class is the carry class of any
`a` with `abRec_L(a) = σ`, and

`relCyclicEquiv σ u_{L/K} = (abRecEquiv L)⁻¹ σ` (`PadicField.relCyclicEquiv_fundClass`):

**the fundamental class, read through periodicity, inverts the reciprocity map** (the degree
`-2 → 0` case of Tate–Nakayama for cyclic `L/K`).

Proof: the character `χ_σ : g ↦ k` (`g|_L = σ^k`) to `ℤ/d` has `χ_σ ∪ κ(a) =` the inflated
carry class of `(σ, a)` (`Brauer.toBr_mk_cupKummer`), and `⟨χ_σ, a⟩ = χ_σ(artin a)`
(`PadicField.pairing_eq_artinChar`).
-/

open ContH2 Brauer

set_option linter.unusedSectionVars false

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
variable (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
  (σ : L ≃ₐ[K] L) (hσ : ∀ g, g ∈ Subgroup.zpowers σ)

/-- The character `σ^k ↦ k` of `Gal(L/K)` to `ℤ/d`, `d = orderOf σ`. -/
noncomputable def genChar : (L ≃ₐ[K] L) →* Multiplicative (ZMod (orderOf σ)) :=
  monoidHomOfForallMemZpowers hσ (g' := Multiplicative.ofAdd 1) (by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one])

theorem genChar_pow (k : ℕ) :
    genChar L σ hσ (σ ^ k) = Multiplicative.ofAdd (k : ZMod (orderOf σ)) := by
  rw [map_pow, genChar, monoidHomOfForallMemZpowers_apply_gen, ← ofAdd_nsmul, nsmul_one]

instance : NeZero (orderOf σ) := ⟨(orderOf_pos σ).ne'⟩

/-- The locally constant character `g ↦ χ_σ(g|_L)` of `Gal(Ω/K)`. -/
noncomputable def genLocChar : LocChar K Ω (orderOf σ) :=
  ⟨(genChar L σ hσ).comp (AlgEquiv.restrictNormalHom L),
    show IsLocallyConstant ((genChar L σ hσ) ∘ (AlgEquiv.restrictNormalHom L)) from
    ((IsLocallyConstant.iff_continuous _).2 (InfiniteGalois.restrictNormalHom_continuous _)).comp _⟩

theorem chiExp_genLocChar (g : Ω ≃ₐ[K] Ω) :
    chiExp (orderOf σ) (genLocChar L σ hσ).1 g =
      idx σ hσ (AlgEquiv.restrictNormalHom L g) := by
  change (Multiplicative.toAdd (genChar L σ hσ (AlgEquiv.restrictNormalHom L g))).val = _
  conv_lhs => rw [← pow_idx σ hσ (AlgEquiv.restrictNormalHom L g)]
  rw [genChar_pow, toAdd_ofAdd, ZMod.val_natCast, Nat.mod_eq_of_lt (idx_lt _ _ _)]

/-- The carry class of `χ_σ` is the inflated carry class of `(σ, a)`. -/
theorem carryClass_genLocChar (α : Ωˣ) (a : Kˣ)
    (hαa : α ^ orderOf σ = Units.map (algebraMap K Ω : K →* Ω) a) :
    carryClass (orderOf σ) (genLocChar L σ hσ).1 (genLocChar L σ hσ).2 α
      (pow_smul_eq_of_pow_eq (orderOf σ) hαa) = infl L (cupClass σ hσ a) := by
  rw [carryClass, cupClass, infl_mk]
  refine congrArg mk (cocycles_ext fun g h => ?_)
  rw [cocyclesMap_apply, cupCocycle_apply, coe_mkCocycle]
  simp only [carryFun, cupFun]
  rw [chiExp_genLocChar, chiExp_genLocChar, hαa, map_pow]
  congr 1

/-- **`inv(infl cup_σ(a)) = k/d` where `abRec_L(a) = σ^k`.** -/
theorem invEquiv_infl_cupClass (a : Kˣ) :
    invEquiv p K Ω (infl L (cupClass σ hσ a)) = Multiplicative.ofAdd
      (zmodToQZ (orderOf σ) (Multiplicative.toAdd (genChar L σ hσ (abRec p L a)))) := by
  rw [← carryClass_genLocChar L σ hσ (rootK (orderOf σ) a) a (rootK_pow _ a),
    ← toBr_cupKummerClass, invEquiv_toBr_cupKummerClass, pairing_eq_artinChar]
  obtain ⟨g, hg⟩ := exists_lift_artin (p := p) (Ω := Ω) a
  rw [artinChar_eq _ _ a g hg]
  change Multiplicative.ofAdd (zmodToQZ _ (Multiplicative.toAdd
    (genChar L σ hσ (AlgEquiv.restrictNormalHom L g)))) = _
  rw [restrictNormalHom_eq_abRec L a g hg]

/-- The fundamental class of a cyclic extension is the carry class of any `a` with
`abRec_L(a) = σ`. -/
theorem cupClass_eq_fundClass (a : Kˣ) (ha : abRec p L a = σ) :
    cupClass σ hσ a = fundClass (p := p) (Ω := Ω) L := by
  apply infl_injective L
  apply (invEquiv p K Ω).injective
  rw [invEquiv_infl_cupClass L σ hσ a, invEquiv_infl_fundClass, ha]
  have hσ1 : genChar L σ hσ σ = Multiplicative.ofAdd 1 := by
    rw [genChar, monoidHomOfForallMemZpowers_apply_gen]
  have hd : (orderOf σ : ℚ) = Module.finrank K L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank]
  have h1 : zmodToQZ (orderOf σ) 1 = ((1 / Module.finrank K L : ℚ) : QZ) := by
    rw [show (1 : ZMod (orderOf σ)) = ((1 : ℤ) : ZMod (orderOf σ)) from Int.cast_one.symm,
      zmodToQZ_intCast, hd]
    push_cast
    rfl
  rw [hσ1, toAdd_ofAdd, h1]

/-- **The fundamental class inverts the reciprocity map**: for a generator `σ` of a cyclic
`L/K`, the periodicity isomorphism with respect to `σ` sends `u_{L/K}` to `(abRecEquiv L)⁻¹ σ`. -/
theorem relCyclicEquiv_fundClass :
    relCyclicEquiv σ hσ (fundClass (p := p) (Ω := Ω) L) = (abRecEquiv p L).symm σ := by
  obtain ⟨a, ha⟩ := abRec_surjective (p := p) L σ
  have h1 : 1 < orderOf σ ∨ orderOf σ = 1 := by
    have := orderOf_pos σ
    omega
  rw [← cupClass_eq_fundClass L σ hσ a ha]
  rcases h1 with h1 | h1
  · rw [relCyclicEquiv_cupClass σ hσ h1, MulEquiv.eq_symm_apply]
    exact ha
  · -- `L = K`: both sides lie in the trivial group `Kˣ/N_{L/K}`
    have hN : normGroup K L = ⊤ := by
      have hfin : Module.finrank K L = 1 := by
        rw [← IsGalois.card_aut_eq_finrank, ← orderOf_eq_card_of_forall_mem_zpowers hσ, h1]
      refine eq_top_iff.2 fun b _ => ?_
      rw [mem_normGroup]
      exact ⟨Units.map (algebraMap K L : K →* L) b, by simp [Algebra.norm_algebraMap, hfin]⟩
    have : Subsingleton (Kˣ ⧸ normGroup K L) := by
      rw [hN]
      exact QuotientGroup.subsingleton_quotient_top
    exact Subsingleton.elim _ _

end PadicField
