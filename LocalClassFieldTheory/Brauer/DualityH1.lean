/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.ArtinPairing
import ContinuousKummerTheory.Kummer.Equiv

/-!
# Local duality for `μ_n` and `ℤ/n` in terms of `H¹(K, μ_n)`

The cup product `H¹(K, ℤ/n) × H¹(K, μ_n) → H²(K, μ_n) ≃ ℤ/n` (`Brauer.cupH1`,
`PadicField.pairingH1`) on continuous cohomology classes (`ContH1`, from
`continuous-kummer-theory`): cup products with coboundaries are coboundaries. Via the Kummer isomorphism
`KummerTheory.kummerEquiv : Kˣ/(Kˣ)ⁿ ≃ H¹(K, μ_n)` it is the pairing `PadicField.pairing`, hence
(`PadicField.pairingH1_kummer`)

`⟨χ, κ(a)⟩ = χ(artin a)`,

and it is **perfect** (`PadicField.eq_one_of_forall_pairingH1_eq_zero`,
`PadicField.eq_one_of_forall_pairingH1_eq_zero'`).
-/

open ContH2 groupCohomology KummerTheory

set_option linter.unusedSectionVars false

namespace Brauer

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsIntegral K Ω]
variable (n : ℕ) [NeZero n]

theorem cupKummerFun_mul (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n))
    (ζ ζ' : (Ω ≃ₐ[K] Ω) → Mu n Ω) :
    cupKummerFun n χ (ζ * ζ') = cupKummerFun n χ ζ * cupKummerFun n χ ζ' := by
  funext gh
  simp only [cupKummerFun, Pi.mul_apply, smul_mul', mul_pow]

/-- Cup products with coboundaries are coboundaries. -/
theorem cupKummerFun_coboundary (χ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod n)) (ξ : Mu n Ω) :
    cupKummerFun n χ (fun g => g • ξ / ξ) =
      dx _ _ (fun g => ((g • ξ) ^ chiExp n χ g)⁻¹) := by
  funext gh
  obtain ⟨g, h⟩ := gh
  simp only [cupKummerFun, dx_apply, smul_div', smul_inv', smul_pow', smul_smul]
  rw [chiExp_mul, mu_pow_mod, pow_add, div_pow]
  mul_abel

/-- The cup product with `χ` on cocycles. -/
noncomputable def cupCocyclesHom (χ : LocChar K Ω n) :
    ContH1.cocycles (Ω ≃ₐ[K] Ω) (Mu n Ω) →* H2Mu K Ω n where
  toFun ζ := mk (cupKummer n χ.1 χ.2 ζ ((IsLocallyConstant.iff_continuous _).2 ζ.2.1) ζ.2.2)
  map_one' := by
    rw [← map_one (mk (G := Ω ≃ₐ[K] Ω) (M := Mu n Ω))]
    congr 1
    refine cocycles_ext fun g h => ?_
    simp [cupKummer, cupKummerFun]
  map_mul' ζ ζ' := by
    rw [← map_mul]
    congr 1
    refine cocycles_ext fun g h => ?_
    simp only [cupKummer, coe_mkCocycle, coe_mul_apply, Subgroup.coe_mul,
      cupKummerFun_mul n χ.1 ζ ζ', Pi.mul_apply]

/-- **The cup product** `H¹(K, μ_n) → H²(K, μ_n)`, `κ ↦ χ ∪ κ`. -/
noncomputable def cupH1 (χ : LocChar K Ω n) : ContH1 (Ω ≃ₐ[K] Ω) (Mu n Ω) →* H2Mu K Ω n :=
  QuotientGroup.lift (ContH1.coboundaries _ _) (cupCocyclesHom n χ) (by
    rintro ζ ⟨ξ, hξ⟩
    rw [MonoidHom.mem_ker, cupCocyclesHom, MonoidHom.coe_mk, OneHom.coe_mk, mk_eq_one_iff]
    refine ⟨fun g => ((g • ξ) ^ chiExp n χ.1 g)⁻¹, ?_, ?_⟩
    · exact (((isLocallyConstant_smul_mu n ξ).prodMk
        (isLocallyConstant_chiExp n χ.2)).comp fun c => c.1 ^ c.2).inv
    · rw [← cupKummerFun_coboundary]
      simp only [cupKummer, coe_mkCocycle]
      congr 1
      funext g
      exact hξ g)

theorem cupH1_mk (χ : LocChar K Ω n) (ζ : ContH1.cocycles (Ω ≃ₐ[K] Ω) (Mu n Ω)) :
    cupH1 n χ (ContH1.mk ζ) =
      mk (cupKummer n χ.1 χ.2 ζ ((IsLocallyConstant.iff_continuous _).2 ζ.2.1) ζ.2.2) := rfl

end Brauer

namespace PadicField

open Brauer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
variable (n : ℕ) [NeZero n]

theorem hasKummerRoots : HasKummerRoots n K Ω := ⟨fun a => exists_root_K n a⟩

/-- **The duality pairing** `H¹(K, ℤ/n) × H¹(K, μ_n) → ℤ/n`, via `H²(K, μ_n) ≃ ℤ/n`. -/
noncomputable def pairingH1 (χ : LocChar K Ω n) (ζ : ContH1 (Ω ≃ₐ[K] Ω) (Mu n Ω)) : ZMod n :=
  Multiplicative.toAdd (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n)) (cupH1 n χ ζ))

theorem cupH1_kummer (χ : LocChar K Ω n) (a : Kˣ) :
    haveI := hasKummerRoots (K := K) (Ω := Ω) n
    cupH1 n χ (kummer n K Ω a) = cupKummerClass n χ a := by
  haveI := hasKummerRoots (K := K) (Ω := Ω) n
  rw [kummer_eq a (rootK n a) (rootK_pow n a), cupH1_mk]
  rfl

/-- On Kummer classes the pairing computes the Artin map: `⟨χ, κ(a)⟩ = χ(artin a)`. -/
theorem pairingH1_kummer (χ : LocChar K Ω n) (a : Kˣ) :
    haveI := hasKummerRoots (K := K) (Ω := Ω) n
    pairingH1 (p := p) n χ (kummer n K Ω a) = artinChar (p := p) n χ a := by
  haveI := hasKummerRoots (K := K) (Ω := Ω) n
  rw [pairingH1, cupH1_kummer, ← pairing_eq_artinChar (p := p)]
  rfl

/-- **Perfectness, left**: a character orthogonal to `H¹(K, μ_n)` is trivial. -/
theorem eq_one_of_forall_pairingH1_eq_zero (χ : LocChar K Ω n)
    (h : ∀ ζ, pairingH1 (p := p) n χ ζ = 0) : χ = 1 := by
  haveI := hasKummerRoots (K := K) (Ω := Ω) n
  refine eq_one_of_forall_pairing_eq_zero (p := p) n χ fun a => ?_
  have := h (kummer n K Ω a)
  rwa [pairingH1, cupH1_kummer] at this

/-- **Perfectness, right**: a class of `H¹(K, μ_n)` orthogonal to all characters is trivial. -/
theorem eq_one_of_forall_pairingH1_eq_zero' (ζ : ContH1 (Ω ≃ₐ[K] Ω) (Mu n Ω))
    (h : ∀ χ : LocChar K Ω n, pairingH1 (p := p) n χ ζ = 0) : ζ = 1 := by
  haveI := hasKummerRoots (K := K) (Ω := Ω) n
  obtain ⟨a, rfl⟩ := kummer_surjective n K Ω ζ
  have ha : a ∈ (powMonoidHom n : Kˣ →* Kˣ).range := by
    by_contra ha
    obtain ⟨χ, hχ⟩ := exists_pairing_ne_zero_of_not_mem_pow (p := p) (Ω := Ω) n ha
    apply hχ
    have := h χ
    rwa [pairingH1, cupH1_kummer] at this
  rw [← MonoidHom.mem_ker, ker_kummer]
  exact ha

end PadicField
