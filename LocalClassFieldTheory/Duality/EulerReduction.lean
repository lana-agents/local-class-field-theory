/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.H3Local

/-!
# Reduction of the local Euler characteristic formula to simple modules

With `H³ = 0` (`PadicField.LocalH3Vanishing`), the Euler characteristic formula is closed under
arbitrary extensions (`PadicField.eulerCharacteristicFor_of_shortExact_of_localH3Vanishing`), so
by dévissage (`Brauer.finite_module_induction`) it suffices to prove it for **simple** finite
discrete `G_K`-modules (irreducible `𝔽_ℓ[G_K]`-modules, `Brauer.IsSimpleGModule`):

* **`PadicField.localEulerCharacteristic_of_simple`** : `LocalH3Vanishing K Ω` and the Euler
  characteristic formula for all simple modules imply `LocalEulerCharacteristic p K Ω`;
* **`PadicField.localEulerCharacteristic_of_h3UnitsVanishing`** : the same with
  `LocalH3Vanishing` replaced by `H³(K', Ωˣ) = 0` for all finite `K' ⊆ Ω`
  (`PadicField.localH3Vanishing_of_h3UnitsVanishing`).

The formula for simple modules is the remaining input (classically: Brauer's induction theorem
reduces it to modules induced from cyclic subgroups, then Shapiro's lemma and the cases `ℤ/ℓ`,
`μ_ℓ`; Serre, *Galois cohomology* II.5.7); it is known here for the simple modules `ℤ/ℓ`
(`PadicField.eulerCharacteristicFor_trivZMod_prime`) and `μ_ℓ`.
-/

open ContH2 groupCohomology

set_option linter.unusedSectionVars false

namespace PadicField

open Brauer

universe u

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

variable (p) in
include hp in
/-- **The local Euler characteristic formula from `H³ = 0` and the simple modules.** -/
theorem localEulerCharacteristic_of_simple (h3 : LocalH3Vanishing.{u} K Ω)
    (hs : ∀ (A : Type u) [CommGroup A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
      [MulDistribMulAction (Ω ≃ₐ[K] Ω) A] [SmoothAction (Ω ≃ₐ[K] Ω) A],
      IsSimpleGModule (Ω ≃ₐ[K] Ω) A → EulerCharacteristicFor p K Ω A) :
    LocalEulerCharacteristic.{u} p K Ω := by
  intro M _ _ _ _ _ _
  refine finite_module_induction (G := Ω ≃ₐ[K] Ω)
    (fun A _ _ => ∀ [TopologicalSpace A] [DiscreteTopology A] [SmoothAction (Ω ≃ₐ[K] Ω) A],
      EulerCharacteristicFor p K Ω A)
    (fun _ _ _ _ _ _ _ => eulerCharacteristicFor_of_subsingleton)
    (fun A _ _ _ _ hsim _ _ _ => hs A hsim) ?_ M
  intro A B C _ _ _ _ _ _ _ _ _ _ _ _ S hA hC _ _ _
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  letI : TopologicalSpace C := ⊥
  haveI : DiscreteTopology C := ⟨rfl⟩
  exact eulerCharacteristicFor_of_shortExact_of_localH3Vanishing h3 S hA hC

variable (p) in
include hp in
/-- **The local Euler characteristic formula from `H³(K', Ωˣ) = 0` and the simple modules.** -/
theorem localEulerCharacteristic_of_h3UnitsVanishing
    (hU : ∀ K' : IntermediateField K Ω, FiniteDimensional K K' → H3UnitsVanishing K' Ω)
    (hs : ∀ (A : Type u) [CommGroup A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
      [MulDistribMulAction (Ω ≃ₐ[K] Ω) A] [SmoothAction (Ω ≃ₐ[K] Ω) A],
      IsSimpleGModule (Ω ≃ₐ[K] Ω) A → EulerCharacteristicFor p K Ω A) :
    LocalEulerCharacteristic.{u} p K Ω :=
  localEulerCharacteristic_of_simple p (localH3Vanishing_of_h3UnitsVanishing p hU) hs

end PadicField
