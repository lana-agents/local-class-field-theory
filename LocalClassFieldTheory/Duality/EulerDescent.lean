/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.EulerFinite

/-!
# Descent of the Euler characteristic formula along `ℓ`-extensions

Let `ℓ` be a prime and `X` a finite discrete `G_K`-module killed by `ℓ`, with a `G_K`-equivariant
automorphism `R` such that `R^ℓ = 1`. Put `D = R - 1`. Then `D^ℓ = R^ℓ - 1 = 0` (characteristic
`ℓ`, `PadicField.dOp_iterate_eq_one`), so `X` is filtered by `X_k = ker D^k`
(`PadicField.kerFilt`, `0 = X_0 ⊆ X_1 ⊆ … ⊆ X_ℓ = X`) and `D^k` maps `X_{k+1}/X_k` injectively
into `X_1 = X^R` (`PadicField.filtMap`). If `#X = #X_1^ℓ` all these maps are onto (counting,
`PadicField.filtMap_surjective_of_card`), and the multiplicativity of the Euler ratio
(`PadicField.eulerRatio_shortExact`, `PadicField.ratioSub_ses`) gives

* **`PadicField.eulerRatio_eq_pow_of_aut`** : `ρ(X) = ρ(X^R)^ℓ`.

Applied to `X = CoInd_{G_{K₁}} M` for a Galois extension `K₁/K` of degree `ℓ`, with `R` the
translation by a generator of `Gal(K₁/K)` (`PadicField.coIndShift`, `X^R = M` the constant
functions) and Shapiro's lemma (`PadicField.eulerRatio_coInd`: `ρ_K(CoInd M) = ρ_{K₁}(M)`):

* **`PadicField.eulerRatio_res_eq_pow`** : `ρ_{K₁}(M) = ρ_K(M)^ℓ` for `M` killed by `ℓ`;
* **`PadicField.eulerCharacteristicFor_of_cyclic_descent`** : the Euler characteristic formula
  for `M` over `K₁` implies it over `K`.
-/

open groupCohomology Brauer ContH2 IntermediateField

set_option linter.unusedSectionVars false

universe v

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

section Binomial

variable {X : Type*} [CommGroup X]

/-- `D x = R x / x`. -/
def dOp (R : X →* X) : X →* X where
  toFun x := R x / x
  map_one' := by simp
  map_mul' x y := by simp only [map_mul]; exact mul_div_mul_comm _ _ _ _

theorem dOp_apply (R : X →* X) (x : X) : dOp R x = R x / x := rfl

/-- **`D^ℓ = 0`**: if `X` is killed by the prime `ℓ` and `R^ℓ = 1`, then `(R - 1)^ℓ = 0`. -/
theorem dOp_iterate_eq_one {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (hX : ∀ x : X, x ^ ℓ = 1) (R : X →* X)
    (hR : ∀ x, R^[ℓ] x = x) (x : X) : (dOp R)^[ℓ] x = 1 := by
  by_cases hs : Subsingleton X
  · exact Subsingleton.elim _ _
  rw [not_subsingleton_iff_nontrivial] at hs
  let R' : AddMonoid.End (Additive X) := MonoidHom.toAdditive R
  let E : AddMonoid.End (Additive X) := R' - 1
  haveI : CharP (AddMonoid.End (Additive X)) ℓ := by
    refine ⟨fun n => ⟨fun h => ?_, fun h => ?_⟩⟩
    · obtain ⟨y, hy⟩ := exists_ne (1 : X)
      have h1 := congrArg (fun f : AddMonoid.End (Additive X) => f (Additive.ofMul y)) h
      simp only [AddMonoid.End.natCast_apply] at h1
      have h2 : y ^ n = 1 := by
        rw [← toMul_ofMul y, ← toMul_nsmul, h1]
        rfl
      rw [← orderOf_eq_prime (hX y) hy]
      exact orderOf_dvd_of_pow_eq_one h2
    · obtain ⟨m, rfl⟩ := h
      ext a
      have : ℓ • a = 0 := by
        rw [← ofMul_toMul a, ← ofMul_pow, hX]
        rfl
      have h0 : ((ℓ * m : ℕ) : AddMonoid.End (Additive X)) a = 0 := by
        rw [AddMonoid.End.natCast_apply, mul_nsmul, this, nsmul_zero]
      rw [h0]
      rfl
  have hsR : Function.Semiconj Additive.ofMul R R' := fun _ => rfl
  have hsD : Function.Semiconj Additive.ofMul (dOp R) E := fun _ => rfl
  have hR'ℓ : R' ^ ℓ = 1 := by
    ext a
    rw [AddMonoid.End.coe_pow, ← ofMul_toMul a, ← hsR.iterate_right ℓ, hR]
    rfl
  have hEℓ : E ^ ℓ = 0 := by
    change (R' - 1) ^ ℓ = 0
    rw [sub_pow_char_of_commute ℓ (Commute.one_right R'), hR'ℓ, one_pow, sub_self]
  have := hsD.iterate_right ℓ x
  rw [← AddMonoid.End.coe_pow, hEℓ] at this
  exact Additive.ofMul.injective this

end Binomial


/-! ### The Euler ratio of a `G_K`-stable subgroup -/

section Sub

variable {X : Type*} [CommGroup X] [Finite X] [TopologicalSpace X] [DiscreteTopology X]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) X] [SmoothAction (Ω ≃ₐ[K] Ω) X]

variable (p K Ω) in
/-- `ρ(B)` for a `G_K`-stable subgroup `B ≤ X`. -/
noncomputable def ratioSub (B : Subgroup X) (hB : IsGStable (G := Ω ≃ₐ[K] Ω) B) : ℚ :=
  letI := subAction B hB
  eulerRatio p K Ω B

theorem ratioSub_eq_of_equiv {M : Type*} [CommGroup M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]
    (B : Subgroup X) (hB : IsGStable (G := Ω ≃ₐ[K] Ω) B) (τ : M ≃* B)
    (hτ : ∀ (g : Ω ≃ₐ[K] Ω) (m : M), (τ (g • m) : X) = g • (τ m : X)) :
    eulerRatio p K Ω M = ratioSub p K Ω B hB := by
  letI := subAction B hB
  haveI := smoothAction_sub B hB
  exact eulerRatio_congr M τ fun g m => Subtype.ext (hτ g m)

theorem ratioSub_congr {B B' : Subgroup X} (h : B = B') (hB : IsGStable (G := Ω ≃ₐ[K] Ω) B)
    (hB' : IsGStable (G := Ω ≃ₐ[K] Ω) B') : ratioSub p K Ω B hB = ratioSub p K Ω B' hB' := by
  subst h
  rfl

theorem ratioSub_top (h : IsGStable (G := Ω ≃ₐ[K] Ω) (⊤ : Subgroup X)) :
    ratioSub p K Ω ⊤ h = eulerRatio p K Ω X :=
  (ratioSub_eq_of_equiv (M := X) ⊤ h Subgroup.topEquiv.symm fun _ _ => rfl).symm

include hp in
theorem ratioSub_bot (h : IsGStable (G := Ω ≃ₐ[K] Ω) (⊥ : Subgroup X)) :
    ratioSub p K Ω ⊥ h = 1 := by
  letI := subAction (⊥ : Subgroup X) h
  haveI := smoothAction_sub (⊥ : Subgroup X) h
  haveI : Subsingleton (⊥ : Subgroup X) := ⟨fun a b => Subtype.ext (by
    rw [(Subgroup.mem_bot.1 a.2), (Subgroup.mem_bot.1 b.2)])⟩
  exact eulerRatio_of_subsingleton (p := p) (K := K) (Ω := Ω) _

include hp in
/-- **Multiplicativity for subgroups**: if `A ≤ B` and `φ : B → C` is an equivariant surjection
with kernel `A`, then `ρ(B) = ρ(A) ρ(C)`. -/
theorem ratioSub_ses (A B C : Subgroup X) (hA : IsGStable (G := Ω ≃ₐ[K] Ω) A)
    (hB : IsGStable (G := Ω ≃ₐ[K] Ω) B) (hC : IsGStable (G := Ω ≃ₐ[K] Ω) C) (hAB : A ≤ B)
    (φ : B →* C) (hφ : ∀ (g : Ω ≃ₐ[K] Ω) (b : B), ((φ ⟨g • (b : X), hB g b b.2⟩ : C) : X) =
      g • (φ b : X))
    (hsurj : Function.Surjective φ) (hker : ∀ b : B, φ b = 1 ↔ (b : X) ∈ A) :
    ratioSub p K Ω B hB = ratioSub p K Ω A hA * ratioSub p K Ω C hC := by
  letI := subAction A hA
  letI := subAction B hB
  letI := subAction C hC
  haveI := smoothAction_sub A hA
  haveI := smoothAction_sub B hB
  haveI := smoothAction_sub C hC
  let S : GShortExact (Ω ≃ₐ[K] Ω) A B C :=
    { i := Subgroup.inclusion hAB
      π := φ
      map_smul_i := fun _ _ => rfl
      map_smul_π := fun g b => Subtype.ext (hφ g b)
      injective := Subgroup.inclusion_injective hAB
      surjective := hsurj
      exact := fun b => by
        rw [hker]
        constructor
        · intro hb
          exact ⟨⟨b, hb⟩, rfl⟩
        · rintro ⟨a, rfl⟩
          exact a.2 }
  exact eulerRatio_shortExact (p := p) S

end Sub

/-! ### The filtration by the kernels of `(R - 1)^k` -/

section Filtration

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
variable {X : Type*} [CommGroup X] [Finite X] [TopologicalSpace X] [DiscreteTopology X]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) X] [SmoothAction (Ω ≃ₐ[K] Ω) X]
variable (R : X →* X) (hR : ∀ (g : Ω ≃ₐ[K] Ω) (x : X), R (g • x) = g • R x)

/-- `D^k = (R - 1)^k`. -/
def dPow : ℕ → (X →* X)
  | 0 => MonoidHom.id X
  | k + 1 => (dOp R).comp (dPow k)

theorem dPow_succ_apply (k : ℕ) (x : X) : dPow R (k + 1) x = dOp R (dPow R k x) := rfl

theorem dPow_apply (k : ℕ) (x : X) : dPow R k x = (dOp R)^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ← ih]; rfl

include hR in
theorem dOp_smul (g : Ω ≃ₐ[K] Ω) (x : X) : dOp R (g • x) = g • dOp R x := by
  rw [dOp_apply, dOp_apply, hR, smul_div']

include hR in
theorem dPow_smul (k : ℕ) (g : Ω ≃ₐ[K] Ω) (x : X) : dPow R k (g • x) = g • dPow R k x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [dPow_succ_apply, dPow_succ_apply, ih, dOp_smul R hR]

/-- `X_k = ker (R - 1)^k`. -/
def kerFilt (k : ℕ) : Subgroup X := (dPow R k).ker

include hR in
theorem filt_stable (k : ℕ) : IsGStable (G := Ω ≃ₐ[K] Ω) (kerFilt R k) := fun g x hx => by
  rw [kerFilt, MonoidHom.mem_ker] at hx ⊢
  rw [dPow_smul R hR, hx, smul_one]

theorem filt_mono (k : ℕ) : kerFilt R k ≤ kerFilt R (k + 1) := fun x hx => by
  rw [kerFilt, MonoidHom.mem_ker] at hx ⊢
  rw [dPow_succ_apply, hx, map_one]

theorem mem_filt_one (x : X) : x ∈ kerFilt R 1 ↔ R x = x := by
  rw [kerFilt, MonoidHom.mem_ker, dPow_apply, Function.iterate_one, dOp_apply, div_eq_one]

theorem filt_zero : kerFilt R 0 = ⊥ := by
  ext x
  rw [kerFilt, MonoidHom.mem_ker, dPow_apply, Function.iterate_zero, id, Subgroup.mem_bot]

/-- `D^k : X_{k+1} → X_1`. -/
def filtMap (k : ℕ) : kerFilt R (k + 1) →* kerFilt R 1 where
  toFun x := ⟨dPow R k x, by
    rw [kerFilt, MonoidHom.mem_ker, dPow_apply, Function.iterate_one, ← dPow_succ_apply]
    exact x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem filtMap_eq_one_iff (k : ℕ) (x : kerFilt R (k + 1)) :
    filtMap R k x = 1 ↔ (x : X) ∈ kerFilt R k :=
  Subtype.ext_iff.trans Iff.rfl

theorem card_filt_succ (k : ℕ) :
    Nat.card (kerFilt R (k + 1)) = Nat.card (kerFilt R k) * Nat.card (filtMap R k).range := by
  rw [card_eq_card_ker_mul_card_range (filtMap R k)]
  congr 1
  refine Nat.card_congr ⟨fun x => ⟨x.1.1, (filtMap_eq_one_iff R k x.1).1 x.2⟩,
    fun y => ⟨⟨y.1, filt_mono R k y.2⟩, (filtMap_eq_one_iff R k _).2 y.2⟩,
    fun x => rfl, fun y => rfl⟩

theorem card_filt_le (k : ℕ) : Nat.card (kerFilt R k) ≤ Nat.card (kerFilt R 1) ^ k := by
  induction k with
  | zero => rw [filt_zero, Subgroup.card_bot, pow_zero]
  | succ k ih =>
    rw [card_filt_succ, pow_succ]
    exact Nat.mul_le_mul ih (Subgroup.card_le_card_group _)

/-- If `#X_n = #X_1^n`, every `D^k : X_{k+1} → X_1`, `k < n`, is surjective. -/
theorem filtMap_surjective_of_card {n : ℕ}
    (hn : Nat.card (kerFilt R n) = Nat.card (kerFilt R 1) ^ n) {k : ℕ} (hk : k < n) :
    Function.Surjective (filtMap R k) := by
  set b := Nat.card (kerFilt R 1)
  have hb : 0 < b := Nat.card_pos
  -- `#X_i ≤ #X_j · b^(i - j)` for `j ≤ i`
  have hle : ∀ j i, j ≤ i → Nat.card (kerFilt R i) ≤ Nat.card (kerFilt R j) * b ^ (i - j) := by
    intro j i hji
    induction i, hji using Nat.le_induction with
    | base => simp
    | succ i hji ih =>
      rw [card_filt_succ, Nat.sub_add_comm hji, pow_succ, ← mul_assoc]
      exact Nat.mul_le_mul ih (Subgroup.card_le_card_group _)
  by_contra hns
  have hlt : Nat.card (filtMap R k).range < b := by
    refine lt_of_le_of_ne (Subgroup.card_le_card_group _) fun h => hns ?_
    exact MonoidHom.range_eq_top.1 (Subgroup.eq_top_of_card_eq _ h)
  have h1 : Nat.card (kerFilt R (k + 1)) < Nat.card (kerFilt R k) * b := by
    rw [card_filt_succ]
    exact Nat.mul_lt_mul_of_pos_left hlt Nat.card_pos
  have h2 := hle (k + 1) n hk
  have h3 := card_filt_le R k
  have : Nat.card (kerFilt R n) < b ^ n := by
    calc Nat.card (kerFilt R n) ≤ Nat.card (kerFilt R (k + 1)) * b ^ (n - (k + 1)) := h2
      _ < Nat.card (kerFilt R k) * b * b ^ (n - (k + 1)) :=
          Nat.mul_lt_mul_of_pos_right h1 (pow_pos hb _)
      _ ≤ b ^ k * b * b ^ (n - (k + 1)) := by gcongr
      _ = b ^ n := by
          rw [mul_assoc, ← pow_succ', ← pow_add]
          congr 1
          omega
  omega

include hp hR in
/-- **`ρ(X) = ρ(X^R)^ℓ`** for a `G_K`-equivariant `R` with `R^ℓ = 1` on a module `X` killed by
the prime `ℓ`, provided `#X = #(X^R)^ℓ`. -/
theorem eulerRatio_eq_pow_of_aut (hX : ∀ x : X, x ^ ℓ = 1) (hRℓ : ∀ x, R^[ℓ] x = x)
    (hcard : Nat.card X = Nat.card (kerFilt R 1) ^ ℓ) :
    eulerRatio p K Ω X = ratioSub p K Ω (kerFilt R 1) (filt_stable R hR 1) ^ ℓ := by
  have htop : kerFilt R ℓ = ⊤ := by
    ext x
    simp only [kerFilt, MonoidHom.mem_ker, dPow_apply, Subgroup.mem_top, iff_true]
    exact dOp_iterate_eq_one hX R hRℓ x
  have hn : Nat.card (kerFilt R ℓ) = Nat.card (kerFilt R 1) ^ ℓ := by
    rw [htop, Subgroup.card_top, hcard]
  have key : ∀ k, k ≤ ℓ → ratioSub p K Ω (kerFilt R k) (filt_stable R hR k) =
      ratioSub p K Ω (kerFilt R 1) (filt_stable R hR 1) ^ k := by
    intro k hk
    induction k with
    | zero =>
      rw [pow_zero, ratioSub_congr (filt_zero R) _ (fun g x hx => by
        rw [Subgroup.mem_bot.1 hx, smul_one]; exact Subgroup.one_mem _)]
      exact ratioSub_bot (p := p) _
    | succ k ih =>
      rw [ratioSub_ses (p := p) (kerFilt R k) (kerFilt R (k + 1)) (kerFilt R 1) (filt_stable R hR k)
        (filt_stable R hR (k + 1)) (filt_stable R hR 1) (filt_mono R k) (filtMap R k)
        (fun g x => dPow_smul R hR k g x) (filtMap_surjective_of_card R hn (by omega))
        (filtMap_eq_one_iff R k), ih (by omega), pow_succ]
  rw [← ratioSub_top (p := p) (fun g x _ => Subgroup.mem_top _),
    ← ratioSub_congr htop (filt_stable R hR ℓ), key ℓ le_rfl]

end Filtration

/-! ### The Euler ratio of a coinduced module -/

section CoIndRatio

variable (K' : IntermediateField K Ω) [FiniteDimensional K K']
variable (M : Type*) [CommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]

/-- **`ρ_K(CoInd_{G_{K'}} M) = ρ_{K'}(M)`** (Shapiro's lemma). -/
theorem eulerRatio_coInd :
    eulerRatio p K Ω (ContH2.CoInd K'.fixingSubgroup M) =
      (letI := resAction K' M; eulerRatio p K' Ω M) := by
  letI := resAction K' M
  have hA := resCompat_resAction K' M
  have hc : padicValNat p (Nat.card (ContH2.CoInd K'.fixingSubgroup M)) *
      Module.finrank ℚ_[p] K = padicValNat p (Nat.card M) * Module.finrank ℚ_[p] K' := by
    rw [ContH2.CoInd.card_coInd, padicValNat.pow,
      card_quotient_fixingSubgroup, ← Module.finrank_mul_finrank ℚ_[p] K K']
    ring
  unfold eulerRatio
  rw [card_h0_coInd hA, card_h1_coInd hA, card_h2_coInd hA, hc]

end CoIndRatio

/-! ### Descent along a cyclic extension of degree `ℓ` -/

section Cyclic

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
variable (K₁ : IntermediateField K Ω) [FiniteDimensional K K₁] [K₁.fixingSubgroup.Normal]
variable {M : Type*} [CommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]

theorem smul_quot_eq_mul (g : Ω ≃ₐ[K] Ω) (c : (Ω ≃ₐ[K] Ω) ⧸ K₁.fixingSubgroup) :
    g • c = (g : (Ω ≃ₐ[K] Ω) ⧸ K₁.fixingSubgroup) * c := by
  induction c using QuotientGroup.induction_on with | H a => rfl

/-- Translation `F ↦ (c ↦ F(c τ))` on `CoInd_{G_{K₁}} M`, a `G_K`-equivariant automorphism. -/
def coIndShift (τ : (Ω ≃ₐ[K] Ω) ⧸ K₁.fixingSubgroup) :
    ContH2.CoInd K₁.fixingSubgroup M →* ContH2.CoInd K₁.fixingSubgroup M where
  toFun F := (fun c => (F : (Ω ≃ₐ[K] Ω) ⧸ K₁.fixingSubgroup → M) (c * τ))
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coIndShift_apply (τ : (Ω ≃ₐ[K] Ω) ⧸ K₁.fixingSubgroup)
    (F : ContH2.CoInd K₁.fixingSubgroup M) (c : (Ω ≃ₐ[K] Ω) ⧸ K₁.fixingSubgroup) :
    coIndShift K₁ τ F c = F (c * τ) := rfl

theorem coIndShift_smul (τ : (Ω ≃ₐ[K] Ω) ⧸ K₁.fixingSubgroup) (g : Ω ≃ₐ[K] Ω)
    (F : ContH2.CoInd K₁.fixingSubgroup M) :
    coIndShift K₁ τ (g • F) = g • coIndShift K₁ τ F := by
  refine ContH2.CoInd.ext fun c => ?_
  change g • F (g⁻¹ • (c * τ)) = g • F (g⁻¹ • c * τ)
  rw [smul_quot_eq_mul, smul_quot_eq_mul, mul_assoc]

theorem coIndShift_iterate (τ : (Ω ≃ₐ[K] Ω) ⧸ K₁.fixingSubgroup) (k : ℕ)
    (F : ContH2.CoInd K₁.fixingSubgroup M) (c : (Ω ≃ₐ[K] Ω) ⧸ K₁.fixingSubgroup) :
    (coIndShift K₁ τ)^[k] F c = F (c * τ ^ k) := by
  induction k generalizing F with
  | zero => rw [Function.iterate_zero, id, pow_zero, mul_one]
  | succ k ih => rw [Function.iterate_succ_apply, ih, coIndShift_apply, pow_succ, mul_assoc]

include hℓ in
/-- **Descent of the Euler characteristic formula along a cyclic extension of degree `ℓ`**: if
`K₁/K` is Galois of prime degree `ℓ` and `M` is killed by `ℓ`, then `ρ_{K₁}(M) = ρ_K(M)^ℓ`; in
particular the formula for `M` over `K₁` implies it over `K`. -/
theorem eulerRatio_res_eq_pow (hdeg : Module.finrank K K₁ = ℓ) (hM : ∀ m : M, m ^ ℓ = 1) :
    (letI := resAction K₁ M; eulerRatio p K₁ Ω M) = eulerRatio p K Ω M ^ ℓ := by
  set U := K₁.fixingSubgroup
  haveI := ContH2.CoInd.smoothAction (A := M) K₁.fixingSubgroup_isOpen
  haveI : Finite (ContH2.CoInd U M) := inferInstanceAs (Finite ((Ω ≃ₐ[K] Ω) ⧸ U → M))
  have hcardQ : Nat.card ((Ω ≃ₐ[K] Ω) ⧸ U) = ℓ := by
    rw [Nat.card_eq_fintype_card, card_quotient_fixingSubgroup, hdeg]
  -- a generator `τ` of `G_K / G_{K₁}`
  haveI : Fact (Nat.card ((Ω ≃ₐ[K] Ω) ⧸ U)).Prime := ⟨hcardQ ▸ hℓ.out⟩
  haveI : Nontrivial ((Ω ≃ₐ[K] Ω) ⧸ U) :=
    Finite.one_lt_card_iff_nontrivial.1 (hcardQ ▸ hℓ.out.one_lt)
  obtain ⟨τ, hτ⟩ := exists_ne (1 : (Ω ≃ₐ[K] Ω) ⧸ U)
  have hτgen : ∀ c : (Ω ≃ₐ[K] Ω) ⧸ U, ∃ k : ℕ, c = τ ^ k := by
    intro c
    have htop : Subgroup.zpowers τ = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      have hdvd := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers τ)
      rcases (Nat.dvd_prime (Fact.out : (Nat.card ((Ω ≃ₐ[K] Ω) ⧸ U)).Prime)).1 hdvd with h | h
      · exact absurd (Subgroup.zpowers_eq_bot.1 (Subgroup.card_eq_one.1 h)) hτ
      · exact h
    have hc : c ∈ Subgroup.zpowers τ := htop ▸ Subgroup.mem_top c
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).2 hc
    exact ⟨k, hk.symm⟩
  have hτℓ : τ ^ ℓ = 1 := by rw [← hcardQ]; exact pow_card_eq_one'
  set R := coIndShift (M := M) K₁ τ
  have hR : ∀ (g : Ω ≃ₐ[K] Ω) (F : ContH2.CoInd U M), R (g • F) = g • R F :=
    coIndShift_smul K₁ τ
  have hRℓ : ∀ F, R^[ℓ] F = F := fun F => ContH2.CoInd.ext fun c => by
    rw [coIndShift_iterate, hτℓ, mul_one]
  have hX : ∀ F : ContH2.CoInd U M, F ^ ℓ = 1 := fun F => funext fun c => hM (F c)
  -- the fixed points of `R` are the constant functions, `≃ M`
  have hconst : ∀ F ∈ kerFilt R 1, ∀ c, F c = F 1 := by
    intro F hF c
    rw [mem_filt_one] at hF
    obtain ⟨k, rfl⟩ := hτgen c
    induction k with
    | zero => rw [pow_zero]
    | succ k ih =>
      have e1 : F (τ ^ (k + 1)) = R F (τ ^ k) := by
        rw [coIndShift_apply, pow_succ]
      rw [e1, hF, ih]
  let e : M ≃* kerFilt R 1 :=
    { toFun := fun m => ⟨diag M U m, (mem_filt_one R _).2 rfl⟩
      invFun := fun F => (F : ContH2.CoInd U M) 1
      left_inv := fun m => rfl
      right_inv := fun F => Subtype.ext (ContH2.CoInd.ext fun c => (hconst F F.2 c).symm)
      map_mul' := fun _ _ => rfl }
  have he : ∀ (g : Ω ≃ₐ[K] Ω) (m : M), ((e (g • m) : kerFilt R 1) : ContH2.CoInd U M) =
      g • ((e m : kerFilt R 1) : ContH2.CoInd U M) := fun g m => diag_smul M U g m
  have hcard : Nat.card (ContH2.CoInd U M) = Nat.card (kerFilt R 1) ^ ℓ := by
    rw [ContH2.CoInd.card_coInd, ← Nat.card_congr e.toEquiv, ← Nat.card_eq_fintype_card,
      hcardQ]
  rw [← eulerRatio_coInd K₁ M, eulerRatio_eq_pow_of_aut R hR hX hRℓ hcard,
    ← ratioSub_eq_of_equiv _ _ e he]

include hℓ in
/-- **The Euler characteristic formula descends along cyclic extensions of degree `ℓ`** for
modules killed by `ℓ`. -/
theorem eulerCharacteristicFor_of_cyclic_descent (hdeg : Module.finrank K K₁ = ℓ)
    (hM : ∀ m : M, m ^ ℓ = 1)
    (h : letI := resAction K₁ M; EulerCharacteristicFor p K₁ Ω M) :
    EulerCharacteristicFor p K Ω M := by
  have key := eulerRatio_res_eq_pow (p := p) K₁ hdeg hM
  letI := resAction K₁ M
  haveI := smoothAction_resAction K₁ M
  have h1 := (eulerCharacteristicFor_iff_eulerRatio (p := p) (K := K₁) (Ω := Ω) M).1 h
  rw [h1] at key
  rw [eulerCharacteristicFor_iff_eulerRatio]
  exact ((pow_eq_one_iff_of_nonneg (eulerRatio_pos M).le hℓ.out.ne_zero).1 key.symm)

end Cyclic

end PadicField
