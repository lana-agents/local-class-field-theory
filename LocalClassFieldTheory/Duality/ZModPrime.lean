/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.Devissage
import LocalClassFieldTheory.Brauer.CorBr

/-!
# `H²(K, ℤ/ℓ)` for a prime `ℓ`, without roots of unity in `K`

## Restriction, conjugation, corestriction (generic)

For a subgroup `H` of a topological group `G` and a `G`-module `M`:

* `ContH2.res H : H²(G, M) → H²(H, M)` (restriction);
* `ContH2.conj H σ hσ : H²(H, M) → H²(H, M)` for `σ ∈ G` normalising `H`, induced by
  `h ↦ σ⁻¹ h σ` and `m ↦ σ • m`; **`ContH2.conj_res`**: `conj_σ ∘ res = res` (inner automorphisms
  act trivially; the cochain identity is `ContH2.cor_res_aux`);
* **`ContH2.res_injective_of_coprime`**: if `H` is open of finite index `d` and `M` is killed by
  `n` with `gcd(n, d) = 1`, restriction is injective (`cor ∘ res = (·)^d`).

## Galois cohomology of `ℤ/ℓ`

Let `ℓ` be a prime, `ζ` a generator of `μ_ℓ(Ω)`, `K' = K(ζ)` and `H = Gal(Ω/K')`. Then
`[K' : K] ≤ ℓ - 1` is prime to `ℓ`, so `res : H²(K, ℤ/ℓ) → H²(K', ℤ/ℓ)` is injective. Over `K'`,
`ℤ/ℓ ≅ μ_ℓ` (`k ↦ ζ^k`), and conjugation by `σ ∈ G_K` acts on `H²(K', μ_ℓ) ⊆ Br(K')` trivially
(every Brauer class of `K'` is restricted from `K`, `PadicField.res_surjective`), while on
`H²(K', ℤ/ℓ)` it acts trivially on restricted classes. Comparing both through `ℤ/ℓ ≅ μ_ℓ`, which
twists conjugation by the cyclotomic character `χ(σ)`, gives `y^{χ(σ)} = y` for `y = res β`, and
`χ(σ) ≠ 1` for some `σ` if `μ_ℓ ⊄ K`. Hence:

* **`PadicField.h2_trivZMod_prime_eq_one`**: `H²(K, ℤ/ℓ) = 0` if `μ_ℓ ⊄ K`;
* **`PadicField.card_h2_trivZMod_prime`**: `#H²(K, ℤ/ℓ) = #μ_ℓ(K)` (in all cases);
* **`PadicField.eulerCharacteristicFor_trivZMod_prime`**: the Euler characteristic formula for
  `ℤ/ℓ`, without any assumption on `K`;
* **`PadicField.tateDualityFor_trivZMod_prime`**, **`PadicField.tateDualityFor_mu_prime`**:
  local Tate duality for `ℤ/ℓ` and `μ_ℓ` in all degrees, without any assumption on `K`.
-/

open ContH2 groupCohomology KummerTheory

set_option linter.unusedSectionVars false

namespace ContH2

section Conj

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]
  (H : Subgroup G)

/-- Restriction `H²(G, M) → H²(H, M)`. -/
def res : ContH2 G M →* ContH2 H M :=
  map H.subtype continuous_subtype_val (MonoidHom.id M) (fun _ _ => rfl)

theorem res_mk (f : cocycles G M) :
    res H (mk f) =
      mk (cocyclesMap H.subtype continuous_subtype_val (MonoidHom.id M) (fun _ _ => rfl) f) :=
  rfl

/-- `H²(G, M)` is killed by `n` if `M` is. -/
theorem pow_eq_one_of_forall {n : ℕ} (hM : ∀ m : M, m ^ n = 1) (α : ContH2 G M) : α ^ n = 1 := by
  induction α using induction_on with | h f => ?_
  rw [← map_pow, ← map_one (mk (G := G) (M := M))]
  congr 1
  exact cocycles_ext fun a b => by simp [hM]

/-- **Restriction to an open subgroup of index prime to `n` is injective** on `H²` of a module
killed by `n`. -/
theorem res_injective_of_coprime [IsTopologicalGroup G] (hH : IsOpen (H : Set G))
    [Fintype (G ⧸ H)] {n : ℕ} (hM : ∀ m : M, m ^ n = 1)
    (hcop : Nat.Coprime n (Fintype.card (G ⧸ H))) : Function.Injective (res (M := M) H) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro α hα
  rw [MonoidHom.mem_ker] at hα
  have h1 : α ^ Fintype.card (G ⧸ H) = 1 := by
    rw [← cor_res H hH α]
    change cor H hH (res H α) = 1
    rw [hα, map_one]
  have h2 := pow_eq_one_of_forall hM α
  have := pow_gcd_eq_one.2 ⟨h2, h1⟩
  rw [hcop, pow_one] at this
  exact this

variable [IsTopologicalGroup G]

/-- Conjugation `h ↦ σ⁻¹ h σ` on a subgroup normalised by `σ`. -/
def conjHom (σ : G) (hσ : ∀ h ∈ H, σ⁻¹ * h * σ ∈ H) : H →* H where
  toFun h := ⟨σ⁻¹ * h * σ, hσ h h.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp only [Subgroup.coe_mul]; group

theorem continuous_conjHom (σ : G) (hσ : ∀ h ∈ H, σ⁻¹ * h * σ ∈ H) :
    Continuous (conjHom H σ hσ) :=
  (((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _)

/-- **Conjugation by `σ`** on `H²(H, M)`: `f ↦ ((g, h) ↦ σ • f(σ⁻¹ g σ, σ⁻¹ h σ))`. -/
def conj (σ : G) (hσ : ∀ h ∈ H, σ⁻¹ * h * σ ∈ H) : ContH2 H M →* ContH2 H M :=
  map (conjHom H σ hσ) (continuous_conjHom H σ hσ) (MulDistribMulAction.toMonoidHom M σ)
    (fun g m => by
      change σ • ((σ⁻¹ * (g : G) * σ) • m) = (g : G) • σ • m
      rw [← mul_smul, ← mul_smul]
      congr 1
      group)

theorem conj_mk (σ : G) (hσ : ∀ h ∈ H, σ⁻¹ * h * σ ∈ H) (f : cocycles H M) :
    conj H σ hσ (mk f) = mk (cocyclesMap (conjHom H σ hσ) (continuous_conjHom H σ hσ)
      (MulDistribMulAction.toMonoidHom M σ) (fun g m => by
        change σ • ((σ⁻¹ * (g : G) * σ) • m) = (g : G) • σ • m
        rw [← mul_smul, ← mul_smul]
        congr 1
        group) f) := rfl

/-- **Inner automorphisms act trivially**: `conj_σ ∘ res = res`. -/
theorem conj_res (σ : G) (hσ : ∀ h ∈ H, σ⁻¹ * h * σ ∈ H) (α : ContH2 G M) :
    conj H σ hσ (res H α) = res H α := by
  induction α using induction_on with | h f => ?_
  rw [res_mk, conj_mk, mk_eq_mk_iff]
  refine ⟨fun x : H => f (σ, σ⁻¹ * x * σ) / f ((x : G), σ), ?_, ?_⟩
  · exact ((isLocallyConstant f).comp_continuous (continuous_const.prodMk
      ((continuous_const.mul continuous_subtype_val).mul continuous_const))).div
      ((isLocallyConstant f).comp_continuous (continuous_subtype_val.prodMk continuous_const))
  · funext gh
    obtain ⟨a, b⟩ := gh
    have key := cor_res_aux (isMulCocycle₂ f) σ a b σ σ
    change (a : G) • (f (σ, σ⁻¹ * (b : G) * σ) / f ((b : G), σ)) /
        (f (σ, σ⁻¹ * ((a : G) * b) * σ) / f ((a : G) * b, σ)) *
        (f (σ, σ⁻¹ * (a : G) * σ) / f ((a : G), σ)) =
      σ • f (σ⁻¹ * (a : G) * σ, σ⁻¹ * (b : G) * σ) / f ((a : G), (b : G))
    rw [key]
    mul_abel

/-- Pushing forward along an `H`-equivariant `ψ : M → N`. -/
theorem conj_map_pow {N : Type*} [CommGroup N] [MulDistribMulAction G N] (σ : G)
    (hσ : ∀ h ∈ H, σ⁻¹ * h * σ ∈ H) (ψ : M →* N)
    (hψ : ∀ (g : H) (m : M), ψ ((MonoidHom.id H) g • m) = g • ψ m) (c : ℕ)
    (htw : ∀ m : M, σ • ψ m = ψ (σ • m) ^ c) (x : ContH2 H M) :
    conj H σ hσ (map (MonoidHom.id H) continuous_id ψ hψ x) =
      map (MonoidHom.id H) continuous_id ψ hψ (conj H σ hσ x) ^ c := by
  induction x using induction_on with | h f => ?_
  rw [map_mk, conj_mk, conj_mk, map_mk, ← map_pow]
  congr 1
  exact cocycles_ext fun a b => htw _

theorem conj_map {N : Type*} [CommGroup N] [MulDistribMulAction G N] (σ : G)
    (hσ : ∀ h ∈ H, σ⁻¹ * h * σ ∈ H) (ψ : M →* N)
    (hψ : ∀ (g : H) (m : M), ψ ((MonoidHom.id H) g • m) = g • ψ m)
    (hψσ : ∀ m : M, σ • ψ m = ψ (σ • m)) (x : ContH2 H M) :
    conj H σ hσ (map (MonoidHom.id H) continuous_id ψ hψ x) =
      map (MonoidHom.id H) continuous_id ψ hψ (conj H σ hσ x) := by
  rw [conj_map_pow H σ hσ ψ hψ 1 (fun m => by rw [pow_one, hψσ]), pow_one]

end Conj

end ContH2

namespace PadicField

open Brauer IntermediateField Polynomial

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

section Zeta

variable (p Ω) in
/-- The generator `ζ = genMu` of `μ_ℓ(Ω)` as an element of `Ω`. -/
noncomputable def zetaΩ : Ω := ((Mu.val (genMu p Ω ℓ) : Ωˣ) : Ω)

theorem mem_zpowers_genMu (x : Mu ℓ Ω) : x ∈ Subgroup.zpowers (genMu p Ω ℓ) :=
  (exists_generator_mu (p := p) (Ω := Ω) ℓ).choose_spec.2 x

theorem smul_eq_of_smul_genMu {g : Ω ≃ₐ[K] Ω} (hg : g • genMu p Ω ℓ = genMu p Ω ℓ)
    (x : Mu ℓ Ω) : g • x = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_genMu (p := p) ℓ x)
  rw [smul_zpow', hg]

theorem isPrimitiveRoot_zetaΩ : IsPrimitiveRoot (zetaΩ p Ω ℓ) ℓ := by
  have h1 : orderOf (zetaΩ p Ω ℓ) = ℓ := by
    rw [zetaΩ, orderOf_units, orderOf_injective _ Mu.val_injective, orderOf_genMu]
  have := IsPrimitiveRoot.orderOf (zetaΩ p Ω ℓ)
  rwa [h1] at this

variable (p K Ω) in
/-- `K' = K(ζ) = K(μ_ℓ)`. -/
noncomputable def kZeta : IntermediateField K Ω := K⟮zetaΩ p Ω ℓ⟯

instance : FiniteDimensional K (kZeta p K Ω ℓ) :=
  adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)

theorem mem_fixingSubgroup_kZeta_iff (g : Ω ≃ₐ[K] Ω) :
    g ∈ (kZeta p K Ω ℓ).fixingSubgroup ↔ g • genMu p Ω ℓ = genMu p Ω ℓ := by
  have hz : g • genMu p Ω ℓ = genMu p Ω ℓ ↔ g (zetaΩ p Ω ℓ) = zetaΩ p Ω ℓ := by
    constructor
    · intro h
      have := congrArg (fun x => ((Mu.val x : Ωˣ) : Ω)) h
      exact this
    · intro h
      exact Mu.ext (Units.ext h)
  rw [hz, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · exact fun h => h _ (mem_adjoin_simple_self K _)
  · intro h x hx
    have hle : kZeta p K Ω ℓ ≤ fixedField (Subgroup.zpowers g) := by
      refine adjoin_simple_le_iff.2 ((mem_fixedField_iff _ _).2 fun τ hτ => ?_)
      have hs : Subgroup.zpowers g ≤ MulAction.stabilizer (Ω ≃ₐ[K] Ω) (zetaΩ p Ω ℓ) :=
        (Subgroup.zpowers_le).2 (MulAction.mem_stabilizer_iff.2 h)
      exact MulAction.mem_stabilizer_iff.1 (hs hτ)
    exact (mem_fixedField_iff _ _).1 (hle hx) g (Subgroup.mem_zpowers g)

theorem smul_eq_of_mem_fixingSubgroup {g : Ω ≃ₐ[K] Ω} (hg : g ∈ (kZeta p K Ω ℓ).fixingSubgroup)
    (x : Mu ℓ Ω) : g • x = x :=
  smul_eq_of_smul_genMu ℓ ((mem_fixingSubgroup_kZeta_iff ℓ g).1 hg) x

theorem conj_mem_fixingSubgroup (σ : Ω ≃ₐ[K] Ω) :
    ∀ h ∈ (kZeta p K Ω ℓ).fixingSubgroup, σ⁻¹ * h * σ ∈ (kZeta p K Ω ℓ).fixingSubgroup := by
  intro h hh
  rw [mem_fixingSubgroup_kZeta_iff, mul_smul, mul_smul,
    smul_eq_of_mem_fixingSubgroup ℓ hh, inv_smul_smul]

theorem finrank_kZeta_lt : Module.finrank K (kZeta p K Ω ℓ) < ℓ := by
  have hint : IsIntegral K (zetaΩ p Ω ℓ) := Algebra.IsIntegral.isIntegral _
  rw [kZeta, adjoin.finrank hint]
  have hroot : aeval (zetaΩ p Ω ℓ) (cyclotomic ℓ K) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (isPrimitiveRoot_zetaΩ (p := p) ℓ).isRoot_cyclotomic hℓ.out.pos
  have hdvd := minpoly.dvd K _ hroot
  have := natDegree_le_of_dvd hdvd (cyclotomic_ne_zero ℓ K)
  rw [natDegree_cyclotomic, Nat.totient_prime hℓ.out] at this
  have := hℓ.out.pos
  omega

theorem coprime_card_quotient_kZeta :
    Nat.Coprime ℓ (Fintype.card ((Ω ≃ₐ[K] Ω) ⧸ (kZeta p K Ω ℓ).fixingSubgroup)) := by
  rw [card_quotient_fixingSubgroup]
  exact Nat.coprime_of_lt_prime Module.finrank_pos.ne' (finrank_kZeta_lt ℓ) hℓ.out

end Zeta

section Main

theorem trivZMod_pow_eq_one (k : TrivZMod ℓ) : k ^ ℓ = 1 := by
  apply TrivZMod.equiv.injective
  rw [map_pow, map_one, ← ofAdd_toAdd (TrivZMod.equiv k), ← ofAdd_nsmul, nsmul_eq_mul,
    ZMod.natCast_self, zero_mul, ofAdd_zero]

theorem mu_pow_eq_one (m : Mu ℓ Ω) : m ^ ℓ = 1 := Mu.ext (by rw [map_pow, Mu.val_pow_n, map_one])

/-- `H²(H, μ_ℓ) → H²(H, Ωˣ)` for `H = Gal(Ω/K(ζ))`. -/
noncomputable def mapVal :
    ContH2 (kZeta p K Ω ℓ).fixingSubgroup (Mu ℓ Ω) →* ContH2 (kZeta p K Ω ℓ).fixingSubgroup Ωˣ :=
  ContH2.map (MonoidHom.id _) continuous_id Mu.val (fun _ _ => rfl)

theorem mapVal_injective : Function.Injective (mapVal (p := p) (K := K) (Ω := Ω) ℓ) := by
  let E : ContH2 (Ω ≃ₐ[kZeta p K Ω ℓ] Ω) (Mu ℓ Ω) ≃*
      ContH2 (kZeta p K Ω ℓ).fixingSubgroup (Mu ℓ Ω) :=
    ContH2.mapEquiv (fixingSubgroupEquiv (kZeta p K Ω ℓ))
      (continuous_fixingSubgroupEquiv (kZeta p K Ω ℓ))
      (continuous_fixingSubgroupEquiv_symm (kZeta p K Ω ℓ)) (fun _ _ => rfl)
  have hE : ∀ z, mapVal ℓ (E z) = brFixingEquiv (kZeta p K Ω ℓ) (toBr ℓ z) := by
    intro z
    induction z using induction_on with | h f => ?_
    rfl
  intro y y' h
  obtain ⟨z, rfl⟩ := E.surjective y
  obtain ⟨z', rfl⟩ := E.surjective y'
  rw [hE, hE] at h
  rw [toBr_injective ℓ hℓ.out.pos ((brFixingEquiv (kZeta p K Ω ℓ)).injective h)]

include hp in
/-- Conjugation acts trivially on `H²(K(ζ), Ωˣ) = Br(K(ζ))`: every class is restricted from `K`. -/
theorem conj_units_eq_self (σ : Ω ≃ₐ[K] Ω)
    (w : ContH2 (kZeta p K Ω ℓ).fixingSubgroup Ωˣ) :
    ContH2.conj _ σ (conj_mem_fixingSubgroup ℓ σ) w = w := by
  obtain ⟨β, rfl⟩ := (brFixingEquiv (kZeta p K Ω ℓ)).surjective w
  obtain ⟨α, rfl⟩ := res_surjective p (kZeta p K Ω ℓ) β
  rw [brFixingEquiv_res]
  exact ContH2.conj_res _ σ _ α

include hp in
/-- Conjugation acts trivially on `H²(K(ζ), μ_ℓ)`. -/
theorem conj_mu_eq_self (σ : Ω ≃ₐ[K] Ω)
    (y : ContH2 (kZeta p K Ω ℓ).fixingSubgroup (Mu ℓ Ω)) :
    ContH2.conj _ σ (conj_mem_fixingSubgroup ℓ σ) y = y := by
  apply mapVal_injective ℓ
  have := ContH2.conj_map _ σ (conj_mem_fixingSubgroup ℓ σ) Mu.val (fun _ _ => rfl)
    (fun _ => rfl) y
  change ContH2.map _ _ _ _ _ = ContH2.map _ _ _ _ _
  rw [← this, conj_units_eq_self]

include hp in
/-- **`H²(K, ℤ/ℓ) = 0` if `μ_ℓ ⊄ K`** (`ℓ` prime). -/
theorem h2_trivZMod_prime_eq_one (hμ : Nat.card (rootsOfUnity ℓ K) ≠ ℓ)
    (β : ContH2 (Ω ≃ₐ[K] Ω) (TrivZMod ℓ)) : β = 1 := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Ω ≃ₐ[K] Ω, σ • genMu p Ω ℓ ≠ genMu p Ω ℓ := by
    by_contra hcon
    push Not at hcon
    apply hμ
    rw [← card_h0_mu (K := K) (Ω := Ω) ℓ]
    have : H0 (Ω ≃ₐ[K] Ω) (Mu ℓ Ω) = ⊤ :=
      eq_top_iff.2 fun x _ g => smul_eq_of_smul_genMu ℓ (hcon g) x
    rw [this, Subgroup.card_top, card_mu (p := p)]
  set ψ := trivZModMuEquiv p Ω ℓ with hψ_def
  have hψ : ∀ (g : (kZeta p K Ω ℓ).fixingSubgroup) (k : TrivZMod ℓ), ψ (g • k) = g • ψ k :=
    fun g k => (smul_eq_of_mem_fixingSubgroup ℓ g.2 (ψ k)).symm
  set c := (Multiplicative.toAdd (TrivZMod.equiv (ψ.symm (σ • genMu p Ω ℓ)))).val with hc_def
  have hc : σ • genMu p Ω ℓ = genMu p Ω ℓ ^ c := by
    conv_lhs => rw [← ψ.apply_symm_apply (σ • genMu p Ω ℓ)]
    rfl
  have htw : ∀ k : TrivZMod ℓ, σ • ψ k = ψ (σ • k) ^ c := by
    intro k
    rw [TrivZMod.smul_eq, trivZModMuEquiv_apply, smul_pow', hc, ← pow_mul, ← pow_mul, mul_comm]
  have hc1 : c ≠ 1 := fun h => hσ (by rw [hc, h, pow_one])
  have hc0 : c ≠ 0 := fun h => by
    rw [h, pow_zero] at hc
    have h1 : genMu p Ω ℓ = 1 := by rw [← inv_smul_smul σ (genMu p Ω ℓ), hc, smul_one]
    have h2 := orderOf_genMu (p := p) (Ω := Ω) ℓ
    rw [h1, orderOf_one] at h2
    exact hℓ.out.one_lt.ne h2
  have hcl : c < ℓ := ZMod.val_lt _
  let x := ContH2.res (kZeta p K Ω ℓ).fixingSubgroup β
  let y := h2Map ψ hψ x
  have hy : y ^ c = y := by
    have e1 := ContH2.conj_map_pow _ σ (conj_mem_fixingSubgroup ℓ σ) ψ.toMonoidHom hψ c htw x
    rw [ContH2.conj_res, conj_mu_eq_self] at e1
    exact e1.symm
  have hyℓ : y ^ ℓ = 1 := ContH2.pow_eq_one_of_forall (mu_pow_eq_one ℓ) y
  have hy1 : y = 1 := by
    have h1 : y ^ (c - 1) = 1 := by
      have : y ^ (c - 1) * y = y := by rw [← pow_succ, Nat.sub_add_cancel (by omega), hy]
      exact mul_eq_right.1 this
    have hcop : Nat.Coprime ℓ (c - 1) := Nat.coprime_of_lt_prime (by omega) (by omega) hℓ.out
    have := pow_gcd_eq_one.2 ⟨hyℓ, h1⟩
    rwa [hcop, pow_one] at this
  have hx1 : x = 1 := by
    apply (h2Map_bijective ψ hψ).1
    rw [map_one]
    exact hy1
  apply ContH2.res_injective_of_coprime _ (kZeta p K Ω ℓ).fixingSubgroup_isOpen
    (trivZMod_pow_eq_one ℓ) (coprime_card_quotient_kZeta ℓ)
  rw [map_one]
  exact hx1

end Main

section Consequences

variable (Ω) in
include hp Ω in
/-- `#μ_ℓ(K) ∈ {1, ℓ}`. -/
theorem card_rootsOfUnity_prime :
    Nat.card (rootsOfUnity ℓ K) = 1 ∨ Nat.card (rootsOfUnity ℓ K) = ℓ := by
  have h : Nat.card (rootsOfUnity ℓ K) ∣ ℓ := by
    have := Subgroup.card_subgroup_dvd_card (H0 (Ω ≃ₐ[K] Ω) (Mu ℓ Ω))
    rwa [card_h0_mu, card_mu (p := p)] at this
  exact (Nat.dvd_prime hℓ.out).1 h

theorem bijective_of_subsingleton {X Y : Type*} [Subsingleton X] [Subsingleton Y] [Nonempty X]
    (f : X → Y) : Function.Bijective f :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨Classical.arbitrary X, Subsingleton.elim _ _⟩⟩

instance subsingleton_hom {X Y : Type*} [Group X] [Group Y] [Subsingleton X] :
    Subsingleton (X →* Y) :=
  ⟨fun φ ψ => MonoidHom.ext fun x => by rw [Subsingleton.elim x 1, map_one, map_one]⟩

section NotInK

variable {ℓ}
variable (hμ : Nat.card (rootsOfUnity ℓ K) ≠ ℓ)
include hp hμ

theorem subsingleton_h2_trivZMod_prime : Subsingleton (ContH2 (Ω ≃ₐ[K] Ω) (TrivZMod ℓ)) :=
  ⟨fun a b => by
    rw [h2_trivZMod_prime_eq_one (p := p) ℓ hμ a, h2_trivZMod_prime_eq_one (p := p) ℓ hμ b]⟩

theorem subsingleton_h0_mu_prime : Subsingleton (H0 (Ω ≃ₐ[K] Ω) (Mu ℓ Ω)) := by
  have h1 : Nat.card (H0 (Ω ≃ₐ[K] Ω) (Mu ℓ Ω)) = 1 := by
    rw [card_h0_mu]
    exact (card_rootsOfUnity_prime (p := p) Ω ℓ).resolve_right hμ
  exact (Nat.card_eq_one_iff_unique.1 h1).1

/-- `H²(K, ℤ/ℓ) × H⁰(K, μ_ℓ) → ℤ/ℓ` is perfect when `μ_ℓ ⊄ K` (both groups are trivial). -/
theorem perfectDeg2_trivZMod_prime :
    PerfectDeg2 (invMu p K Ω ℓ) (powPairing (K := K) (Ω := Ω) ℓ) := by
  haveI := subsingleton_h2_trivZMod_prime (p := p) (Ω := Ω) hμ
  haveI := subsingleton_h0_mu_prime (p := p) (Ω := Ω) hμ
  exact bijective_of_subsingleton _

/-- `H⁰(K, μ_ℓ) × H²(K, ℤ/ℓ) → ℤ/ℓ` is perfect when `μ_ℓ ⊄ K` (both groups are trivial). -/
theorem perfectDeg0_mu_prime :
    PerfectDeg0 (invMu p K Ω ℓ) (powPairing (K := K) (Ω := Ω) ℓ).swap := by
  haveI := subsingleton_h2_trivZMod_prime (p := p) (Ω := Ω) hμ
  haveI := subsingleton_h0_mu_prime (p := p) (Ω := Ω) hμ
  exact bijective_of_subsingleton _

end NotInK

include hp in
/-- **`#H²(K, ℤ/ℓ) = #μ_ℓ(K)`** for a prime `ℓ`. -/
theorem card_h2_trivZMod_prime :
    Nat.card (ContH2 (Ω ≃ₐ[K] Ω) (TrivZMod ℓ)) = Nat.card (rootsOfUnity ℓ K) := by
  by_cases hμ : Nat.card (rootsOfUnity ℓ K) = ℓ
  · rw [Nat.card_congr (h2TrivEquiv (p := p) hμ).toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, hμ]
  · haveI := subsingleton_h2_trivZMod_prime (p := p) (Ω := Ω) hμ
    rw [Nat.card_of_subsingleton (1 : ContH2 (Ω ≃ₐ[K] Ω) (TrivZMod ℓ)),
      (card_rootsOfUnity_prime (p := p) Ω ℓ).resolve_right hμ]

include hp in
/-- **The local Euler characteristic formula for `ℤ/ℓ`**, `ℓ` prime, without any assumption on
`K`. -/
theorem eulerCharacteristicFor_trivZMod_prime : EulerCharacteristicFor p K Ω (TrivZMod ℓ) := by
  have hpos : Nat.card (rootsOfUnity ℓ K) ≠ 0 := by
    rcases card_rootsOfUnity_prime (p := p) (K := K) Ω ℓ with h | h <;> rw [h]
    · exact one_ne_zero
    · exact hℓ.out.ne_zero
  refine ⟨finite_h1_trivZMod (p := p) ℓ, Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [card_h2_trivZMod_prime (p := p)]
    exact hpos
  · rw [card_h1_trivZMod (p := p), card_h2_trivZMod_prime (p := p), TrivZMod.h0_eq_top,
      Subgroup.card_top, TrivZMod.card]

include hp in
/-- **Local Tate duality for `ℤ/ℓ`**, `ℓ` prime, in all degrees, without any assumption on `K`. -/
theorem tateDualityFor_trivZMod_prime : TateDualityFor p K Ω (TrivZMod ℓ) ℓ := by
  by_cases hμ : Nat.card (rootsOfUnity ℓ K) = ℓ
  · exact tateDualityFor_trivZMod hμ
  · exact ⟨perfectDeg0_eval_trivZMod ℓ, perfectDeg1_eval_trivZMod ℓ,
      (perfectDeg_eval_trivZMod_iff ℓ).2.2.2 (perfectDeg2_trivZMod_prime hμ)⟩

include hp in
/-- **Local Tate duality for `μ_ℓ`**, `ℓ` prime, in all degrees, without any assumption on `K`. -/
theorem tateDualityFor_mu_prime : TateDualityFor p K Ω (Mu ℓ Ω) ℓ := by
  by_cases hμ : Nat.card (rootsOfUnity ℓ K) = ℓ
  · exact tateDualityFor_mu hμ
  · exact ⟨(perfectDeg_eval_mu_iff ℓ).1.2 (perfectDeg0_mu_prime hμ), perfectDeg1_eval_mu ℓ,
      perfectDeg2_eval_mu ℓ⟩

end Consequences

section General

/-- `ℤ/ab ≃ ℤ/a × ℤ/b` for coprime `a, b` (Chinese remainder theorem). -/
noncomputable def trivZModCRT {a b : ℕ} (h : a.Coprime b) :
    TrivZMod (a * b) ≃* TrivZMod a × TrivZMod b where
  toFun k := (Multiplicative.ofAdd (ZMod.chineseRemainder h (Multiplicative.toAdd k)).1,
    Multiplicative.ofAdd (ZMod.chineseRemainder h (Multiplicative.toAdd k)).2)
  invFun q := Multiplicative.ofAdd ((ZMod.chineseRemainder h).symm
    (Multiplicative.toAdd q.1, Multiplicative.toAdd q.2))
  left_inv k := by
    change Multiplicative.ofAdd ((ZMod.chineseRemainder h).symm
      ((ZMod.chineseRemainder h (Multiplicative.toAdd k)).1,
        (ZMod.chineseRemainder h (Multiplicative.toAdd k)).2)) = k
    rw [Prod.mk.eta, RingEquiv.symm_apply_apply, ofAdd_toAdd]
  right_inv q := by
    change (Multiplicative.ofAdd (ZMod.chineseRemainder h ((ZMod.chineseRemainder h).symm
      (Multiplicative.toAdd q.1, Multiplicative.toAdd q.2))).1,
      Multiplicative.ofAdd (ZMod.chineseRemainder h ((ZMod.chineseRemainder h).symm
      (Multiplicative.toAdd q.1, Multiplicative.toAdd q.2))).2) = q
    rw [RingEquiv.apply_symm_apply]
    rfl
  map_mul' k k' := by
    change (Multiplicative.ofAdd (ZMod.chineseRemainder h
        (Multiplicative.toAdd k + Multiplicative.toAdd k')).1,
      Multiplicative.ofAdd (ZMod.chineseRemainder h
        (Multiplicative.toAdd k + Multiplicative.toAdd k')).2) = _
    rw [map_add]
    rfl

include hp in
/-- The Euler characteristic formula for `ℤ/ab` from `ℤ/a` and `ℤ/b`, `a, b` coprime. -/
theorem eulerCharacteristicFor_trivZMod_mul {a b : ℕ} [NeZero a] [NeZero b] (h : a.Coprime b)
    (ha : EulerCharacteristicFor p K Ω (TrivZMod a))
    (hb : EulerCharacteristicFor p K Ω (TrivZMod b)) :
    EulerCharacteristicFor p K Ω (TrivZMod (a * b)) :=
  eulerCharacteristicFor_of_equiv (trivZModCRT h).symm (fun _ _ => rfl)
    (eulerCharacteristicFor_prod ha hb)

include hp in
/-- **The local Euler characteristic formula for `ℤ/n`** provided `μ_{ℓ^e} ⊆ K` for every prime
power `ℓ^e ∣ n` with `e ≥ 2` (no condition on the primes dividing `n` exactly once). -/
theorem eulerCharacteristicFor_trivZMod_of_primePow (n : ℕ) [NeZero n]
    (h : ∀ ℓ e : ℕ, ℓ.Prime → 2 ≤ e → ℓ ^ e ∣ n → Nat.card (rootsOfUnity (ℓ ^ e) K) = ℓ ^ e) :
    EulerCharacteristicFor p K Ω (TrivZMod n) := by
  have key : ∀ m : ℕ, m ≠ 0 → (∀ ℓ e : ℕ, ℓ.Prime → 2 ≤ e → ℓ ^ e ∣ m →
      Nat.card (rootsOfUnity (ℓ ^ e) K) = ℓ ^ e) → EulerCharacteristicFor p K Ω (TrivZMod m) := by
    intro m
    induction m using Nat.recOnPosPrimePosCoprime with
    | prime_pow ℓ k hℓ hk =>
      intro hne h
      haveI : NeZero (ℓ ^ k) := ⟨hne⟩
      rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
      · haveI : Fact ℓ.Prime := ⟨hℓ⟩
        rw [pow_one]
        exact eulerCharacteristicFor_trivZMod_prime ℓ
      · exact eulerCharacteristicFor_trivZMod (h ℓ k hℓ hk2 dvd_rfl)
    | zero => exact fun h => absurd rfl h
    | one =>
      intro _ _
      haveI : Subsingleton (TrivZMod 1) :=
        inferInstanceAs (Subsingleton (Multiplicative (ZMod 1)))
      exact eulerCharacteristicFor_of_subsingleton
    | coprime a b ha hb hab iha ihb =>
      intro _ h
      haveI : NeZero a := ⟨by omega⟩
      haveI : NeZero b := ⟨by omega⟩
      exact eulerCharacteristicFor_trivZMod_mul hab
        (iha (by omega) fun ℓ e hℓ he hd => h ℓ e hℓ he (dvd_mul_of_dvd_left hd b))
        (ihb (by omega) fun ℓ e hℓ he hd => h ℓ e hℓ he (dvd_mul_of_dvd_right hd a))
  exact key n (NeZero.ne n) h

include hp in
/-- **The local Euler characteristic formula for `ℤ/n`, `n` squarefree**, without any assumption
on `K`. -/
theorem eulerCharacteristicFor_trivZMod_of_squarefree (n : ℕ) [NeZero n] (hn : Squarefree n) :
    EulerCharacteristicFor p K Ω (TrivZMod n) := by
  refine eulerCharacteristicFor_trivZMod_of_primePow n fun ℓ e hℓ he hd => absurd ?_ hℓ.one_lt.ne'
  have h2 : ℓ * ℓ ∣ n := (pow_two ℓ ▸ pow_dvd_pow ℓ he).trans hd
  exact Nat.isUnit_iff.1 (hn ℓ h2)

include hp in
/-- **The local Euler characteristic formula for finite modules with trivial action**, provided
`μ_{ℓ^e} ⊆ K` for every prime power `ℓ^e ∣ exp(M)` with `e ≥ 2`. -/
theorem eulerCharacteristicFor_of_trivial_of_primePow (M : Type*) [CommGroup M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalGroup M]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]
    (htriv : ∀ (g : Ω ≃ₐ[K] Ω) (m : M), g • m = m)
    (h : ∀ ℓ e : ℕ, ℓ.Prime → 2 ≤ e → ℓ ^ e ∣ Monoid.exponent M →
      Nat.card (rootsOfUnity (ℓ ^ e) K) = ℓ ^ e) : EulerCharacteristicFor p K Ω M :=
  eulerCharacteristicFor_of_trivial' M htriv fun n _ _ hdvd =>
    eulerCharacteristicFor_trivZMod_of_primePow n fun ℓ e hℓ he hd => h ℓ e hℓ he (hd.trans hdvd)

include hp in
/-- **The local Euler characteristic formula for finite modules with trivial action and
squarefree exponent** (e.g. elementary abelian `ℓ`-groups), without any assumption on `K`. -/
theorem eulerCharacteristicFor_of_trivial_of_squarefree (M : Type*) [CommGroup M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalGroup M]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]
    (htriv : ∀ (g : Ω ≃ₐ[K] Ω) (m : M), g • m = m) (hsq : Squarefree (Monoid.exponent M)) :
    EulerCharacteristicFor p K Ω M :=
  eulerCharacteristicFor_of_trivial' M htriv fun n _ _ hdvd =>
    eulerCharacteristicFor_trivZMod_of_squarefree n (hsq.squarefree_of_dvd hdvd)

end General

end PadicField
