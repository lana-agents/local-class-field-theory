/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.TrivialModules
import LocalClassFieldTheory.Brauer.KummerCompat

/-!
# Local Tate duality for `ℤ/n` and `μ_n` in all degrees

* **`PadicField.h2Hom_surjective_of_euler`**: conversely to the dévissage, if the Euler
  characteristic formula holds for `A`, `B` and `C` in `0 → A → B → C → 0`, then
  `H²(K, B) → H²(K, C)` is surjective (count along the exact sequence ending in the image);
* `PadicField.h2_castMulHom_bijective`: the reduction `H²(K, ℤ/N) → H²(K, ℤ/m)` is bijective when
  `m ∣ N` and `#μ_N(K) = #μ_m(K)`;
* **`PadicField.perfectDeg2_trivZMod_all`**, **`PadicField.perfectDeg0_mu_all`**: the pairing
  `H²(K, ℤ/n) × H⁰(K, μ_n) → H²(K, μ_n) ≃ ℤ/n` is perfect on both sides, for every `n ≥ 1` and
  without any assumption on `K`. With `m = #μ_n(K)` one has `μ_m ⊆ K`, `H⁰(K, μ_n) = μ_m`, and
  the pairing with `ι(γ^j)` (`γ` a generator of `μ_m`, `ι : μ_m ⊆ μ_n`) is
  `β ↦ ι_*(τ_*(red β))^j` (`PadicField.cup20_powPairing_muIncl`), where `red : ℤ/n → ℤ/m` and
  `τ : ℤ/m ≃ μ_m`; `ι_*` is injective on `H²` (both embed into `Br(K)`);
* **`PadicField.tateDualityFor_trivZMod_all`**, **`PadicField.tateDualityFor_mu_all`**: local Tate
  duality for `ℤ/n` and `μ_n` in degrees `0, 1, 2`, for every `n ≥ 1`;
* `PadicField.card_h2_eq_card_h0_dual_trivZMod`: `#H²(K, ℤ/n) = #H⁰(K, Hom(ℤ/n, μ_n))`.
-/

open ContH2 groupCohomology KummerTheory

set_option linter.unusedSectionVars false

namespace PadicField

open Brauer

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

local notation "G_K" => Ω ≃ₐ[K] Ω

/-! ### Surjectivity on `H²` from the Euler characteristic formula -/

section Surj

variable {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C] [Finite A] [Finite B]
  [Finite C] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalGroup A]
  [TopologicalSpace B] [DiscreteTopology B] [IsTopologicalGroup B]
  [TopologicalSpace C] [DiscreteTopology C] [IsTopologicalGroup C]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) A] [MulDistribMulAction (Ω ≃ₐ[K] Ω) B]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) C] [SmoothAction (Ω ≃ₐ[K] Ω) B]

include hp in
/-- **If the Euler characteristic formula holds for `A`, `B` and `C`, then `H²(K, B) → H²(K, C)` is
surjective.** -/
theorem h2Hom_surjective_of_euler (S : GShortExact G_K A B C)
    (hA : EulerCharacteristicFor p K Ω A) (hB : EulerCharacteristicFor p K Ω B)
    (hC : EulerCharacteristicFor p K Ω C) :
    Function.Surjective (h2Hom (G := G_K) S.π S.map_smul_π) := by
  obtain ⟨hA1, hA2, eA⟩ := hA
  obtain ⟨hB1, hB2, eB⟩ := hB
  obtain ⟨hC1, hC2, eC⟩ := hC
  haveI := hC2
  set φ := h2Hom (G := G_K) S.π S.map_smul_π
  have key := card_identity_of_exact _ _ _ _ _ _ (h2Hom (G := G_K) S.i S.map_smul_i)
    φ.rangeRestrict S.h0Hom_injective S.exact_h0B S.exact_h0C S.exact_h1A S.exact_h1B S.exact_h1C
    S.exact_h2A (by rw [MonoidHom.ker_rangeRestrict, S.exact_h2B])
    (MonoidHom.rangeRestrict_surjective _)
  rw [eA, eB, eC, S.card_eq_mul, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', add_mul,
    pow_add] at key
  set PA := p ^ (padicValNat p (Nat.card A) * Module.finrank ℚ_[p] K)
  set PC := p ^ (padicValNat p (Nat.card C) * Module.finrank ℚ_[p] K)
  set X := Nat.card (H0 G_K B) * Nat.card (ContH2 G_K B) * PA * PC * Nat.card (H0 G_K A) *
    Nat.card (ContH2 G_K A) * Nat.card (H0 G_K C)
  have hX : 0 < X := by
    have h1 : 0 < PA := pow_pos hp.out.pos _
    have h2 : 0 < PC := pow_pos hp.out.pos _
    simp only [X]
    have := Nat.card_pos (α := H0 G_K B)
    have := Nat.card_pos (α := ContH2 G_K B)
    have := Nat.card_pos (α := H0 G_K A)
    have := Nat.card_pos (α := ContH2 G_K A)
    have := Nat.card_pos (α := H0 G_K C)
    positivity
  have e : X * Nat.card φ.range = X * Nat.card (ContH2 G_K C) := by
    calc X * Nat.card φ.range = _ := by simp only [X]; ring
      _ = _ := key
      _ = X * Nat.card (ContH2 G_K C) := by simp only [X]; ring
  have hI := Nat.eq_of_mul_eq_mul_left hX e
  exact MonoidHom.range_eq_top.1 ((Subgroup.card_eq_iff_eq_top _).1 hI)

end Surj

/-! ### Reduction `H²(K, ℤ/N) → H²(K, ℤ/m)` -/

include hp in
/-- The reduction `H²(K, ℤ/N) → H²(K, ℤ/m)` is surjective for `m ∣ N`. -/
theorem h2_castMulHom_surjective' (m N : ℕ) [NeZero m] [NeZero N] (h : m ∣ N) :
    Function.Surjective (h2Hom (G := G_K) (castMulHom h) (fun _ _ => rfl)) := by
  obtain ⟨r, rfl⟩ : ∃ r, N = r * m := ⟨N / m, (Nat.div_mul_cancel h).symm⟩
  haveI : NeZero r := ⟨left_ne_zero_of_mul (NeZero.ne (r * m))⟩
  exact h2Hom_surjective_of_euler (p := p) (K := K) (Ω := Ω) (trivZModSES G_K r m)
    (eulerCharacteristicFor_trivZMod_all r) (eulerCharacteristicFor_trivZMod_all (r * m))
    (eulerCharacteristicFor_trivZMod_all m)

include hp in
/-- The reduction `H²(K, ℤ/N) → H²(K, ℤ/m)` is bijective if `m ∣ N` and `#μ_N(K) = #μ_m(K)`. -/
theorem h2_castMulHom_bijective (m N : ℕ) [NeZero m] [NeZero N] (h : m ∣ N)
    (hc : Nat.card (rootsOfUnity N K) = Nat.card (rootsOfUnity m K)) :
    Function.Bijective (h2Hom (G := G_K) (castMulHom h) (fun _ _ => rfl)) := by
  haveI : Finite (ContH2 G_K (TrivZMod N)) :=
    (eulerCharacteristicFor_trivZMod_all (p := p) (K := K) (Ω := Ω) N).2.1
  exact (h2_castMulHom_surjective' (p := p) m N h).bijective_of_nat_card_le (by
    rw [card_h2_trivZMod (p := p), card_h2_trivZMod (p := p), hc])

/-! ### Roots of unity -/

include hp Ω in
/-- With `m = #μ_n(K)`, `μ_m(K) = μ_n(K)`, so `#μ_m(K) = m`. -/
theorem card_rootsOfUnity_card (n : ℕ) [NeZero n] :
    Nat.card (rootsOfUnity (Nat.card (rootsOfUnity n K)) K) = Nat.card (rootsOfUnity n K) := by
  have hmn := card_rootsOfUnity_dvd (p := p) (Ω := Ω) (K := K) n
  have heq : rootsOfUnity (Nat.card (rootsOfUnity n K)) K = rootsOfUnity n K := by
    refine le_antisymm (rootsOfUnity_le_of_dvd hmn) fun x hx => ?_
    rw [mem_rootsOfUnity]
    have := pow_card_eq_one' (G := rootsOfUnity n K) (x := ⟨x, hx⟩)
    exact congrArg Subtype.val this
  rw [heq]

/-! ### The pairing `H²(K, ℤ/n) × H⁰(K, μ_n) → ℤ/n` -/

theorem genMu_pow_mod (m : ℕ) [NeZero m] (v : ℕ) : genMu p Ω m ^ (v % m) = genMu p Ω m ^ v := by
  have h : v % m = v % orderOf (genMu p Ω m) := by rw [orderOf_genMu]
  rw [h, pow_mod_orderOf]

section Pairing

variable {n m : ℕ} [NeZero n] [NeZero m] (hmn : m ∣ n) (hμm : Nat.card (rootsOfUnity m K) = m)

include hp in
/-- `g • ι(ζ) = ι(g • ζ)` for the inclusion `ι : μ_m ⊆ μ_n`. -/
theorem smul_muIncl (g : G_K) (ζ : Mu m Ω) : g • muIncl hmn ζ = muIncl hmn (g • ζ) :=
  Mu.ext rfl

include hp hμm in
/-- **The pairing with `ι(γ^j)`**, `γ` the chosen generator of `μ_m ⊆ K`:
`β ∪ ι(γ^j) = ι_*(τ_*(red β))^j`. -/
theorem cup20_powPairing_muIncl (β : ContH2 G_K (TrivZMod n)) (ζ : H0 G_K (Mu n Ω)) (j : ℕ)
    (hζ : (ζ : Mu n Ω) = muIncl hmn (genMu p Ω m ^ j)) :
    cup20 (powPairing n) β ζ = h2MuIncl hmn (h2Map (trivZModMuEquiv p Ω m)
      (trivZModMuEquiv_smul (p := p) hμm) (h2Hom (castMulHom hmn) (fun _ _ => rfl) β)) ^ j := by
  induction β using induction_on with | h f => ?_
  rw [cup20_apply, cup02_mk, h2Hom_mk]
  simp only [h2Map, h2MuIncl, map_mk]
  rw [← map_pow]
  congr 1
  refine cocycles_ext fun a b => ?_
  change (ζ : Mu n Ω) ^ (Multiplicative.toAdd (TrivZMod.equiv (f (a, b)))).val =
    (muIncl hmn (trivZModMuEquiv p Ω m (castMulHom hmn (f (a, b))))) ^ j
  rw [hζ, trivZModMuEquiv_apply, ← map_pow, ← map_pow]
  congr 1
  set v := (Multiplicative.toAdd (TrivZMod.equiv (f (a, b)))).val
  have hv : (Multiplicative.toAdd (TrivZMod.equiv (castMulHom hmn (f (a, b))))).val = v % m := by
    change (ZMod.cast (Multiplicative.toAdd (f (a, b))) : ZMod m).val = v
      % m
    rw [ZMod.cast_eq_val, ZMod.val_natCast]
    rfl
  rw [hv, genMu_pow_mod (p := p), ← pow_mul, ← pow_mul, mul_comm]

include hp in
/-- `ι_* : H²(K, μ_m) → H²(K, μ_n)` is injective. -/
theorem h2MuIncl_injective : Function.Injective (h2MuIncl (K := K) (Ω := Ω) hmn) := by
  intro x y hxy
  apply toBr_injective (K := K) (Ω := Ω) m (Nat.pos_of_ne_zero (NeZero.ne m))
  rw [← toBr_h2MuIncl hmn x, ← toBr_h2MuIncl hmn y, hxy]

include hp hμm in
/-- Every element of `H⁰(K, μ_n)` killed by `m` is `ι(γ^j)` for some `j`. -/
theorem exists_eq_muIncl_genMu (ζ : H0 G_K (Mu n Ω)) (hζm : (ζ : Mu n Ω) ^ m = 1) :
    ∃ j : ℕ, (ζ : Mu n Ω) = muIncl hmn (genMu p Ω m ^ j) := by
  have h' : Mu.val (ζ : Mu n Ω) ^ m = 1 := by rw [← map_pow, hζm, map_one]
  obtain ⟨k, hk⟩ := (trivZModMuEquiv p Ω m).surjective (Mu.mk _ h')
  refine ⟨(Multiplicative.toAdd (TrivZMod.equiv k)).val, Mu.ext ?_⟩
  rw [val_muIncl, ← trivZModMuEquiv_apply, hk, Mu.val_mk]

end Pairing

section Duality

variable (n : ℕ) [NeZero n]

include hp in
theorem card_h0_mu_pos : 0 < Nat.card (rootsOfUnity n K) := by
  haveI : NeZero (n : K) := ⟨by
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
    exact Nat.cast_ne_zero.2 (NeZero.ne n)⟩
  exact Nat.card_pos

include hp in
theorem pow_card_h0_mu (ζ : H0 G_K (Mu n Ω)) :
    (ζ : Mu n Ω) ^ Nat.card (rootsOfUnity n K) = 1 := by
  rw [← card_h0_mu (K := K) (Ω := Ω) n]
  have := pow_card_eq_one' (G := H0 G_K (Mu n Ω)) (x := ζ)
  exact congrArg Subtype.val this

include hp in
/-- **Local duality for `ℤ/n` in degree `2`**: `H²(K, ℤ/n) × H⁰(K, μ_n) → ℤ/n` is perfect, for
every `n ≥ 1` and every `K`. -/
theorem perfectDeg2_trivZMod_all :
    PerfectDeg2 (invMu p K Ω n) (powPairing (K := K) (Ω := Ω) n) := by
  set m := Nat.card (rootsOfUnity n K) with hm_def
  have hmn : m ∣ n := card_rootsOfUnity_dvd (p := p) (Ω := Ω) (K := K) n
  haveI : NeZero m := ⟨(card_h0_mu_pos (p := p) (K := K) n).ne'⟩
  have hμm : Nat.card (rootsOfUnity m K) = m := card_rootsOfUnity_card (p := p) (Ω := Ω) n
  have hγ : ∀ g : G_K, g • muIncl hmn (genMu p Ω m) = muIncl hmn (genMu p Ω m) := fun g => by
    rw [smul_muIncl (p := p), smul_mu_eq (p := p) hμm]
  let ζ₀ : H0 G_K (Mu n Ω) := ⟨muIncl hmn (genMu p Ω m), hγ⟩
  have hζ₀ : (ζ₀ : Mu n Ω) = muIncl hmn (genMu p Ω m ^ 1) := by rw [pow_one]
  have hred := h2_castMulHom_bijective (p := p) (K := K) (Ω := Ω) m n hmn hμm.symm
  have hinj : Function.Injective fun β : ContH2 G_K (TrivZMod n) =>
      (invMu p K Ω n).comp (cup20 (powPairing n) β) := by
    intro β β' h
    have h0 := DFunLike.congr_fun h ζ₀
    simp only [MonoidHom.comp_apply] at h0
    have h1 := (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n))).injective h0
    rw [cup20_powPairing_muIncl (p := p) hmn hμm β ζ₀ 1 hζ₀,
      cup20_powPairing_muIncl (p := p) hmn hμm β' ζ₀ 1 hζ₀, pow_one, pow_one] at h1
    exact hred.1 ((h2Map_bijective _ _).1 (h2MuIncl_injective (p := p) hmn h1))
  haveI : Finite (H0 G_K (Mu n Ω)) := inferInstance
  haveI : Finite (H0 G_K (Mu n Ω) →* Multiplicative (ZMod n)) :=
    Finite.of_injective (fun φ : H0 G_K (Mu n Ω) →* Multiplicative (ZMod n) =>
      (φ : H0 G_K (Mu n Ω) → Multiplicative (ZMod n))) DFunLike.coe_injective
  refine hinj.bijective_of_nat_card_le ?_
  calc Nat.card (H0 G_K (Mu n Ω) →* Multiplicative (ZMod n)) ≤ Nat.card (H0 G_K (Mu n Ω)) :=
        card_hom_zmod_le _ n
    _ = Nat.card (ContH2 G_K (TrivZMod n)) := by
        rw [card_h0_mu, card_h2_trivZMod (p := p)]

include hp in
/-- **Local duality for `μ_n` in degree `0`**: `H⁰(K, μ_n) × H²(K, ℤ/n) → ℤ/n` is perfect, for
every `n ≥ 1` and every `K`. -/
theorem perfectDeg0_mu_all :
    PerfectDeg0 (invMu p K Ω n) (powPairing (K := K) (Ω := Ω) n).swap := by
  set m := Nat.card (rootsOfUnity n K) with hm_def
  have hmn : m ∣ n := card_rootsOfUnity_dvd (p := p) (Ω := Ω) (K := K) n
  haveI : NeZero m := ⟨(card_h0_mu_pos (p := p) (K := K) n).ne'⟩
  have hμm : Nat.card (rootsOfUnity m K) = m := card_rootsOfUnity_card (p := p) (Ω := Ω) n
  have hred := h2_castMulHom_bijective (p := p) (K := K) (Ω := Ω) m n hmn hμm.symm
  set Jm := h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne m))
  set x₀ : H2Mu K Ω m := Jm.symm (Multiplicative.ofAdd 1)
  obtain ⟨y₀, hy₀⟩ := (h2Map_bijective (trivZModMuEquiv p Ω m)
    (trivZModMuEquiv_smul (p := p) hμm)).2 x₀
  obtain ⟨β₀, hβ₀⟩ := hred.2 y₀
  have hinj : Function.Injective fun ζ : H0 G_K (Mu n Ω) =>
      (invMu p K Ω n).comp (cup02 (powPairing (K := K) n).swap ζ) := by
    intro ζ ζ' h
    obtain ⟨j, hj⟩ := exists_eq_muIncl_genMu (p := p) hmn hμm ζ (pow_card_h0_mu (p := p) n ζ)
    obtain ⟨j', hj'⟩ := exists_eq_muIncl_genMu (p := p) hmn hμm ζ'
      (pow_card_h0_mu (p := p) n ζ')
    have h0 := DFunLike.congr_fun h β₀
    simp only [MonoidHom.comp_apply] at h0
    have h1 := (h2MuEquiv p K Ω (Nat.pos_of_ne_zero (NeZero.ne n))).injective h0
    rw [← cup20_apply, ← cup20_apply, cup20_powPairing_muIncl (p := p) hmn hμm β₀ ζ j hj,
      cup20_powPairing_muIncl (p := p) hmn hμm β₀ ζ' j' hj', hβ₀, hy₀,
      ← map_pow (h2MuIncl hmn) x₀ j, ← map_pow (h2MuIncl hmn) x₀ j'] at h1
    have h2 := congrArg (fun x => Multiplicative.toAdd (Jm x)) (h2MuIncl_injective (p := p) hmn h1)
    simp only [map_pow, x₀, MulEquiv.apply_symm_apply, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul,
      mul_one] at h2
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    apply Subtype.ext
    rw [hj, hj', ← genMu_pow_mod (p := p), h2, genMu_pow_mod (p := p)]
  haveI : Finite (ContH2 G_K (TrivZMod n)) :=
    (eulerCharacteristicFor_trivZMod_all (p := p) (K := K) (Ω := Ω) n).2.1
  haveI : Finite (ContH2 G_K (TrivZMod n) →* Multiplicative (ZMod n)) :=
    Finite.of_injective (fun φ : ContH2 G_K (TrivZMod n) →* Multiplicative (ZMod n) =>
      (φ : ContH2 G_K (TrivZMod n) → Multiplicative (ZMod n))) DFunLike.coe_injective
  refine hinj.bijective_of_nat_card_le ?_
  calc Nat.card (ContH2 G_K (TrivZMod n) →* Multiplicative (ZMod n)) ≤
        Nat.card (ContH2 G_K (TrivZMod n)) := card_hom_zmod_le _ n
    _ = Nat.card (H0 G_K (Mu n Ω)) := by rw [card_h0_mu, card_h2_trivZMod (p := p)]

include hp in
/-- **Local Tate duality for `ℤ/n`**, all degrees, every `n ≥ 1`, without any assumption on `K`. -/
theorem tateDualityFor_trivZMod_all : TateDualityFor p K Ω (TrivZMod n) n :=
  ⟨perfectDeg0_eval_trivZMod n, perfectDeg1_eval_trivZMod n,
    (perfectDeg_eval_trivZMod_iff n).2.2.2 (perfectDeg2_trivZMod_all n)⟩

include hp in
/-- **Local Tate duality for `μ_n`**, all degrees, every `n ≥ 1`, without any assumption on `K`. -/
theorem tateDualityFor_mu_all : TateDualityFor p K Ω (Mu n Ω) n :=
  ⟨(perfectDeg_eval_mu_iff n).1.2 (perfectDeg0_mu_all n), perfectDeg1_eval_mu n,
    perfectDeg2_eval_mu n⟩

include hp in
/-- **`#H²(K, ℤ/n) = #H⁰(K, (ℤ/n)^∨)`**, `(ℤ/n)^∨ = Hom(ℤ/n, μ_n)`. -/
theorem card_h2_eq_card_h0_dual_trivZMod :
    Nat.card (ContH2 G_K (TrivZMod n)) =
      Nat.card (H0 G_K (CartierDual n Ω (TrivZMod n))) := by
  rw [card_h2_trivZMod (p := p), ← card_h0_mu (K := K) (Ω := Ω) n]
  exact Nat.card_congr (Equiv.ofBijective _ (h0Map_bijective (dualTrivEquiv n)
    (dualTrivEquiv_smul n)))

end Duality

end PadicField
