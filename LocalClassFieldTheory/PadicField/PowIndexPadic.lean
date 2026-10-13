/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.PadicField.PowIndex
import LocalClassFieldTheory.PadicField.Ramification
import LocalClassFieldTheory.PadicField.Complete

/-!
# `[Kˣ : (Kˣ)ⁿ] = n · #μ_n(K) · p^{v_p(n) [K : ℚ_p]}`

For a finite extension `K` of `ℚ_p` we specialise `PowIndex.index_range_pow_field` to
`R = 𝒪 p K` and compute `#(𝒪/n𝒪) = q^{v_K(n)} = p^{v_p(n) [K : ℚ_p]}`:

* `PadicField.v_natCast`: `v_K(n) = e(K/ℚ_p) · v_p(n)`;
* `PadicField.q_eq_pow`: `q = p^{f(K/ℚ_p)}`;
* `PadicField.card_quot_natCast`: `#(𝒪/n𝒪) = p^{v_p(n) [K : ℚ_p]}` (`e f = [K : ℚ_p]`);
* **`PadicField.index_range_pow`**: `[Kˣ : (Kˣ)ⁿ] = n · #μ_n(K) · p^{v_p(n) [K : ℚ_p]}`, i.e.
  `#(Kˣ/(Kˣ)ⁿ) = n · #μ_n(K) / |n|_K` with `|n|_K = p^{-v_p(n) [K : ℚ_p]}` the normalised absolute
  value. This is the arithmetic input of the local Euler characteristic formula for `μ_n`.
-/

open IsLocalRing

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]

theorem v_p_Qp : v p ((p : ℚ_[p])) = 1 := by
  have hexpo : expo p ℚ_[p] = 1 := by simp [expo, Module.finrank_self]
  have hwp : wval p ((p : ℚ_[p])) = 1 := by rw [wval_natCast_p, hexpo]; rfl
  have hg : valGen p ℚ_[p] = 1 := by
    have h1 := valGen_le p ℚ_[p] one_pos (natCast_p_ne_zero (p := p) (K := ℚ_[p]))
      (by rw [hwp]; rfl)
    have h0 := valGen_pos p ℚ_[p]
    omega
  rw [v, hwp, hg]
  rfl

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

theorem v_natCast_of_coprime {m : ℕ} (hm : p.Coprime m) : v p ((m : K)) = 0 := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have hm0 : (m : ℚ_[p]) ≠ 0 := by
    refine Nat.cast_ne_zero.2 ?_
    rintro rfl
    exact hp.out.one_lt.ne' (Nat.coprime_zero_right p |>.1 hm)
  have hmK : (m : K) = algebraMap ℚ_[p] K (m : ℚ_[p]) := by simp
  have h0 : (m : K) ≠ 0 := by
    rw [hmK]; exact (map_ne_zero_iff _ (algebraMap ℚ_[p] K).injective).2 hm0
  rw [← nrm_eq_one_iff_v_eq_zero h0, hmK, nrm_algebraMap]
  exact (Padic.norm_natCast_eq_one_iff (p := p)).2 hm

/-- `v_K(n) = e(K/ℚ_p) · v_p(n)`. -/
theorem v_natCast (n : ℕ) [NeZero n] :
    v p ((n : K)) = e p ℚ_[p] K * padicValNat p n := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have hn0 : n ≠ 0 := NeZero.ne n
  rw [← Nat.factorization_def n hp.out]
  set a := n.factorization p
  set m := n / p ^ a
  have hdec : p ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcop : p.Coprime m := Nat.coprime_ordCompl hp.out hn0
  have hm0 : m ≠ 0 := by rintro h; rw [h, mul_zero] at hdec; exact hn0 hdec.symm
  have hpK : (p : K) = algebraMap ℚ_[p] K (p : ℚ_[p]) := by simp
  have hp0 : (p : K) ≠ 0 := natCast_p_ne_zero
  have hmK0 : (m : K) ≠ 0 := Nat.cast_ne_zero.2 hm0
  have hvp : v p ((p : K)) = e p ℚ_[p] K := by rw [hpK, v_algebraMap, v_p_Qp, mul_one]
  conv_lhs => rw [← hdec]
  rw [Nat.cast_mul, Nat.cast_pow, v_mul (pow_ne_zero _ hp0) hmK0, v_pow hp0, hvp,
    v_natCast_of_coprime hcop, add_zero]
  ring

/-- The residue field of `K` has `p^{f(K/ℚ_p)}` elements. -/
theorem q_eq_pow : q p K = p ^ f p ℚ_[p] K := by
  classical
  haveI := Fintype.ofFinite (𝓴 p K)
  haveI := Fintype.ofFinite (𝓴 p ℚ_[p])
  have hQ : Nat.card (𝓴 p ℚ_[p]) = p := by
    rw [Nat.card_congr ((ResidueField.mapEquiv (integersQpEquiv p)).trans
      (PadicInt.residueField (p := p))).toEquiv, Nat.card_zmod]
  rw [q, f, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := 𝓴 p ℚ_[p]),
    ← Nat.card_eq_fintype_card, hQ]

/-- **`#(𝒪/n𝒪) = p^{v_p(n) [K : ℚ_p]}`**. -/
theorem card_quot_natCast (n : ℕ) [NeZero n] :
    Nat.card (𝒪 p K ⧸ Ideal.span {(n : 𝒪 p K)}) =
      p ^ (padicValNat p n * Module.finrank ℚ_[p] K) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have hn0 : (n : 𝒪 p K) ≠ 0 := by
    intro h
    have := congrArg (algebraMap (𝒪 p K) K) h
    rw [map_natCast, map_zero] at this
    exact NeZero.ne n (Nat.cast_eq_zero.1 this)
  have hspan : Ideal.span {(n : 𝒪 p K)} =
      maximalIdeal (𝒪 p K) ^ (v p (((n : 𝒪 p K)) : K)).toNat := by
    rw [Integers.maximalIdeal_eq_span, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.2 (Integers.associated_ϖ_pow hn0).symm
  have hmax : maximalIdeal (𝒪 p K) ≠ ⊥ := Integers.maximalIdeal_ne_bot (p := p) K
  rw [hspan, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime hmax,
    Submodule.cardQuot_apply]
  change q p K ^ _ = _
  have hv : v p (((n : 𝒪 p K)) : K) = e p ℚ_[p] K * padicValNat p n := by
    rw [show (((n : 𝒪 p K)) : K) = (n : K) by rw [Integers.coe_eq_algebraMap, map_natCast],
      v_natCast]
  rw [hv, show ((e p ℚ_[p] K : ℤ) * (padicValNat p n : ℤ)).toNat =
      e p ℚ_[p] K * padicValNat p n by norm_cast, q_eq_pow, ← pow_mul,
    ← e_mul_f (p := p) (K := ℚ_[p]) (L := K)]
  ring_nf

/-- **The index of the `n`-th powers**: `[Kˣ : (Kˣ)ⁿ] = n · #μ_n(K) · p^{v_p(n) [K : ℚ_p]}`. -/
theorem index_range_pow (n : ℕ) [NeZero n] :
    (powMonoidHom n : Kˣ →* Kˣ).range.index =
      n * Nat.card (rootsOfUnity n K) * p ^ (padicValNat p n * Module.finrank ℚ_[p] K) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  have hn0 : (n : 𝒪 p K) ≠ 0 := by
    intro h
    have := congrArg (algebraMap (𝒪 p K) K) h
    rw [map_natCast, map_zero] at this
    exact NeZero.ne n (Nat.cast_eq_zero.1 this)
  have hker : (powMonoidHom n : Kˣ →* Kˣ).ker = rootsOfUnity n K := by
    ext x
    rw [MonoidHom.mem_ker, powMonoidHom_apply, mem_rootsOfUnity]
  rw [PowIndex.index_range_pow_field (R := 𝒪 p K) K n hn0, card_quot_natCast, hker]
  ring

end PadicField
