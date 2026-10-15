/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.Shapiro

/-!
# Tate's theorem `H³ = 0` for class-formation-type modules (group cohomology part)

Let `G` be a finite (discrete) group and `A` a `G`-module. We prove `H³(G, A) = 0` (in the cocycle
form `ContH2.H3Trivial`) from low-degree information, by induction along subgroups:

* **`ContH2.h3Trivial_of_subsingleton_group`**: the trivial group;
* **`ContH2.h3Trivial_of_forall_prime`** (Sylow reduction): if for every prime `ℓ` some subgroup
  `S` of index prime to `ℓ` has `H³(S, A) = 0`, then `H³(G, A) = 0` (`z^{[G:S]}` is a coboundary by
  `cor ∘ res = [G : S]`, and the indices generate `ℤ`);
* **`ContH2.h3Trivial_of_index_prime`** (the `ℓ`-step): let `H ⊴ G` have prime index `ℓ`. If
  `H¹(G, A) = 0`, `H²(G, A)` is cyclic of order `|G|`, `|H²(H, A)| ≤ |H|` and `H³(H, A) = 0`, then
  `H³(G, A) = 0`.

The `ℓ`-step uses the coinduced module `M = CoInd H A = Map(G/H, A)` and the two exact sequences
`0 → A → M → J → 0` (diagonal, then `D f(c) = f(c) / f(σ⁻¹c)` for a generator `σ` of `G/H`) and
`0 → J → M → A → 0` (`J` the kernel of the trace `f ↦ ∏_c f(c)`). By Shapiro,
`H³(G, M) = H³(H, A) = 0` and `|H²(G, M)| ≤ |H²(H, A)| ≤ |H|`; the trace on `H²` contains the
`ℓ`-th powers of the cyclic group `H²(G, A)` of order `ℓ |H|` in its image, so it is injective;
with `H¹(G, A) = 0` this gives `H²(G, J) = 0`, and then `H³(G, A) ↪ H³(G, M) = 0`.

For local fields the hypotheses are Hilbert 90, `Br(L/K) ≅ ℤ/[L:K]` and `|H²(H, Lˣ)| ≤ |H|`
(`LocalClassFieldTheory.Duality.TateH3Local`). Reference: Tate's theorem on cohomologically
trivial modules / class formations, Serre, *Local fields* IX §8, Cassels–Fröhlich IV.10; the
present route avoids cup products and Tate cohomology.
-/

open groupCohomology Brauer

set_option linter.unusedSectionVars false

namespace ContH2

variable {G A : Type*} [Group G] [CommGroup A] [MulDistribMulAction G A]
  [TopologicalSpace G] [DiscreteTopology G]

/-! ### The trivial group -/

theorem h3Trivial_of_subsingleton_group [Subsingleton G] : H3Trivial G A := by
  intro z _ hz
  refine ⟨1, .of_discrete _, ?_⟩
  funext ⟨a, b, c⟩
  rw [Subsingleton.elim a 1, Subsingleton.elim b 1, Subsingleton.elim c 1, dc2_one]
  have := hz 1 1 1 1
  simp only [one_smul, mul_one, mul_eq_left] at this
  exact this.symm

/-! ### Sylow reduction -/

theorem dc2_inv (f : G × G → A) : dc2 f⁻¹ = (dc2 f)⁻¹ := by
  rw [← one_div, dc2_div, dc2_one, one_div]

/-- If the restriction of a `3`-cocycle to `S` is a coboundary, then `z ^ [G : S]` is a
coboundary. -/
theorem exists_dc2_eq_pow_index [Finite G] (S : Subgroup G) (hS : H3Trivial S A)
    {z : G × G × G → A} (hz : IsMulCocycle₃ z) : ∃ f : G × G → A, dc2 f = z ^ S.index := by
  classical
  haveI : Fintype (G ⧸ S) := Fintype.ofFinite _
  obtain ⟨f, -, hf⟩ := hS (fun x => z (x.1, x.2.1, x.2.2)) (.of_discrete _)
    (fun a b c d => hz a b c d)
  refine ⟨corFun S f / qFun3 S z, ?_⟩
  rw [dc2_div, dc2_corFun, hf, corFun3_res S hz, mul_div_cancel_right, Subgroup.index,
    Nat.card_eq_fintype_card]

/-- **Sylow reduction for `H³`**: if for every prime `ℓ` there is a subgroup of index prime to
`ℓ` with vanishing `H³`, then `H³(G, A) = 0`. -/
theorem h3Trivial_of_forall_prime [Finite G]
    (h : ∀ ℓ : ℕ, ℓ.Prime → ∃ S : Subgroup G, ¬ ℓ ∣ S.index ∧ H3Trivial S A) :
    H3Trivial G A := by
  intro z _ hz
  let I : AddSubgroup ℤ :=
    { carrier := {n | ∃ f : G × G → A, dc2 f = z ^ n}
      zero_mem' := ⟨1, by rw [dc2_one, zpow_zero]⟩
      add_mem' := by
        rintro m n ⟨f, hf⟩ ⟨g, hg⟩
        exact ⟨f * g, by rw [dc2_mul, hf, hg, zpow_add]⟩
      neg_mem' := by
        rintro n ⟨f, hf⟩
        exact ⟨f⁻¹, by rw [dc2_inv, hf, zpow_neg]⟩ }
  have hidx : ∀ S : Subgroup G, H3Trivial S A → (S.index : ℤ) ∈ I := fun S hS => by
    obtain ⟨f, hf⟩ := exists_dc2_eq_pow_index S hS hz
    exact ⟨f, by rw [hf, zpow_natCast]⟩
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic I
  have hdvd : ∀ S : Subgroup G, H3Trivial S A → a ∣ (S.index : ℤ) := fun S hS => by
    have := hidx S hS
    rw [ha, AddSubgroup.mem_closure_singleton] at this
    obtain ⟨k, hk⟩ := this
    exact ⟨k, by rw [← hk, smul_eq_mul, mul_comm]⟩
  have ha1 : a.natAbs = 1 := by
    by_contra hne
    obtain ⟨ℓ, hℓ, hℓa⟩ := Nat.exists_prime_and_dvd hne
    obtain ⟨S, hSℓ, hS⟩ := h ℓ hℓ
    apply hSℓ
    have h1 : (ℓ : ℤ) ∣ a := Int.natCast_dvd.2 hℓa
    exact Int.natCast_dvd_natCast.1 (h1.trans (hdvd S hS))
  have h1 : (1 : ℤ) ∈ I := by
    have haI : a ∈ I := by rw [ha]; exact AddSubgroup.subset_closure rfl
    rcases Int.natAbs_eq_iff.1 ha1 with h | h
    · rw [h] at haI; exact haI
    · rw [h] at haI; simpa using I.neg_mem haI
  obtain ⟨f, hf⟩ := h1
  exact ⟨f, .of_discrete _, by rw [hf, zpow_one]⟩

/-! ### Group-theoretic counting -/

theorem injective_of_card_le_card_range {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (h : Nat.card X ≤ Nat.card f.range) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_le_one_iff_eq_bot]
  have e := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at e
  have hr : 0 < Nat.card f.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Nat.card_pos
  nlinarith

theorem card_le_card_range_pow {X : Type*} [CommGroup X] [Finite X] [IsCyclic X] {n : ℕ}
    (hn : 0 < n) :
    Nat.card X ≤ n * Nat.card (powMonoidHom n : X →* X).range := by
  classical
  haveI := Fintype.ofFinite X
  have e := Subgroup.card_eq_card_quotient_mul_card_subgroup (powMonoidHom n : X →* X).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv] at e
  have hk : Nat.card (powMonoidHom n : X →* X).ker ≤ n := by
    have := IsCyclic.card_pow_eq_one_le (α := X) hn
    calc Nat.card (powMonoidHom n : X →* X).ker
        = (Finset.univ.filter fun a : X => a ^ n = 1).card := by
          rw [Nat.card_congr (Equiv.subtypeEquivRight fun a => by
            rw [MonoidHom.mem_ker, powMonoidHom_apply]), Nat.card_eq_fintype_card,
            Fintype.card_subtype]
      _ ≤ n := this
  rw [e, mul_comm]
  exact Nat.mul_le_mul_right _ hk

/-! ### The `ℓ`-step -/

section Prime

variable (H : Subgroup G)

namespace CoInd

/-- Build an element of `CoInd H A` from a function. -/
def mk (f : G ⧸ H → A) : CoInd H A := f

@[simp]
theorem mk_apply (f : G ⧸ H → A) (c : G ⧸ H) : mk H f c = f c := rfl

/-- The diagonal `A → CoInd H A`, `a ↦ (c ↦ a)`. -/
def diag : A →* CoInd H A where
  toFun a := mk H fun _ => a
  map_one' := rfl
  map_mul' _ _ := rfl

theorem diag_apply (a : A) (c : G ⧸ H) : diag H a c = a := rfl

theorem diag_smul (g : G) (a : A) : diag H (g • a) = g • diag H a := rfl

section Trace

variable [Fintype (G ⧸ H)]

/-- The trace `CoInd H A → A`, `f ↦ ∏_c f(c)`. -/
noncomputable def trace : CoInd H A →* A where
  toFun f := ∏ c, f c
  map_one' := Finset.prod_const_one
  map_mul' _ _ := Finset.prod_mul_distrib

theorem trace_apply (f : CoInd H A) : trace H f = ∏ c, f c := rfl

theorem trace_smul (g : G) (f : CoInd H A) : trace H (g • f) = g • trace H f := by
  rw [trace_apply, trace_apply, Finset.smul_prod']
  exact prod_reindex H (fun c => g • f c) g

theorem trace_diag (a : A) : trace H (diag H a) = a ^ Fintype.card (G ⧸ H) := by
  rw [trace_apply]
  exact Finset.prod_const a

open Classical in
/-- The point mass at the base coset. -/
noncomputable def single (a : A) : CoInd H A := mk H (Pi.mulSingle (base H) a)

theorem trace_single (a : A) : trace H (single H a) = a := by
  classical
  rw [trace_apply]
  refine (Finset.prod_congr rfl fun c _ => ?_).trans (Fintype.prod_pi_mulSingle' (base H) a)
  simp only [single, mk_apply]

end Trace

section Normal

variable [H.Normal] (σ : G)

theorem smul_eq_mul_quot (g : G) (c : G ⧸ H) : g • c = (g : G ⧸ H) * c := by
  induction c using QuotientGroup.induction_on with
  | H x => rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.mk_mul]

/-- `D f(c) = f(c) / f(σ⁻¹ • c)`. -/
def dif : CoInd H A →* CoInd H A where
  toFun f := mk H fun c => f c / f (σ⁻¹ • c)
  map_one' := by
    apply ext
    intro c
    exact div_one 1
  map_mul' f f' := by
    apply ext
    intro c
    exact mul_div_mul_comm _ _ _ _

theorem dif_apply (f : CoInd H A) (c : G ⧸ H) : dif H σ f c = f c / f (σ⁻¹ • c) := rfl

theorem dif_smul (hQ : ∀ a b : G ⧸ H, a * b = b * a) (g : G) (f : CoInd H A) :
    dif H σ (g • f) = g • dif H σ f := by
  apply ext
  intro c
  rw [dif_apply, smul_apply, smul_apply, smul_apply, dif_apply, smul_div']
  congr 3
  rw [smul_eq_mul_quot, smul_eq_mul_quot, smul_eq_mul_quot, smul_eq_mul_quot, ← mul_assoc,
    ← mul_assoc, hQ (g⁻¹ : G) (σ⁻¹ : G)]

variable [Fintype (G ⧸ H)] in
theorem trace_dif (f : CoInd H A) : trace H (dif H σ f) = 1 := by
  rw [trace_apply]
  simp only [dif_apply]
  rw [Finset.prod_div_distrib, prod_reindex H (fun c => f c) σ, div_self']

theorem dif_diag (a : A) : dif H σ (diag H a) = 1 := by
  apply ext
  intro c
  exact div_self' a

theorem diag_injective : Function.Injective (diag (A := A) H) := fun _ _ h =>
  congrFun h (base H)

theorem smul_inv_eq (c : G ⧸ H) : σ⁻¹ • c = (σ : G ⧸ H)⁻¹ * c := by
  rw [smul_eq_mul_quot, QuotientGroup.mk_inv]

variable {σ}

variable [Finite (G ⧸ H)] in
theorem exists_pow_eq (hgen : Subgroup.zpowers (σ : G ⧸ H) = ⊤) (c : G ⧸ H) :
    ∃ k : ℕ, (σ : G ⧸ H) ^ k = c :=
  mem_powers_iff_mem_zpowers.2 (hgen ▸ Subgroup.mem_top c)

variable [Finite (G ⧸ H)] in
/-- The kernel of `D` is the diagonal. -/
theorem eq_diag_of_dif (hgen : Subgroup.zpowers (σ : G ⧸ H) = ⊤) {f : CoInd H A}
    (hf : dif H σ f = 1) : f = diag H (f (base H)) := by
  have h1 : ∀ c, f c = f ((σ : G ⧸ H)⁻¹ * c) := fun c => by
    have := congrFun hf c
    rw [dif_apply, smul_inv_eq] at this
    exact div_eq_one.1 this
  have h2 : ∀ k : ℕ, f ((σ : G ⧸ H) ^ k) = f (base H) := by
    intro k
    induction k with
    | zero => rw [pow_zero]; rfl
    | succ k ih => rw [h1, pow_succ', inv_mul_cancel_left, ih]
  apply ext
  intro c
  obtain ⟨k, rfl⟩ := exists_pow_eq H hgen c
  rw [h2, diag_apply]

variable [Fintype (G ⧸ H)] in
/-- `D` maps onto the kernel of the trace. -/
theorem exists_dif_eq (hgen : Subgroup.zpowers (σ : G ⧸ H) = ⊤) {j : CoInd H A}
    (hj : trace H j = 1) : ∃ f : CoInd H A, dif H σ f = j := by
  classical
  set s : G ⧸ H := (σ : G ⧸ H) with hs
  set N := orderOf s with hN
  have hN0 : 0 < N := orderOf_pos s
  have hex := exists_pow_eq H hgen
  let n : G ⧸ H → ℕ := fun c => Nat.find (hex c)
  have hn_spec : ∀ c, s ^ n c = c := fun c => Nat.find_spec (hex c)
  have hn_lt : ∀ c, n c < N := fun c => by
    by_contra hlt
    have h1 : n c ≤ n c % N := Nat.find_min' (hex c) (m := n c % N) (by
      rw [pow_mod_orderOf, hn_spec])
    have := Nat.mod_lt (n c) hN0
    omega
  have hn_pow : ∀ k < N, n (s ^ k) = k := fun k hk =>
    pow_injOn_Iio_orderOf (Set.mem_Iio.2 (hn_lt _)) (Set.mem_Iio.2 hk) (hn_spec _)
  have htot : ∏ i ∈ Finset.range N, j (s ^ i) = 1 := by
    rw [← hj, trace_apply]
    refine Finset.prod_nbij (fun i => s ^ i) (fun _ _ => Finset.mem_univ _)
      (fun a ha b hb hab => pow_injOn_Iio_orderOf (by simpa using ha) (by simpa using hb) hab)
      (fun c _ => ⟨n c, by simpa using hn_lt c, hn_spec c⟩) (fun _ _ => rfl)
  let f : CoInd H A := mk H fun c => ∏ i ∈ Finset.range (n c), j (s ^ (i + 1))
  refine ⟨f, ext fun c => ?_⟩
  rw [dif_apply, smul_inv_eq, ← hs]
  simp only [f, mk_apply]
  obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rcases Nat.eq_zero_or_pos (n c) with h0 | hpos
  · have hc : c = 1 := by rw [← hn_spec c, h0, pow_zero]
    have hsN : s⁻¹ * c = s ^ M := by
      rw [hc, mul_one, inv_eq_iff_mul_eq_one, ← pow_succ', ← hM, hN, pow_orderOf_eq_one]
    rw [h0, hsN, hn_pow _ (by omega), Finset.prod_range_zero, one_div]
    have h' := htot
    rw [hM, Finset.prod_range_succ', pow_zero, ← hc] at h'
    exact (eq_inv_of_mul_eq_one_right h').symm
  · obtain ⟨m, hm⟩ : ∃ m, n c = m + 1 := ⟨n c - 1, by omega⟩
    have hsm : s⁻¹ * c = s ^ m := by
      rw [← hn_spec c, hm, pow_succ', inv_mul_cancel_left]
    rw [hsm, hn_pow m (by have := hn_lt c; omega), hm, Finset.prod_range_succ,
      mul_div_cancel_left, ← hm, hn_spec]

end Normal


end CoInd

end Prime


theorem dx_comp {M N : Type*} [CommGroup M] [CommGroup N] [MulDistribMulAction G M]
    [MulDistribMulAction G N] (φ : M →* N) (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m)
    (Y : G → M) (x : G × G) : φ (dx G M Y x) = dx G N (fun g => φ (Y g)) x := by
  obtain ⟨a, b⟩ := x
  rw [dx_apply, dx_apply, map_mul, map_div, hφ]

theorem dx_smul_div {M : Type*} [CommGroup M] [MulDistribMulAction G M] (m : M) :
    dx G M (fun g => g • m / m) = 1 := by
  funext ⟨g, h⟩
  simp only [dx_apply, smul_div', ← mul_smul, Pi.one_apply]
  mul_abel

open CoInd in
/-- **The `ℓ`-step of Tate's theorem**: let `H ⊴ G` be a normal subgroup of prime index of a
finite group. If `H¹(G, A) = 0`, `H²(G, A)` is cyclic of order `|G|`, `|H²(H, A)| ≤ |H|` and
`H³(H, A) = 0`, then `H³(G, A) = 0`. -/
theorem h3Trivial_of_index_prime [Finite G] (H : Subgroup G) [H.Normal] (hℓ : H.index.Prime)
    (h90 : ∀ y : G → A, IsMulCocycle₁ y → IsMulCoboundary₁ y)
    [Finite (ContH2 H A)] (hH : Nat.card (ContH2 H A) ≤ Nat.card H)
    [Finite (ContH2 G A)] [IsCyclic (ContH2 G A)] (hG : Nat.card (ContH2 G A) = Nat.card G)
    (h3 : H3Trivial H A) : H3Trivial G A := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hℓ' : Fintype.card (G ⧸ H) = H.index := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  -- `G/H` is cyclic of prime order
  haveI : Fact (Nat.card (G ⧸ H)).Prime := ⟨hℓ⟩
  haveI hcyc : IsCyclic (G ⧸ H) := isCyclic_of_prime_card rfl
  have hQ : ∀ a b : G ⧸ H, a * b = b * a := (IsCyclic.commGroup (α := G ⧸ H)).mul_comm
  obtain ⟨s, hs⟩ := hcyc.exists_generator
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective s
  have hgen : Subgroup.zpowers (σ : G ⧸ H) = ⊤ := eq_top_iff.2 fun x _ => hs x
  have hsmulD : ∀ (g : G) (f : CoInd H A), dif H σ (g • f) = g • dif H σ f := dif_smul H σ hQ
  -- Step 1: the trace is injective on `H²(G, M)`
  have hS : Function.Injective (shapiro A H) := shapiro_injective
  haveI : Finite (ContH2 G (CoInd H A)) := Finite.of_injective _ hS
  have hc : Nat.card (ContH2 G (CoInd H A)) ≤ Nat.card H :=
    (Nat.card_le_card_of_injective _ hS).trans hH
  set trH := h2Hom (G := G) (trace (A := A) H) (trace_smul H) with htrH
  set dH := h2Hom (G := G) (diag (A := A) H) (fun g a => diag_smul H g a) with hdH
  have hpow : ∀ x, trH (dH x) = x ^ H.index := by
    intro x
    rw [htrH, hdH, h2Hom_comp]
    induction x using induction_on with | h c => ?_
    rw [h2Hom_mk, ← map_pow]
    congr 1
    apply cocycles_ext
    intro a b
    simp only [cocyclesMap_apply, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.id_apply,
      trace_diag, hℓ']
    rfl
  have hrange : (powMonoidHom H.index : ContH2 G A →* ContH2 G A).range ≤ trH.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨dH x, hpow x⟩
  have hidx0 : 0 < H.index := hℓ.pos
  have hcard : Nat.card H ≤ Nat.card (powMonoidHom H.index : ContH2 G A →* ContH2 G A).range := by
    have h1 := card_le_card_range_pow (X := ContH2 G A) hidx0
    rw [hG, ← H.card_mul_index, mul_comm] at h1
    exact Nat.le_of_mul_le_mul_left h1 hidx0
  have htr_inj : Function.Injective trH :=
    injective_of_card_le_card_range trH (hc.trans (hcard.trans (Subgroup.card_le_of_le hrange)))
  -- Step 2: `H²(G, J) = 0` for `J = ker(trace)`
  have hJ : ∀ F : G × G → CoInd H A, IsMulCocycle₂ F → (∀ x, trace H (F x) = 1) →
      ∃ Y : G → CoInd H A, (∀ g, trace H (Y g) = 1) ∧ dx G _ Y = F := by
    intro F hF hFt
    have h1 : trH (mk (mkCocycle F (.of_discrete _) hF)) = 1 := by
      rw [htrH, h2Hom_mk, mk_eq_one_iff]
      refine ⟨1, .of_discrete _, ?_⟩
      rw [dx_one]
      funext ⟨a, b⟩
      exact (hFt (a, b)).symm
    obtain ⟨Y, -, hY⟩ := (mk_eq_one_iff _).1 (htr_inj (h1.trans (map_one trH).symm))
    rw [coe_mkCocycle] at hY
    have hc1 : IsMulCocycle₁ (fun g => trace H (Y g)) := by
      refine GShortExact.isMulCocycle₁_of_dx_eq_one (G := G) fun a b => ?_
      rw [← dx_comp (trace H) (trace_smul H), hY]
      exact hFt (a, b)
    obtain ⟨a, ha⟩ := h90 _ hc1
    refine ⟨fun g => Y g / (g • single H a / single H a), fun g => ?_, ?_⟩
    · rw [map_div, map_div, trace_smul, trace_single, ha, div_self']
    · change dx G _ (Y / fun g => g • single H a / single H a) = F
      rw [div_eq_mul_inv, dx_mul, dx_inv, dx_smul_div, inv_one, mul_one, hY]
  -- Step 3: `H³(G, A) ↪ H³(G, M) = 0`
  intro z _ hz
  have hz' : IsMulCocycle₃ fun x => diag H (z x) :=
    isMulCocycle₃_comp (diag H) (fun g a => diag_smul H g a) hz
  obtain ⟨F, -, hF⟩ := CoInd.h3Trivial h3 _ (.of_discrete _) hz'
  have hDF : IsMulCocycle₂ fun x => dif H σ (F x) := by
    rw [isMulCocycle₂_iff_dc2]
    intro a b c
    rw [← map_dc2 (dif H σ) hsmulD F, hF, dif_diag]
  obtain ⟨Y, hYt, hY⟩ := hJ _ hDF fun x => trace_dif H σ (F x)
  choose Y' hY' using fun g => exists_dif_eq H hgen (hYt g)
  have hk : ∀ x, dif H σ ((F / dx G _ Y') x) = 1 := by
    intro x
    rw [Pi.div_apply, map_div, dx_comp (dif H σ) hsmulD, show (fun g => dif H σ (Y' g)) = Y from
      funext hY', hY, div_self']
  refine ⟨fun x => (F / dx G _ Y') x (base H), .of_discrete _, ?_⟩
  have hdiag : (fun x => diag H ((F / dx G _ Y') x (base H))) = F / dx G _ Y' :=
    funext fun x => (eq_diag_of_dif H hgen (hk x)).symm
  funext x
  apply diag_injective H
  have hdd : dc2 (dx G _ Y') = 1 := by
    funext ⟨a, b, c⟩
    exact (isMulCocycle₂_iff_dc2 _).1 (isMulCocycle₂_dx Y') a b c
  rw [map_dc2 (diag H) (fun g a => diag_smul H g a), hdiag, dc2_div, hdd, div_one, hF]

end ContH2
