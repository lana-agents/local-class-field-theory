/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.LongExact
import LocalClassFieldTheory.Duality.Cartier

/-!
# Dévissage for the local Euler characteristic

From the long exact sequence `LocalClassFieldTheory.Duality.LongExact` of a short exact sequence
`0 → A → B → C → 0` of discrete `G`-modules we get, by counting along the exact sequence
`0 → H⁰(A) → H⁰(B) → H⁰(C) → H¹(A) → H¹(B) → H¹(C) → H²(A) → H²(B) → H²(C) → 0` (exact on the
right **provided** `H²(B) → H²(C)` is surjective),

`#H¹(B) · #H⁰(A) #H²(A) #H⁰(C) #H²(C) = #H¹(A) #H¹(C) · #H⁰(B) #H²(B)`

(`Brauer.GShortExact.card_identity`; an identity of cardinals in `ℕ`, valid also for infinite
groups with the convention `Nat.card = 0`), i.e. `χ(B) = χ(A) χ(C)`. Consequences for a finite
extension `K` of `ℚ_p`:

* **`PadicField.eulerCharacteristicFor_of_shortExact`**: if the Euler characteristic formula
  holds for `A` and `C` and `H²(K, B) → H²(K, C)` is surjective, it holds for `B`;
* `PadicField.eulerCharacteristicFor_of_split`: the surjectivity holds when `B → C` has an
  equivariant section; `PadicField.eulerCharacteristicFor_prod`, `..._pi`: products;
* `PadicField.eulerCharacteristicFor_of_equiv`: invariance under equivariant isomorphisms;
* **`PadicField.eulerCharacteristicFor_of_trivial`**: every finite module `M` with trivial
  action satisfies the Euler characteristic formula if `K` contains the `e`-th roots of unity,
  `e = exp(M)` (structure theorem: `M ≃ ∏ ℤ/n_i`, `n_i ∣ e`);
* **`PadicField.eulerCharacteristicFor_pi_mu`**: `M = ∏ μ_{n_i}` (no condition on `K`).

The surjectivity of `H²(B) → H²(C)` for arbitrary (non-split) extensions is equivalent to the
injectivity of `H³(K, A) → H³(K, B)` and follows from `cd(G_K) = 2`; since `H³` is not
formalised, it is kept as an explicit hypothesis in `eulerCharacteristicFor_of_shortExact`.
-/

open ContH2 groupCohomology KummerTheory

set_option linter.unusedSectionVars false

namespace Brauer

/-! ### Counting along exact sequences -/

theorem card_eq_card_ker_mul_card_range {X Y : Type*} [Group X] [Group Y] (φ : X →* Y) :
    Nat.card X = Nat.card φ.ker * Nat.card φ.range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, mul_comm,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]

/-- **Multiplicativity of alternating products along a nine-term exact sequence**
`1 → A₀ → B₀ → C₀ → A₁ → B₁ → C₁ → A₂ → B₂ → C₂ → 1`. -/
theorem card_identity_of_exact {A₀ B₀ C₀ A₁ B₁ C₁ A₂ B₂ C₂ : Type*} [Group A₀] [Group B₀]
    [Group C₀] [Group A₁] [Group B₁] [Group C₁] [Group A₂] [Group B₂] [Group C₂]
    (i₀ : A₀ →* B₀) (p₀ : B₀ →* C₀) (d₀ : C₀ →* A₁) (i₁ : A₁ →* B₁) (p₁ : B₁ →* C₁)
    (d₁ : C₁ →* A₂) (i₂ : A₂ →* B₂) (p₂ : B₂ →* C₂) (hi₀ : Function.Injective i₀)
    (e₀ : p₀.ker = i₀.range) (e₁ : d₀.ker = p₀.range) (e₂ : i₁.ker = d₀.range)
    (e₃ : p₁.ker = i₁.range) (e₄ : d₁.ker = p₁.range) (e₅ : i₂.ker = d₁.range)
    (e₆ : p₂.ker = i₂.range) (hp₂ : Function.Surjective p₂) :
    Nat.card B₁ * (Nat.card A₀ * Nat.card A₂ * (Nat.card C₀ * Nat.card C₂)) =
      Nat.card A₁ * Nat.card C₁ * (Nat.card B₀ * Nat.card B₂) := by
  have hA₀ := card_eq_card_ker_mul_card_range i₀
  have hB₀ := card_eq_card_ker_mul_card_range p₀
  have hC₀ := card_eq_card_ker_mul_card_range d₀
  have hA₁ := card_eq_card_ker_mul_card_range i₁
  have hB₁ := card_eq_card_ker_mul_card_range p₁
  have hC₁ := card_eq_card_ker_mul_card_range d₁
  have hA₂ := card_eq_card_ker_mul_card_range i₂
  have hB₂ := card_eq_card_ker_mul_card_range p₂
  have hC₂ : Nat.card C₂ = Nat.card p₂.range := by
    rw [MonoidHom.range_eq_top.2 hp₂, Subgroup.card_top]
  rw [(MonoidHom.ker_eq_bot_iff i₀).2 hi₀, Subgroup.card_bot, one_mul] at hA₀
  rw [e₀] at hB₀
  rw [e₁] at hC₀
  rw [e₂] at hA₁
  rw [e₃] at hB₁
  rw [e₄] at hC₁
  rw [e₅] at hA₂
  rw [e₆] at hB₂
  rw [hA₀, hB₀, hC₀, hA₁, hB₁, hC₁, hA₂, hB₂, hC₂]
  ring

/-- In an exact sequence `X → Y → Z` with `X`, `Z` finite, `Y` is finite. -/
theorem finite_of_exact {X Y Z : Type*} [Group X] [Group Y] [Group Z] [Finite X] [Finite Z]
    (f : X →* Y) (g : Y →* Z) (h : g.ker = f.range) : Finite Y := by
  haveI : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  haveI : Finite g.ker := by rw [h]; infer_instance
  apply Nat.finite_of_card_ne_zero
  rw [card_eq_card_ker_mul_card_range g]
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

/-! ### Products of smooth modules -/

instance SmoothAction.prod {G M N : Type*} [Group G] [TopologicalSpace G] [CommGroup M]
    [CommGroup N] [MulDistribMulAction G M] [MulDistribMulAction G N] [SmoothAction G M]
    [SmoothAction G N] : SmoothAction G (M × N) :=
  ⟨fun m => (SmoothAction.isLocallyConstant_smul (G := G) m.1).prodMk
    (SmoothAction.isLocallyConstant_smul (G := G) m.2)⟩

instance SmoothAction.pi {G ι : Type*} [Finite ι] {M : ι → Type*} [Group G] [TopologicalSpace G]
    [∀ i, CommGroup (M i)] [∀ i, MulDistribMulAction G (M i)] [∀ i, SmoothAction G (M i)] :
    SmoothAction G (∀ i, M i) := by
  refine ⟨fun m => ?_⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  have h : ∀ i, ∀ᶠ g in nhds g₀, g • m i = g₀ • m i := fun i =>
    (IsLocallyConstant.iff_eventually_eq _).1 (SmoothAction.isLocallyConstant_smul (m i)) g₀
  filter_upwards [Filter.eventually_all.2 h] with g hg
  exact funext hg

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- `0 → A → A × C → C → 0`. -/
def GShortExact.prod (A C : Type*) [CommGroup A] [CommGroup C] [MulDistribMulAction G A]
    [MulDistribMulAction G C] : GShortExact G A (A × C) C where
  i := MonoidHom.inl A C
  π := MonoidHom.snd A C
  map_smul_i _ _ := by ext <;> simp
  map_smul_π _ _ := rfl
  injective _ _ h := congrArg Prod.fst h
  surjective c := ⟨(1, c), rfl⟩
  exact b := by
    refine ⟨fun h => ⟨b.1, Prod.ext rfl h.symm⟩, ?_⟩
    rintro ⟨a, rfl⟩
    rfl

namespace GShortExact

variable {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]
  [MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]
  (S : GShortExact G A B C)

/-- An equivariant section of `B → C` makes `H²(B) → H²(C)` surjective. -/
theorem h2Hom_surjective_of_section (σ : C →* B) (hσ : ∀ (g : G) (c : C), σ (g • c) = g • σ c)
    (hπσ : ∀ c, S.π (σ c) = c) : Function.Surjective (h2Hom (G := G) S.π S.map_smul_π) := by
  intro γ
  refine ⟨h2Hom σ hσ γ, ?_⟩
  induction γ using induction_on with | h c => ?_
  rw [h2Hom_mk, h2Hom_mk]
  congr 1
  exact cocycles_ext fun g h => by simp [hπσ]

include S in
theorem card_eq_mul : Nat.card B = Nat.card A * Nat.card C := by
  rw [card_eq_card_ker_mul_card_range S.π, MonoidHom.range_eq_top.2 S.surjective,
    Subgroup.card_top]
  congr 1
  have : S.π.ker = S.i.range := by ext b; exact S.exact b
  rw [this]
  exact (Nat.card_congr (MonoidHom.ofInjective S.injective).toEquiv).symm

variable [IsTopologicalGroup G]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalGroup A]
  [TopologicalSpace B] [DiscreteTopology B] [IsTopologicalGroup B] [SmoothAction G B]
  [TopologicalSpace C] [DiscreteTopology C] [IsTopologicalGroup C]

/-- **`χ(B) = χ(A) χ(C)`** (as an identity of cardinals), if `H²(B) → H²(C)` is surjective. -/
theorem card_identity (hsurj : Function.Surjective (h2Hom (G := G) S.π S.map_smul_π)) :
    Nat.card (ContH1 G B) * (Nat.card (H0 G A) * Nat.card (ContH2 G A) *
      (Nat.card (H0 G C) * Nat.card (ContH2 G C))) =
      Nat.card (ContH1 G A) * Nat.card (ContH1 G C) *
        (Nat.card (H0 G B) * Nat.card (ContH2 G B)) :=
  card_identity_of_exact _ _ _ _ _ _ _ _ S.h0Hom_injective S.exact_h0B S.exact_h0C S.exact_h1A
    S.exact_h1B S.exact_h1C S.exact_h2A S.exact_h2B hsurj

end GShortExact

end Brauer

namespace PadicField

open Brauer

universe u

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

section Devissage

variable {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C] [Finite A] [Finite B]
  [Finite C] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalGroup A]
  [TopologicalSpace B] [DiscreteTopology B] [IsTopologicalGroup B]
  [TopologicalSpace C] [DiscreteTopology C] [IsTopologicalGroup C]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) A] [MulDistribMulAction (Ω ≃ₐ[K] Ω) B]
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) C] [SmoothAction (Ω ≃ₐ[K] Ω) B]

include hp in
/-- **Dévissage for the Euler characteristic**: for a short exact sequence `0 → A → B → C → 0`
of finite discrete `G_K`-modules such that `H²(K, B) → H²(K, C)` is surjective, the Euler
characteristic formula for `A` and `C` implies it for `B`. -/
theorem eulerCharacteristicFor_of_shortExact (S : GShortExact (Ω ≃ₐ[K] Ω) A B C)
    (hsurj : Function.Surjective (h2Hom (G := Ω ≃ₐ[K] Ω) S.π S.map_smul_π))
    (hA : EulerCharacteristicFor p K Ω A) (hC : EulerCharacteristicFor p K Ω C) :
    EulerCharacteristicFor p K Ω B := by
  obtain ⟨hA1, hA2, hA⟩ := hA
  obtain ⟨hC1, hC2, hC⟩ := hC
  haveI := hA1
  haveI := hA2
  haveI := hC1
  haveI := hC2
  haveI hB1 : Finite (ContH1 (Ω ≃ₐ[K] Ω) B) := finite_of_exact _ _ S.exact_h1B
  haveI hB2 : Finite (ContH2 (Ω ≃ₐ[K] Ω) B) := finite_of_exact _ _ S.exact_h2B
  refine ⟨hB1, hB2, ?_⟩
  have key := S.card_identity hsurj
  rw [hA, hC] at key
  have hX : 0 < Nat.card (H0 (Ω ≃ₐ[K] Ω) A) * Nat.card (ContH2 (Ω ≃ₐ[K] Ω) A) *
      (Nat.card (H0 (Ω ≃ₐ[K] Ω) C) * Nat.card (ContH2 (Ω ≃ₐ[K] Ω) C)) :=
    Nat.mul_pos (Nat.mul_pos Nat.card_pos Nat.card_pos) (Nat.mul_pos Nat.card_pos Nat.card_pos)
  rw [S.card_eq_mul, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', add_mul, pow_add]
  apply Nat.eq_of_mul_eq_mul_right hX
  rw [key]
  ring

include hp in
/-- Dévissage for a split short exact sequence. -/
theorem eulerCharacteristicFor_of_split (S : GShortExact (Ω ≃ₐ[K] Ω) A B C) (σ : C →* B)
    (hσ : ∀ (g : Ω ≃ₐ[K] Ω) (c : C), σ (g • c) = g • σ c) (hπσ : ∀ c, S.π (σ c) = c)
    (hA : EulerCharacteristicFor p K Ω A) (hC : EulerCharacteristicFor p K Ω C) :
    EulerCharacteristicFor p K Ω B :=
  eulerCharacteristicFor_of_shortExact S (S.h2Hom_surjective_of_section σ hσ hπσ) hA hC

include hp in
/-- **The Euler characteristic formula for a product** `A × C`. -/
theorem eulerCharacteristicFor_prod [SmoothAction (Ω ≃ₐ[K] Ω) A] [SmoothAction (Ω ≃ₐ[K] Ω) C]
    (hA : EulerCharacteristicFor p K Ω A) (hC : EulerCharacteristicFor p K Ω C) :
    EulerCharacteristicFor p K Ω (A × C) :=
  eulerCharacteristicFor_of_split (GShortExact.prod A C) (MonoidHom.inr A C)
    (fun g c => by ext <;> simp) (fun _ => rfl) hA hC

end Devissage

section Transport

variable {M M' : Type*} [CommGroup M] [CommGroup M'] [TopologicalSpace M] [DiscreteTopology M]
  [IsTopologicalGroup M] [TopologicalSpace M'] [DiscreteTopology M'] [IsTopologicalGroup M']
  [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [MulDistribMulAction (Ω ≃ₐ[K] Ω) M']
  [SmoothAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M']

/-- The Euler characteristic formula is invariant under equivariant isomorphisms. -/
theorem eulerCharacteristicFor_of_equiv (τ : M ≃* M')
    (hτ : ∀ (g : Ω ≃ₐ[K] Ω) (x : M), τ (g • x) = g • τ x) (h : EulerCharacteristicFor p K Ω M) :
    EulerCharacteristicFor p K Ω M' := by
  obtain ⟨h1, h2, h⟩ := h
  have b0 := h0Map_bijective τ hτ
  have b1 := h1Map_bijective τ hτ
  have b2 := h2Map_bijective τ hτ
  refine ⟨Finite.of_surjective _ b1.2, Finite.of_surjective _ b2.2, ?_⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ b1), ← Nat.card_congr (Equiv.ofBijective _ b0),
    ← Nat.card_congr (Equiv.ofBijective _ b2), ← Nat.card_congr τ.toEquiv]
  exact h

/-- The Euler characteristic formula for the trivial module. -/
theorem eulerCharacteristicFor_of_subsingleton [Subsingleton M] :
    EulerCharacteristicFor p K Ω M := by
  haveI : Subsingleton (ContH1 (Ω ≃ₐ[K] Ω) M) := ⟨fun x y => by
    induction x using ContH1.induction_on with | h x => ?_
    induction y using ContH1.induction_on with | h y => ?_
    congr 1
    exact Subtype.ext (funext fun _ => Subsingleton.elim _ _)⟩
  haveI : Subsingleton (ContH2 (Ω ≃ₐ[K] Ω) M) := ⟨fun x y => by
    induction x using induction_on with | h x => ?_
    induction y using induction_on with | h y => ?_
    congr 1
    exact Subtype.ext (funext fun _ => Subsingleton.elim _ _)⟩
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [Nat.card_of_subsingleton (1 : ContH1 (Ω ≃ₐ[K] Ω) M),
    Nat.card_of_subsingleton (1 : H0 (Ω ≃ₐ[K] Ω) M),
    Nat.card_of_subsingleton (1 : ContH2 (Ω ≃ₐ[K] Ω) M), Nat.card_of_subsingleton (1 : M)]
  simp

end Transport

/-- `∏_{j < k+1} Z_j ≃ Z_0 × ∏_{j < k} Z_{j+1}`. -/
def piFinSuccMulEquiv {k : ℕ} (Z : Fin (k + 1) → Type*) [∀ j, Monoid (Z j)] :
    (∀ j, Z j) ≃* Z 0 × ∀ j : Fin k, Z j.succ where
  toFun f := (f 0, fun j => f j.succ)
  invFun q := Fin.cons q.1 q.2
  left_inv f := Fin.cons_self_tail f
  right_inv q := by simp
  map_mul' _ _ := rfl

/-- **The Euler characteristic formula for a finite product.** -/
theorem eulerCharacteristicFor_pi : ∀ (k : ℕ) (Z : Fin k → Type u) [∀ j, CommGroup (Z j)]
    [∀ j, Finite (Z j)] [∀ j, TopologicalSpace (Z j)] [∀ j, DiscreteTopology (Z j)]
    [∀ j, IsTopologicalGroup (Z j)] [∀ j, MulDistribMulAction (Ω ≃ₐ[K] Ω) (Z j)]
    [∀ j, SmoothAction (Ω ≃ₐ[K] Ω) (Z j)], (∀ j, EulerCharacteristicFor p K Ω (Z j)) →
    EulerCharacteristicFor p K Ω (∀ j, Z j)
  | 0, _, _, _, _, _, _, _, _, _ => eulerCharacteristicFor_of_subsingleton
  | k + 1, Z, _, _, _, _, _, _, _, h => by
    have hP := eulerCharacteristicFor_prod (h 0)
      (eulerCharacteristicFor_pi k (fun j => Z j.succ) fun j => h j.succ)
    exact eulerCharacteristicFor_of_equiv (piFinSuccMulEquiv Z).symm
      (symm_smul (piFinSuccMulEquiv Z) fun _ _ => rfl) hP

include hp in
/-- **The Euler characteristic formula for `∏ μ_{n_j}`** (no condition on `K`). -/
theorem eulerCharacteristicFor_pi_mu (k : ℕ) (m : Fin k → ℕ) [∀ j, NeZero (m j)] :
    EulerCharacteristicFor p K Ω (∀ j, Mu (m j) Ω) :=
  eulerCharacteristicFor_pi k _ fun j => eulerCharacteristicFor_mu (m j)

/-- `n_i ∣ exp(M)` for a decomposition `M ≃ ∏ ℤ/n_i`. -/
theorem dvd_exponent_of_equiv {ι M : Type*} [Monoid M] {n : ι → ℕ}
    (e : M ≃* ((i : ι) → Multiplicative (ZMod (n i)))) (i : ι) :
    n i ∣ Monoid.exponent M := by
  classical
  have : n i = orderOf (e.symm <| Pi.mulSingle i <| .ofAdd 1) := by
    simpa only [MulEquiv.orderOf_eq, orderOf_piMulSingle, orderOf_ofAdd_eq_addOrderOf]
      using (ZMod.addOrderOf_one (n i)).symm
  exact this ▸ Monoid.order_dvd_exponent _

/-- **Dévissage for modules with trivial action**: if the Euler characteristic formula holds
for `ℤ/n` for every `n > 1` dividing `e = exp(M)`, it holds for every finite `M` with trivial
action (structure theorem: `M ≃ ∏ ℤ/n_i` with `n_i ∣ e`). -/
theorem eulerCharacteristicFor_of_trivial' (M : Type*) [CommGroup M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalGroup M]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]
    (htriv : ∀ (g : Ω ≃ₐ[K] Ω) (m : M), g • m = m)
    (h : ∀ (n : ℕ) [NeZero n], 1 < n → n ∣ Monoid.exponent M →
      EulerCharacteristicFor p K Ω (TrivZMod n)) : EulerCharacteristicFor p K Ω M := by
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite M
  let eι := Fintype.equivFin ι
  let m : Fin (Fintype.card ι) → ℕ := fun j => n (eι.symm j)
  haveI : ∀ j, NeZero (m j) := fun j => ⟨by have := hn (eι.symm j); simp only [m]; omega⟩
  have hm : ∀ j, EulerCharacteristicFor p K Ω (TrivZMod (m j)) := fun j =>
    h (m j) (hn (eι.symm j)) (dvd_exponent_of_equiv e (eι.symm j))
  have hP := eulerCharacteristicFor_pi (Fintype.card ι) (fun j => TrivZMod (m j)) hm
  let τ' : ((i : ι) → Multiplicative (ZMod (n i))) ≃* ∀ j, TrivZMod (m j) :=
    { Equiv.piCongrLeft' (fun i => Multiplicative (ZMod (n i))) eι with
      map_mul' := fun _ _ => rfl }
  exact eulerCharacteristicFor_of_equiv (e.trans τ').symm
    (fun g x => by rw [htriv]; rfl) hP

include hp in
/-- **The Euler characteristic formula for finite modules with trivial action**, provided `K`
contains the `e`-th roots of unity, `e = exp(M)`. -/
theorem eulerCharacteristicFor_of_trivial (M : Type*) [CommGroup M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalGroup M]
    [MulDistribMulAction (Ω ≃ₐ[K] Ω) M] [SmoothAction (Ω ≃ₐ[K] Ω) M]
    (htriv : ∀ (g : Ω ≃ₐ[K] Ω) (m : M), g • m = m)
    [HasEnoughRootsOfUnity K (Monoid.exponent M)] : EulerCharacteristicFor p K Ω M := by
  haveI : NeZero (Monoid.exponent M) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  refine eulerCharacteristicFor_of_trivial' M htriv fun n _ _ hdvd => ?_
  haveI := HasEnoughRootsOfUnity.of_dvd K hdvd
  exact eulerCharacteristicFor_trivZMod (HasEnoughRootsOfUnity.natCard_rootsOfUnity K _)

end PadicField
