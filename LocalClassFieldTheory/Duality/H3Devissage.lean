/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.H3Vanishing

/-!
# Dévissage for `H³ = 0` in cocycle form

For a topological group `G` we show that the property `ContH2.H3Trivial G -` (every locally
constant `3`-cocycle is the coboundary of a locally constant `2`-cochain) behaves well along
short exact sequences and isomorphisms:

* **`Brauer.GShortExact.h3Trivial`** : for `0 → A → B → C → 0` (with `G` acting smoothly on
  `B`), `H3Trivial G A` and `H3Trivial G C` imply `H3Trivial G B` (the degree-three part
  `H³(A) → H³(B) → H³(C)` of the long exact sequence, in cocycle form);
* `Brauer.h3Trivial_of_mulEquiv`, `Brauer.h3Trivial_of_subsingleton`.

We also construct, for a `G`-stable subgroup `B ≤ A`, the actions of `G` on `B` and on `A ⧸ B`
and the short exact sequence `0 → B → A → A ⧸ B → 0` (`Brauer.subQuotSES`), and prove an
induction principle for finite smooth `G`-modules (`Brauer.finite_module_induction`): a property
that holds for trivial and for **simple** modules (`Brauer.IsSimpleGModule`) and is closed under
extensions holds for all finite smooth modules.
-/

open ContH2 groupCohomology

set_option linter.unusedSectionVars false

namespace ContH2

variable {G M : Type*} [Group G] [CommGroup M] [MulDistribMulAction G M]

theorem dc2_mul (f f' : G × G → M) : dc2 (f * f') = dc2 f * dc2 f' := by
  ext ⟨a, b, c⟩
  simp only [dc2_apply, Pi.mul_apply, smul_mul']
  mul_abel

theorem dc2_one : dc2 (1 : G × G → M) = 1 := by
  ext ⟨a, b, c⟩
  simp

theorem isMulCocycle₃_mul {z z' : G × G × G → M} (hz : IsMulCocycle₃ z)
    (hz' : IsMulCocycle₃ z') : IsMulCocycle₃ (z * z') := by
  intro a b c d
  have h1 := hz a b c d
  have h2 := hz' a b c d
  simp only [Pi.mul_apply, smul_mul']
  calc a • z (b, c, d) * a • z' (b, c, d) * (z (a, b * c, d) * z' (a, b * c, d)) *
        (z (a, b, c) * z' (a, b, c)) =
      (a • z (b, c, d) * z (a, b * c, d) * z (a, b, c)) *
        (a • z' (b, c, d) * z' (a, b * c, d) * z' (a, b, c)) := by mul_abel
    _ = _ := by rw [h1, h2]; mul_abel

theorem isMulCocycle₃_inv {z : G × G × G → M} (hz : IsMulCocycle₃ z) :
    IsMulCocycle₃ z⁻¹ := by
  intro a b c d
  have h1 := hz a b c d
  simp only [Pi.inv_apply, smul_inv']
  rw [← mul_inv, ← mul_inv, ← mul_inv, h1]

theorem isMulCocycle₃_div {z z' : G × G × G → M} (hz : IsMulCocycle₃ z)
    (hz' : IsMulCocycle₃ z') : IsMulCocycle₃ (z / z') := by
  rw [div_eq_mul_inv]
  exact isMulCocycle₃_mul hz (isMulCocycle₃_inv hz')

theorem isMulCocycle₃_comp {N : Type*} [CommGroup N] [MulDistribMulAction G N] (φ : M →* N)
    (hφ : ∀ (g : G) (m : M), φ (g • m) = g • φ m) {z : G × G × G → M} (hz : IsMulCocycle₃ z) :
    IsMulCocycle₃ fun x => φ (z x) := by
  intro a b c d
  simp only [← hφ, ← map_mul, hz a b c d]

end ContH2

namespace Brauer

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- `H³` vanishes for the trivial module. -/
theorem h3Trivial_of_subsingleton {A : Type*} [CommGroup A] [MulDistribMulAction G A]
    [Subsingleton A] : H3Trivial G A :=
  fun _ _ _ => ⟨1, IsLocallyConstant.const 1, funext fun _ => Subsingleton.elim _ _⟩

/-- `H3Trivial` is invariant under equivariant isomorphisms. -/
theorem h3Trivial_of_mulEquiv {A A' : Type*} [CommGroup A] [CommGroup A']
    [MulDistribMulAction G A] [MulDistribMulAction G A'] (τ : A ≃* A')
    (hτ : ∀ (g : G) (a : A), τ (g • a) = g • τ a) (h : H3Trivial G A) : H3Trivial G A' := by
  intro z hzl hz
  have hτ' : ∀ (g : G) (a : A'), τ.symm (g • a) = g • τ.symm a := fun g a => by
    apply τ.injective
    rw [hτ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  obtain ⟨f, hfl, hf⟩ := h (fun x => τ.symm (z x)) (hzl.comp _)
    (isMulCocycle₃_comp τ.symm.toMonoidHom hτ' hz)
  refine ⟨fun x => τ (f x), hfl.comp _, funext fun x => ?_⟩
  refine (map_dc2 τ.toMonoidHom hτ f x).symm.trans ?_
  change τ (dc2 f x) = z x
  rw [hf, MulEquiv.apply_symm_apply]

namespace GShortExact

variable [IsTopologicalGroup G]
variable {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]
  [MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]
  [SmoothAction G B] (S : GShortExact G A B C)

include S in
/-- **`H³(A) = 0` and `H³(C) = 0` imply `H³(B) = 0`** (in cocycle form). -/
theorem h3Trivial (hA : H3Trivial G A) (hC : H3Trivial G C) : H3Trivial G B := by
  intro z hzl hz
  obtain ⟨g, hgl, hg⟩ := hC (fun x => S.π (z x)) (hzl.comp _)
    (isMulCocycle₃_comp S.π S.map_smul_π hz)
  set g' : G × G → B := fun x => S.sec (g x) with hg'_def
  have hg'l : IsLocallyConstant g' := hgl.comp _
  set w : G × G × G → B := z / dc2 g' with hw_def
  have hπw : ∀ x, S.π (w x) = 1 := fun x => by
    rw [hw_def, Pi.div_apply, map_div, map_dc2 S.π S.map_smul_π]
    have : (fun y => S.π (g' y)) = g := funext fun y => S.π_sec _
    rw [this, hg, div_self']
  set a : G × G × G → A := fun x => S.pre (w x) with ha_def
  have hia : ∀ x, S.i (a x) = w x := fun x => S.i_pre (hπw x)
  have hwl : IsLocallyConstant w := hzl.div (isLocallyConstant_dc2 hg'l)
  have hwc : IsMulCocycle₃ w := isMulCocycle₃_div hz (isMulCocycle₃_dc2 g')
  have hac : IsMulCocycle₃ a := isMulCocycle₃_comp_of_injective S.i S.map_smul_i S.injective
    (by simpa only [hia] using hwc)
  obtain ⟨h, hhl, hh⟩ := hA a (hwl.comp _) hac
  refine ⟨g' * fun x => S.i (h x), hg'l.mul (hhl.comp _), ?_⟩
  rw [dc2_mul]
  funext x
  rw [Pi.mul_apply, ← map_dc2 S.i S.map_smul_i, hh, hia, hw_def, Pi.div_apply]
  exact mul_div_cancel _ _

end GShortExact

/-! ### Sub- and quotient modules -/

section SubQuot

variable {A : Type*} [CommGroup A] [MulDistribMulAction G A]

/-- A subgroup stable under `G`. -/
def IsGStable (B : Subgroup A) : Prop := ∀ (g : G) (b : A), b ∈ B → g • b ∈ B

/-- The action of `G` on a `G`-stable subgroup. -/
@[reducible]
def subAction (B : Subgroup A) (hB : IsGStable (G := G) B) : MulDistribMulAction G B where
  smul g b := ⟨g • (b : A), hB g b b.2⟩
  one_smul b := Subtype.ext (one_smul G (b : A))
  mul_smul g h b := Subtype.ext (mul_smul g h (b : A))
  smul_mul g a b := Subtype.ext (smul_mul' g (a : A) b)
  smul_one g := Subtype.ext (smul_one g)

/-- The action of `G` on the quotient by a `G`-stable subgroup. -/
@[reducible]
def quotAction (B : Subgroup A) (hB : IsGStable (G := G) B) :
    MulDistribMulAction G (A ⧸ B) where
  smul g := QuotientGroup.map B B (MulDistribMulAction.toMonoidHom A g) (fun b hb => hB g b hb)
  one_smul x := by
    induction x using QuotientGroup.induction_on with | H a => ?_
    change QuotientGroup.mk ((1 : G) • a) = _
    rw [one_smul]
  mul_smul g h x := by
    induction x using QuotientGroup.induction_on with | H a => ?_
    change QuotientGroup.mk ((g * h) • a) = QuotientGroup.mk (g • h • a)
    rw [mul_smul]
  smul_mul g x y := map_mul _ x y
  smul_one g := map_one _

theorem quotAction_smul_mk (B : Subgroup A) (hB : IsGStable (G := G) B) (g : G) (a : A) :
    @HSMul.hSMul G (A ⧸ B) (A ⧸ B) (@instHSMul G (A ⧸ B) (quotAction B hB).toSMul) g
      (QuotientGroup.mk a) = QuotientGroup.mk (g • a) := rfl

/-- The short exact sequence `0 → B → A → A ⧸ B → 0`. -/
@[reducible]
def subQuotSES (B : Subgroup A) (hB : IsGStable (G := G) B) :
    @GShortExact G B A (A ⧸ B) _ _ _ _ (subAction B hB) _ (quotAction B hB) :=
  @GShortExact.mk G B A (A ⧸ B) _ _ _ _ (subAction B hB) _ (quotAction B hB)
    B.subtype (QuotientGroup.mk' B) (fun _ _ => rfl) (fun _ _ => rfl) Subtype.val_injective
    (QuotientGroup.mk'_surjective B) (fun b => by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.range_subtype])

theorem smoothAction_sub [SmoothAction G A] (B : Subgroup A) (hB : IsGStable (G := G) B) :
    @SmoothAction G B _ (subAction B hB).toSMul := by
  letI := subAction B hB
  exact ⟨fun b => IsLocallyConstant.desc (fun g : G => g • b) Subtype.val
    (SmoothAction.isLocallyConstant_smul (G := G) (b : A)) Subtype.val_injective⟩

theorem smoothAction_quot [SmoothAction G A] (B : Subgroup A) (hB : IsGStable (G := G) B) :
    @SmoothAction G (A ⧸ B) _ (quotAction B hB).toSMul := by
  letI := quotAction B hB
  refine ⟨fun x => ?_⟩
  induction x using QuotientGroup.induction_on with | H a => ?_
  exact (SmoothAction.isLocallyConstant_smul (G := G) a).comp _

end SubQuot

/-! ### Induction on finite modules -/

/-- A **simple** `G`-module: non-trivial, without `G`-stable subgroups other than `⊥`, `⊤`. -/
def IsSimpleGModule (G A : Type*) [Group G] [CommGroup A] [MulDistribMulAction G A] : Prop :=
  Nontrivial A ∧ ∀ B : Subgroup A, IsGStable (G := G) B → B = ⊥ ∨ B = ⊤

universe u

/-- **Induction principle for finite smooth `G`-modules.** A property of finite smooth modules
which holds for trivial and simple modules and is closed under extensions holds for all finite
smooth modules. -/
theorem finite_module_induction
    (P : ∀ (A : Type u) [CommGroup A] [MulDistribMulAction G A], Prop)
    (htriv : ∀ (A : Type u) [CommGroup A] [MulDistribMulAction G A] [Subsingleton A], P A)
    (hsimple : ∀ (A : Type u) [CommGroup A] [MulDistribMulAction G A] [Finite A]
      [SmoothAction G A], IsSimpleGModule G A → P A)
    (hext : ∀ (A B C : Type u) [CommGroup A] [CommGroup B] [CommGroup C]
      [MulDistribMulAction G A] [MulDistribMulAction G B] [MulDistribMulAction G C]
      [Finite A] [Finite B] [Finite C] [SmoothAction G A] [SmoothAction G B]
      [SmoothAction G C], GShortExact G A B C → P A → P C → P B)
    (A : Type u) [CommGroup A] [MulDistribMulAction G A] [Finite A] [SmoothAction G A] :
    P A := by
  induction h : Nat.card A using Nat.strong_induction_on generalizing A with
  | _ n ih => ?_
  by_cases hs : Subsingleton A
  · exact htriv A
  rw [not_subsingleton_iff_nontrivial] at hs
  by_cases hsim : IsSimpleGModule G A
  · exact hsimple A hsim
  simp only [IsSimpleGModule, hs, true_and, not_forall, not_or] at hsim
  obtain ⟨B, hB, hB0, hB1⟩ := hsim
  letI := subAction B hB
  letI := quotAction B hB
  haveI := smoothAction_sub B hB
  haveI := smoothAction_quot B hB
  have hcard : Nat.card A = Nat.card B * Nat.card (A ⧸ B) := by
    rw [mul_comm]; exact Subgroup.card_eq_card_quotient_mul_card_subgroup B
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hQpos : 0 < Nat.card (A ⧸ B) := Nat.card_pos
  have hB2 : 1 < Nat.card B := by
    rw [Subgroup.one_lt_card_iff_ne_bot]; exact hB0
  have hQ2 : 1 < Nat.card (A ⧸ B) := by
    by_contra hle
    have h1 : Nat.card (A ⧸ B) = 1 := by omega
    apply hB1
    rw [← Subgroup.index_eq_one, Subgroup.index, h1]
  refine hext B A (A ⧸ B) (subQuotSES B hB) ?_ ?_
  · exact ih _ (by rw [← h, hcard]; exact lt_mul_of_one_lt_right hBpos hQ2) B rfl
  · exact ih _ (by rw [← h, hcard]; exact lt_mul_of_one_lt_left hQpos hB2) (A ⧸ B) rfl

end Brauer
