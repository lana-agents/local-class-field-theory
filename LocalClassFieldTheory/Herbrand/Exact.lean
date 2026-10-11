/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Herbrand.Basic

/-!
# Multiplicativity of the Herbrand quotient in short exact sequences

Let `0 → A →i B →π C → 0` be a short exact sequence of additive commutative groups compatible
with endomorphisms `σ_A`, `σ_B`, `σ_C` (with `σ_B ^ n = 1`). We construct the exact hexagon

`Ĥ⁰(A) → Ĥ⁰(B) → Ĥ⁰(C) →δ Ĥ⁻¹(A) → Ĥ⁻¹(B) → Ĥ⁻¹(C) →δ Ĥ⁰(A)`

and deduce `|Ĥ⁰(B)| |Ĥ⁻¹(A)| |Ĥ⁻¹(C)| = |Ĥ⁻¹(B)| |Ĥ⁰(A)| |Ĥ⁰(C)|`, i.e. `h(B) = h(A) h(C)`.

Everything is done for the generic Tate quotients `TateQuot P Q = ker P ⧸ im Q` of a pair of
endomorphisms with `P ∘ Q = 0 = Q ∘ P` on `B`: the structure `Herbrand.SES` bundles the short
exact sequence, and `Herbrand.SES.swap` exchanges the roles of `P` and `Q`, so that only three
exactness statements have to be proved (`SES.exact_mapB`, `SES.exact_mapC`, `SES.exact_delta`).

## Main results

* `Herbrand.card_mul_card_eq_of_hexagon`: for an exact cycle of six groups, the alternating
  product of the orders is `1`.
* `Herbrand.card_H0_mul_card_Hm1_eq`: the cardinality identity for a short exact sequence.
* `Herbrand.finite_H0_of_ses`, `Herbrand.finite_Hm1_of_ses`: finiteness of the middle term.
* `Herbrand.herbrand_eq_mul_of_ses`: `h(B) = h(A) h(C)`.
* `Herbrand.herbrand_eq_of_finite_quotient`: `h(B) = h(A)` when `A ≤ B` has finite index.
-/

open Function

namespace Herbrand

/-! ### Exact sequences of finite groups -/

section ExactCard

variable {X Y Z : Type*} [AddGroup X] [AddGroup Y] [AddGroup Z]

theorem card_eq_card_range_mul_card_range (f : X →+ Y) (g : Y →+ Z)
    (h : f.range = g.ker) : Nat.card Y = Nat.card f.range * Nat.card g.range := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker, mul_comm,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv, h]

theorem finite_of_exact [Finite X] [Finite Z] (f : X →+ Y) (g : Y →+ Z)
    (h : f.range = g.ker) : Finite Y := by
  have : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  apply Nat.finite_of_card_ne_zero
  rw [card_eq_card_range_mul_card_range f g h]
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

/-- For an exact cycle `G₀ → G₁ → ⋯ → G₅ → G₀` of groups, the alternating product of the orders
is `1` (as an identity of `Nat.card`s, valid without finiteness hypotheses). -/
theorem card_mul_card_eq_of_hexagon {G₀ G₁ G₂ G₃ G₄ G₅ : Type*} [AddGroup G₀] [AddGroup G₁]
    [AddGroup G₂] [AddGroup G₃] [AddGroup G₄] [AddGroup G₅]
    (f₀ : G₀ →+ G₁) (f₁ : G₁ →+ G₂) (f₂ : G₂ →+ G₃) (f₃ : G₃ →+ G₄) (f₄ : G₄ →+ G₅)
    (f₅ : G₅ →+ G₀) (h₀ : f₅.range = f₀.ker) (h₁ : f₀.range = f₁.ker) (h₂ : f₁.range = f₂.ker)
    (h₃ : f₂.range = f₃.ker) (h₄ : f₃.range = f₄.ker) (h₅ : f₄.range = f₅.ker) :
    Nat.card G₀ * Nat.card G₂ * Nat.card G₄ = Nat.card G₁ * Nat.card G₃ * Nat.card G₅ := by
  rw [card_eq_card_range_mul_card_range _ _ h₀, card_eq_card_range_mul_card_range _ _ h₁,
    card_eq_card_range_mul_card_range _ _ h₂, card_eq_card_range_mul_card_range _ _ h₃,
    card_eq_card_range_mul_card_range _ _ h₄, card_eq_card_range_mul_card_range _ _ h₅]
  ring

end ExactCard

/-! ### The exact hexagon for generic Tate quotients -/

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- A short exact sequence `0 → A → B → C → 0` compatible with pairs of endomorphisms
`(P_A, Q_A)`, `(P_B, Q_B)`, `(P_C, Q_C)`, where `P_B ∘ Q_B = 0 = Q_B ∘ P_B`. -/
structure SES (PA QA : A →+ A) (PB QB : B →+ B) (PC QC : C →+ C) where
  /-- The injection `A → B`. -/
  i : A →+ B
  /-- The surjection `B → C`. -/
  π : B →+ C
  inj : Injective i
  surj : Surjective π
  exact : i.range = π.ker
  iP : ∀ x, i (PA x) = PB (i x)
  iQ : ∀ x, i (QA x) = QB (i x)
  πP : ∀ x, π (PB x) = PC (π x)
  πQ : ∀ x, π (QB x) = QC (π x)
  PQ : ∀ x, PB (QB x) = 0
  QP : ∀ x, QB (PB x) = 0

namespace SES

variable {PA QA : A →+ A} {PB QB : B →+ B} {PC QC : C →+ C}
variable (S : SES PA QA PB QB PC QC)

/-- Exchange the roles of `P` and `Q`. -/
def swap : SES QA PA QB PB QC PC where
  i := S.i
  π := S.π
  inj := S.inj
  surj := S.surj
  exact := S.exact
  iP := S.iQ
  iQ := S.iP
  πP := S.πQ
  πQ := S.πP
  PQ := S.QP
  QP := S.PQ

theorem exists_of_π_eq_zero {b : B} (hb : S.π b = 0) : ∃ a, S.i a = b := by
  have : b ∈ S.i.range := S.exact ▸ hb
  exact this

theorem π_i (a : A) : S.π (S.i a) = 0 := by
  have : S.i a ∈ S.π.ker := S.exact ▸ ⟨a, rfl⟩
  exact this

/-- `Ĥ(A) → Ĥ(B)`. -/
noncomputable def mapA : TateQuot PA QA →+ TateQuot PB QB := TateQuot.map S.i S.iP S.iQ

/-- `Ĥ(B) → Ĥ(C)`. -/
noncomputable def mapB : TateQuot PB QB →+ TateQuot PC QC := TateQuot.map S.π S.πP S.πQ

theorem exists_delta (c : AddMonoidHom.ker PC) :
    ∃ a : AddMonoidHom.ker QA, ∃ b, S.π b = c ∧ S.i a = PB b := by
  obtain ⟨b, hb⟩ := S.surj c
  have h1 : S.π (PB b) = 0 := by rw [S.πP, hb]; exact c.2
  obtain ⟨a, ha⟩ := S.exists_of_π_eq_zero h1
  refine ⟨⟨a, ?_⟩, b, hb, ha⟩
  apply S.inj
  rw [map_zero, S.iQ, ha, S.QP]

/-- The connecting map on representatives. -/
noncomputable def deltaAux (c : AddMonoidHom.ker PC) : TateQuot QA PA :=
  ((S.exists_delta c).choose : TateQuot QA PA)

theorem deltaAux_eq {c : AddMonoidHom.ker PC} (a : AddMonoidHom.ker QA) (b : B)
    (hb : S.π b = c) (ha : S.i a = PB b) : S.deltaAux c = (a : TateQuot QA PA) := by
  obtain ⟨b', hb', ha'⟩ := (S.exists_delta c).choose_spec
  rw [deltaAux, TateQuot.mk_eq_mk_iff]
  obtain ⟨x, hx⟩ := S.exists_of_π_eq_zero (b := b' - b) (by rw [map_sub, hb, hb', sub_self])
  refine ⟨x, S.inj ?_⟩
  rw [S.iP, hx, map_sub, map_sub, ha, ha']

/-- The connecting homomorphism `δ : Ĥ_{(P,Q)}(C) → Ĥ_{(Q,P)}(A)`. -/
noncomputable def delta : TateQuot PC QC →+ TateQuot QA PA :=
  QuotientAddGroup.lift _
    { toFun := S.deltaAux
      map_zero' := by
        rw [S.deltaAux_eq 0 0 (map_zero _) (by simp)]
        rfl
      map_add' := fun c₁ c₂ => by
        obtain ⟨a₁, b₁, hb₁, ha₁⟩ := S.exists_delta c₁
        obtain ⟨a₂, b₂, hb₂, ha₂⟩ := S.exists_delta c₂
        rw [S.deltaAux_eq a₁ b₁ hb₁ ha₁, S.deltaAux_eq a₂ b₂ hb₂ ha₂,
          S.deltaAux_eq (a₁ + a₂) (b₁ + b₂) (by rw [map_add, hb₁, hb₂]; rfl)
            (by rw [AddSubgroup.coe_add, map_add, map_add, ha₁, ha₂])]
        rfl }
    (by
      intro c hc
      rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range] at hc
      obtain ⟨c', hc'⟩ := hc
      obtain ⟨b', rfl⟩ := S.surj c'
      rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        S.deltaAux_eq 0 (QB b') (by rw [S.πQ, hc']) (by simp [S.PQ])]
      rfl)

theorem delta_mk {c : AddMonoidHom.ker PC} (a : AddMonoidHom.ker QA) (b : B)
    (hb : S.π b = c) (ha : S.i a = PB b) : S.delta (c : TateQuot PC QC) = (a : TateQuot QA PA) :=
  S.deltaAux_eq a b hb ha

/-- Exactness at `Ĥ(B)`. -/
theorem exact_mapB : S.mapA.range = S.mapB.ker := by
  ext x
  induction x using QuotientAddGroup.induction_on with | H b => ?_
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker, mapB, TateQuot.map_mk,
    TateQuot.mk_eq_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    induction y using QuotientAddGroup.induction_on with | H a => ?_
    rw [mapA, TateQuot.map_mk, TateQuot.mk_eq_mk_iff] at hy
    obtain ⟨z, hz⟩ := hy
    refine ⟨-S.π z, ?_⟩
    simp [← S.πQ, hz, S.π_i]
  · rintro ⟨c', hc'⟩
    obtain ⟨b', rfl⟩ := S.surj c'
    obtain ⟨a, ha⟩ := S.exists_of_π_eq_zero (b := b - QB b')
      (by rw [map_sub, S.πQ, hc']; exact sub_self _)
    refine ⟨((⟨a, ?_⟩ : AddMonoidHom.ker PA) : TateQuot PA QA), ?_⟩
    · apply S.inj
      rw [map_zero, S.iP, ha, map_sub, S.PQ, AddMonoidHom.mem_ker.1 b.2, sub_zero]
    · rw [mapA, TateQuot.map_mk, TateQuot.mk_eq_mk_iff]
      exact ⟨-b', by simp [ha]⟩

/-- Exactness at `Ĥ(C)`. -/
theorem exact_mapC : S.mapB.range = S.delta.ker := by
  ext x
  induction x using QuotientAddGroup.induction_on with | H c => ?_
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨y, hy⟩
    induction y using QuotientAddGroup.induction_on with | H b => ?_
    rw [← hy, mapB, TateQuot.map_mk, S.delta_mk 0 b rfl (by simp [AddMonoidHom.mem_ker.1 b.2])]
    rfl
  · intro h
    obtain ⟨a, b, hb, ha⟩ := S.exists_delta c
    rw [S.delta_mk a b hb ha, TateQuot.mk_eq_zero_iff] at h
    obtain ⟨a', ha'⟩ := h
    refine ⟨((⟨b - S.i a', ?_⟩ : AddMonoidHom.ker PB) : TateQuot PB QB), ?_⟩
    · rw [AddMonoidHom.mem_ker, map_sub, ← S.iP, ha', ← ha, sub_self]
    · rw [mapB, TateQuot.map_mk]
      congr 1
      ext
      simp [S.π_i, hb]

/-- Exactness at `Ĥ_{(Q,P)}(A)`. -/
theorem exact_delta : S.delta.range = S.swap.mapA.ker := by
  ext x
  induction x using QuotientAddGroup.induction_on with | H a => ?_
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker, mapA, TateQuot.map_mk,
    TateQuot.mk_eq_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    induction y using QuotientAddGroup.induction_on with | H c => ?_
    obtain ⟨a', b, hb, ha'⟩ := S.exists_delta c
    rw [S.delta_mk a' b hb ha', TateQuot.mk_eq_mk_iff] at hy
    obtain ⟨z, hz⟩ := hy
    refine ⟨b - S.i z, ?_⟩
    change PB (b - S.i z) = S.i a
    rw [map_sub, ← S.iP, hz, map_sub, ← ha', sub_sub_cancel]
  · rintro ⟨b, hb⟩
    refine ⟨((⟨S.π b, ?_⟩ : AddMonoidHom.ker PC) : TateQuot PC QC), ?_⟩
    · rw [AddMonoidHom.mem_ker, ← S.πP]
      change S.π (PB b) = 0
      rw [show PB b = S.i a from hb, S.π_i]
    · exact S.delta_mk a b rfl hb.symm

/-- The cardinality identity coming from the exact hexagon. -/
theorem card_mul_card_eq (S : SES PA QA PB QB PC QC) :
    Nat.card (TateQuot PA QA) * Nat.card (TateQuot PC QC) * Nat.card (TateQuot QB PB) =
      Nat.card (TateQuot PB QB) * Nat.card (TateQuot QA PA) * Nat.card (TateQuot QC PC) :=
  card_mul_card_eq_of_hexagon S.mapA S.mapB S.delta S.swap.mapA S.swap.mapB S.swap.delta
    S.swap.exact_delta S.exact_mapB S.exact_mapC S.exact_delta S.swap.exact_mapB
    S.swap.exact_mapC

theorem finite_B (S : SES PA QA PB QB PC QC) [Finite (TateQuot PA QA)] [Finite (TateQuot PC QC)] :
    Finite (TateQuot PB QB) :=
  finite_of_exact S.mapA S.mapB S.exact_mapB

end SES

/-! ### Short exact sequences of cyclic modules -/

section Cyclic

variable {σA : AddMonoid.End A} {σB : AddMonoid.End B} {σC : AddMonoid.End C} {n : ℕ}

/-- The `SES` of generic Tate quotients `(D, N)` attached to a short exact sequence of modules
with compatible endomorphisms. -/
def SES.ofCyclic (hσB : σB ^ n = 1) (i : A →+ B) (π : B →+ C) (hi : Injective i)
    (hπ : Surjective π) (hex : i.range = π.ker) (hiσ : ∀ x, i (σA x) = σB (i x))
    (hπσ : ∀ x, π (σB x) = σC (π x)) :
    SES (D σA) (N σA n) (D σB) (N σB n) (D σC) (N σC n) where
  i := i
  π := π
  inj := hi
  surj := hπ
  exact := hex
  iP := map_D_apply i hiσ
  iQ := map_N_apply i hiσ
  πP := map_D_apply π hπσ
  πQ := map_N_apply π hπσ
  PQ := D_N_apply hσB
  QP := N_D_apply hσB

variable (hσB : σB ^ n = 1) (i : A →+ B) (π : B →+ C) (hi : Injective i) (hπ : Surjective π)
  (hex : i.range = π.ker) (hiσ : ∀ x, i (σA x) = σB (i x)) (hπσ : ∀ x, π (σB x) = σC (π x))
include hσB hi hπ hex hiσ hπσ

/-- For a short exact sequence `0 → A → B → C → 0` of modules with compatible endomorphisms,
`|Ĥ⁰(B)| |Ĥ⁻¹(A)| |Ĥ⁻¹(C)| = |Ĥ⁻¹(B)| |Ĥ⁰(A)| |Ĥ⁰(C)|` (as `Nat.card`s; this is unconditional,
but only meaningful when all groups are finite). -/
theorem card_H0_mul_card_Hm1_eq :
    Nat.card (H0 σB n) * Nat.card (Hm1 σA n) * Nat.card (Hm1 σC n) =
      Nat.card (Hm1 σB n) * Nat.card (H0 σA n) * Nat.card (H0 σC n) := by
  have := (SES.ofCyclic hσB i π hi hπ hex hiσ hπσ).card_mul_card_eq
  simp only [H0, Hm1] at this ⊢
  linarith

theorem finite_H0_of_ses [Finite (H0 σA n)] [Finite (H0 σC n)] : Finite (H0 σB n) :=
  (SES.ofCyclic hσB i π hi hπ hex hiσ hπσ).finite_B

theorem finite_Hm1_of_ses [Finite (Hm1 σA n)] [Finite (Hm1 σC n)] : Finite (Hm1 σB n) :=
  (SES.ofCyclic hσB i π hi hπ hex hiσ hπσ).swap.finite_B

/-- The Herbrand quotient is multiplicative in short exact sequences. -/
theorem herbrand_eq_mul_of_ses [Finite (H0 σA n)] [Finite (Hm1 σA n)] [Finite (H0 σC n)]
    [Finite (Hm1 σC n)] : herbrand σB n = herbrand σA n * herbrand σC n := by
  have := finite_Hm1_of_ses hσB i π hi hπ hex hiσ hπσ
  have key := card_H0_mul_card_Hm1_eq hσB i π hi hπ hex hiσ hπσ
  have h1 : (Nat.card (Hm1 σA n) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h2 : (Nat.card (Hm1 σB n) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h3 : (Nat.card (Hm1 σC n) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [herbrand, herbrand, herbrand, div_mul_div_comm, div_eq_div_iff h2 (mul_ne_zero h1 h3)]
  exact_mod_cast (by linarith [key] : _)

end Cyclic

/-! ### Subgroups of finite index -/

section FiniteIndex

variable {M : Type*} [AddCommGroup M] {σ : AddMonoid.End M} {n : ℕ}
variable (hσ : σ ^ n = 1) (A : AddSubgroup M) (hA : ∀ x ∈ A, σ x ∈ A)

theorem range_subtype_eq_ker_mk' : A.subtype.range = (QuotientAddGroup.mk' A).ker := by
  rw [AddSubgroup.range_subtype, QuotientAddGroup.ker_mk']

include hσ

theorem finite_H0_of_finite_quotient [Finite (M ⧸ A)] [Finite (H0 (restrict σ A hA) n)] :
    Finite (H0 σ n) :=
  finite_H0_of_ses hσ A.subtype (QuotientAddGroup.mk' A) Subtype.val_injective
    (QuotientAddGroup.mk'_surjective A) (range_subtype_eq_ker_mk' A)
    (σA := restrict σ A hA) (σC := quotientEnd σ A hA) (fun _ => rfl) (fun _ => rfl)

theorem finite_Hm1_of_finite_quotient [Finite (M ⧸ A)] [Finite (Hm1 (restrict σ A hA) n)] :
    Finite (Hm1 σ n) :=
  finite_Hm1_of_ses hσ A.subtype (QuotientAddGroup.mk' A) Subtype.val_injective
    (QuotientAddGroup.mk'_surjective A) (range_subtype_eq_ker_mk' A)
    (σA := restrict σ A hA) (σC := quotientEnd σ A hA) (fun _ => rfl) (fun _ => rfl)

/-- Passing to a `σ`-stable subgroup of finite index does not change the Herbrand quotient. -/
theorem herbrand_eq_of_finite_quotient [Finite (M ⧸ A)] [Finite (H0 (restrict σ A hA) n)]
    [Finite (Hm1 (restrict σ A hA) n)] : herbrand σ n = herbrand (restrict σ A hA) n := by
  rw [herbrand_eq_mul_of_ses hσ A.subtype (QuotientAddGroup.mk' A) Subtype.val_injective
    (QuotientAddGroup.mk'_surjective A) (range_subtype_eq_ker_mk' A)
    (σA := restrict σ A hA) (σC := quotientEnd σ A hA) (fun _ => rfl) (fun _ => rfl),
    herbrand_eq_one_of_finite (quotientEnd_pow_eq_one hA hσ), mul_one]

end FiniteIndex

end Herbrand
