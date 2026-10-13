/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# The profinite integers `Ẑ` and the homomorphisms `a ↦ g ^ a`

`Ẑ = lim_n ℤ/n` (`Brauer.ZHat`) is realised as the compatible families in `∏_{n > 0} ℤ/n`
(along the reductions `ℤ/m → ℤ/n` for `n ∣ m`), with the subspace topology of the product of the
discrete groups `ℤ/n`.

* `Brauer.intToZHat : ℤ →+ Ẑ` is injective (`Brauer.intToZHat_injective`) and has dense image
  (`Brauer.denseRange_intToZHat`); `Ẑ` is compact (`Brauer.ZHat.compactSpace`).
* For a profinite group `G` (compact, totally disconnected topological group) and `g ∈ G`,
  `Brauer.zhatPow g : Multiplicative Ẑ →ₜ* G` is the continuous homomorphism with
  `zhatPow g k = g ^ k` for `k ∈ ℤ` (`Brauer.zhatPow_intToZHat`). In the finite quotient
  `G ⧸ U` (`U` open normal) it is `a ↦ g ^ (a mod |G ⧸ U|)` (`Brauer.zhatPow_mk`), and it is
  the unique such continuous homomorphism (`Brauer.eq_zhatPow`).
* `Brauer.zhatPow_mem_iff`: if `U` is an open normal subgroup with `g ^ k ∈ U ↔ m ∣ k`, then
  `zhatPow g a ∈ U ↔ a ≡ 0 (mod m)`.
* `Brauer.zhatPow_pow_inv_mul_mem`: in the same situation, `g ^ a ≡ g ^ (a mod m)` modulo `U`.
* `Brauer.zhatPow_surjective`: if the powers of `g` are dense (`g` is a topological generator),
  `zhatPow g` is surjective.
-/

set_option linter.unusedSectionVars false

open CategoryTheory

namespace Brauer

/-- The profinite integers `Ẑ = lim_n ℤ/n`, as compatible families in `∏_{n > 0} ℤ/n`. -/
def ZHat : AddSubgroup (∀ n : ℕ+, ZMod n) where
  carrier := {x | ∀ n m : ℕ+, ∀ h : (n : ℕ) ∣ m, ZMod.castHom h (ZMod n) (x m) = x n}
  add_mem' hx hy n m h := by rw [Pi.add_apply, Pi.add_apply, map_add, hx n m h, hy n m h]
  zero_mem' n m h := by simp
  neg_mem' hx n m h := by rw [Pi.neg_apply, Pi.neg_apply, map_neg, hx n m h]

/-- The canonical map `ℤ → Ẑ`. -/
def intToZHat : ℤ →+ ZHat :=
  (AddMonoidHom.pi fun n : ℕ+ => (Int.castAddHom (ZMod n))).codRestrict _
    fun k n m h => by simp

theorem intToZHat_injective : Function.Injective intToZHat := by
  rw [injective_iff_map_eq_zero]
  intro k hk
  have h : ((k : ZMod (k.natAbs + 1))) = 0 :=
    congrArg (fun x : ZHat => (x : ∀ n : ℕ+, ZMod n) (⟨k.natAbs + 1, by omega⟩ : ℕ+)) hk
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  push_cast at h
  exact Int.eq_zero_of_abs_lt_dvd h (by rw [Int.abs_eq_natAbs]; omega)

@[simp]
theorem intToZHat_apply (k : ℤ) (n : ℕ+) : (intToZHat k : ∀ n : ℕ+, ZMod n) n = k := rfl

theorem ZHat.castHom_apply (a : ZHat) {n m : ℕ+} (h : (n : ℕ) ∣ m) :
    ZMod.castHom h (ZMod n) ((a : ∀ n : ℕ+, ZMod n) m) = (a : ∀ n : ℕ+, ZMod n) n :=
  a.2 n m h

theorem ZHat.ext {a b : ZHat}
    (h : ∀ n : ℕ+, (a : ∀ n : ℕ+, ZMod n) n = (b : ∀ n : ℕ+, ZMod n) n) : a = b :=
  Subtype.ext (funext h)

/-! ### Topology -/

theorem isClosed_ZHat : IsClosed (ZHat : Set (∀ n : ℕ+, ZMod n)) := by
  have : (ZHat : Set (∀ n : ℕ+, ZMod n)) = ⋂ n : ℕ+, ⋂ m : ℕ+, ⋂ h : (n : ℕ) ∣ m,
      {x | ZMod.castHom h (ZMod n) (x m) = x n} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [this]
  exact isClosed_iInter fun n ↦ isClosed_iInter fun m ↦ isClosed_iInter fun h ↦
    isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply m)) (continuous_apply n)

instance ZHat.compactSpace : CompactSpace ZHat :=
  isCompact_iff_compactSpace.1 isClosed_ZHat.isCompact

theorem continuous_ZHat_apply (n : ℕ+) : Continuous fun a : ZHat ↦ (a : ∀ n : ℕ+, ZMod n) n :=
  (continuous_apply n).comp continuous_subtype_val

/-- `ℤ` is dense in `Ẑ`. -/
theorem denseRange_intToZHat : DenseRange intToZHat := by
  refine dense_iff_inter_open.2 fun U hU ⟨a, ha⟩ ↦ ?_
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.1 hU
  obtain ⟨I, u, hu, hIV⟩ := isOpen_pi_iff.1 hV _ ha
  set N : ℕ+ := ⟨∏ i ∈ I, (i : ℕ), Finset.prod_pos fun i _ ↦ i.pos⟩
  refine ⟨intToZHat ((a : ∀ n : ℕ+, ZMod n) N).val, hIV fun i hi ↦ ?_, ⟨_, rfl⟩⟩
  have hiN : (i : ℕ) ∣ N := Finset.dvd_prod_of_mem (fun i : ℕ+ ↦ (i : ℕ)) hi
  change ((((a : ∀ n : ℕ+, ZMod n) N).val : ℤ) : ZMod i) ∈ u i
  have h := ZHat.castHom_apply a hiN
  rw [ZMod.castHom_apply] at h
  rw [Int.cast_natCast, ZMod.natCast_val, h]
  exact (hu i hi).2

theorem denseRange_ofAdd_intToZHat :
    DenseRange fun k : ℤ ↦ Multiplicative.ofAdd (intToZHat k) :=
  DenseRange.comp (Multiplicative.ofAdd.surjective.denseRange) denseRange_intToZHat
    continuous_ofAdd

/-! ### Powers in finite groups -/

theorem pow_eq_pow_mod {Q : Type*} [Monoid Q] {x : Q} {N : ℕ} (hx : x ^ N = 1) (k : ℕ) :
    x ^ (k % N) = x ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k N, pow_add, pow_mul, hx, one_pow, mul_one]

theorem pow_val_castHom {Q : Type*} [Monoid Q] {x : Q} {N M : ℕ} [NeZero N] [NeZero M]
    (hx : x ^ N = 1) (h : N ∣ M) (y : ZMod M) :
    x ^ (ZMod.castHom h (ZMod N) y).val = x ^ y.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast, pow_eq_pow_mod hx]

theorem pow_val_intCast {Q : Type*} [Group Q] {x : Q} {N : ℕ} [NeZero N] (hx : x ^ N = 1)
    (k : ℤ) : x ^ (k : ZMod N).val = x ^ k := by
  rw [← zpow_natCast, ZMod.val_intCast]
  conv_rhs => rw [← Int.emod_add_mul_ediv k N, zpow_add, zpow_mul, zpow_natCast, hx, one_zpow,
    mul_one]

theorem pow_val_add {Q : Type*} [Monoid Q] {x : Q} {N : ℕ} [NeZero N] (hx : x ^ N = 1)
    (a b : ZMod N) : x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, pow_eq_pow_mod hx, pow_add]

/-! ### The homomorphism `a ↦ g ^ a` -/

section ZHatPow

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- `|G ⧸ U|` for an open normal subgroup `U`, as a positive integer. -/
noncomputable def quotCard (U : OpenNormalSubgroup G) : ℕ+ :=
  ⟨Nat.card (G ⧸ U.toSubgroup), Nat.card_pos⟩

theorem mk_pow_quotCard (U : OpenNormalSubgroup G) (x : G ⧸ U.toSubgroup) :
    x ^ (quotCard U : ℕ) = 1 :=
  pow_card_eq_one'

/-- The image of `g ^ a` in `G ⧸ U`: `g ^ (a mod |G ⧸ U|)`. -/
noncomputable def powComp (g : G) (U : OpenNormalSubgroup G) (a : ZHat) : G ⧸ U.toSubgroup :=
  (QuotientGroup.mk g : G ⧸ U.toSubgroup) ^ ((a : ∀ n : ℕ+, ZMod n) (quotCard U)).val

theorem powComp_eq_of_dvd (g : G) (U : OpenNormalSubgroup G) (a : ZHat) {n : ℕ+}
    (hn : (quotCard U : ℕ) ∣ n) :
    powComp g U a = (QuotientGroup.mk g : G ⧸ U.toSubgroup) ^ ((a : ∀ n : ℕ+, ZMod n) n).val := by
  rw [powComp, ← ZHat.castHom_apply a hn, pow_val_castHom (mk_pow_quotCard U _) hn]

theorem powComp_add (g : G) (U : OpenNormalSubgroup G) (a b : ZHat) :
    powComp g U (a + b) = powComp g U a * powComp g U b :=
  pow_val_add (mk_pow_quotCard U _) _ _

theorem powComp_map (g : G) {U V : OpenNormalSubgroup G} (h : U ≤ V) (a : ZHat) :
    QuotientGroup.map _ _ (MonoidHom.id G) h (powComp g U a) = powComp g V a := by
  have hdvd : (quotCard V : ℕ) ∣ quotCard U :=
    Subgroup.index_dvd_of_le (H := U.toSubgroup) (K := V.toSubgroup) h
  rw [powComp, map_pow, powComp_eq_of_dvd g V a hdvd]
  rfl

/-- The family `(g ^ a mod U)_U` as a point of the limit of the finite quotients of `G`. -/
noncomputable def toLim (g : G) (a : ZHat) :
    ProfiniteGrp.limit (ProfiniteGrp.diagram (ProfiniteGrp.of G)) :=
  ⟨fun U ↦ powComp g U a, fun _ _ π ↦ powComp_map g (leOfHom π) a⟩

theorem continuous_toLim (g : G) : Continuous (toLim g) := by
  refine continuous_induced_rng.2 (continuous_pi fun U ↦ ?_)
  rw [continuous_def]
  intro s _
  exact (continuous_ZHat_apply (quotCard U)).isOpen_preimage
    ((fun y : ZMod (quotCard U) ↦ (QuotientGroup.mk g : G ⧸ U.toSubgroup) ^ y.val) ⁻¹' s)
    (isOpen_discrete _)

/-- `G` is the limit of its finite quotients. -/
noncomputable def limEquiv :
    G ≃ₜ* ProfiniteGrp.limit (ProfiniteGrp.diagram (ProfiniteGrp.of G)) :=
  ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor (ProfiniteGrp.of G)

theorem limEquiv_val (x : G) (U : OpenNormalSubgroup G) :
    ((limEquiv x).val U : G ⧸ U.toSubgroup) = QuotientGroup.mk x := rfl

/-- Elements of a profinite group are determined by their images in the finite quotients. -/
theorem eq_of_forall_mk_eq {x y : G}
    (h : ∀ U : OpenNormalSubgroup G,
      (QuotientGroup.mk x : G ⧸ U.toSubgroup) = QuotientGroup.mk y) : x = y :=
  limEquiv.injective (Subtype.ext (funext h))

/-- **The continuous homomorphism `Ẑ → G`, `a ↦ g ^ a`.** -/
noncomputable def zhatPow (g : G) : Multiplicative ZHat →ₜ* G where
  toFun a := limEquiv.symm (toLim g a.toAdd)
  map_one' := by
    change limEquiv.symm (toLim g 0) = 1
    rw [← map_one limEquiv.symm]
    congr 1
    refine Subtype.ext (funext fun U ↦ ?_)
    change (QuotientGroup.mk g : G ⧸ U.toSubgroup) ^ ((0 : ∀ n : ℕ+, ZMod n) _).val = 1
    simp
  map_mul' a b := by
    rw [← map_mul limEquiv.symm]
    congr 1
    exact Subtype.ext (funext fun U ↦ powComp_add g U a.toAdd b.toAdd)
  continuous_toFun := limEquiv.symm.continuous.comp ((continuous_toLim g).comp continuous_toAdd)

theorem zhatPow_mk (g : G) (U : OpenNormalSubgroup G) (a : Multiplicative ZHat) :
    (QuotientGroup.mk (zhatPow g a) : G ⧸ U.toSubgroup) = powComp g U a.toAdd := by
  rw [← limEquiv_val]
  change (limEquiv (limEquiv.symm (toLim g a.toAdd))).val U = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  rfl

/-- `zhatPow g` extends `k ↦ g ^ k`. -/
theorem zhatPow_intToZHat (g : G) (k : ℤ) :
    zhatPow g (Multiplicative.ofAdd (intToZHat k)) = g ^ k := by
  refine eq_of_forall_mk_eq fun U ↦ ?_
  rw [zhatPow_mk, powComp, toAdd_ofAdd, intToZHat_apply, QuotientGroup.mk_zpow,
    pow_val_intCast (mk_pow_quotCard U _)]

theorem zhatPow_one (g : G) : zhatPow g (Multiplicative.ofAdd (intToZHat 1)) = g := by
  rw [zhatPow_intToZHat, zpow_one]

/-- **Uniqueness**: a continuous homomorphism `Ẑ → G` sending `1` to `g` is `zhatPow g`. -/
theorem eq_zhatPow (g : G) (f : Multiplicative ZHat →ₜ* G)
    (hf : f (Multiplicative.ofAdd (intToZHat 1)) = g) : f = zhatPow g := by
  have h := denseRange_ofAdd_intToZHat.equalizer f.continuous (zhatPow g).continuous
    (funext fun k ↦ by
      change f (Multiplicative.ofAdd (intToZHat k)) = zhatPow g (Multiplicative.ofAdd _)
      rw [zhatPow_intToZHat, ← hf, ← map_zpow, ← ofAdd_zsmul, ← map_zsmul, zsmul_one]
      rfl)
  exact ContinuousMonoidHom.ext (congrFun h)

/-- If `g ^ k ∈ U ↔ m ∣ k` for an open normal subgroup `U`, then `g ^ a ∈ U ↔ a ≡ 0 (mod m)`. -/
theorem zhatPow_mem_iff (g : G) (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.Normal]
    {m : ℕ+} (hm : ∀ k : ℕ, g ^ k ∈ U ↔ (m : ℕ) ∣ k) (a : Multiplicative ZHat) :
    zhatPow g a ∈ U ↔ (a.toAdd : ∀ n : ℕ+, ZMod n) m = 0 := by
  let U' : OpenNormalSubgroup G := { toSubgroup := U, isOpen' := hU }
  have hmN : (m : ℕ) ∣ quotCard U' := (hm _).1 (by
    rw [← QuotientGroup.eq_one_iff (N := U), QuotientGroup.mk_pow]
    exact mk_pow_quotCard U' _)
  change zhatPow g a ∈ U'.toSubgroup ↔ _
  rw [← QuotientGroup.eq_one_iff, zhatPow_mk, powComp, ← QuotientGroup.mk_pow,
    QuotientGroup.eq_one_iff, ← ZHat.castHom_apply a.toAdd hmN, ZMod.castHom_apply,
    ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff]
  exact hm _

/-- `g ^ a ≡ g ^ (a mod m)` modulo an open normal subgroup `U` with `g ^ k ∈ U ↔ m ∣ k`. -/
theorem zhatPow_pow_inv_mul_mem (g : G) (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.Normal]
    {m : ℕ+} (hm : ∀ k : ℕ, g ^ k ∈ U ↔ (m : ℕ) ∣ k) (a : Multiplicative ZHat) :
    (g ^ ((a.toAdd : ∀ n : ℕ+, ZMod n) m).val)⁻¹ * zhatPow g a ∈ U := by
  set j := ((a.toAdd : ∀ n : ℕ+, ZMod n) m).val
  have h : (g ^ j)⁻¹ = zhatPow g (Multiplicative.ofAdd (intToZHat (-(j : ℤ)))) := by
    rw [zhatPow_intToZHat, zpow_neg, zpow_natCast]
  rw [h, ← map_mul, zhatPow_mem_iff g U hU hm]
  change ((-(j : ℤ) : ℤ) : ZMod m) + (a.toAdd : ∀ n : ℕ+, ZMod n) m = 0
  rw [Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val, neg_add_cancel]

/-- If `g` is a topological generator (its powers are dense), `zhatPow g` is surjective. -/
theorem zhatPow_surjective [T2Space G] (g : G) (hg : Dense (Subgroup.zpowers g : Set G)) :
    Function.Surjective (zhatPow g) := by
  have hcl : IsClosed (Set.range (zhatPow g)) :=
    (isCompact_range (zhatPow g).continuous).isClosed
  have hsub : (Subgroup.zpowers g : Set G) ⊆ Set.range (zhatPow g) := by
    rintro _ ⟨k, rfl⟩
    exact ⟨_, zhatPow_intToZHat g k⟩
  intro x
  have h := closure_mono hsub (hg x)
  rwa [hcl.closure_eq] at h

end ZHatPow

end Brauer
