/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import ContinuousKummerTheory.Kummer.PAdic

/-!
# The index of `n`-th powers: `[Kˣ : (Kˣ)ⁿ] = n · #μ_n(K) · #(𝒪/n𝒪)`

Let `R` be a complete discrete valuation ring with finite residue field and fraction field `K`, and
let `n ≠ 0` in `R`. We compute the index of the `n`-th powers exactly:

* `PowIndex.index_range_pow_units`: `[Rˣ : (Rˣ)ⁿ] = #(R/nR) · #μ_n(R)`;
* `PowIndex.index_range_pow_field`: `[Kˣ : (Kˣ)ⁿ] = n · #(R/nR) · #μ_n(K)`.

The proof is the classical "Herbrand quotient" argument for the endomorphism `x ↦ xⁿ`:

* `PowIndex.index_range_pow_mul_card`: for a commutative group `A` and a subgroup `H` of finite
  index, `[A : Aⁿ] · #H[n] = [H : Hⁿ] · #A[n]` (pure group theory);
* for `d ∈ 𝔪` the `n`-th power map sends the congruence subgroup `1 + n d R`
  (`PowIndex.onePlus`) **onto** `1 + n² d R` (`PowIndex.map_pow_onePlus`): one inclusion is the
  binomial identity `(1 + n d y)ⁿ = 1 + n² d (y + Q(y))` (`KummerTheory.one_add_pow_eq`), the other
  the `𝔪`-adic fixed point argument of `KummerTheory.exists_pow_eq_one_add`;
* `[1 + c R : 1 + c d R] = #(R/dR)` whenever `d ∣ c`, via `1 + c a ↦ a mod d`
  (`PowIndex.relIndex_onePlus`);
* `1 + n ϖ^j R` contains no non-trivial `n`-th root of unity for `j` large (Krull intersection).

With `H = 1 + n ϖ^j R` this gives `[Rˣ : (Rˣ)ⁿ] = [H : Hⁿ] · #μ_n = #(R/nR) · #μ_n`, and
`Kˣ ≅ Rˣ × ℤ` (`PowIndex.unitsProdEquiv`) contributes the factor `n`.
-/

open IsLocalRing

set_option linter.unusedSectionVars false

namespace PowIndex

/-! ### A group-theoretic lemma -/

/-- **`[A : Aⁿ] · #(H[n]) = [H : Hⁿ] · #(A[n])`** for a subgroup `H` of finite index of a
commutative group `A` (with the convention `Nat.card = 0` for infinite sets). -/
theorem index_range_pow_mul_card {A : Type*} [CommGroup A] (n : ℕ) (H : Subgroup A)
    (hH : H.index ≠ 0) :
    (powMonoidHom n : A →* A).range.index * Nat.card ↥((powMonoidHom n : A →* A).ker ⊓ H) =
      (H.map (powMonoidHom n : A →* A)).relIndex H * Nat.card (powMonoidHom n : A →* A).ker := by
  set f : A →* A := powMonoidHom n with hf
  have hle : H.map f ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    exact H.pow_mem hy n
  have h1 := H.index_map f
  have h2 := Subgroup.relIndex_mul_index hle
  have h4 := Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ f.ker)
  rw [Subgroup.relIndex_sup_left] at h4
  have h5 := Subgroup.relIndex_mul_relIndex ⊥ (f.ker ⊓ H) f.ker bot_le inf_le_left
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, Subgroup.inf_relIndex_left] at h5
  have ha : (H ⊔ f.ker).index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h4
    exact hH h4.symm
  have hr : f.range.index = (H.map f).relIndex H * H.relIndex f.ker := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha)
    rw [← h1, ← h2, ← h4]
    ring
  rw [hr, ← h5]
  ring

/-! ### Congruence subgroups `1 + c R` -/

section Local

variable {R : Type*} [CommRing R]

/-- The congruence subgroup `1 + c R` of `Rˣ`. -/
def onePlus (c : R) : Subgroup Rˣ where
  carrier := {u | ∃ a : R, (u : R) = 1 + c * a}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro u w ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b + c * a * b, by rw [Units.val_mul, ha, hb]; ring⟩
  inv_mem' := by
    rintro u ⟨a, ha⟩
    refine ⟨-(a * ↑u⁻¹), ?_⟩
    have h : (u : R) * ↑u⁻¹ = 1 := u.mul_inv
    rw [ha] at h
    linear_combination h

theorem mem_onePlus {c : R} {u : Rˣ} : u ∈ onePlus c ↔ ∃ a : R, (u : R) = 1 + c * a := Iff.rfl

theorem onePlus_congr {c c' : R} (h : c = c') : onePlus c = onePlus c' := by rw [h]

/-- `1 + c R` is the kernel of `Rˣ → (R/cR)ˣ`. -/
theorem onePlus_eq_ker (c : R) :
    onePlus c = (Units.map (Ideal.Quotient.mk (Ideal.span {c}) : R →* R ⧸ Ideal.span {c})).ker := by
  ext u
  rw [mem_onePlus, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
    MonoidHom.coe_coe, ← map_one (Ideal.Quotient.mk (Ideal.span {c})), Ideal.Quotient.eq,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [ha]; ring⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by linear_combination -ha⟩

theorem index_onePlus_ne_zero (c : R) [Finite (R ⧸ Ideal.span {c})] : (onePlus c).index ≠ 0 := by
  rw [onePlus_eq_ker, Subgroup.index_ker]
  exact Nat.card_pos.ne'

variable [IsLocalRing R]

theorem isUnit_one_add_mul {c : R} (hc : c ∈ maximalIdeal R) (a : R) : IsUnit (1 + c * a) := by
  have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(c * a))
    ((IsLocalRing.mem_maximalIdeal _).1 (neg_mem (Ideal.mul_mem_right a _ hc)))
  rwa [sub_neg_eq_add] at this

/-! ### `n`-th powers of `1 + n d R` -/

/-- The fixed-point form of the Hensel lemma for `n`-th powers, with the root in `1 + n d R`
(the argument of `KummerTheory.exists_pow_eq_one_add`). -/
theorem exists_pow_eq_one_add' [IsAdicComplete (maximalIdeal R) R] (m : ℕ) {d : R}
    (hd : d ∈ maximalIdeal R) (w : R) :
    ∃ y : R, (1 + ((m + 1 : ℕ) : R) * d * y) ^ (m + 1) =
      1 + ((m + 1 : ℕ) : R) ^ 2 * d * w := by
  obtain ⟨y, hy⟩ := KummerTheory.exists_fixedPoint_of_adicContraction (maximalIdeal R)
    (fun y => w - KummerTheory.powCorr m d y)
    (fun y y' => by
      refine ⟨-∑ k ∈ Finset.range m, ((m + 1).choose (k + 2) : R) * ((m + 1 : ℕ) : R) ^ k *
        d ^ (k + 1) * ∑ i ∈ Finset.range (k + 2), y ^ i * y' ^ (k + 2 - 1 - i), ?_, ?_⟩
      · refine neg_mem (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_)
        exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hd _ k.succ_pos)
      · simp only [KummerTheory.powCorr, sub_sub_sub_cancel_left, neg_mul, Finset.sum_mul,
          ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_assoc _ (∑ i ∈ _, _), geom_sum₂_mul]
        ring)
  refine ⟨y, ?_⟩
  rw [KummerTheory.one_add_pow_eq, show y + KummerTheory.powCorr m d y = w by
    linear_combination -hy]

/-- **The `n`-th power map sends `1 + n d R` onto `1 + n² d R`** (`d ∈ 𝔪`, `n ≥ 1`). -/
theorem map_pow_onePlus [IsAdicComplete (maximalIdeal R) R] (m : ℕ) {d : R}
    (hd : d ∈ maximalIdeal R) :
    (onePlus (((m + 1 : ℕ) : R) * d)).map (powMonoidHom (m + 1) : Rˣ →* Rˣ) =
      onePlus (((m + 1 : ℕ) : R) ^ 2 * d) := by
  ext w
  constructor
  · rintro ⟨u, ⟨a, ha⟩, rfl⟩
    refine ⟨a + KummerTheory.powCorr m d a, ?_⟩
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, ha, KummerTheory.one_add_pow_eq]
  · rintro ⟨b, hb⟩
    obtain ⟨y, hy⟩ := exists_pow_eq_one_add' m hd b
    have hu : IsUnit (1 + ((m + 1 : ℕ) : R) * d * y) :=
      isUnit_one_add_mul (Ideal.mul_mem_left _ _ hd) _
    refine ⟨hu.unit, ⟨y, by rw [IsUnit.unit_spec]⟩, ?_⟩
    apply Units.ext
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, IsUnit.unit_spec, hy, hb, mul_assoc]

/-! ### The index `[1 + c R : 1 + c d R]` -/

variable [IsDomain R]

theorem coeff_unique {c : R} (hc : c ≠ 0) {a b : R} (h : 1 + c * a = 1 + c * b) : a = b :=
  mul_left_cancel₀ hc (add_left_cancel h)

/-- The coefficient `a` of `u = 1 + c a ∈ 1 + c R`. -/
noncomputable def coeff (c : R) (u : onePlus c) : R := Classical.choose u.2

theorem coeff_spec (c : R) (u : onePlus c) : ((u : Rˣ) : R) = 1 + c * coeff c u :=
  Classical.choose_spec u.2

theorem coeff_eq {c : R} (hc : c ≠ 0) (u : onePlus c) {a : R} (h : ((u : Rˣ) : R) = 1 + c * a) :
    coeff c u = a :=
  coeff_unique hc ((coeff_spec c u).symm.trans h)

/-- `1 + c a ↦ a mod d`, a homomorphism `1 + c R → R/dR` when `d ∣ c`. -/
noncomputable def coeffHom {c d : R} (hc : c ≠ 0) (hdc : d ∣ c) :
    onePlus c →* Multiplicative (R ⧸ Ideal.span {d}) where
  toFun u := Multiplicative.ofAdd (Ideal.Quotient.mk _ (coeff c u))
  map_one' := by
    rw [coeff_eq hc 1 (a := 0) (by simp)]
    simp
  map_mul' u w := by
    rw [coeff_eq hc (u * w) (a := coeff c u + coeff c w + c * coeff c u * coeff c w)
      (by rw [Subgroup.coe_mul, Units.val_mul, coeff_spec, coeff_spec]; ring), ← ofAdd_add,
      ← map_add]
    congr 1
    rw [Ideal.Quotient.eq]
    obtain ⟨e, rfl⟩ := hdc
    exact Ideal.mem_span_singleton'.2 ⟨e * coeff (d * e) u * coeff (d * e) w, by ring⟩

theorem coeffHom_surjective {c d : R} (hc : c ≠ 0) (hdc : d ∣ c) (hcm : c ∈ maximalIdeal R) :
    Function.Surjective (coeffHom hc hdc) := by
  intro x
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (Multiplicative.toAdd x)
  refine ⟨⟨(isUnit_one_add_mul hcm a).unit, a, by rw [IsUnit.unit_spec]⟩, ?_⟩
  change Multiplicative.ofAdd (Ideal.Quotient.mk _ (coeff c _)) = x
  rw [coeff_eq hc _ (a := a) (by rw [IsUnit.unit_spec]), ha, ofAdd_toAdd]

theorem ker_coeffHom {c d : R} (hc : c ≠ 0) (hdc : d ∣ c) :
    (coeffHom hc hdc).ker = (onePlus (c * d)).subgroupOf (onePlus c) := by
  ext u
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_onePlus]
  change Multiplicative.ofAdd (Ideal.Quotient.mk _ (coeff c u)) = 1 ↔ _
  rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by rw [coeff_spec, ← hb]; ring⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, by rw [coeff_eq hc u (a := d * b) (by rw [hb]; ring)]; ring⟩

/-- **`[1 + c R : 1 + c d R] = #(R/dR)`** for `0 ≠ c ∈ 𝔪` and `d ∣ c`. -/
theorem relIndex_onePlus {c d : R} (hc : c ≠ 0) (hdc : d ∣ c) (hcm : c ∈ maximalIdeal R) :
    (onePlus (c * d)).relIndex (onePlus c) = Nat.card (R ⧸ Ideal.span {d}) := by
  rw [Subgroup.relIndex, ← ker_coeffHom hc hdc, Subgroup.index_ker,
    MonoidHom.range_eq_top_of_surjective _ (coeffHom_surjective hc hdc hcm),
    Subgroup.card_top]
  rfl

end Local

/-! ### Discrete valuation rings -/

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Finite (ResidueField R)]

theorem finite_quotient_span {c : R} (hc : c ≠ 0) : Finite (R ⧸ Ideal.span {c}) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [IsLocalRing.finite_quotient_iff]
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {c}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) hϖ
  exact ⟨k, by rw [hk, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩

/-- For `j` large, `1 + ϖ^j R` contains no non-trivial `n`-th root of unity. -/
theorem exists_onePlus_inf_ker (n : ℕ) [NeZero n] {t : R} (ht : t ∈ maximalIdeal R) :
    ∃ j : ℕ, ∀ u ∈ onePlus (t ^ j), u ^ n = 1 → u = 1 := by
  classical
  haveI : Fintype (rootsOfUnity n R) := Fintype.ofFinite _
  have hk : ∀ ζ : rootsOfUnity n R, ∃ k : ℕ, ζ ≠ 1 → ((ζ : Rˣ) : R) - 1 ∉ maximalIdeal R ^ k := by
    intro ζ
    by_cases h1 : ζ = 1
    · exact ⟨0, fun h => (h h1).elim⟩
    by_contra hcon
    have hcon' : ∀ k, ((ζ : Rˣ) : R) - 1 ∈ maximalIdeal R ^ k := fun k => by
      by_contra h
      exact hcon ⟨k, fun _ => h⟩
    apply h1
    have h0 : ((ζ : Rˣ) : R) - 1 = 0 := by
      refine IsHausdorff.haus' (I := maximalIdeal R) _ fun k => ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      exact hcon' k
    exact Subtype.ext (Units.ext (sub_eq_zero.1 h0))
  choose k hk using hk
  refine ⟨Finset.univ.sup k, fun u hu hun => ?_⟩
  by_contra hu1
  set ζ : rootsOfUnity n R := ⟨u, (mem_rootsOfUnity n u).2 hun⟩
  have hζ : ζ ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  apply hk ζ hζ
  obtain ⟨a, ha⟩ := hu
  change (u : R) - 1 ∈ _
  rw [ha, add_sub_cancel_left]
  refine Ideal.mul_mem_right _ _ ?_
  exact Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ ζ)) (Ideal.pow_mem_pow ht _)

/-- **`[Rˣ : (Rˣ)ⁿ] = #(R/nR) · #μ_n(R)`** for a complete discrete valuation ring `R` with finite
residue field and `n ≠ 0` in `R`. -/
theorem index_range_pow_units (n : ℕ) (hn : (n : R) ≠ 0) :
    (powMonoidHom n : Rˣ →* Rˣ).range.index =
      Nat.card (R ⧸ Ideal.span {(n : R)}) * Nat.card (powMonoidHom n : Rˣ →* Rˣ).ker := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖm : ϖ ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  haveI : NeZero (m + 1) := ⟨hn0⟩
  obtain ⟨j, hj⟩ := exists_onePlus_inf_ker (R := R) (m + 1) hϖm
  set N : R := ((m + 1 : ℕ) : R)
  set c : R := N * ϖ ^ (j + 1) with hc_def
  have hc : c ≠ 0 := mul_ne_zero hn (pow_ne_zero _ hϖ.ne_zero)
  have hcm : c ∈ maximalIdeal R := Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hϖm _ j.succ_pos)
  haveI := finite_quotient_span hc
  have key := index_range_pow_mul_card (m + 1) (onePlus c) (index_onePlus_ne_zero c)
  have hbot : (powMonoidHom (m + 1) : Rˣ →* Rˣ).ker ⊓ onePlus c = ⊥ := by
    rw [eq_bot_iff]
    rintro u ⟨hu1, hu2⟩
    rw [Subgroup.mem_bot]
    refine hj u ?_ hu1
    obtain ⟨a, ha⟩ := hu2
    exact ⟨N * ϖ * a, by rw [ha, hc_def, pow_succ]; ring⟩
  have hmap : (onePlus c).map (powMonoidHom (m + 1) : Rˣ →* Rˣ) = onePlus (c * N) := by
    rw [hc_def, map_pow_onePlus m (Ideal.pow_mem_of_mem _ hϖm _ j.succ_pos)]
    exact onePlus_congr (by simp only [N, Nat.succ_eq_add_one]; push_cast; ring)
  rw [hbot, Subgroup.card_bot, mul_one, hmap,
    relIndex_onePlus hc (Dvd.intro _ rfl) hcm] at key
  exact key

end DVR

/-! ### The fraction field: `Kˣ ≅ Rˣ × ℤ` -/

section Field

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

theorem algebraMap_ne_zero {ϖ : R} (hϖ : Irreducible ϖ) : algebraMap R K ϖ ≠ 0 := by
  simpa using (IsFractionRing.injective R K).ne hϖ.ne_zero

/-- `(u, k) ↦ u ϖ^k`. -/
noncomputable def unitsProdHom {ϖ : R} (hϖ : Irreducible ϖ) : Rˣ × Multiplicative ℤ →* Kˣ :=
  (Units.map (algebraMap R K : R →* K)).coprod
    (zpowersHom Kˣ (Units.mk0 (algebraMap R K ϖ) (algebraMap_ne_zero K hϖ)))

theorem unitsProdHom_apply {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ) (k : Multiplicative ℤ) :
    ((unitsProdHom K hϖ (u, k) : Kˣ) : K) =
      algebraMap R K u * algebraMap R K ϖ ^ Multiplicative.toAdd k := by
  simp [unitsProdHom, zpowersHom_apply, Units.val_zpow_eq_zpow_val]

theorem unitsProdHom_bijective {ϖ : R} (hϖ : Irreducible ϖ) :
    Function.Bijective (unitsProdHom K hϖ) := by
  refine ⟨(injective_iff_map_eq_one _).2 fun ⟨u, k⟩ h => ?_, fun x => ?_⟩
  · have h' := congrArg (fun y : Kˣ => (y : K)) h
    simp only [unitsProdHom_apply, Units.val_one] at h'
    set k' : ℤ := Multiplicative.toAdd k
    have hk : k' = 0 := by
      by_contra hk0
      rcases Int.eq_nat_or_neg k' with ⟨m, hm | hm⟩
      · have hm0 : m ≠ 0 := by rintro rfl; exact hk0 (by simp [hm])
        rw [hm, zpow_natCast, ← map_pow, ← map_mul] at h'
        have h1 : (u : R) * ϖ ^ m = 1 := IsFractionRing.injective R K (by rw [h', map_one])
        exact hϖ.not_isUnit ((isUnit_pow_iff hm0).1
          (isUnit_of_mul_isUnit_right (x := (u : R)) (by rw [h1]; exact isUnit_one)))
      · have hm0 : m ≠ 0 := by rintro rfl; exact hk0 (by simp [hm])
        rw [hm, zpow_neg, zpow_natCast, ← map_pow, mul_inv_eq_one₀ (by
          rw [map_pow]; exact pow_ne_zero _ (algebraMap_ne_zero K hϖ))] at h'
        have h1 : (u : R) = ϖ ^ m := IsFractionRing.injective R K h'
        exact hϖ.not_isUnit ((isUnit_pow_iff hm0).1 (h1 ▸ u.isUnit))
    have hk1 : k = 1 := by
      change Multiplicative.ofAdd k' = 1
      rw [hk, ofAdd_zero]
    rw [hk, zpow_zero, mul_one, ← map_one (algebraMap R K)] at h'
    have hu : (u : R) = 1 := IsFractionRing.injective R K h'
    rw [hk1, show u = 1 from Units.ext hu]
    rfl
  · obtain ⟨k, u, hx⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (K := K) hϖ x.ne_zero
    refine ⟨(u, Multiplicative.ofAdd k), Units.ext ?_⟩
    rw [unitsProdHom_apply, hx, Units.smul_def, Algebra.smul_def, toAdd_ofAdd]

/-- **`Kˣ ≅ Rˣ × ℤ`**, `(u, k) ↦ u ϖ^k`. -/
noncomputable def unitsProdEquiv {ϖ : R} (hϖ : Irreducible ϖ) : Rˣ × Multiplicative ℤ ≃* Kˣ :=
  MulEquiv.ofBijective _ (unitsProdHom_bijective K hϖ)

end Field

section PowEquiv

variable {G G' : Type*} [CommGroup G] [CommGroup G']

theorem range_pow_map_equiv (e : G ≃* G') (n : ℕ) :
    (powMonoidHom n : G' →* G').range = (powMonoidHom n : G →* G).range.map (e : G →* G') := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x ^ n, ⟨_, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨e z, by simp⟩

theorem ker_pow_map_equiv (e : G ≃* G') (n : ℕ) :
    (powMonoidHom n : G' →* G').ker = (powMonoidHom n : G →* G).ker.map (e : G →* G') := by
  ext y
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at hy
    change (powMonoidHom n) (e.symm y) = 1
    rw [powMonoidHom_apply, ← map_pow, hy, map_one]
  · rintro ⟨z, hz, rfl⟩
    change (powMonoidHom n) z = 1 at hz
    rw [powMonoidHom_apply] at hz
    rw [MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow, hz, map_one]

theorem index_range_pow_equiv (e : G ≃* G') (n : ℕ) :
    (powMonoidHom n : G' →* G').range.index = (powMonoidHom n : G →* G).range.index := by
  rw [range_pow_map_equiv e, Subgroup.index_map_equiv]

theorem card_ker_pow_equiv (e : G ≃* G') (n : ℕ) :
    Nat.card (powMonoidHom n : G' →* G').ker = Nat.card (powMonoidHom n : G →* G).ker := by
  rw [ker_pow_map_equiv e, Subgroup.card_map_of_injective e.injective]

variable {H : Type*} [CommGroup H]

theorem powMonoidHom_prod (n : ℕ) :
    (powMonoidHom n : G × H →* G × H) = (powMonoidHom n).prodMap (powMonoidHom n) := by
  ext <;> rfl

theorem index_range_pow_prod (n : ℕ) :
    (powMonoidHom n : G × H →* G × H).range.index =
      (powMonoidHom n : G →* G).range.index * (powMonoidHom n : H →* H).range.index := by
  rw [powMonoidHom_prod, MonoidHom.range_prodMap, Subgroup.index_prod]

theorem card_ker_pow_prod (n : ℕ) :
    Nat.card (powMonoidHom n : G × H →* G × H).ker =
      Nat.card (powMonoidHom n : G →* G).ker * Nat.card (powMonoidHom n : H →* H).ker := by
  rw [powMonoidHom_prod, MonoidHom.ker_prodMap,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]

end PowEquiv

theorem index_range_pow_int (n : ℕ) [NeZero n] :
    (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range.index = n := by
  set χ : Multiplicative ℤ →* Multiplicative (ZMod n) :=
    (Int.castAddHom (ZMod n)).toMultiplicative
  have hχ : Function.Surjective χ := fun x =>
    ⟨Multiplicative.ofAdd (Multiplicative.toAdd x).valMinAbs, by
      change Multiplicative.ofAdd (((Multiplicative.toAdd x).valMinAbs : ℤ) : ZMod n) = x
      rw [ZMod.coe_valMinAbs, ofAdd_toAdd]⟩
  have hker : (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range = χ.ker := by
    ext k
    rw [MonoidHom.mem_ker]
    change _ ↔ Multiplicative.ofAdd (((Multiplicative.toAdd k : ℤ)) : ZMod n) = 1
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨Multiplicative.toAdd m, by simp [powMonoidHom_apply, toAdd_pow]⟩
    · rintro ⟨m, hm⟩
      exact ⟨Multiplicative.ofAdd m, by
        rw [powMonoidHom_apply, ← ofAdd_nsmul, nsmul_eq_mul, ← hm, ofAdd_toAdd]⟩
  rw [hker, Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ hχ, Subgroup.card_top]
  exact Nat.card_zmod n

theorem card_ker_pow_int (n : ℕ) [NeZero n] :
    Nat.card (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).ker = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => ?_⟩, ⟨1⟩⟩
  have h0 : ∀ x : Multiplicative ℤ, x ^ n = 1 → x = 1 := by
    intro x hx
    rw [← ofAdd_toAdd x, ← ofAdd_nsmul, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff,
      nsmul_eq_mul, mul_eq_zero] at hx
    rcases hx with hx | hx
    · exact absurd (by exact_mod_cast hx) (NeZero.ne n)
    · rw [← ofAdd_toAdd x, hx, ofAdd_zero]
  exact Subtype.ext ((h0 a ha).trans (h0 b hb).symm)

section FieldIndex

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [Finite (ResidueField R)]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- **`[Kˣ : (Kˣ)ⁿ] = n · #(R/nR) · #μ_n(K)`** for the fraction field `K` of a complete discrete
valuation ring `R` with finite residue field and `n ≠ 0` in `R`. -/
theorem index_range_pow_field (n : ℕ) (hn : (n : R) ≠ 0) :
    (powMonoidHom n : Kˣ →* Kˣ).range.index =
      n * Nat.card (R ⧸ Ideal.span {(n : R)}) * Nat.card (powMonoidHom n : Kˣ →* Kˣ).ker := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : NeZero n := ⟨by rintro rfl; simp at hn⟩
  set e := unitsProdEquiv K hϖ
  rw [index_range_pow_equiv e, card_ker_pow_equiv e, index_range_pow_prod, card_ker_pow_prod,
    index_range_pow_units n hn, index_range_pow_int, card_ker_pow_int]
  ring

end FieldIndex

end PowIndex
