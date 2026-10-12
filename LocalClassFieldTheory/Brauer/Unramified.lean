/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.Absolute
import LocalClassFieldTheory.Reciprocity.Artin

/-!
# The unramified Brauer group `Br(K^ur/K) ≃ ℚ/ℤ`

Let `K` be finite over `ℚ_[p]` and `Ω/K` an algebraically closed Galois extension (an algebraic
closure). For the unramified extensions `K_n ⊆ Ω` we have `Br(K_n/K) ≃ (1/n)ℤ/ℤ` via the invariant
`PadicField.invUnr` (`v_K` of the periodicity element for the Frobenius, divided by `n`). The
invariants are compatible with inflation `K_n ⊆ K_{n'}` (`PadicField.invUnr_inflRel`), so they glue
to an isomorphism on the subgroup of unramified classes

`PadicField.brUr p K Ω = ⋃_n infl(Br(K_n/K)) ≤ Br(K)`, `PadicField.invUrEquiv : brUr ≃* ℚ/ℤ`.

## Main results

* `PadicField.invUnr_mk` : `inv [f] = v_K(∏_{i<n} f(Frob^i, Frob)) / n`.
* `PadicField.card_relBr_unramifiedOfDegree` : `|Br(K_n/K)| = n`.
* `PadicField.invUnr_inflRel` : compatibility with inflation.
* `PadicField.brUr`, `PadicField.invUr`, `PadicField.invUr_infl`, `PadicField.invUrEquiv`.
-/

open ContH2 Brauer IntermediateField

namespace PadicField

variable {p : ℕ} [hp : Fact p.Prime]

section Abstract

variable {K L : Type*} [Field K] [Field L] [Algebra ℚ_[p] K] [Algebra ℚ_[p] L]
  [Algebra K L] [IsScalarTower ℚ_[p] K L] [FiniteDimensional ℚ_[p] K]
  [FiniteDimensional ℚ_[p] L] [FiniteDimensional K L] [IsGalois K L]

theorem invUnr_mk (h : IsUnramified p K L) (f : cocycles (L ≃ₐ[K] L) Lˣ) :
    invUnr h (mk f) = vQZ p K (Module.finrank K L) (phiUnits (frob h) (mem_zpowers_frob h) f) := by
  simp only [invUnr, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    relCyclicEquiv_mk, QuotientGroup.lift_mk]

include hp in
theorem vQZ_pow {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (a : Kˣ) :
    vQZ p K (n * m) (a ^ m) = vQZ p K n a := by
  rw [vQZ_apply, vQZ_apply, Units.val_pow_eq_pow_val, v_pow a.ne_zero]
  congr 2
  push_cast
  field_simp

end Abstract

variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

local notation "Kn" n => unramifiedOfDegree p K Ω n

theorem card_relBr_unramifiedOfDegree {n : ℕ} (hn : 0 < n) :
    Nat.card (RelBr K (Kn n)) = n := by
  rw [card_rel_of_isCyclic (p := p), finrank_unramifiedOfDegree p K Ω hn]

/-- The invariant of `Br(K_n/K)`. -/
noncomputable abbrev invN (n : ℕ) : RelBr K (Kn n) →* Multiplicative QZ :=
  invUnr (isUnramified_unramifiedOfDegree p K Ω n)

theorem invUnr_inflRel {n n' : ℕ} (hn : 0 < n) (hn' : 0 < n') (h : (Kn n) ≤ Kn n')
    (α : RelBr K (Kn n)) : invN n' (inflRel h α) = invN n α := by
  obtain ⟨m, rfl⟩ := (unramifiedOfDegree_le_iff hn hn').1 h
  have hm : 0 < m := Nat.pos_of_mul_pos_left hn'
  induction α using ContH2.induction_on with | h f => ?_
  simp only [invN]
  rw [inflRel, map_mk, invUnr_mk, invUnr_mk, finrank_unramifiedOfDegree p K Ω hn,
    finrank_unramifiedOfDegree p K Ω hn', ← vQZ_pow hn.ne' hm.ne']
  congr 1
  apply Units.ext
  apply (algebraMap K (Kn (n * m))).injective
  rw [algebraMap_phiUnits, Units.val_pow_eq_pow_val, map_pow]
  have hφ := phiFun_mapFun (frobT p K Ω n) (resHom h)
    (Units.map (inclusion h : (Kn n) →* (Kn (n * m))))
    (frobT p K Ω (n * m)) (resHom_frobT hn hn' h) f
  rw [orderOf_frob, orderOf_frob, finrank_unramifiedOfDegree p K Ω hn,
    finrank_unramifiedOfDegree p K Ω hn', Nat.mul_div_cancel_left _ hn] at hφ
  have e1 : (cocyclesMap (resHom h) continuous_of_discreteTopology
      (Units.map (inclusion h : (Kn n) →* (Kn (n * m)))) (units_map_inclusion_resHom_smul h) f :
      _ × _ → _) = mapFun (resHom h) (Units.map (inclusion h : (Kn n) →* (Kn (n * m)))) f := rfl
  rw [e1, hφ, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, ← algebraMap_phiUnits]
  rfl

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] in
theorem le_mul_left' {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : (Kn n) ≤ Kn (n * m) :=
  unramifiedOfDegree_le_of_dvd (Nat.mul_pos hn hm).ne' (dvd_mul_right n m)

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] [IsAlgClosed Ω] in
theorem le_mul_right' {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : (Kn m) ≤ Kn (n * m) :=
  unramifiedOfDegree_le_of_dvd (Nat.mul_pos hn hm).ne' (dvd_mul_left m n)

/-- The class of `a ∈ Kˣ` in `Br(K_n/K)`. -/
noncomputable abbrev unrClassN (n : ℕ) (a : Kˣ) : RelBr K (Kn n) :=
  unrClass (isUnramified_unramifiedOfDegree p K Ω n) a

theorem invN_unrClassN {n : ℕ} (hn : 0 < n) (a : Kˣ) :
    invN n (unrClassN (p := p) (Ω := Ω) n a) = vQZ p K n a := by
  rw [invUnr_unrClass, finrank_unramifiedOfDegree p K Ω hn]

variable (p K Ω) in
/-- The **unramified Brauer group** `Br(K^ur/K) = ⋃_n infl(Br(K_n/K)) ≤ Br(K)`. -/
noncomputable def brUr : Subgroup (Br K Ω) where
  carrier := {α | ∃ n, 0 < n ∧ ∃ β : RelBr K (Kn n), infl (Ω := Ω) (Kn n) β = α}
  mul_mem' := by
    rintro _ _ ⟨n, hn, β, rfl⟩ ⟨m, hm, β', rfl⟩
    refine ⟨n * m, Nat.mul_pos hn hm,
      inflRel (le_mul_left' hn hm) β * inflRel (le_mul_right' hn hm) β', ?_⟩
    rw [map_mul, infl_inflRel, infl_inflRel]
  one_mem' := ⟨1, one_pos, 1, map_one _⟩
  inv_mem' := by
    rintro _ ⟨n, hn, β, rfl⟩
    exact ⟨n, hn, β⁻¹, map_inv _ _⟩

omit [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω] in
theorem infl_mem_brUr {n : ℕ} (hn : 0 < n) (β : RelBr K (Kn n)) :
    infl (Ω := Ω) (Kn n) β ∈ brUr p K Ω := ⟨n, hn, β, rfl⟩

variable [IsGalois K Ω]

theorem invN_eq_of_infl_eq {n n' : ℕ} (hn : 0 < n) (hn' : 0 < n') (β : RelBr K (Kn n))
    (β' : RelBr K (Kn n')) (h : infl (Ω := Ω) (Kn n) β = infl (Kn n') β') :
    invN n β = invN n' β' := by
  have e : inflRel (le_mul_left' hn hn') β = inflRel (le_mul_right' hn hn') β' := by
    apply infl_injective (Kn (n * n'))
    rw [infl_inflRel, infl_inflRel, h]
  rw [← invUnr_inflRel hn (Nat.mul_pos hn hn') (le_mul_left' hn hn'), e,
    invUnr_inflRel hn' (Nat.mul_pos hn hn')]

/-- The invariant on `Br(K^ur/K)` (as a function). -/
noncomputable def invUrFun (α : brUr p K Ω) : Multiplicative QZ :=
  invN (Classical.choose α.2) (Classical.choose (Classical.choose_spec α.2).2)

theorem invUrFun_eq (α : brUr p K Ω) {n : ℕ} (hn : 0 < n) (β : RelBr K (Kn n))
    (hβ : infl (Kn n) β = (α : Br K Ω)) : invUrFun α = invN n β := by
  have h₀ := Classical.choose_spec α.2
  have h₁ := Classical.choose_spec h₀.2
  exact invN_eq_of_infl_eq h₀.1 hn _ _ (h₁.trans hβ.symm)

/-- **The invariant map** `inv : Br(K^ur/K) →* ℚ/ℤ`. -/
noncomputable def invUr : brUr p K Ω →* Multiplicative QZ where
  toFun := invUrFun
  map_one' := by
    rw [invUrFun_eq 1 one_pos 1 (map_one _), map_one]
  map_mul' α α' := by
    obtain ⟨n, hn, β, hβ⟩ := α.2
    obtain ⟨m, hm, β', hβ'⟩ := α'.2
    rw [invUrFun_eq α hn β hβ, invUrFun_eq α' hm β' hβ',
      invUrFun_eq (α * α') (Nat.mul_pos hn hm)
        (inflRel (le_mul_left' hn hm) β * inflRel (le_mul_right' hn hm) β'),
      map_mul, invUnr_inflRel hn (Nat.mul_pos hn hm), invUnr_inflRel hm (Nat.mul_pos hn hm)]
    rw [map_mul, infl_inflRel, infl_inflRel, hβ, hβ']
    rfl

theorem invUr_infl {n : ℕ} (hn : 0 < n) (β : RelBr K (Kn n)) :
    invUr ⟨infl (Kn n) β, infl_mem_brUr hn β⟩ = invN n β :=
  invUrFun_eq _ hn β rfl

theorem invUr_injective : Function.Injective (invUr (p := p) (K := K) (Ω := Ω)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨α, n, hn, β, rfl⟩ h
  rw [MonoidHom.mem_ker, invUr_infl hn] at h
  have : β = 1 := invUnr_injective _ (h.trans (map_one _).symm)
  rw [Subgroup.mem_bot]
  ext
  simp [this]

theorem invUr_surjective : Function.Surjective (invUr (p := p) (K := K) (Ω := Ω)) := by
  intro x
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd x)
  have hπ : IsUniformizer p K (uniformizer p K) := uniformizer_spec
  set π : Kˣ := Units.mk0 _ hπ.ne_zero
  refine ⟨⟨_, infl_mem_brUr r.den_pos (unrClassN r.den (π ^ r.num))⟩, ?_⟩
  rw [invUr_infl r.den_pos, invN_unrClassN r.den_pos, vQZ_apply, Units.val_zpow_eq_zpow_val,
    v_zpow (Units.ne_zero π)]
  simp only [π, Units.val_mk0]
  rw [show v p (uniformizer p K) = 1 from hπ, mul_one, Rat.num_div_den]
  rfl

/-- **`Br(K^ur/K) ≃ ℚ/ℤ`** via the invariant map. -/
noncomputable def invUrEquiv : brUr p K Ω ≃* Multiplicative QZ :=
  MulEquiv.ofBijective invUr ⟨invUr_injective, invUr_surjective⟩

end PadicField
