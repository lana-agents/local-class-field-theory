/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Duality.H3Devissage
import LocalClassFieldTheory.Brauer.Corestriction

/-!
# Corestriction in degree three and injectivity of restriction on `H³`

Let `H ≤ G` be an open subgroup of finite index `m` of a topological group, with coset
representatives `c.out` and `κ(c, g) = (c.out)⁻¹ g (g⁻¹ • c).out ∈ H`
(`ContH2.kappa`, see `LocalClassFieldTheory.Brauer.Corestriction`). The **corestriction** of a
`3`-cochain `z` of `H` is

`(cor z)(g, h, k) = ∏_{c ∈ G/H} c.out • z(κ(c, g), κ(g⁻¹ • c, h), κ(h⁻¹ g⁻¹ • c, k))`
(`ContH2.corFun3`).

* `ContH2.dc2_corFun` : `d ∘ cor = cor ∘ d` from `2`- to `3`-cochains;
* **`ContH2.corFun3_res`** : `cor ∘ res = (·)^m` on `3`-cocycles up to an explicit coboundary:
  `(cor res z) = z^m · d q` with
  `q(a, b) = ∏_c z(c.out, κ(c, a), κ(a⁻¹c, b)) / z(a, (a⁻¹c).out, κ(a⁻¹c, b)) ·
  z(a, b, (b⁻¹a⁻¹c).out)` (`ContH2.qFun3`, obtained from the prism homotopy between the two
  maps `x ↦ c.out⁻¹ x` and `x ↦ κ(c, x)` on homogeneous cochains; per coset it is four
  applications of the cocycle identity, `ContH2.cor_res_aux3`);
* **`ContH2.h3Trivial_of_res`** : if `H³(H, M) = 0` (cocycle form) and `M` is finite with
  `x^m = 1 → x = 1`, then `H³(G, M) = 0`.
-/

open groupCohomology Finset

set_option linter.unusedSectionVars false

namespace ContH2

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]
variable (H : Subgroup G) [Fintype (G ⧸ H)]

/-- The corestriction of a `3`-cochain of `H`. -/
noncomputable def corFun3 (z : H × H × H → M) : G × G × G → M := fun x =>
  ∏ c : G ⧸ H, c.out • z (kappa H c x.1, kappa H (x.1⁻¹ • c) x.2.1,
    kappa H (x.2.1⁻¹ • x.1⁻¹ • c) x.2.2)

omit [TopologicalSpace G] in
theorem corFun3_apply (z : H × H × H → M) (g h k : G) :
    corFun3 H z (g, h, k) = ∏ c : G ⧸ H, c.out • z (kappa H c g, kappa H (g⁻¹ • c) h,
      kappa H (h⁻¹ • g⁻¹ • c) k) := rfl

omit [TopologicalSpace G] in
/-- **Corestriction commutes with the coboundary** `C²(H) → C³(H)`. -/
theorem dc2_corFun (f : H × H → M) : dc2 (corFun H f) = corFun3 H (dc2 f) := by
  ext ⟨g, h, k⟩
  have e : g • corFun H f (h, k) =
      ∏ c : G ⧸ H, c.out • (kappa H c g • f (kappa H (g⁻¹ • c) h,
        kappa H (h⁻¹ • g⁻¹ • c) k)) := by
    rw [corFun_apply, smul_prod', ← prod_reindex H _ g]
    refine prod_congr rfl fun c _ => ?_
    rw [Subgroup.smul_def, ← mul_smul g (Quotient.out (g⁻¹ • c)),
      ← mul_smul (Quotient.out c) (kappa H c g : G), out_mul_kappa]
  rw [dc2_apply, e, corFun_apply, corFun_apply, corFun_apply, corFun3_apply]
  simp only [kappa_mul, mul_inv_rev, mul_smul]
  rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_div_distrib]
  refine prod_congr rfl fun c _ => ?_
  rw [dc2_apply]
  simp only [smul_div', smul_mul']

omit [TopologicalSpace G] in
/-- The per-coset identity behind `cor ∘ res = [G : H]` in degree three. -/
theorem cor_res_aux3 {z : G × G × G → M} (hz : IsMulCocycle₃ z) (a b d s0 s1 s2 s3 : G) :
    s0 • z (s0⁻¹ * a * s1, s1⁻¹ * b * s2, s2⁻¹ * d * s3) =
      z (a, b, d) * (a • (z (s1, s1⁻¹ * b * s2, s2⁻¹ * d * s3) /
          z (b, s2, s2⁻¹ * d * s3) * z (b, d, s3)) *
        (z (s0, s0⁻¹ * a * s1, s1⁻¹ * (b * d) * s3) / z (a, s1, s1⁻¹ * (b * d) * s3) *
          z (a, b * d, s3)) /
        ((z (s0, s0⁻¹ * (a * b) * s2, s2⁻¹ * d * s3) / z (a * b, s2, s2⁻¹ * d * s3) *
          z (a * b, d, s3)) *
         (z (s0, s0⁻¹ * a * s1, s1⁻¹ * b * s2) / z (a, s1, s1⁻¹ * b * s2) * z (a, b, s2)))) := by
  have h1 := hz s0 (s0⁻¹ * a * s1) (s1⁻¹ * b * s2) (s2⁻¹ * d * s3)
  rw [show s0⁻¹ * a * s1 * (s1⁻¹ * b * s2) = s0⁻¹ * (a * b) * s2 by group,
    show s0 * (s0⁻¹ * a * s1) = a * s1 by group,
    show s1⁻¹ * b * s2 * (s2⁻¹ * d * s3) = s1⁻¹ * (b * d) * s3 by group] at h1
  have h2 := hz a s1 (s1⁻¹ * b * s2) (s2⁻¹ * d * s3)
  rw [show s1 * (s1⁻¹ * b * s2) = b * s2 by group,
    show s1⁻¹ * b * s2 * (s2⁻¹ * d * s3) = s1⁻¹ * (b * d) * s3 by group] at h2
  have h3 := hz a b s2 (s2⁻¹ * d * s3)
  rw [show s2 * (s2⁻¹ * d * s3) = d * s3 by group] at h3
  have h4 := hz a b d s3
  simp only [smul_mul', smul_div']
  rw [← div_eq_one]
  rw [← div_eq_one] at h1 h2 h3 h4
  calc _ = (s0 • z (s0⁻¹ * a * s1, s1⁻¹ * b * s2, s2⁻¹ * d * s3) *
          z (s0, s0⁻¹ * (a * b) * s2, s2⁻¹ * d * s3) * z (s0, s0⁻¹ * a * s1, s1⁻¹ * b * s2) /
          (z (a * s1, s1⁻¹ * b * s2, s2⁻¹ * d * s3) *
            z (s0, s0⁻¹ * a * s1, s1⁻¹ * (b * d) * s3))) /
        (a • z (s1, s1⁻¹ * b * s2, s2⁻¹ * d * s3) * z (a, b * s2, s2⁻¹ * d * s3) *
          z (a, s1, s1⁻¹ * b * s2) /
          (z (a * s1, s1⁻¹ * b * s2, s2⁻¹ * d * s3) * z (a, s1, s1⁻¹ * (b * d) * s3))) *
        (a • z (b, s2, s2⁻¹ * d * s3) * z (a, b * s2, s2⁻¹ * d * s3) * z (a, b, s2) /
          (z (a * b, s2, s2⁻¹ * d * s3) * z (a, b, d * s3))) /
        (a • z (b, d, s3) * z (a, b * d, s3) * z (a, b, d) /
          (z (a * b, d, s3) * z (a, b, d * s3))) := by mul_abel
    _ = 1 := by rw [h1, h2, h3, h4]; simp

/-- The primitive in `cor ∘ res = [G : H]` in degree three. -/
noncomputable def qFun3 (z : G × G × G → M) : G × G → M := fun x =>
  ∏ c : G ⧸ H, z (c.out, kappa H c x.1, kappa H (x.1⁻¹ • c) x.2) /
    z (x.1, (x.1⁻¹ • c).out, kappa H (x.1⁻¹ • c) x.2) * z (x.1, x.2, (x.2⁻¹ • x.1⁻¹ • c).out)

omit [TopologicalSpace G] in
/-- **`cor ∘ res = (·)^{[G : H]}` on `3`-cocycles**, up to the coboundary of `qFun3`. -/
theorem corFun3_res {z : G × G × G → M} (hz : IsMulCocycle₃ z) :
    corFun3 H (fun x : H × H × H => z (x.1, x.2.1, x.2.2)) =
      z ^ Fintype.card (G ⧸ H) * dc2 (qFun3 H z) := by
  ext ⟨g, h, k⟩
  rw [corFun3_apply, Pi.mul_apply, Pi.pow_apply, dc2_apply, ← card_univ, ← prod_const]
  have hq : g • qFun3 H z (h, k) = ∏ c : G ⧸ H, g • (z ((g⁻¹ • c).out,
      kappa H (g⁻¹ • c) h, kappa H (h⁻¹ • g⁻¹ • c) k) /
      z (h, (h⁻¹ • g⁻¹ • c).out, kappa H (h⁻¹ • g⁻¹ • c) k) *
      z (h, k, (k⁻¹ • h⁻¹ • g⁻¹ • c).out)) := by
    rw [qFun3, smul_prod', ← prod_reindex H _ g]
  rw [hq, qFun3, qFun3, qFun3]
  simp only [mul_inv_rev, mul_smul]
  rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_div_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun c _ => ?_
  simp only [coe_kappa, mul_inv_rev, mul_smul]
  exact cor_res_aux3 hz g h k _ _ _ _

section Topology

variable [IsTopologicalGroup G] {H}

omit [Fintype (G ⧸ H)] in
theorem continuous_out_smul₂ (hH : IsOpen (H : Set G)) (c : G ⧸ H) :
    Continuous fun x : G × G => (x.2⁻¹ • x.1⁻¹ • c).out := by
  have : (fun x : G × G => (x.2⁻¹ • x.1⁻¹ • c).out) =
      (fun g : G => (g⁻¹ • c).out) ∘ fun x : G × G => x.1 * x.2 := by
    funext x
    simp only [Function.comp_apply, mul_inv_rev, mul_smul]
  rw [this]
  exact (continuous_out_smul hH c).comp (continuous_fst.mul continuous_snd)

theorem isLocallyConstant_qFun3 (hH : IsOpen (H : Set G)) {z : G × G × G → M}
    (hz : IsLocallyConstant z) : IsLocallyConstant (qFun3 H z) := by
  refine isLocallyConstant_prod _ _ fun c _ => ?_
  have hk1 : Continuous fun x : G × G => (kappa H c x.1 : G) :=
    continuous_subtype_val.comp ((continuous_kappa hH c).comp continuous_fst)
  have hk2 : Continuous fun x : G × G => (kappa H (x.1⁻¹ • c) x.2 : G) :=
    continuous_subtype_val.comp (continuous_kappa₂ hH c)
  refine (IsLocallyConstant.div ?_ ?_).mul ?_
  · exact hz.comp_continuous (continuous_const.prodMk (hk1.prodMk hk2))
  · exact hz.comp_continuous (continuous_fst.prodMk
      (((continuous_out_smul hH c).comp continuous_fst).prodMk hk2))
  · exact hz.comp_continuous (continuous_fst.prodMk
      (continuous_snd.prodMk (continuous_out_smul₂ hH c)))

variable (H)

/-- **Restriction to an open subgroup of finite index `m` is injective on `H³`** for a finite
module on which `x ↦ x^m` is injective, in cocycle form: `H3Trivial H M → H3Trivial G M`. -/
theorem h3Trivial_of_res (hH : IsOpen (H : Set G)) [Finite M]
    (hM : ∀ m : M, m ^ Fintype.card (G ⧸ H) = 1 → m = 1) (h : H3Trivial H M) :
    H3Trivial G M := by
  intro z hzl hz
  set n := Fintype.card (G ⧸ H)
  have hzHl : IsLocallyConstant fun x : H × H × H => z (x.1, x.2.1, x.2.2) :=
    hzl.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))
  have hzHc : IsMulCocycle₃ fun x : H × H × H => z (x.1, x.2.1, x.2.2) :=
    fun a b c d => hz a b c d
  obtain ⟨f, hfl, hf⟩ := h _ hzHl hzHc
  have key : z ^ n = dc2 (corFun H f / qFun3 H z) := by
    rw [dc2_div, dc2_corFun, hf, corFun3_res H hz, mul_div_cancel_right]
  -- invert `x ↦ x^n`
  let pm : M →* M := powMonoidHom n
  have hinj : Function.Injective pm := by
    intro x y hxy
    have : (x / y) ^ n = 1 := by
      rw [div_pow]; exact div_eq_one.2 hxy
    exact div_eq_one.1 (hM _ this)
  let e : M ≃* M := MulEquiv.ofBijective pm hinj.bijective_of_finite
  have he : ∀ (g : G) (x : M), e.symm (g • x) = g • e.symm x := fun g x => by
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    change g • x = (g • e.symm x) ^ n
    rw [← smul_pow']
    congr 1
    exact (e.apply_symm_apply x).symm
  refine ⟨fun x => e.symm ((corFun H f / qFun3 H z) x),
    ((isLocallyConstant_corFun hH hfl).div (isLocallyConstant_qFun3 hH hzl)).comp _, ?_⟩
  funext x
  refine (map_dc2 e.symm.toMonoidHom he _ x).symm.trans ?_
  change e.symm (dc2 (corFun H f / qFun3 H z) x) = z x
  rw [← key, Pi.pow_apply]
  apply e.injective
  rw [MulEquiv.apply_symm_apply]
  rfl

end Topology

end ContH2
