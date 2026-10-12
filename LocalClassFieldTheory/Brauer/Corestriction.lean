/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.InfRes

/-!
# Corestriction in degree two

Let `H ≤ G` be an open subgroup of finite index of a topological group. With representatives
`c.out` of the left cosets `c ∈ G ⧸ H` and `κ(c, g) = (c.out)⁻¹ g (g⁻¹ • c).out ∈ H`, the
**corestriction** of a 2-cocycle `f` of `H` is

`(cor f)(g, h) = ∏_{c ∈ G/H} c.out • f(κ(c, g), κ(g⁻¹ • c, h))`.

It is a 2-cocycle (`ContH2.isMulCocycle₂_corFun`: the cocycle identity holds factor by factor after
reindexing `c ↦ g⁻¹ • c`), maps coboundaries to coboundaries, and `cor ∘ res = (·)^{[G : H]}`
(`ContH2.cor_res`): for a 2-cocycle `E` of `G`,
`(cor res E)(g, h) = E(g, h)^{[G:H]} · (dq)(g, h)` with
`q(x) = ∏_c E(c.out, κ(c, x)) / E(x, (x⁻¹ • c).out)` (three applications of the cocycle identity per
factor).
-/

open groupCohomology Finset

set_option linter.unusedSectionVars false

namespace ContH2

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]
variable (H : Subgroup G)

omit [TopologicalSpace G] in
theorem out_inv_mul_mem (c : G ⧸ H) (g : G) : (c.out)⁻¹ * g * (g⁻¹ • c).out ∈ H := by
  have h1 : (QuotientGroup.mk (g⁻¹ • c).out : G ⧸ H) = QuotientGroup.mk (g⁻¹ * c.out) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk,
      QuotientGroup.out_eq']
  rw [QuotientGroup.eq] at h1
  have := H.inv_mem h1
  simpa [mul_inv_rev, mul_assoc] using this

/-- `κ(c, g) = (c.out)⁻¹ g (g⁻¹ • c).out ∈ H`. -/
noncomputable def kappa (c : G ⧸ H) (g : G) : H := ⟨(c.out)⁻¹ * g * (g⁻¹ • c).out, out_inv_mul_mem H c g⟩

omit [TopologicalSpace G] in
theorem coe_kappa (c : G ⧸ H) (g : G) : (kappa H c g : G) = (c.out)⁻¹ * g * (g⁻¹ • c).out := rfl

omit [TopologicalSpace G] in
theorem kappa_mul (c : G ⧸ H) (g h : G) :
    kappa H c (g * h) = kappa H c g * kappa H (g⁻¹ • c) h := by
  apply Subtype.ext
  simp only [coe_kappa, Subgroup.coe_mul, mul_inv_rev, mul_smul]
  group

omit [TopologicalSpace G] in
theorem out_mul_kappa (c : G ⧸ H) (g : G) :
    c.out * (kappa H c g : G) = g * (g⁻¹ • c).out := by
  rw [coe_kappa]
  group

variable [Fintype (G ⧸ H)]

/-- The corestriction of a 2-cochain of `H`. -/
noncomputable def corFun (f : H × H → M) : G × G → M :=
  fun gh => ∏ c : G ⧸ H, c.out • f (kappa H c gh.1, kappa H (gh.1⁻¹ • c) gh.2)

omit [TopologicalSpace G] in
theorem corFun_apply (f : H × H → M) (g h : G) :
    corFun H f (g, h) = ∏ c : G ⧸ H, c.out • f (kappa H c g, kappa H (g⁻¹ • c) h) := rfl

omit [TopologicalSpace G] in
theorem prod_reindex {N : Type*} [CommMonoid N] (F : G ⧸ H → N) (g : G) :
    ∏ c : G ⧸ H, F (g⁻¹ • c) = ∏ c : G ⧸ H, F c :=
  Fintype.prod_equiv (MulAction.toPerm g⁻¹) _ _ (fun _ => rfl)

theorem isMulCocycle₂_corFun {f : H × H → M} (hf : IsMulCocycle₂ f) :
    IsMulCocycle₂ (corFun H f) := by
  intro g h k
  -- reindex `g • cor(h, k)` by `c ↦ g⁻¹ • c`
  have e : g • corFun H f (h, k) =
      ∏ c : G ⧸ H, c.out • (kappa H c g • f (kappa H (g⁻¹ • c) h,
        kappa H (h⁻¹ • g⁻¹ • c) k)) := by
    rw [corFun_apply, smul_prod', ← prod_reindex H _ g]
    refine prod_congr rfl fun c _ => ?_
    rw [Subgroup.smul_def, ← mul_smul g (Quotient.out (g⁻¹ • c)),
      ← mul_smul (Quotient.out c) (kappa H c g : G), out_mul_kappa]
  rw [e, corFun_apply, corFun_apply, corFun_apply, ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun c _ => ?_
  rw [← smul_mul', ← smul_mul']
  congr 1
  have := hf (kappa H c g) (kappa H (g⁻¹ • c) h) (kappa H (h⁻¹ • g⁻¹ • c) k)
  rw [← kappa_mul, ← kappa_mul] at this
  rw [smul_smul, ← mul_inv_rev] at this ⊢
  exact this

/-- The corestriction of a 1-cochain of `H`. -/
noncomputable def corFun₁ (x : H → M) : G → M := fun g => ∏ c : G ⧸ H, c.out • x (kappa H c g)

theorem smul_corFun₁ (x : H → M) (g h : G) :
    g • corFun₁ H x h = ∏ c : G ⧸ H, c.out • (kappa H c g • x (kappa H (g⁻¹ • c) h)) := by
  rw [corFun₁, smul_prod', ← prod_reindex H _ g]
  refine prod_congr rfl fun c _ => ?_
  rw [Subgroup.smul_def, ← mul_smul g (Quotient.out (g⁻¹ • c)),
    ← mul_smul (Quotient.out c) (kappa H c g : G), out_mul_kappa]

/-- Corestriction maps coboundaries to coboundaries. -/
theorem corFun_dx (x : H → M) : corFun H (dx H M x) = dx G M (corFun₁ H x) := by
  funext gh
  obtain ⟨g, h⟩ := gh
  rw [corFun_apply, dx_apply, smul_corFun₁]
  simp only [corFun₁, kappa_mul, dx_apply]
  rw [← prod_div_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun c _ => ?_
  rw [smul_mul', smul_div']

omit [TopologicalSpace G] [Fintype (G ⧸ H)] in
/-- The per-coset identity behind `cor ∘ res = [G : H]`. -/
theorem cor_res_aux {E : G × G → M} (hE : IsMulCocycle₂ E) (a g h B U : G) :
    a • E (a⁻¹ * g * B, B⁻¹ * h * U) =
      E (g, h) * (g • (E (B, B⁻¹ * h * U) / E (h, U)) /
        (E (a, a⁻¹ * (g * h) * U) / E (g * h, U)) * (E (a, a⁻¹ * g * B) / E (g, B))) := by
  have h1 := hE a (a⁻¹ * g * B) (B⁻¹ * h * U)
  rw [show a * (a⁻¹ * g * B) = g * B by group,
    show a⁻¹ * g * B * (B⁻¹ * h * U) = a⁻¹ * (g * h) * U by group] at h1
  have h2 := hE g B (B⁻¹ * h * U)
  rw [show B * (B⁻¹ * h * U) = h * U by group] at h2
  have h3 := hE g h U
  have e1 : a • E (a⁻¹ * g * B, B⁻¹ * h * U) =
      E (g * B, B⁻¹ * h * U) * E (a, a⁻¹ * g * B) / E (a, a⁻¹ * (g * h) * U) := by
    rw [h1]; mul_abel
  have e2 : E (g * B, B⁻¹ * h * U) = g • E (B, B⁻¹ * h * U) * E (g, h * U) / E (g, B) := by
    rw [← h2]; mul_abel
  have e3 : E (g, h * U) = E (g * h, U) * E (g, h) / g • E (h, U) := by
    rw [h3]; mul_abel
  rw [e1, e2, e3, smul_div']
  mul_abel

/-- The primitive in `cor ∘ res = [G : H]`. -/
noncomputable def qFun (E : G × G → M) : G → M :=
  fun x => ∏ c : G ⧸ H, E (c.out, kappa H c x) / E (x, (x⁻¹ • c).out)

/-- **`cor ∘ res = (·)^{[G : H]}` on cocycles**, up to the coboundary of `qFun`. -/
theorem corFun_res {E : G × G → M} (hE : IsMulCocycle₂ E) :
    corFun H (fun x : H × H => E (x.1, x.2)) =
      E ^ Fintype.card (G ⧸ H) * dx G M (qFun H E) := by
  funext gh
  obtain ⟨g, h⟩ := gh
  rw [corFun_apply, Pi.mul_apply, Pi.pow_apply, dx_apply, ← card_univ, ← prod_const]
  have hq : g • qFun H E h = ∏ c : G ⧸ H, g • (E ((g⁻¹ • c).out, kappa H (g⁻¹ • c) h) /
      E (h, (h⁻¹ • g⁻¹ • c).out)) := by
    rw [qFun, smul_prod', ← prod_reindex H _ g]
  rw [hq, qFun, qFun, ← prod_div_distrib, ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun c _ => ?_
  simp only [coe_kappa]
  rw [mul_inv_rev, mul_smul]
  exact cor_res_aux hE _ g h _ _

section Topology

variable [IsTopologicalGroup G] {H}

theorem isLocallyConstant_smul_quot (hH : IsOpen (H : Set G)) (c : G ⧸ H) :
    IsLocallyConstant fun g : G => g⁻¹ • c := by
  haveI := QuotientGroup.discreteTopology hH
  have : (fun g : G => g⁻¹ • c) = (QuotientGroup.mk : G → G ⧸ H) ∘ fun g => g⁻¹ * c.out := by
    funext g
    simp only [Function.comp_apply]
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl
  rw [this, IsLocallyConstant.iff_continuous]
  exact QuotientGroup.continuous_mk.comp (continuous_inv.mul continuous_const)

theorem continuous_out_smul (hH : IsOpen (H : Set G)) (c : G ⧸ H) :
    Continuous fun g : G => (g⁻¹ • c).out :=
  ((isLocallyConstant_smul_quot hH c).comp _).continuous

theorem continuous_kappa (hH : IsOpen (H : Set G)) (c : G ⧸ H) :
    Continuous (kappa H c) :=
  ((continuous_const.mul continuous_id).mul (continuous_out_smul hH c)).subtype_mk _

theorem continuous_kappa₂ (hH : IsOpen (H : Set G)) (c : G ⧸ H) :
    Continuous fun gh : G × G => kappa H (gh.1⁻¹ • c) gh.2 := by
  refine Continuous.subtype_mk ?_ _
  have h1 : Continuous fun gh : G × G => (gh.1⁻¹ • c).out :=
    (continuous_out_smul hH c).comp continuous_fst
  have h2 : Continuous fun gh : G × G => (gh.2⁻¹ • gh.1⁻¹ • c).out := by
    have : (fun gh : G × G => (gh.2⁻¹ • gh.1⁻¹ • c).out) =
        (fun g : G => (g⁻¹ • c).out) ∘ fun gh : G × G => gh.1 * gh.2 := by
      funext gh
      simp only [Function.comp_apply, mul_inv_rev, mul_smul]
    rw [this]
    exact (continuous_out_smul hH c).comp (continuous_fst.mul continuous_snd)
  exact (h1.inv.mul continuous_snd).mul h2

theorem isLocallyConstant_prod {X N : Type*} [TopologicalSpace X] [CommMonoid N] {ι : Type*}
    (s : Finset ι) (F : ι → X → N) (hF : ∀ i ∈ s, IsLocallyConstant (F i)) :
    IsLocallyConstant fun x => ∏ i ∈ s, F i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty]
    exact IsLocallyConstant.const 1
  | insert i s hi ih =>
    simp only [prod_insert hi]
    exact (hF i (mem_insert_self i s)).mul (ih fun j hj => hF j (mem_insert_of_mem hj))

theorem isLocallyConstant_corFun (hH : IsOpen (H : Set G)) {f : H × H → M}
    (hf : IsLocallyConstant f) : IsLocallyConstant (corFun H f) := by
  refine isLocallyConstant_prod _ _ fun c _ => ?_
  have : Continuous fun gh : G × G => (kappa H c gh.1, kappa H (gh.1⁻¹ • c) gh.2) :=
    ((continuous_kappa hH c).comp continuous_fst).prodMk (continuous_kappa₂ hH c)
  exact (hf.comp_continuous this).comp _

theorem isLocallyConstant_corFun₁ (hH : IsOpen (H : Set G)) {x : H → M}
    (hx : IsLocallyConstant x) : IsLocallyConstant (corFun₁ H x) :=
  isLocallyConstant_prod _ _ fun c _ => (hx.comp_continuous (continuous_kappa hH c)).comp _

theorem isLocallyConstant_qFun (hH : IsOpen (H : Set G)) {E : G × G → M}
    (hE : IsLocallyConstant E) : IsLocallyConstant (qFun H E) := by
  refine isLocallyConstant_prod _ _ fun c _ => ?_
  refine IsLocallyConstant.div ?_ ?_
  · exact hE.comp_continuous (continuous_const.prodMk
      (continuous_subtype_val.comp (continuous_kappa hH c)))
  · exact hE.comp_continuous (continuous_id.prodMk (continuous_out_smul hH c))

variable (H)

/-- Corestriction on cocycles. -/
noncomputable def corCocycles (hH : IsOpen (H : Set G)) : cocycles H M →* cocycles G M where
  toFun f := mkCocycle (corFun H f) (isLocallyConstant_corFun hH (isLocallyConstant f))
    (isMulCocycle₂_corFun H (isMulCocycle₂ f))
  map_one' := cocycles_ext fun g h => by
    simp [corFun_apply]
  map_mul' f f' := cocycles_ext fun g h => by
    simp only [coe_mkCocycle, corFun_apply, coe_mul_apply, smul_mul', prod_mul_distrib]

/-- **Corestriction** `H²(H, M) → H²(G, M)` for an open subgroup of finite index. -/
noncomputable def cor (hH : IsOpen (H : Set G)) : ContH2 H M →* ContH2 G M :=
  QuotientGroup.map _ _ (corCocycles H hH) (by
    rintro f ⟨x, hx, hxf⟩
    refine ⟨corFun₁ H x, isLocallyConstant_corFun₁ hH hx, ?_⟩
    rw [← corFun_dx, hxf]
    rfl)

theorem cor_mk (hH : IsOpen (H : Set G)) (f : cocycles H M) :
    cor H hH (mk f) = mk (corCocycles H hH f) := rfl

/-- **`cor ∘ res = (·)^{[G : H]}`**. -/
theorem cor_res (hH : IsOpen (H : Set G)) (α : ContH2 G M) :
    cor H hH (ContH2.map H.subtype continuous_subtype_val (MonoidHom.id M) (fun _ _ => rfl) α) =
      α ^ Fintype.card (G ⧸ H) := by
  induction α using ContH2.induction_on with | h E => ?_
  rw [map_mk, cor_mk, ← map_pow, mk_eq_mk_iff]
  refine ⟨qFun H E, isLocallyConstant_qFun hH (isLocallyConstant E), ?_⟩
  have h := corFun_res H (isMulCocycle₂ E)
  funext gh
  obtain ⟨g, h'⟩ := gh
  have := congrFun h (g, h')
  simp only [Pi.mul_apply, Pi.pow_apply] at this
  change dx G M (qFun H E) (g, h') = corFun H (fun x : H × H => E (x.1, x.2)) (g, h') /
    E (g, h') ^ Fintype.card (G ⧸ H)
  rw [this, mul_div_cancel_left]

end Topology

end ContH2
