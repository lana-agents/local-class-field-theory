/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import LocalClassFieldTheory.Brauer.ContH2

/-!
# Inflation–restriction in degree two

Let `φ : G →* Q` be a continuous surjection onto a discrete group, `N = ker φ` (an open normal
subgroup), and `ψ : A →* M` an injective compatible map onto `M^N`. If `H¹(N, M) = 0` (for locally
constant cochains), then a class `[f] ∈ H²(G, M)` whose restriction to `N` is trivial is inflated
from `H²(Q, A)` (`ContH2.exists_map_eq_of_res`). Together with `ContH2.map_injective` this is the
exact sequence `0 → H²(Q, M^N) → H²(G, M) → H²(N, M)`.

Proof (explicit cocycles): normalise `f` on `N × N` by an extension of the given primitive; kill
the values `f(g, n)` with the cochain `s(gN)·m ↦ f(s(gN), m)` (`s` a section of `φ`); then
`n ↦ f(n, h)` is a 1-cocycle of `N` depending only on `hN`, and Hilbert 90 for `N` kills
`f(n, h)`; a cocycle with `f(g, n) = f(n, g) = 1` is constant on cosets with values in `M^N`.
-/

open groupCohomology

namespace ContH2

variable {G M : Type*} [Group G] [TopologicalSpace G] [CommGroup M] [MulDistribMulAction G M]
variable {Q A : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [CommGroup A]
  [MulDistribMulAction Q A]

/-- A cocycle which is trivial on `G × N` and `N × G` is inflated from `Q`. -/
theorem exists_map_eq_of_trivial (φ : G →* Q) (hφ : Continuous φ) (hφs : Function.Surjective φ)
    (ψ : A →* M) (hψ : Function.Injective ψ) (h : ∀ (g : G) (m : A), ψ (φ g • m) = g • ψ m)
    (hfix : ∀ m : M, (∀ n ∈ φ.ker, n • m = m) → m ∈ ψ.range) (f : cocycles G M)
    (h1 : ∀ g, ∀ n ∈ φ.ker, f (g, n) = 1) (h2 : ∀ g, ∀ n ∈ φ.ker, f (n, g) = 1) :
    ∃ F : cocycles Q A, cocyclesMap φ hφ ψ h F = f := by
  have hc := isMulCocycle₂ f
  -- invariance under right translation by `N` in both variables
  have hR : ∀ g k, ∀ n ∈ φ.ker, f (g, k * n) = f (g, k) := by
    intro g k n hn
    have := hc g k n
    rw [h1 _ n hn, h1 _ n hn, smul_one, one_mul, one_mul] at this
    exact this.symm
  have hconj : ∀ k, ∀ n ∈ φ.ker, k⁻¹ * n * k ∈ φ.ker := by
    intro k n hn
    rw [MonoidHom.mem_ker] at hn ⊢
    simp [hn]
  have hL : ∀ g k, ∀ n ∈ φ.ker, f (g * n, k) = f (g, k) := by
    intro g k n hn
    have := hc g n k
    rw [h1 g n hn, mul_one, h2 _ n hn, smul_one, one_mul,
      show n * k = k * (k⁻¹ * n * k) by group, hR _ _ _ (hconj k n hn)] at this
    exact this
  have hfixf : ∀ g k, ∀ n ∈ φ.ker, n • f (g, k) = f (g, k) := by
    intro g k n hn
    have := hc n g k
    rw [h2 _ n hn, h2 _ n hn, mul_one, mul_one, show n * g = g * (g⁻¹ * n * g) by group,
      hL _ _ _ (hconj g n hn)] at this
    exact this.symm
  have hdep : ∀ g g' k k', φ g = φ g' → φ k = φ k' → f (g, k) = f (g', k') := by
    intro g g' k k' hg hk
    have hg' : g⁻¹ * g' ∈ φ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hg, inv_mul_cancel]
    have hk' : k⁻¹ * k' ∈ φ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hk, inv_mul_cancel]
    rw [← mul_inv_cancel_left g g', hL _ _ _ hg', ← mul_inv_cancel_left k k', hR _ _ _ hk']
  -- descend
  have hmem : ∀ g k, f (g, k) ∈ ψ.range := fun g k => hfix _ (fun n hn => hfixf g k n hn)
  let s := Function.surjInv hφs
  have hs : ∀ q, φ (s q) = q := Function.surjInv_eq hφs
  let F : Q × Q → A := fun qq => Classical.choose (hmem (s qq.1) (s qq.2))
  have hF : ∀ q q', ψ (F (q, q')) = f (s q, s q') := fun q q' =>
    Classical.choose_spec (hmem (s q) (s q'))
  have hFφ : ∀ g k, ψ (F (φ g, φ k)) = f (g, k) := fun g k => by
    rw [hF]; exact hdep _ _ _ _ (hs _) (hs _)
  have hFc : IsMulCocycle₂ F := by
    intro a b c
    obtain ⟨g, rfl⟩ := hφs a
    obtain ⟨k, rfl⟩ := hφs b
    obtain ⟨l, rfl⟩ := hφs c
    apply hψ
    rw [map_mul, map_mul, h, ← map_mul φ, ← map_mul φ, hFφ, hFφ, hFφ, hFφ]
    exact hc g k l
  refine ⟨mkCocycle F (.of_discrete _) hFc, cocycles_ext fun g k => ?_⟩
  rw [cocyclesMap_apply, coe_mkCocycle, hFφ]

section Aux

omit [TopologicalSpace G] in
theorem isMulCocycle₂_mul {f f' : G × G → M} (hf : IsMulCocycle₂ f) (hf' : IsMulCocycle₂ f') :
    IsMulCocycle₂ (f * f') := by
  intro a b c
  simp only [Pi.mul_apply, smul_mul']
  calc f (a * b, c) * f' (a * b, c) * (f (a, b) * f' (a, b))
      = (f (a * b, c) * f (a, b)) * (f' (a * b, c) * f' (a, b)) := by mul_abel
    _ = (a • f (b, c) * f (a, b * c)) * (a • f' (b, c) * f' (a, b * c)) := by
        rw [hf a b c, hf' a b c]
    _ = _ := by mul_abel

open scoped Topology in
/-- The coboundary of a locally constant cochain is locally constant (smooth action). -/
theorem isLocallyConstant_dx [IsTopologicalGroup G]
    (hsmooth : ∀ m : M, IsLocallyConstant fun g : G => g • m)
    {x : G → M} (hx : IsLocallyConstant x) : IsLocallyConstant (dx G M x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨g, k⟩
  have e1 : ∀ᶠ q : G × G in 𝓝 (g, k), x q.2 = x k :=
    (continuous_snd.continuousAt (x := (g, k))).eventually
      ((IsLocallyConstant.iff_eventually_eq x).1 hx k)
  have e2 : ∀ᶠ q : G × G in 𝓝 (g, k), x q.1 = x g :=
    (continuous_fst.continuousAt (x := (g, k))).eventually
      ((IsLocallyConstant.iff_eventually_eq x).1 hx g)
  have e3 : ∀ᶠ q : G × G in 𝓝 (g, k), x (q.1 * q.2) = x (g * k) :=
    (continuous_mul.continuousAt (x := (g, k))).eventually
      ((IsLocallyConstant.iff_eventually_eq x).1 hx (g * k))
  have e4 : ∀ᶠ q : G × G in 𝓝 (g, k), q.1 • x k = g • x k :=
    (continuous_fst.continuousAt (x := (g, k))).eventually
      ((IsLocallyConstant.iff_eventually_eq _).1 (hsmooth (x k)) g)
  filter_upwards [e1, e2, e3, e4] with q h1 h2 h3 h4
  simp only [dx, h1, h2, h3, h4]

omit [MulDistribMulAction G M] in
open Classical in
/-- Extension by `1` of a locally constant function on an open subgroup. -/
theorem isLocallyConstant_extend [IsTopologicalGroup G] {N : Subgroup G} (hN : IsOpen (N : Set G))
    (x : N → M)
    (hx : IsLocallyConstant x) :
    IsLocallyConstant fun g => if hg : g ∈ N then x ⟨g, hg⟩ else 1 := by
  have hNc : IsClosed (N : Set G) := Subgroup.isClosed_of_isOpen N hN
  intro S
  have : (fun g => if hg : g ∈ N then x ⟨g, hg⟩ else 1) ⁻¹' S =
      Subtype.val '' (x ⁻¹' S) ∪ (if (1 : M) ∈ S then (N : Set G)ᶜ else ∅) := by
    ext g
    by_cases hg : g ∈ N
    · simp only [Set.mem_preimage, hg, dite_true, Set.mem_union, Set.mem_image]
      constructor
      · intro h; exact Or.inl ⟨⟨g, hg⟩, h, rfl⟩
      · rintro (⟨y, hy, rfl⟩ | h)
        · exact hy
        · split_ifs at h with h1
          · exact absurd hg h
          · exact h.elim
    · simp only [Set.mem_preimage, hg, dite_false, Set.mem_union, Set.mem_image]
      constructor
      · intro h
        right
        rw [if_pos h]
        exact hg
      · rintro (⟨y, -, rfl⟩ | h)
        · exact absurd y.2 hg
        · split_ifs at h with h1
          · exact h1
          · exact h.elim
  rw [this]
  refine (hN.isOpenMap_subtype_val _ (hx S)).union ?_
  split_ifs
  · exact hNc.isOpen_compl
  · exact isOpen_empty

end Aux

open Classical in
/-- **Inflation–restriction in degree two**: if the restriction of `[f]` to `N = ker φ` is trivial
(and `H¹(N, M) = 0`), then `[f]` is inflated from `H²(Q, M^N)`. -/
theorem exists_map_eq_of_res [IsTopologicalGroup G] (φ : G →* Q) (hφ : Continuous φ)
    (hφs : Function.Surjective φ)
    (ψ : A →* M) (hψ : Function.Injective ψ) (h : ∀ (g : G) (m : A), ψ (φ g • m) = g • ψ m)
    (hfix : ∀ m : M, (∀ n ∈ φ.ker, n • m = m) → m ∈ ψ.range)
    (hsmooth : ∀ m : M, IsLocallyConstant fun g : G => g • m)
    (hH1 : ∀ c : φ.ker → M, IsLocallyConstant c → IsMulCocycle₁ c → IsMulCoboundary₁ c)
    (f : cocycles G M) (x : φ.ker → M) (hx : IsLocallyConstant x)
    (hfx : ∀ n n' : φ.ker, f ((n : G), (n' : G)) = (n : G) • x n' / x (n * n') * x n) :
    ∃ β : ContH2 Q A, map φ hφ ψ h β = mk f := by
  have hφl : IsLocallyConstant φ := (IsLocallyConstant.iff_continuous φ).2 hφ
  have hNo : IsOpen (φ.ker : Set G) := by
    have : (φ.ker : Set G) = φ ⁻¹' {1} := by ext g; simp
    rw [this]
    exact hφl.isOpen_fiber 1
  have hfc := isMulCocycle₂ f
  have hfl := isLocallyConstant f
  -- Step 1: normalise on `N × N`
  let x' : G → M := fun g => if hg : g ∈ φ.ker then x ⟨g, hg⟩ else 1
  have hx' : IsLocallyConstant x' := by convert isLocallyConstant_extend hNo x hx
  let f₁ : G × G → M := f * dx G M x'⁻¹
  have hf₁c : IsMulCocycle₂ f₁ := isMulCocycle₂_mul hfc (isMulCocycle₂_dx _)
  have hf₁l : IsLocallyConstant f₁ := hfl.mul (isLocallyConstant_dx hsmooth hx'.inv)
  have hf₁N : ∀ n ∈ φ.ker, ∀ n' ∈ φ.ker, f₁ (n, n') = 1 := by
    intro n hn n' hn'
    simp only [f₁, Pi.mul_apply, dx_inv, Pi.inv_apply, dx_apply, x', hn, hn', dite_true,
      φ.ker.mul_mem hn hn']
    rw [hfx ⟨n, hn⟩ ⟨n', hn'⟩, mul_inv_eq_one]
    rfl
  -- Step 2: kill `f₁ (g, n)`
  let s : Q → G := fun q => if q = 1 then 1 else Function.surjInv hφs q
  have hs : ∀ q, φ (s q) = q := by
    intro q
    by_cases hq : q = 1
    · simp [s, hq]
    · simp only [s, hq, if_false]
      exact Function.surjInv_eq hφs q
  have hs1 : s 1 = 1 := by simp [s]
  have hsl : IsLocallyConstant fun g => s (φ g) := hφl.comp s
  have hsm : ∀ g, (s (φ g))⁻¹ * g ∈ φ.ker := by
    intro g
    rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
  let y : G → M := fun g => f₁ (s (φ g), (s (φ g))⁻¹ * g)
  have hyl : IsLocallyConstant y := by
    refine hf₁l.comp_continuous ?_
    exact hsl.continuous.prodMk (hsl.continuous.inv.mul continuous_id)
  let f₂ : G × G → M := f₁ * dx G M y
  have hf₂c : IsMulCocycle₂ f₂ := isMulCocycle₂_mul hf₁c (isMulCocycle₂_dx _)
  have hf₂l : IsLocallyConstant f₂ := hf₁l.mul (isLocallyConstant_dx hsmooth hyl)
  have hf₁11 : f₁ (1, 1) = 1 := hf₁N 1 φ.ker.one_mem 1 φ.ker.one_mem
  have hf₂1 : ∀ g, ∀ n ∈ φ.ker, f₂ (g, n) = 1 := by
    intro g n hn
    have hφn : φ n = 1 := hn
    have hφgn : φ (g * n) = φ g := by rw [map_mul, hφn, mul_one]
    have hyn : y n = 1 := by
      simp only [y, hφn, hs1, inv_one, one_mul]
      rw [map_one_fst_of_isMulCocycle₂ hf₁c, hf₁11]
    have key := hf₁c (s (φ g)) ((s (φ g))⁻¹ * g) n
    rw [hf₁N _ (hsm g) n hn, smul_one, one_mul, mul_inv_cancel_left] at key
    have hy1 : y (g * n) = f₁ (s (φ g), (s (φ g))⁻¹ * g * n) := by
      simp only [y, hφgn, mul_assoc]
    change f₁ (g, n) * dx G M y (g, n) = 1
    rw [dx_apply, hyn, smul_one, hy1, ← key]
    change _ * (_ / _ * f₁ (s (φ g), (s (φ g))⁻¹ * g)) = 1
    mul_abel
  -- Step 3: kill `f₂ (n, h)` by Hilbert 90 for `N`
  have hR₂ : ∀ g k, ∀ n ∈ φ.ker, f₂ (g, k * n) = f₂ (g, k) := by
    intro g k n hn
    have := hf₂c g k n
    rw [hf₂1 _ n hn, hf₂1 _ n hn, smul_one, one_mul, one_mul] at this
    exact this.symm
  have hconj : ∀ k, ∀ n ∈ φ.ker, k⁻¹ * n * k ∈ φ.ker := by
    intro k n hn
    rw [MonoidHom.mem_ker] at hn ⊢
    simp [hn]
  let c : Q → φ.ker → M := fun q n => f₂ ((n : G), s q)
  have hcc : ∀ q, IsMulCocycle₁ (c q) := by
    intro q n n'
    have := hf₂c n n' (s q)
    rw [hf₂1 _ _ n'.2, mul_one, show (n' : G) * s q = s q * ((s q)⁻¹ * n' * s q) by group,
      hR₂ _ _ _ (hconj _ _ n'.2)] at this
    exact this
  have hcl : ∀ q, IsLocallyConstant (c q) := fun q =>
    hf₂l.comp_continuous (continuous_subtype_val.prodMk continuous_const)
  let z : Q → M := fun q => if q = 1 then 1 else Classical.choose (hH1 _ (hcl q) (hcc q))
  have hz : ∀ q, ∀ n : φ.ker, (n : G) • z q / z q = c q n := by
    intro q n
    by_cases hq : q = 1
    · simp only [z, hq, if_true, smul_one, div_one, c, hs1]
      exact (hf₂1 _ 1 φ.ker.one_mem).symm
    · simp only [z, hq, if_false]
      exact Classical.choose_spec (hH1 _ (hcl q) (hcc q)) n
  let w : G → M := fun g => z (φ g)
  have hwl : IsLocallyConstant w := hφl.comp z
  have hf₂2 : ∀ n ∈ φ.ker, ∀ k, f₂ (n, k) = n • w k / w k := by
    intro n hn k
    have e := hz (φ k) ⟨n, hn⟩
    simp only [c] at e
    rw [show k = s (φ k) * ((s (φ k))⁻¹ * k) by group, hR₂ _ _ _ (hsm k)]
    simp only [w, mul_inv_cancel_left]
    exact e.symm
  let f₃ : G × G → M := f₂ * dx G M w⁻¹
  have hf₃c : IsMulCocycle₂ f₃ := isMulCocycle₂_mul hf₂c (isMulCocycle₂_dx _)
  have hf₃l : IsLocallyConstant f₃ := hf₂l.mul (isLocallyConstant_dx hsmooth hwl.inv)
  have hw1 : ∀ n ∈ φ.ker, w n = 1 := by
    intro n hn
    simp [w, z, MonoidHom.mem_ker.1 hn]
  have hf₃1 : ∀ g, ∀ n ∈ φ.ker, f₃ (g, n) = 1 := by
    intro g n hn
    have : φ (g * n) = φ g := by rw [map_mul, MonoidHom.mem_ker.1 hn, mul_one]
    simp only [f₃, Pi.mul_apply, dx_inv, Pi.inv_apply, dx_apply, hf₂1 g n hn, hw1 n hn,
      smul_one, w, this]
    mul_abel
  have hf₃2 : ∀ g, ∀ n ∈ φ.ker, f₃ (n, g) = 1 := by
    intro g n hn
    have : φ (n * g) = φ g := by rw [map_mul, MonoidHom.mem_ker.1 hn, one_mul]
    simp only [f₃, Pi.mul_apply, dx_inv, Pi.inv_apply, dx_apply, hf₂2 n hn g, hw1 n hn]
    simp only [w, this]
    mul_abel
  -- Step 4: descend
  obtain ⟨F, hF⟩ := exists_map_eq_of_trivial φ hφ hφs ψ hψ h hfix
    (mkCocycle f₃ hf₃l hf₃c) hf₃1 hf₃2
  refine ⟨mk F, ?_⟩
  rw [map_mk, hF, mk_eq_mk_iff]
  refine ⟨x'⁻¹ * y * w⁻¹, (hx'.inv.mul hyl).mul hwl.inv, ?_⟩
  ext q
  simp only [coe_mkCocycle, f₃, f₂, f₁, dx_inv, dx_mul, Pi.mul_apply, Pi.inv_apply, Pi.div_apply]
  mul_abel

end ContH2
