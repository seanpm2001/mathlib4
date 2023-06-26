/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn

! This file was ported from Lean 3 source module geometry.manifold.cont_mdiff_mfderiv
! leanprover-community/mathlib commit e354e865255654389cc46e6032160238df2e0f40
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Geometry.Manifold.MFDeriv
import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
### Interactions between differentiability, smoothness and manifold derivatives

We give the relation between `mdifferentiable`, `cont_mdiff`, `mfderiv`, `tangent_map`
and related notions.

## Main statements

* `cont_mdiff_on.cont_mdiff_on_tangent_map_within` states that the bundled derivative
  of a `Cⁿ` function in a domain is `Cᵐ` when `m + 1 ≤ n`.
* `cont_mdiff.cont_mdiff_tangent_map` states that the bundled derivative
  of a `Cⁿ` function is `Cᵐ` when `m + 1 ≤ n`.
-/


open Set Function Filter ChartedSpace SmoothManifoldWithCorners Bundle

open scoped Topology Manifold Bundle

/-! ### Definition of smooth functions between manifolds -/


variable {𝕜 : Type _} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type _}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type _} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type _} [TopologicalSpace M] [ChartedSpace H M]
  [Is : SmoothManifoldWithCorners I M]
  -- declare a smooth manifold `M'` over the pair `(E', H')`.
  {E' : Type _}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type _} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type _} [TopologicalSpace M'] [ChartedSpace H' M']
  [I's : SmoothManifoldWithCorners I' M']
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type _}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type _} [TopologicalSpace N] [ChartedSpace G N]
  [Js : SmoothManifoldWithCorners J N]
  -- declare a smooth manifold `N'` over the pair `(F', G')`.
  {F' : Type _}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type _} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type _} [TopologicalSpace N'] [ChartedSpace G' N']
  [J's : SmoothManifoldWithCorners J' N']
  -- declare some additional normed spaces, used for fibers of vector bundles
  {F₁ : Type _}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {F₂ : Type _} [NormedAddCommGroup F₂]
  [NormedSpace 𝕜 F₂]
  -- declare functions, sets, points and smoothness indices
  {f f₁ : M → M'}
  {s s₁ t : Set M} {x : M} {m n : ℕ∞}

-- Porting note: section about deducing differentiability from smoothness moved to
-- `Geometry.Manifold.`MFDeriv`

/-! ### The derivative of a smooth function is smooth -/


section mfderiv

/-- The function that sends `x` to the `y`-derivative of `f(x,y)` at `g(x)` is `C^m` at `x₀`,
where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^n` at `(x₀, g(x₀))` for `n ≥ m + 1` and `g` is `C^m` at `x₀`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
This result is used to show that maps into the 1-jet bundle and cotangent bundle are smooth.
`cont_mdiff_at.mfderiv_id` and `cont_mdiff_at.mfderiv_const` are special cases of this.

This result should be generalized to a `cont_mdiff_within_at` for `mfderiv_within`.
If we do that, we can deduce `cont_mdiff_on.cont_mdiff_on_tangent_map_within` from this.
-/
protected theorem ContMDiffAt.mfderiv {x₀ : N} (f : N → M → M') (g : N → M)
    (hf : ContMDiffAt (J.prod I) I' n (Function.uncurry f) (x₀, g x₀)) (hg : ContMDiffAt J I m g x₀)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt J 𝓘(𝕜, E →L[𝕜] E') m
      (inTangentCoordinates I I' g (fun x => f x (g x)) (fun x => mfderiv I I' (f x) (g x)) x₀)
      x₀ := by
  have h4f : ContinuousAt (fun x => f x (g x)) x₀ :=
    ContinuousAt.comp_of_eq hf.continuousAt (continuousAt_id.prod hg.continuousAt) rfl
  have h4f := h4f.preimage_mem_nhds (extChartAt_source_mem_nhds I' (f x₀ (g x₀)))
  have h3f := contMDiffAt_iff_contMDiffAt_nhds.mp (hf.of_le <| (self_le_add_left 1 m).trans hmn)
  have h2f : ∀ᶠ x₂ in 𝓝 x₀, ContMDiffAt I I' 1 (f x₂) (g x₂) := by
    refine' ((continuousAt_id.prod hg.continuousAt).tendsto.eventually h3f).mono fun x hx => _
    exact hx.comp (g x) (contMDiffAt_const.prod_mk contMDiffAt_id)
  have h2g := hg.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds I (g x₀))
  have :
    ContDiffWithinAt 𝕜 m
      (fun x =>
        fderivWithin 𝕜
          (extChartAt I' (f x₀ (g x₀)) ∘ f ((extChartAt J x₀).symm x) ∘ (extChartAt I (g x₀)).symm)
          (range I) (extChartAt I (g x₀) (g ((extChartAt J x₀).symm x))))
      (range J) (extChartAt J x₀ x₀) := by
    rw [contMDiffAt_iff] at hf hg 
    simp_rw [Function.comp, uncurry, extChartAt_prod, LocalEquiv.prod_coe_symm,
      ModelWithCorners.range_prod] at hf ⊢
    refine' ContDiffWithinAt.fderivWithin _ hg.2 I.unique_diff hmn (mem_range_self _) _
    · simp_rw [extChartAt_to_inv]; exact hf.2
    · rw [← image_subset_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact mem_range_self _
  have :
    ContMDiffAt J 𝓘(𝕜, E →L[𝕜] E') m
      (fun x =>
        fderivWithin 𝕜 (extChartAt I' (f x₀ (g x₀)) ∘ f x ∘ (extChartAt I (g x₀)).symm) (range I)
          (extChartAt I (g x₀) (g x)))
      x₀ := by
    simp_rw [contMDiffAt_iff_source_of_mem_source (mem_chart_source G x₀),
      contMDiffWithinAt_iff_contDiffWithinAt, Function.comp]
    exact this
  have :
    ContMDiffAt J 𝓘(𝕜, E →L[𝕜] E') m
      (fun x =>
        fderivWithin 𝕜
          (extChartAt I' (f x₀ (g x₀)) ∘
            (extChartAt I' (f x (g x))).symm ∘
              writtenInExtChartAt I I' (g x) (f x) ∘
                extChartAt I (g x) ∘ (extChartAt I (g x₀)).symm)
          (range I) (extChartAt I (g x₀) (g x)))
      x₀ := by
    refine' this.congr_of_eventuallyEq _
    filter_upwards [h2g, h2f]
    intro x₂ hx₂ h2x₂
    have :
        ∀ x ∈ (extChartAt I (g x₀)).symm ⁻¹' (extChartAt I (g x₂)).source ∩
          (extChartAt I (g x₀)).symm ⁻¹' (f x₂ ⁻¹' (extChartAt I' (f x₂ (g x₂))).source),
          (extChartAt I' (f x₀ (g x₀)) ∘ (extChartAt I' (f x₂ (g x₂))).symm ∘
            writtenInExtChartAt I I' (g x₂) (f x₂) ∘ extChartAt I (g x₂) ∘
            (extChartAt I (g x₀)).symm) x =
          extChartAt I' (f x₀ (g x₀)) (f x₂ ((extChartAt I (g x₀)).symm x)) := by
      rintro x ⟨hx, h2x⟩
      simp_rw [writtenInExtChartAt, Function.comp_apply]
      rw [(extChartAt I (g x₂)).left_inv hx, (extChartAt I' (f x₂ (g x₂))).left_inv h2x]
    refine' Filter.EventuallyEq.fderivWithin_eq_nhds _
    refine' eventually_of_mem (inter_mem _ _) this
    · exact extChartAt_preimage_mem_nhds' _ _ hx₂ (extChartAt_source_mem_nhds I (g x₂))
    refine' extChartAt_preimage_mem_nhds' _ _ hx₂ _
    exact h2x₂.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds _ _)
  /- The conclusion is equal to the following, when unfolding coord_change of
      `tangent_bundle_core` -/
  have :
    ContMDiffAt J 𝓘(𝕜, E →L[𝕜] E') m
      (fun x =>
        (fderivWithin 𝕜 (extChartAt I' (f x₀ (g x₀)) ∘ (extChartAt I' (f x (g x))).symm) (range I')
              (extChartAt I' (f x (g x)) (f x (g x)))).comp
          ((mfderiv I I' (f x) (g x)).comp
            (fderivWithin 𝕜 (extChartAt I (g x) ∘ (extChartAt I (g x₀)).symm) (range I)
              (extChartAt I (g x₀) (g x)))))
      x₀ := by
    refine' this.congr_of_eventuallyEq _
    filter_upwards [h2g, h2f, h4f]
    intro x₂ hx₂ h2x₂ h3x₂
    symm
    rw [(h2x₂.mdifferentiableAt le_rfl).mfderiv]
    have hI := (contDiffWithinAt_ext_coord_change I (g x₂) (g x₀) <|
      LocalEquiv.mem_symm_trans_source _ hx₂ <|
        mem_extChartAt_source I (g x₂)).differentiableWithinAt le_top
    have hI' :=
      (contDiffWithinAt_ext_coord_change I' (f x₀ (g x₀)) (f x₂ (g x₂)) <|
            LocalEquiv.mem_symm_trans_source _ (mem_extChartAt_source I' (f x₂ (g x₂)))
              h3x₂).differentiableWithinAt le_top
    have h3f := (h2x₂.mdifferentiableAt le_rfl).2
    refine' fderivWithin.comp₃ _ hI' h3f hI _ _ _ _ (I.unique_diff _ <| mem_range_self _)
    · exact fun x _ => mem_range_self _
    · exact fun x _ => mem_range_self _
    ·
      simp_rw [writtenInExtChartAt, Function.comp_apply,
        (extChartAt I (g x₂)).left_inv (mem_extChartAt_source I (g x₂))]
    · simp_rw [Function.comp_apply, (extChartAt I (g x₀)).left_inv hx₂]
  refine' this.congr_of_eventuallyEq _
  filter_upwards [h2g, h4f] with x hx h2x
  rw [inTangentCoordinates_eq]
  · rfl
  · rwa [extChartAt_source] at hx 
  · rwa [extChartAt_source] at h2x 
#align cont_mdiff_at.mfderiv ContMDiffAt.mfderiv

/-- The derivative `D_yf(y)` is `C^m` at `x₀`, where the derivative is taken as a continuous
linear map. We have to assume that `f` is `C^n` at `x₀` for some `n ≥ m + 1`.
We have to insert a coordinate change from `x₀` to `x` to make the derivative sensible.
This is a special case of `cont_mdiff_at.mfderiv` where `f` does not contain any parameters and
`g = id`.
-/
theorem ContMDiffAt.mfderiv_const {x₀ : M} {f : M → M'} (hf : ContMDiffAt I I' n f x₀)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt I 𝓘(𝕜, E →L[𝕜] E') m (inTangentCoordinates I I' id f (mfderiv I I' f) x₀) x₀ :=
  haveI : ContMDiffAt (I.prod I) I' n (fun x : M × M => f x.2) (x₀, x₀) :=
    ContMDiffAt.comp (x₀, x₀) hf contMDiffAt_snd
  this.mfderiv (fun _ => f) id contMDiffAt_id hmn
#align cont_mdiff_at.mfderiv_const ContMDiffAt.mfderiv_const

/-- The function that sends `x` to the `y`-derivative of `f(x,y)` at `g(x)` applied to `g₂(x)` is
`C^n` at `x₀`, where the derivative is taken as a continuous linear map.
We have to assume that `f` is `C^(n+1)` at `(x₀, g(x₀))` and `g` is `C^n` at `x₀`.
We have to insert a coordinate change from `x₀` to `g₁(x)` to make the derivative sensible.

This is  similar to `cont_mdiff_at.mfderiv`, but where the continuous linear map is applied to a
(variable) vector.
-/
theorem ContMDiffAt.mfderiv_apply {x₀ : N'} (f : N → M → M') (g : N → M) (g₁ : N' → N) (g₂ : N' → E)
    (hf : ContMDiffAt (J.prod I) I' n (Function.uncurry f) (g₁ x₀, g (g₁ x₀)))
    (hg : ContMDiffAt J I m g (g₁ x₀)) (hg₁ : ContMDiffAt J' J m g₁ x₀)
    (hg₂ : ContMDiffAt J' 𝓘(𝕜, E) m g₂ x₀) (hmn : m + 1 ≤ n) :
    ContMDiffAt J' 𝓘(𝕜, E') m
      (fun x => inTangentCoordinates I I' g (fun x => f x (g x))
        (fun x => mfderiv I I' (f x) (g x)) (g₁ x₀) (g₁ x) (g₂ x)) x₀ :=
  ((hf.mfderiv f g hg hmn).comp_of_eq hg₁ rfl).clm_apply hg₂
#align cont_mdiff_at.mfderiv_apply ContMDiffAt.mfderiv_apply

end mfderiv

/-! ### The tangent map of a smooth function is smooth -/

section tangentMap

/-- If a function is `C^n` with `1 ≤ n` on a domain with unique derivatives, then its bundled
derivative is continuous. In this auxiliary lemma, we prove this fact when the source and target
space are model spaces in models with corners. The general fact is proved in
`cont_mdiff_on.continuous_on_tangent_map_within`-/
theorem ContMDiffOn.continuousOn_tangentMapWithin_aux {f : H → H'} {s : Set H}
    (hf : ContMDiffOn I I' n f s) (hn : 1 ≤ n) (hs : UniqueMDiffOn I s) :
    ContinuousOn (tangentMapWithin I I' f s) (π (TangentSpace I) ⁻¹' s) := by
  suffices h :
    ContinuousOn
      (fun p : H × E =>
        (f p.fst,
          (fderivWithin 𝕜 (writtenInExtChartAt I I' p.fst f) (I.symm ⁻¹' s ∩ range I)
                ((extChartAt I p.fst) p.fst) :
              E →L[𝕜] E')
            p.snd))
      (Prod.fst ⁻¹' s)
  · have A := (tangentBundleModelSpaceHomeomorph H I).continuous
    rw [continuous_iff_continuousOn_univ] at A 
    have B :=
      ((tangentBundleModelSpaceHomeomorph H' I').symm.continuous.comp_continuousOn h).comp' A
    have :
      univ ∩ (tangentBundleModelSpaceHomeomorph H I) ⁻¹' (Prod.fst ⁻¹' s) =
        π (TangentSpace I) ⁻¹' s :=
      by ext ⟨x, v⟩; simp only [mfld_simps]
    rw [this] at B 
    apply B.congr
    rintro ⟨x, v⟩ hx
    dsimp [tangentMapWithin]
    -- Porting note: was `ext; · rfl`
    refine congr_arg (Sigma.mk _) ?_
    simp only [mfld_simps]
    apply congr_fun
    apply congr_arg
    rw [MDifferentiableWithinAt.mfderivWithin (hf.mdifferentiableOn hn x hx)]
    rfl
  suffices h :
    ContinuousOn
      (fun p : H × E =>
        (fderivWithin 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I p.fst) : E →L[𝕜] E') p.snd)
      (Prod.fst ⁻¹' s)
  · dsimp [writtenInExtChartAt, extChartAt]
    exact (ContinuousOn.comp hf.continuousOn continuous_fst.continuousOn Subset.rfl).prod h
  suffices h : ContinuousOn (fderivWithin 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)) (I '' s)
  · have C := ContinuousOn.comp h I.continuous_toFun.continuousOn Subset.rfl
    have A : Continuous fun q : (E →L[𝕜] E') × E => q.1 q.2 :=
      isBoundedBilinearMapApply.continuous
    have B :
      ContinuousOn
        (fun p : H × E => (fderivWithin 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I p.1), p.2))
        (Prod.fst ⁻¹' s) := by
      apply ContinuousOn.prod _ continuous_snd.continuousOn
      refine C.comp continuousOn_fst ?_
      exact preimage_mono (subset_preimage_image _ _)
    exact A.comp_continuousOn B
  rw [contMDiffOn_iff] at hf 
  let x : H := I.symm (0 : E)
  let y : H' := I'.symm (0 : E')
  have A := hf.2 x y
  simp only [I.image_eq, inter_comm, mfld_simps] at A ⊢
  apply A.continuousOn_fderivWithin _ hn
  convert hs.uniqueDiffOn_target_inter x using 1
  simp only [inter_comm, mfld_simps]
#align cont_mdiff_on.continuous_on_tangent_map_within_aux ContMDiffOn.continuousOn_tangentMapWithin_aux

/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative is
`C^m` when `m+1 ≤ n`. In this auxiliary lemma, we prove this fact when the source and target space
are model spaces in models with corners. The general fact is proved in
`cont_mdiff_on.cont_mdiff_on_tangent_map_within` -/
theorem ContMDiffOn.contMDiffOn_tangentMapWithin_aux {f : H → H'} {s : Set H}
    (hf : ContMDiffOn I I' n f s) (hmn : m + 1 ≤ n) (hs : UniqueMDiffOn I s) :
    ContMDiffOn I.tangent I'.tangent m (tangentMapWithin I I' f s) (π (TangentSpace I) ⁻¹' s) := by
  have m_le_n : m ≤ n := by
    apply le_trans _ hmn
    have : m + 0 ≤ m + 1 := add_le_add_left (zero_le _) _
    simpa only [add_zero] using this
  have one_le_n : 1 ≤ n := by
    apply le_trans _ hmn
    change 0 + 1 ≤ m + 1
    exact add_le_add_right (zero_le _) _
  have U' : UniqueDiffOn 𝕜 (range I ∩ I.symm ⁻¹' s) := by
    intro y hy
    simpa only [UniqueMDiffOn, UniqueMDiffWithinAt, hy.1, inter_comm, mfld_simps] using
      hs (I.symm y) hy.2
  rw [contMDiffOn_iff]
  refine' ⟨hf.continuousOn_tangentMapWithin_aux one_le_n hs, fun p q => _⟩
  have A :
    range I ×ˢ univ ∩
        ((Equiv.sigmaEquivProd H E).symm ∘ fun p : E × E => (I.symm p.fst, p.snd)) ⁻¹'
          (π (TangentSpace I) ⁻¹' s) =
      (range I ∩ I.symm ⁻¹' s) ×ˢ univ :=
    by ext ⟨x, v⟩; simp only [mfld_simps]
  suffices h :
    ContDiffOn 𝕜 m
      (((fun p : H' × E' => (I' p.fst, p.snd)) ∘ Equiv.sigmaEquivProd H' E') ∘
        tangentMapWithin I I' f s ∘
          (Equiv.sigmaEquivProd H E).symm ∘ fun p : E × E => (I.symm p.fst, p.snd))
      ((range I ∩ I.symm ⁻¹' s) ×ˢ univ)
  · simpa using h
  change
    ContDiffOn 𝕜 m
      (fun p : E × E =>
        ((I' (f (I.symm p.fst)), (mfderivWithin I I' f s (I.symm p.fst) : E → E') p.snd) : E' × E'))
      ((range I ∩ I.symm ⁻¹' s) ×ˢ univ)
  -- check that all bits in this formula are `C^n`
  have hf' := contMDiffOn_iff.1 hf
  have A : ContDiffOn 𝕜 m (I' ∘ f ∘ I.symm) (range I ∩ I.symm ⁻¹' s) := by
    simpa only [mfld_simps] using (hf'.2 (I.symm 0) (I'.symm 0)).of_le m_le_n
  have B : ContDiffOn 𝕜 m ((I' ∘ f ∘ I.symm) ∘ Prod.fst) ((range I ∩ I.symm ⁻¹' s) ×ˢ univ) :=
    A.comp contDiff_fst.contDiffOn (prod_subset_preimage_fst _ _)
  suffices C :
    ContDiffOn 𝕜 m
      (fun p : E × E => (fderivWithin 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) p.1 : _) p.2)
      ((range I ∩ I.symm ⁻¹' s) ×ˢ univ)
  · apply ContDiffOn.prod B _
    apply C.congr fun p hp => _
    simp only [mfld_simps] at hp 
    simp only [mfderivWithin, hf.mdifferentiableOn one_le_n _ hp.2, hp.1, if_pos, mfld_simps]
  have D :
    ContDiffOn 𝕜 m (fun x => fderivWithin 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) x)
      (range I ∩ I.symm ⁻¹' s) := by
    have : ContDiffOn 𝕜 n (I' ∘ f ∘ I.symm) (range I ∩ I.symm ⁻¹' s) := by
      simpa only [mfld_simps] using hf'.2 (I.symm 0) (I'.symm 0)
    simpa only [inter_comm] using this.fderivWithin U' hmn
  have := D.comp contDiff_fst.contDiffOn (prod_subset_preimage_fst _ _)
  have := ContDiffOn.prod this contDiff_snd.contDiffOn
  exact is_bounded_bilinearMap_apply.contDiff.comp_contDiffOn this
#align cont_mdiff_on.cont_mdiff_on_tangent_map_within_aux ContMDiffOn.contMDiffOn_tangentMapWithin_aux

/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative
is `C^m` when `m+1 ≤ n`. -/
theorem ContMDiffOn.contMDiffOn_tangentMapWithin (hf : ContMDiffOn I I' n f s) (hmn : m + 1 ≤ n)
    (hs : UniqueMDiffOn I s) :
    ContMDiffOn I.tangent I'.tangent m (tangentMapWithin I I' f s) (π (TangentSpace I) ⁻¹' s) := by
  /- The strategy of the proof is to avoid unfolding the definitions, and reduce by functoriality
    to the case of functions on the model spaces, where we have already proved the result.
    Let `l` and `r` be the charts to the left and to the right, so that we have
    ```
       l^{-1}      f       r
    H --------> M ---> M' ---> H'
    ```
    Then the tangent map `T(r ∘ f ∘ l)` is smooth by a previous result. Consider the composition
    ```
        Tl        T(r ∘ f ∘ l^{-1})         Tr^{-1}
    TM -----> TH -------------------> TH' ---------> TM'
    ```
    where `Tr^{-1}` and `Tl` are the tangent maps of `r^{-1}` and `l`. Writing `Tl` and `Tr^{-1}` as
    composition of charts (called `Dl` and `il` for `l` and `Dr` and `ir` in the proof below), it
    follows that they are smooth. The composition of all these maps is `Tf`, and is therefore smooth
    as a composition of smooth maps.
    -/
  have m_le_n : m ≤ n := by
    apply le_trans _ hmn
    have : m + 0 ≤ m + 1 := add_le_add_left (zero_le _) _
    simpa only [add_zero]
  have one_le_n : 1 ≤ n := by
    apply le_trans _ hmn
    change 0 + 1 ≤ m + 1
    exact add_le_add_right (zero_le _) _
  -- First step: local reduction on the space, to a set `s'` which is contained in chart domains.
  refine' contMDiffOn_of_locally_contMDiffOn fun p hp => _
  have hf' := contMDiffOn_iff.1 hf
  simp only [mfld_simps] at hp 
  let l := chartAt H p.proj
  set Dl := chartAt (ModelProd H E) p with hDl
  let r := chartAt H' (f p.proj)
  let Dr := chartAt (ModelProd H' E') (tangentMapWithin I I' f s p)
  let il := chartAt (ModelProd H E) (tangentMap I I l p)
  let ir := chartAt (ModelProd H' E') (tangentMap I I' (r ∘ f) p)
  let s' := f ⁻¹' r.source ∩ s ∩ l.source
  let s'_lift := π (TangentSpace I) ⁻¹' s'
  let s'l := l.target ∩ l.symm ⁻¹' s'
  let s'l_lift := π (TangentSpace I) ⁻¹' s'l
  rcases continuousOn_iff'.1 hf'.1 r.source r.open_source with ⟨o, o_open, ho⟩
  suffices h : ContMDiffOn I.tangent I'.tangent m (tangentMapWithin I I' f s) s'_lift
  · refine' ⟨π (TangentSpace I) ⁻¹' (o ∩ l.source), _, _, _⟩
    show IsOpen (π (TangentSpace I) ⁻¹' (o ∩ l.source));
    exact (IsOpen.inter o_open l.open_source).preimage (FiberBundle.continuous_proj E _)
    show p ∈ π (TangentSpace I) ⁻¹' (o ∩ l.source)
    · simp
      have : p.proj ∈ f ⁻¹' r.source ∩ s := by simp [hp]
      rw [ho] at this 
      exact this.1
    · have : π (TangentSpace I) ⁻¹' s ∩ π (TangentSpace I) ⁻¹' (o ∩ l.source) = s'_lift := by
        dsimp only; rw [ho]; mfld_set_tac
      rw [this]
      exact h
  /- Second step: check that all functions are smooth, and use the chain rule to write the bundled
    derivative as a composition of a function between model spaces and of charts.
    Convention: statements about the differentiability of `a ∘ b ∘ c` are named `diff_abc`. Statements
    about differentiability in the bundle have a `_lift` suffix. -/
  have U' : UniqueMDiffOn I s' := by
    apply UniqueMDiffOn.inter _ l.open_source
    rw [ho, inter_comm]
    exact hs.inter o_open
  have U'l : UniqueMDiffOn I s'l := U'.uniqueMDiffOn_preimage (mdifferentiable_chart _ _)
  have diff_f : ContMDiffOn I I' n f s' := hf.mono (by mfld_set_tac)
  have diff_r : ContMDiffOn I' I' n r r.source := contMDiffOn_chart
  have diff_rf : ContMDiffOn I I' n (r ∘ f) s' := by
    apply ContMDiffOn.comp diff_r diff_f fun x hx => _
    simp only [mfld_simps] at hx ; simp only [hx, mfld_simps]
  have diff_l : ContMDiffOn I I n l.symm s'l :=
    haveI A : ContMDiffOn I I n l.symm l.target := contMDiffOn_chart_symm
    A.mono (by mfld_set_tac)
  have diff_rfl : ContMDiffOn I I' n (r ∘ f ∘ l.symm) s'l := by
    apply ContMDiffOn.comp diff_rf diff_l
    mfld_set_tac
  have diff_rfl_lift :
    ContMDiffOn I.tangent I'.tangent m (tangentMapWithin I I' (r ∘ f ∘ l.symm) s'l) s'l_lift :=
    diff_rfl.contMDiffOn_tangentMapWithin_aux hmn U'l
  have diff_irrfl_lift :
    ContMDiffOn I.tangent I'.tangent m (ir ∘ tangentMapWithin I I' (r ∘ f ∘ l.symm) s'l) s'l_lift :=
    haveI A : ContMDiffOn I'.tangent I'.tangent m ir ir.source := contMDiffOn_chart
    ContMDiffOn.comp A diff_rfl_lift fun p hp => by simp only [mfld_simps]
  have diff_Drirrfl_lift :
    ContMDiffOn I.tangent I'.tangent m (Dr.symm ∘ ir ∘ tangentMapWithin I I' (r ∘ f ∘ l.symm) s'l)
      s'l_lift := by
    have A : ContMDiffOn I'.tangent I'.tangent m Dr.symm Dr.target := contMDiffOn_chart_symm
    apply ContMDiffOn.comp A diff_irrfl_lift fun p hp => _
    simp only [mfld_simps] at hp 
    simp only [hp, mfld_simps]
  -- conclusion of this step: the composition of all the maps above is smooth
  have diff_DrirrflilDl :
    ContMDiffOn I.tangent I'.tangent m
      (Dr.symm ∘ (ir ∘ tangentMapWithin I I' (r ∘ f ∘ l.symm) s'l) ∘ il.symm ∘ Dl) s'_lift := by
    have A : ContMDiffOn I.tangent I.tangent m Dl Dl.source := contMDiffOn_chart
    have A' : ContMDiffOn I.tangent I.tangent m Dl s'_lift := by
      apply A.mono fun p hp => _
      simp only [mfld_simps] at hp 
      simp only [hp, mfld_simps]
    have B : ContMDiffOn I.tangent I.tangent m il.symm il.target := contMDiffOn_chart_symm
    have C : ContMDiffOn I.tangent I.tangent m (il.symm ∘ Dl) s'_lift :=
      ContMDiffOn.comp B A' fun p hp => by simp only [mfld_simps]
    apply ContMDiffOn.comp diff_Drirrfl_lift C fun p hp => _
    simp only [mfld_simps] at hp 
    simp only [hp, TotalSpace.proj, mfld_simps]
  /- Third step: check that the composition of all the maps indeed coincides with the derivative we
    are looking for -/
  have eq_comp :
    ∀ q ∈ s'_lift,
      tangentMapWithin I I' f s q =
        (Dr.symm ∘ ir ∘ tangentMapWithin I I' (r ∘ f ∘ l.symm) s'l ∘ il.symm ∘ Dl) q := by
    intro q hq
    simp only [mfld_simps] at hq 
    have U'q : UniqueMDiffWithinAt I s' q.1 := by apply U'; simp only [hq, s', mfld_simps]
    have U'lq : UniqueMDiffWithinAt I s'l (Dl q).1 := by apply U'l; simp only [hq, s'l, mfld_simps]
    have A :
      tangentMapWithin I I' ((r ∘ f) ∘ l.symm) s'l (il.symm (Dl q)) =
        tangentMapWithin I I' (r ∘ f) s' (tangentMapWithin I I l.symm s'l (il.symm (Dl q))) := by
      refine' tangentMapWithin_comp_at (il.symm (Dl q)) _ _ (fun p hp => _) U'lq
      · apply diff_rf.mdifferentiableOn one_le_n
        simp only [hq, mfld_simps]
      · apply diff_l.mdifferentiableOn one_le_n
        simp only [hq, mfld_simps]
      · simp only [mfld_simps] at hp ; simp only [hp, mfld_simps]
    have B : tangentMapWithin I I l.symm s'l (il.symm (Dl q)) = q := by
      have :
        tangentMapWithin I I l.symm s'l (il.symm (Dl q)) = tangentMap I I l.symm (il.symm (Dl q)) :=
        by
        refine' tangentMapWithin_eq_tangentMap U'lq _
        refine' mdifferentiableAt_atlas_symm _ (chart_mem_atlas _ _) _
        simp only [hq, mfld_simps]
      rw [this, tangentMap_chart_symm, hDl]
      · simp only [hq, mfld_simps]
        have : q ∈ (chartAt (ModelProd H E) p).source := by simp only [hq, mfld_simps]
        exact (chartAt (ModelProd H E) p).left_inv this
      · simp only [hq, mfld_simps]
    have C :
      tangentMapWithin I I' (r ∘ f) s' q =
        tangentMapWithin I' I' r r.source (tangentMapWithin I I' f s' q) := by
      refine' tangentMapWithin_comp_at q _ _ (fun r hr => _) U'q
      · apply diff_r.mdifferentiableOn one_le_n
        simp only [hq, mfld_simps]
      · apply diff_f.mdifferentiableOn one_le_n
        simp only [hq, mfld_simps]
      · simp only [s', mfld_simps] at hr 
        simp only [hr, mfld_simps]
    have D :
      Dr.symm (ir (tangentMapWithin I' I' r r.source (tangentMapWithin I I' f s' q))) =
        tangentMapWithin I I' f s' q := by
      have A :
        tangentMapWithin I' I' r r.source (tangentMapWithin I I' f s' q) =
          tangentMap I' I' r (tangentMapWithin I I' f s' q) := by
        apply tangentMapWithin_eq_tangentMap
        · apply IsOpen.uniqueMDiffWithinAt _ r.open_source; simp [hq]
        · refine' mdifferentiableAt_atlas _ (chart_mem_atlas _ _) _
          simp only [hq, mfld_simps]
      have : f p.proj = (tangentMapWithin I I' f s p).1 := rfl
      rw [A]
      dsimp [r, Dr]
      rw [this, tangentMap_chart]
      · simp only [hq, mfld_simps]
        have :
          tangentMapWithin I I' f s' q ∈
            (chartAt (ModelProd H' E') (tangentMapWithin I I' f s p)).source :=
          by simp only [hq, mfld_simps]
        exact (chartAt (ModelProd H' E') (tangentMapWithin I I' f s p)).left_inv this
      · simp only [hq, mfld_simps]
    have E : tangentMapWithin I I' f s' q = tangentMapWithin I I' f s q := by
      refine' tangentMapWithin_subset (by mfld_set_tac) U'q _
      apply hf.mdifferentiableOn one_le_n
      simp only [hq, mfld_simps]
    simp only [(· ∘ ·), A, B, C, D, E.symm]
  exact diff_DrirrflilDl.congr eq_comp
#align cont_mdiff_on.cont_mdiff_on_tangent_map_within ContMDiffOn.contMDiffOn_tangentMapWithin

/-- If a function is `C^n` on a domain with unique derivatives, with `1 ≤ n`, then its bundled
derivative is continuous there. -/
theorem ContMDiffOn.continuousOn_tangentMapWithin (hf : ContMDiffOn I I' n f s) (hmn : 1 ≤ n)
    (hs : UniqueMDiffOn I s) :
    ContinuousOn (tangentMapWithin I I' f s) (π (TangentSpace I) ⁻¹' s) :=
  haveI :
    ContMDiffOn I.tangent I'.tangent 0 (tangentMapWithin I I' f s) (π (TangentSpace I) ⁻¹' s) :=
    hf.contMDiffOn_tangentMapWithin hmn hs
  this.continuousOn
#align cont_mdiff_on.continuous_on_tangent_map_within ContMDiffOn.continuousOn_tangentMapWithin

/-- If a function is `C^n`, then its bundled derivative is `C^m` when `m+1 ≤ n`. -/
theorem ContMDiff.contMDiff_tangentMap (hf : ContMDiff I I' n f) (hmn : m + 1 ≤ n) :
    ContMDiff I.tangent I'.tangent m (tangentMap I I' f) := by
  rw [← contMDiffOn_univ] at hf ⊢
  convert hf.contMDiffOn_tangentMapWithin hmn uniqueMDiffOn_univ
  rw [tangentMapWithin_univ]
#align cont_mdiff.cont_mdiff_tangent_map ContMDiff.contMDiff_tangentMap

/-- If a function is `C^n`, with `1 ≤ n`, then its bundled derivative is continuous. -/
theorem ContMDiff.continuous_tangentMap (hf : ContMDiff I I' n f) (hmn : 1 ≤ n) :
    Continuous (tangentMap I I' f) := by
  rw [← contMDiffOn_univ] at hf 
  rw [continuous_iff_continuousOn_univ]
  convert hf.continuousOn_tangentMapWithin hmn uniqueMDiffOn_univ
  rw [tangentMapWithin_univ]
#align cont_mdiff.continuous_tangent_map ContMDiff.continuous_tangentMap

end tangentMap

namespace TangentBundle

variable (I M)

open Bundle

/-- The derivative of the zero section of the tangent bundle maps `⟨x, v⟩` to `⟨⟨x, 0⟩, ⟨v, 0⟩⟩`.

Note that, as currently framed, this is a statement in coordinates, thus reliant on the choice
of the coordinate system we use on the tangent bundle.

However, the result itself is coordinate-dependent only to the extent that the coordinates
determine a splitting of the tangent bundle.  Moreover, there is a canonical splitting at each
point of the zero section (since there is a canonical horizontal space there, the tangent space
to the zero section, in addition to the canonical vertical space which is the kernel of the
derivative of the projection), and this canonical splitting is also the one that comes from the
coordinates on the tangent bundle in our definitions. So this statement is not as crazy as it
may seem.

TODO define splittings of vector bundles; state this result invariantly. -/
theorem tangentMap_tangentBundle_pure (p : TangentBundle I M) :
    tangentMap I I.tangent (zeroSection (TangentSpace I)) p = ⟨⟨p.proj, 0⟩, ⟨p.2, 0⟩⟩ := by
  rcases p with ⟨x, v⟩
  have N : I.symm ⁻¹' (chartAt H x).target ∈ 𝓝 (I ((chartAt H x) x)) := by
    apply IsOpen.mem_nhds
    apply (LocalHomeomorph.open_target _).preimage I.continuous_inv_fun
    simp only [mfld_simps]
  have A : MDifferentiableAt I I.tangent (fun x => @total_space_mk M (TangentSpace I) x 0) x :=
    haveI : Smooth I (I.prod 𝓘(𝕜, E)) (zero_section (TangentSpace I : M → Type _)) :=
      Bundle.smooth_zeroSection 𝕜 (TangentSpace I : M → Type _)
    this.mdifferentiableAt
  have B :
    fderivWithin 𝕜 (fun x' : E => (x', (0 : E))) (Set.range ⇑I) (I ((chartAt H x) x)) v = (v, 0) :=
    by
    rw [fderivWithin_eq_fderiv, DifferentiableAt.fderiv_prod]
    · simp
    · exact differentiableAt_id'
    · exact differentiableAt_const _
    · exact ModelWithCorners.uniqueDiffAt_image I
    · exact differentiableAt_id'.prod (differentiableAt_const _)
  simp only [Bundle.zeroSection, tangentMap, mfderiv, total_space.proj_mk, A, if_pos, chartAt,
    FiberBundle.chartedSpace_chartAt, TangentBundle.trivializationAt_apply, tangentBundleCore,
    Function.comp, ContinuousLinearMap.map_zero, mfld_simps]
  rw [← fderivWithin_inter N] at B 
  rw [← fderivWithin_inter N, ← B]
  congr 2
  refine' fderivWithin_congr (fun y hy => _) _
  · simp only [mfld_simps] at hy 
    simp only [hy, Prod.mk.inj_iff, mfld_simps]
  · simp only [Prod.mk.inj_iff, mfld_simps]
#align tangent_bundle.tangent_map_tangent_bundle_pure TangentBundle.tangentMap_tangentBundle_pure

end TangentBundle

namespace ContMDiffMap

-- These helpers for dot notation have been moved here from `geometry.manifold.cont_mdiff_map`
-- to avoid needing to import `geometry.manifold.cont_mdiff_mfderiv` there.
-- (However as a consequence we import `geometry.manifold.cont_mdiff_map` here now.)
-- They could be moved to another file (perhaps a new file) if desired.
open scoped Manifold

protected theorem mdifferentiable' (f : C^n⟮I, M; I', M'⟯) (hn : 1 ≤ n) : MDifferentiable I I' f :=
  f.contMDiff.mdifferentiable hn
#align cont_mdiff_map.mdifferentiable' ContMDiffMap.mdifferentiable'

protected theorem mdifferentiable (f : C^∞⟮I, M; I', M'⟯) : MDifferentiable I I' f :=
  f.contMDiff.mdifferentiable le_top
#align cont_mdiff_map.mdifferentiable ContMDiffMap.mdifferentiable

protected theorem mdifferentiableAt (f : C^∞⟮I, M; I', M'⟯) {x} : MDifferentiableAt I I' f x :=
  f.mdifferentiable x
#align cont_mdiff_map.mdifferentiable_at ContMDiffMap.mdifferentiableAt

end ContMDiffMap
