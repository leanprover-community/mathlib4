/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Geometry.Manifold.PoincareConjecture
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Glouglou

All this should probably be extended to `Within` versions, as we will need them when defining
things on manifolds possibly with boundary.

-/

noncomputable section

section LieBracketVectorField

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The Lie bracket `[V, W] (x)` of two vector fields at a point, defined as
`DW(x) (V x) - DV(x) (W x)`. -/
def lieBracket (V W : E → E) (x : E) : E :=
  fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)

lemma lieBracket_eq (V W : E → E) :
    lieBracket 𝕜 V W = fun x ↦ fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x) := rfl

/-- The Lie derivative of a function with respect to a vector field `L_V f(x)`. This is just
`Df(x) (V x)`, but the notation emphasizes how this is linear in `f`.-/
def lieDeriv (V : E → E) (f : E → F) (x : E) : F := fderiv 𝕜 f x (V x)

lemma lieDeriv_eq (V : E → E) (f : E → F) : lieDeriv 𝕜 V f = fun x ↦ fderiv 𝕜 f x (V x) := rfl

/-- The equation `L_V L_W f - L_W L_V f = L_{[V, W]} f`, which is the motivation for the definition
of the Lie bracket. This requires the second derivative of `f` to be symmetric. -/
lemma sub_eq_lieDeriv_lieBracket (V W : E → E) (f : E → F) (x : E)
    (hf : ∀ v w, fderiv 𝕜 (fderiv 𝕜 f) x v w = fderiv 𝕜 (fderiv 𝕜 f) x w v)
    (h'f : ContDiffAt 𝕜 2 f x) (hV : DifferentiableAt 𝕜 V x) (hW : DifferentiableAt 𝕜 W x) :
    lieDeriv 𝕜 V (lieDeriv 𝕜 W f) x - lieDeriv 𝕜 W (lieDeriv 𝕜 V f) x =
      lieDeriv 𝕜 (lieBracket 𝕜 V W) f x := by
  have A : DifferentiableAt 𝕜 (fderiv 𝕜 f) x :=
    (h'f.fderiv_right (m := 1) le_rfl).differentiableAt le_rfl
  simp only [lieDeriv_eq, lieBracket_eq]
  rw [fderiv_clm_apply A hV, fderiv_clm_apply A hW]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply, map_sub, hf]
  abel

/-- The pullback of a vector field under a function, defined
as `(f^* V) (x) = Df(x)^{-1} (V (f x))`. If `Df(x)` is not invertible, we use the junk value `0`.
-/
def pullback (f : E → F) (V : F → F) (x : E) : E := (fderiv 𝕜 f x).inverse (V (f x))

variable {𝕜}

lemma pullback_eq_of_fderiv_eq
    {f : E → F} {M : E ≃L[𝕜] F} {x : E} (hf : M = fderiv 𝕜 f x) (V : F → F) :
    pullback 𝕜 f V x = M.symm (V (f x)) := by simp [pullback, ← hf]

lemma pullback_eq_of_not_exists {f : E → F} {x : E}
    (h : ¬(∃ M : E ≃L[𝕜] F, M = fderiv 𝕜 f x)) (V : F → F) :
    pullback 𝕜 f V x = 0 := by simp [pullback, h]

open scoped Topology Filter

theorem fderiv.comp'
    {f : E → F} {g : F → G} (x : E) (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun y ↦ g (f y)) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) :=
  fderiv.comp x hg hf

lemma fderiv_pullback (f : E → F) (V : F → F) (x : E) (h'f : ∃ M : E ≃L[𝕜] F, M = fderiv 𝕜 f x) :
    fderiv 𝕜 f x (pullback 𝕜 f V x) = V (f x) := by
  rcases h'f with ⟨M, hM⟩
  simp [pullback_eq_of_fderiv_eq hM, ← hM]

/-- The equation `L_{f^* V} (g ∘ f) (x) = (L_V g) (f x)`, which is essentially the definition of
the pullback.
Note that `hf` can probably be removed, as it's implied by `h'f`.
-/
lemma lieDeriv_pullback (f : E → F) (V : F → F) (g : F → G) (x : E)
    (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableAt 𝕜 f x) (h'f : ∃ M : E ≃L[𝕜] F, M = fderiv 𝕜 f x) :
    lieDeriv 𝕜 (pullback 𝕜 f V) (g ∘ f) x = lieDeriv 𝕜 V g (f x) := by
  rcases h'f with ⟨M, hM⟩
  rw [lieDeriv, lieDeriv, fderiv.comp _ hg hf]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [fderiv_pullback]
  exact ⟨M, hM⟩

open Set

variable [CompleteSpace E]

/-- If a `C^2` map has an invertible derivative at a point, then nearby derivatives can be written
as continuous linear equivs, which depend in a `C^1` way on the point, as well as their inverse, and
moreover one can compute the derivative of the inverse. -/
lemma exists_continuousLinearEquiv_fderiv_symm_eq
    (f : E → F) (x : E) (h'f : ContDiffAt 𝕜 2 f x) (hf : ∃ M : E ≃L[𝕜] F, M = fderiv 𝕜 f x) :
    ∃ N : E → (E ≃L[𝕜] F), ContDiffAt 𝕜 1 (fun y ↦ (N y : E →L[𝕜] F)) x
    ∧ ContDiffAt 𝕜 1 (fun y ↦ ((N y).symm : F →L[𝕜] E)) x
    ∧ (∀ᶠ y in 𝓝 x, N y = fderiv 𝕜 f y)
    ∧ ∀ v, fderiv 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) x v
      = - (N x).symm  ∘L ((fderiv 𝕜 (fderiv 𝕜 f) x v)) ∘L (N x).symm := by
  classical
  rcases hf with ⟨M, hM⟩
  let U := {y | ∃ (N : E ≃L[𝕜] F), N = fderiv 𝕜 f y}
  have hU : U ∈ 𝓝 x := by
    have I : range ((↑) : (E ≃L[𝕜] F) → E →L[𝕜] F) ∈ 𝓝 (fderiv 𝕜 f x) := by
      rw [← hM]
      exact M.nhds
    have : ContinuousAt (fderiv 𝕜 f) x := (h'f.fderiv_right (m := 1) le_rfl).continuousAt
    exact this I
  let N : E → (E ≃L[𝕜] F) := fun x ↦ if h : x ∈ U then h.choose else M
  have eN : (fun y ↦ (N y : E →L[𝕜] F)) =ᶠ[𝓝 x] fun y ↦ fderiv 𝕜 f y := by
    filter_upwards [hU] with y hy
    simpa only [hy, ↓reduceDIte, N] using Exists.choose_spec hy
  have hN : ContDiffAt 𝕜 1 (fun y ↦ (N y : E →L[𝕜] F)) x := by
    have : ContDiffAt 𝕜 1 (fun y ↦ fderiv 𝕜 f y) x := h'f.fderiv_right (m := 1) (le_rfl)
    apply this.congr_of_eventuallyEq eN
  have hN' : ContDiffAt 𝕜 1 (fun y ↦ ((N y).symm : F →L[𝕜] E)) x := by
    have : ContDiffAt 𝕜 1 (ContinuousLinearMap.inverse ∘ (fun y ↦ (N y : E →L[𝕜] F))) x :=
      (contDiffAt_map_inverse (N x)).comp x hN
    convert this with y
    simp only [Function.comp_apply, ContinuousLinearMap.inverse_equiv]
  refine ⟨N, hN, hN', eN, fun v ↦ ?_⟩
  have A' y : ContinuousLinearMap.compL 𝕜 F E F (N y : E →L[𝕜] F) ((N y).symm : F →L[𝕜] E)
      = ContinuousLinearMap.id 𝕜 F := by ext; simp
  have : fderiv 𝕜 (fun y ↦ ContinuousLinearMap.compL 𝕜 F E F (N y : E →L[𝕜] F)
      ((N y).symm : F →L[𝕜] E)) x v = 0 := by simp [A']
  have I : (N x : E →L[𝕜] F) ∘L (fderiv 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) x v) =
      - (fderiv 𝕜 (fun y ↦ (N y : E →L[𝕜] F)) x v) ∘L ((N x).symm : F →L[𝕜] E) := by
    rw [ContinuousLinearMap.fderiv_of_bilinear _ (hN.differentiableAt le_rfl)
      (hN'.differentiableAt le_rfl)] at this
    simpa [eq_neg_iff_add_eq_zero] using this
  have B (M : F →L[𝕜] E) : M = ((N x).symm : F →L[𝕜] E) ∘L ((N x) ∘L M) := by
    ext; simp
  rw [B (fderiv 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) x v), I]
  simp only [ContinuousLinearMap.comp_neg, neg_inj, eN.fderiv_eq]

/-- The Lie bracket commutes with taking pullbacks. This requires the function to have symmetric
second derivative. -/
lemma lieBracket_pullback (f : E → F) (V W : F → F) (x : E)
    (hf : ∀ v w, fderiv 𝕜 (fderiv 𝕜 f) x v w = fderiv 𝕜 (fderiv 𝕜 f) x w v)
    (h'f : ContDiffAt 𝕜 2 f x) (hV : DifferentiableAt 𝕜 V (f x)) (hW : DifferentiableAt 𝕜 W (f x)) :
    lieBracket 𝕜 (pullback 𝕜 f V) (pullback 𝕜 f W) x = pullback 𝕜 f (lieBracket 𝕜 V W) x := by
  by_cases h : ∃ M : E ≃L[𝕜] F, M = fderiv 𝕜 f x; swap
  · simp [pullback_eq_of_not_exists h, lieBracket_eq]
  rcases exists_continuousLinearEquiv_fderiv_symm_eq f x h'f h
    with ⟨M, -, M_symm_smooth, hM, M_diff⟩
  have hMx : M x = fderiv 𝕜 f x := (mem_of_mem_nhds hM :)
  have AV : fderiv 𝕜 (pullback 𝕜 f V) x =
      fderiv 𝕜 (fun y ↦ ((M y).symm : F →L[𝕜] E) (V (f y))) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hM] with y hy using pullback_eq_of_fderiv_eq hy _
  have AW : fderiv 𝕜 (pullback 𝕜 f W) x =
      fderiv 𝕜 (fun y ↦ ((M y).symm : F →L[𝕜] E) (W (f y))) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hM] with y hy using pullback_eq_of_fderiv_eq hy _
  have Af : DifferentiableAt 𝕜 f x := h'f.differentiableAt one_le_two
  simp only [lieBracket_eq, pullback_eq_of_fderiv_eq hMx, map_sub, AV, AW]
  rw [fderiv_clm_apply, fderiv_clm_apply]
  · simp [fderiv.comp' x hW Af, ← hMx,
      fderiv.comp' x hV Af, M_diff, hf]
  · exact M_symm_smooth.differentiableAt le_rfl
  · exact hV.comp x Af
  · exact M_symm_smooth.differentiableAt le_rfl
  · exact hW.comp x Af

end LieBracketVectorField

open Bundle Filter Function

open scoped Bundle Manifold

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {I : ModelWithCorners 𝕜 E H}
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {I' : ModelWithCorners 𝕜 E' H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M']

variable (I I' M M') in
/-- The tangent bundle of a product is canonically isomorphic to the product of the tangent
bundles. -/
@[simps] def equivTangentBundleProd :
    TangentBundle (I.prod I') (M × M') ≃ (TangentBundle I M) × (TangentBundle I' M') where
  toFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  invFun p := ⟨(p.1.1, p.2.1), (p.1.2, p.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma equivTangentBundleProd_eq_tangentMap_prod_tangentMap :
    equivTangentBundleProd I I' M M' = fun (p : TangentBundle (I.prod I') (M × M')) ↦
      (tangentMap (I.prod I') I Prod.fst p, tangentMap (I.prod I') I' Prod.snd p) := by
  simp only [tangentMap_prod_fst, tangentMap_prod_snd]; rfl

lemma smooth_equivTangentBundleProd :
    Smooth (I.prod I').tangent (I.tangent.prod I'.tangent) (equivTangentBundleProd I I' M M') := by
  rw [equivTangentBundleProd_eq_tangentMap_prod_tangentMap]
  exact smooth_fst.tangentMap.prod_mk smooth_snd.tangentMap

open scoped Topology

/-- The canonical equivalence between the product of tangent bundles and the tangent bundle of a
product is smooth. -/
lemma smooth_equivTangentBundleProd_symm :
    Smooth (I.tangent.prod I'.tangent) (I.prod I').tangent
      (equivTangentBundleProd I I' M M').symm := by
  /- I am really unhappy with this proof, but I haven't found a more functorial one, so I have to
  unfold more definitions than I'd like. The argument goes as follows: since we're looking at a
  map into a vector bundle whose basis map is smooth, it suffices to check the smoothness of the
  second coordinate. We're in a product, so it suffices to check that each projection is smooth.
  We notice that the first projection is the composition of the tangent map to `(x : M) ↦ (x, b.2)`
  with obvious extensions or restrictions, and the tangent map to a smooth map is smooth, so we're
  done.
  The issue is with checking differentiability everywhere (to justify that the derivative of a
  product is the product of the derivatives), and writing down things.
  -/
  simp only [Smooth, ContMDiff, Prod.forall]
  intro a b
  rw [contMDiffAt_totalSpace]
  simp only [equivTangentBundleProd, Equiv.coe_fn_symm_mk, TangentBundle.trivializationAt_apply,
    PartialHomeomorph.extend, prodChartedSpace_chartAt, PartialHomeomorph.prod_toPartialEquiv,
    PartialEquiv.prod, PartialHomeomorph.toFun_eq_coe, PartialHomeomorph.coe_coe_symm,
    modelWithCorners_prod_toPartialEquiv, ModelWithCorners.toPartialEquiv_coe,
    ModelWithCorners.toPartialEquiv_coe_symm, ModelWithCorners.source_eq, Set.univ_prod_univ,
    ModelWithCorners.target_eq, PartialEquiv.coe_trans, comp_def, PartialEquiv.coe_trans_symm,
    PartialEquiv.coe_symm_mk, modelWithCorners_prod_coe, comp_apply]
  refine ⟨?_, (contMDiffAt_prod_module_iff _).2 ⟨?_, ?_⟩⟩
  · exact ContMDiffAt.prod_map (smoothAt_proj (TangentSpace I)) (smoothAt_proj (TangentSpace I'))
  · -- check that, in the fiber, the first projection is smooth in charts
    -- for this, write down a map which is obviously smooth (`C` below) and then check that the two
    -- maps coincide, up to obvious compositions.
    have C : ContMDiffAt I.tangent (I.prod I').tangent ⊤ (fun (p : TangentBundle I M)
        ↦ (⟨(p.1, b.1), (p.2, 0)⟩ : TangentBundle (I.prod I') (M × M'))) a := by
      let f : M → M × M' := fun m ↦ (m, b.1)
      have A : Smooth I.tangent (I.prod I').tangent (tangentMap I (I.prod I') f) := by
        apply Smooth.tangentMap
        exact smooth_id.prod_mk smooth_const
      have B : tangentMap I (I.prod I') f = fun p ↦ ⟨(p.1, b.1), (p.2, 0)⟩ := by
        ext p : 1
        exact tangentMap_prod_left I I'
      rw [B] at A
      exact A a
    have Z := ((contMDiffAt_totalSpace _ _).1 C).2
    simp only [modelWithCornersSelf_prod, TangentBundle.trivializationAt_apply,
      PartialHomeomorph.extend, prodChartedSpace_chartAt, PartialHomeomorph.prod_toPartialEquiv,
      PartialEquiv.prod, PartialHomeomorph.toFun_eq_coe, PartialHomeomorph.coe_coe_symm,
      modelWithCorners_prod_toPartialEquiv, ModelWithCorners.toPartialEquiv_coe,
      ModelWithCorners.toPartialEquiv_coe_symm, ModelWithCorners.source_eq, Set.univ_prod_univ,
      ModelWithCorners.target_eq, PartialEquiv.coe_trans, comp_def, PartialEquiv.coe_trans_symm,
      PartialEquiv.coe_symm_mk, modelWithCorners_prod_coe, comp_apply] at Z
    have D1 : ContMDiff (𝓘(𝕜, E × E')) (𝓘(𝕜, E)) ⊤ (Prod.fst : E × E' → E) := by
      rw [contMDiff_iff_contDiff]; exact contDiff_fst
    have D2 : ContMDiffAt (I.tangent.prod I'.tangent) I.tangent ⊤ Prod.fst (a, b) := smoothAt_fst
    have U' := (ContMDiffAt.comp a D1.contMDiffAt Z).comp (a, b) D2
    apply U'.congr_of_eventuallyEq
    filter_upwards [chart_source_mem_nhds (ModelProd (ModelProd H E) (ModelProd H' E')) (a, b)]
      with p hp
    clear U' D1 D2 C Z
    simp only [prodChartedSpace_chartAt, PartialHomeomorph.prod_toPartialEquiv,
      PartialEquiv.prod_source, Set.mem_prod, TangentBundle.mem_chart_source_iff] at hp
    let φ (x : E) := I ((chartAt H a.proj) ((chartAt H p.1.proj).symm (I.symm x)))
    have D0 : DifferentiableWithinAt 𝕜 φ (Set.range I) (I ((chartAt H p.1.proj) p.1.proj)) := by
      apply ContDiffWithinAt.differentiableWithinAt (n := ⊤) _ le_top
      apply contDiffWithinAt_ext_coord_change
      simp [hp.1]
    have D (w : TangentBundle I' M') :
        DifferentiableWithinAt 𝕜 (φ ∘ (Prod.fst : E × E' → E)) (Set.range (Prod.map ↑I ↑I'))
        (I ((chartAt H p.1.proj) p.1.proj), I' ((chartAt H' w.proj) w.proj)) :=
      DifferentiableWithinAt.comp (t := Set.range I) _ (by exact D0)
        differentiableWithinAt_fst (by simp [mapsTo_fst_prod])
    let φ' (x : E') := I' ((chartAt H' b.proj) ((chartAt H' b.proj).symm (I'.symm x)))
    have D0' : DifferentiableWithinAt 𝕜 φ' (Set.range I')
        (I' ((chartAt H' b.proj) b.proj)) := by
      apply ContDiffWithinAt.differentiableWithinAt (n := ⊤) _ le_top
      apply contDiffWithinAt_ext_coord_change
      simp
    have D' : DifferentiableWithinAt 𝕜 (φ' ∘ Prod.snd) (Set.range (Prod.map I I'))
        (I ((chartAt H p.1.proj) p.1.proj), I' ((chartAt H' b.proj) b.proj)) :=
      DifferentiableWithinAt.comp (t := Set.range I') _ (by exact D0') differentiableWithinAt_snd
        (by simp [mapsTo_snd_prod])
    have U w : UniqueDiffWithinAt 𝕜 (Set.range (Prod.map I I'))
        (I ((chartAt H p.1.proj) p.1.proj), I' w) := by
      simp only [Set.range_prod_map]
      apply UniqueDiffWithinAt.prod
      · exact ModelWithCorners.uniqueDiffWithinAt_image I
      · exact ModelWithCorners.uniqueDiffWithinAt_image I'
    simp only [Set.range_prod_map, ContinuousLinearMap.prod_apply, comp_def, comp_apply]
    rw [DifferentiableWithinAt.fderivWithin_prod (by exact D _) ?_ (U _)]; swap
    · let φ'' (x : E') := I' ((chartAt H' b.proj) ((chartAt H' p.2.proj).symm (I'.symm x)))
      have D0' : DifferentiableWithinAt 𝕜 φ'' (Set.range I')
          (I' ((chartAt H' p.2.proj) p.2.proj)) := by
        apply ContDiffWithinAt.differentiableWithinAt (n := ⊤) _ le_top
        apply contDiffWithinAt_ext_coord_change
        simp [hp.2]
      have D' : DifferentiableWithinAt 𝕜 (φ'' ∘ Prod.snd) (Set.range (Prod.map I I'))
          (I ((chartAt H p.1.proj) p.1.proj), I' ((chartAt H' p.2.proj) p.2.proj)) :=
        DifferentiableWithinAt.comp (t := Set.range I') _ (by exact D0')
          differentiableWithinAt_snd (by simp [mapsTo_snd_prod])
      exact D'
    rw [DifferentiableWithinAt.fderivWithin_prod (by exact D _) (by exact D') (U _)]
    change fderivWithin 𝕜 (φ ∘ Prod.fst) _ _ _ = fderivWithin 𝕜 (φ ∘ Prod.fst) _ _ _
    rw [Set.range_prod_map] at U ⊢
    rw [fderivWithin.comp _ (by exact D0) differentiableWithinAt_fst mapsTo_fst_prod (U _),
      fderivWithin.comp _ (by exact D0) differentiableWithinAt_fst mapsTo_fst_prod (U _)]
    simp [fderivWithin_fst, U]
  · -- check that, in the fiber, the second projection is smooth in charts
    -- for this, write down a map which is obviously smooth (`C` below) and then check that the two
    -- maps coincide, up to obvious compositions.
    have C : ContMDiffAt I'.tangent (I.prod I').tangent ⊤ (fun (p : TangentBundle I' M')
        ↦ (⟨(a.1, p.1), (0, p.2)⟩ : TangentBundle (I.prod I') (M × M'))) b := by
      let f : M' → M × M' := fun m ↦ (a.1, m)
      have A : Smooth I'.tangent (I.prod I').tangent (tangentMap I' (I.prod I') f) := by
        apply Smooth.tangentMap
        exact smooth_const.prod_mk smooth_id
      have B : tangentMap I' (I.prod I') f = fun p ↦ ⟨(a.1, p.1), (0, p.2)⟩ := by
        ext p : 1
        exact tangentMap_prod_right I I'
      rw [B] at A
      exact A b
    have Z := ((contMDiffAt_totalSpace _ _).1 C).2
    simp only [modelWithCornersSelf_prod, TangentBundle.trivializationAt_apply,
      PartialHomeomorph.extend, prodChartedSpace_chartAt, PartialHomeomorph.prod_toPartialEquiv,
      PartialEquiv.prod, PartialHomeomorph.toFun_eq_coe, PartialHomeomorph.coe_coe_symm,
      modelWithCorners_prod_toPartialEquiv, ModelWithCorners.toPartialEquiv_coe,
      ModelWithCorners.toPartialEquiv_coe_symm, ModelWithCorners.source_eq, Set.univ_prod_univ,
      ModelWithCorners.target_eq, PartialEquiv.coe_trans, comp_def, PartialEquiv.coe_trans_symm,
      PartialEquiv.coe_symm_mk, modelWithCorners_prod_coe, comp_apply] at Z
    have D1 : ContMDiff (𝓘(𝕜, E × E')) (𝓘(𝕜, E')) ⊤ (Prod.snd : E × E' → E') := by
      rw [contMDiff_iff_contDiff]; exact contDiff_snd
    have D2 : ContMDiffAt (I.tangent.prod I'.tangent) I'.tangent ⊤ Prod.snd (a, b) := smoothAt_snd
    have U' := (ContMDiffAt.comp b D1.contMDiffAt Z).comp (a, b) D2
    apply U'.congr_of_eventuallyEq
    filter_upwards [chart_source_mem_nhds (ModelProd (ModelProd H E) (ModelProd H' E')) (a, b)]
      with p hp
    clear U' D1 D2 C Z
    simp only [prodChartedSpace_chartAt, PartialHomeomorph.prod_toPartialEquiv,
      PartialEquiv.prod_source, Set.mem_prod, TangentBundle.mem_chart_source_iff] at hp
    let φ (x : E') := I' ((chartAt H' b.proj) ((chartAt H' p.2.proj).symm (I'.symm x)))
    have D0 : DifferentiableWithinAt 𝕜 φ (Set.range I') (I' ((chartAt H' p.2.proj) p.2.proj)) := by
      apply ContDiffWithinAt.differentiableWithinAt (n := ⊤) _ le_top
      apply contDiffWithinAt_ext_coord_change
      simp [hp.2]
    have D (w : TangentBundle I M) :
        DifferentiableWithinAt 𝕜 (φ ∘ (Prod.snd : E × E' → E')) (Set.range (Prod.map ↑I ↑I'))
        (I ((chartAt H w.proj) w.proj), I' ((chartAt H' p.2.proj) p.2.proj)) :=
      DifferentiableWithinAt.comp (t := Set.range I') _ (by exact D0)
        differentiableWithinAt_snd (by simp [mapsTo_snd_prod])
    let φ' (x : E) := I ((chartAt H a.proj) ((chartAt H a.proj).symm (I.symm x)))
    have D0' : DifferentiableWithinAt 𝕜 φ' (Set.range I)
        (I ((chartAt H a.proj) a.proj)) := by
      apply ContDiffWithinAt.differentiableWithinAt (n := ⊤) _ le_top
      apply contDiffWithinAt_ext_coord_change
      simp
    have D' : DifferentiableWithinAt 𝕜 (φ' ∘ Prod.fst) (Set.range (Prod.map I I'))
        (I ((chartAt H a.proj) a.proj), I' ((chartAt H' p.2.proj) p.2.proj)) :=
      DifferentiableWithinAt.comp (t := Set.range I) _ (by exact D0') differentiableWithinAt_fst
        (by simp [mapsTo_fst_prod])
    have U w : UniqueDiffWithinAt 𝕜 (Set.range (Prod.map I I'))
        (I w, I' ((chartAt H' p.2.proj) p.2.proj)) := by
      simp only [Set.range_prod_map]
      apply UniqueDiffWithinAt.prod
      · exact ModelWithCorners.uniqueDiffWithinAt_image I
      · exact ModelWithCorners.uniqueDiffWithinAt_image I'
    simp only [Set.range_prod_map, ContinuousLinearMap.prod_apply, comp_def, comp_apply]
    rw [DifferentiableWithinAt.fderivWithin_prod ?_ (by exact D _) (U _)]; swap
    · let φ'' (x : E) := I ((chartAt H a.proj) ((chartAt H p.1.proj).symm (I.symm x)))
      have D0' : DifferentiableWithinAt 𝕜 φ'' (Set.range I)
          (I ((chartAt H p.1.proj) p.1.proj)) := by
        apply ContDiffWithinAt.differentiableWithinAt (n := ⊤) _ le_top
        apply contDiffWithinAt_ext_coord_change
        simp [hp.1]
      have D' : DifferentiableWithinAt 𝕜 (φ'' ∘ Prod.fst) (Set.range (Prod.map I I'))
          (I ((chartAt H p.1.proj) p.1.proj), I' ((chartAt H' p.2.proj) p.2.proj)) :=
        DifferentiableWithinAt.comp (t := Set.range I) _ (by exact D0')
          differentiableWithinAt_fst (by simp [mapsTo_fst_prod])
      exact D'
    rw [DifferentiableWithinAt.fderivWithin_prod (by exact D') (by exact D a) (U _)]
    change fderivWithin 𝕜 (φ ∘ Prod.snd) _ _ _ = fderivWithin 𝕜 (φ ∘ Prod.snd) _ _ _
    rw [Set.range_prod_map] at U ⊢
    rw [fderivWithin.comp _ (by exact D0) differentiableWithinAt_snd mapsTo_snd_prod (U _),
      fderivWithin.comp _ (by exact D0) differentiableWithinAt_snd mapsTo_snd_prod (U _)]
    simp [fderivWithin_snd, U]







variable {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I G]

/-- The invariant vector field associated to a vector in the Lie alebra. -/
def invariantVectorField (v : TangentSpace I (1 : G)) (g : G) : TangentSpace I g :=
  mfderiv I I (fun a ↦ g * a) (1 : G) v

theorem contMDiff_invariantVectorField (v : TangentSpace I (1 : G)) :
    ContMDiff I I.tangent ⊤
      (fun (g : G) ↦ (invariantVectorField v g : TangentBundle I G)) := by
  let fg : G → TangentBundle I G := fun g ↦ TotalSpace.mk' E g 0
  have sfg : Smooth I I.tangent fg := smooth_zeroSection _ _
  let fv : G → TangentBundle I G := fun _ ↦ TotalSpace.mk' E 1 v
  have sfv : Smooth I I.tangent fv := smooth_const
  let F₁ : G → (TangentBundle I G × TangentBundle I G) := fun g ↦ (fg g, fv g)
  have S₁ : Smooth I (I.tangent.prod I.tangent) F₁ := Smooth.prod_mk sfg sfv
  let F₂ : (TangentBundle I G × TangentBundle I G) → TangentBundle (I.prod I) (G × G) :=
    (equivTangentBundleProd I I G G).symm
  have S₂ : Smooth (I.tangent.prod I.tangent) (I.prod I).tangent F₂ :=
    smooth_equivTangentBundleProd_symm
  let F₃ : TangentBundle (I.prod I) (G × G) → TangentBundle I G :=
    tangentMap (I.prod I) I (fun (p : G × G) ↦ p.1 * p.2)
  have S₃ : Smooth (I.prod I).tangent I.tangent F₃ := by
    apply ContMDiff.contMDiff_tangentMap _ (m := ⊤) le_rfl
    exact smooth_mul I (G := G)
  let S := (S₃.comp S₂).comp S₁
  convert S with g
  · simp [F₁, F₂, F₃]
  · simp only [comp_apply, tangentMap, F₃, F₂, F₁]
    rw [mfderiv_prod_eq_add_apply _ _ _ (smooth_mul I (G := G)).mdifferentiableAt]
    simp [invariantVectorField]

end
