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

#check Bundle.smooth_zeroSection

#check ChartedSpace.LiftPropWithinAt

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (I : ModelWithCorners 𝕜 E H)
    {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (I' : ModelWithCorners 𝕜 E' H')
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
    (M' : Type*) [TopologicalSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M']


def foobar : TangentBundle (I.prod I') (M × M') ≃ (TangentBundle I M) × (TangentBundle I' M') where
  toFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  invFun p := ⟨(p.1.1, p.2.1), (p.1.2, p.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma foobar_eq_tangentMap_prod_tangentMap :
    foobar I I' M M' = fun (p : TangentBundle (I.prod I') (M × M')) ↦
      (tangentMap (I.prod I') I Prod.fst p, tangentMap (I.prod I') I' Prod.snd p) := by
  simp only [tangentMap_prod_fst, tangentMap_prod_snd]; rfl

lemma smooth_foobar :
    Smooth (I.prod I').tangent (I.tangent.prod I'.tangent) (foobar I I' M M') := by
  rw [foobar_eq_tangentMap_prod_tangentMap]
  exact smooth_fst.tangentMap.prod_mk smooth_snd.tangentMap

lemma smooth_foobar_symm :
    Smooth (I.tangent.prod I'.tangent) (I.prod I').tangent (foobar I I' M M').symm := by
  simp only [Smooth, ContMDiff, Prod.forall]
  intro a b
  rw [contMDiffAt_totalSpace]
  refine ⟨?_, ?_⟩
  · exact ContMDiffAt.prod_map (smoothAt_proj (TangentSpace I)) (smoothAt_proj (TangentSpace I'))

  /-
  let g : M' → M × M' := fun m ↦ (a.1, m)
  have A' : Smooth I'.tangent (I.prod I').tangent (tangentMap I' (I.prod I') g) := by
    apply Smooth.tangentMap
    exact smooth_const.prod_mk smooth_id
  have B' : tangentMap I' (I.prod I') g = fun p ↦ ⟨(a.1, p.1), (0, p.2)⟩ := by
    ext p : 1
    exact tangentMap_prod_right I I'
  rw [B'] at A'
  have C' := A' b
  have Z' := ((contMDiffAt_totalSpace _ _).1 C').2
  simp only [modelWithCornersSelf_prod, TangentBundle.trivializationAt_apply,
    PartialHomeomorph.extend, prodChartedSpace_chartAt, PartialHomeomorph.prod_toPartialEquiv,
    PartialEquiv.prod, PartialHomeomorph.toFun_eq_coe, PartialHomeomorph.coe_coe_symm,
    modelWithCorners_prod_toPartialEquiv, ModelWithCorners.toPartialEquiv_coe,
    ModelWithCorners.toPartialEquiv_coe_symm, ModelWithCorners.source_eq, Set.univ_prod_univ,
    ModelWithCorners.target_eq, PartialEquiv.coe_trans, comp_def, PartialEquiv.coe_trans_symm,
    PartialEquiv.coe_symm_mk, modelWithCorners_prod_coe, comp_apply] at Z'
  -/




  simp only [foobar, Equiv.coe_fn_symm_mk, TangentBundle.trivializationAt_apply,
    PartialHomeomorph.extend, prodChartedSpace_chartAt, PartialHomeomorph.prod_toPartialEquiv,
    PartialEquiv.prod, PartialHomeomorph.toFun_eq_coe, PartialHomeomorph.coe_coe_symm,
    modelWithCorners_prod_toPartialEquiv, ModelWithCorners.toPartialEquiv_coe,
    ModelWithCorners.toPartialEquiv_coe_symm, ModelWithCorners.source_eq, Set.univ_prod_univ,
    ModelWithCorners.target_eq, PartialEquiv.coe_trans, comp_def, PartialEquiv.coe_trans_symm,
    PartialEquiv.coe_symm_mk, modelWithCorners_prod_coe, comp_apply,]
  simp_rw [DifferentiableWithinAt.fderivWithin_prod sorry sorry sorry]
  simp
  convert_to ContMDiffAt (I.tangent.prod I'.tangent) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) ⊤
    (fun (x : TangentBundle I M × TangentBundle I' M') ↦
    ((fderivWithin 𝕜 (fun x_1 ↦ I ((chartAt H a.proj) ((chartAt H x.1.proj).symm (I.symm x_1.1))))
          (Set.range (Prod.map ↑I ↑I')) (I ((chartAt H x.1.proj) x.1.proj), I' ((chartAt H' x.2.proj) x.2.proj)))
        (x.1.snd, x.2.snd),
      (fderivWithin 𝕜 (fun x_1 ↦ I' ((chartAt H' b.proj) ((chartAt H' x.2.proj).symm (I'.symm x_1.2))))
          (Set.range (Prod.map I I')) (I ((chartAt H x.1.proj) x.1.proj), I' ((chartAt H' x.2.proj) x.2.proj)))
        (x.1.snd, x.2.snd))) (a, b)
  · sorry
  · sorry
  apply ContMDiffAt.prod_mk
  · let f : M → M × M' := fun m ↦ (m, b.1)
    have A : Smooth I.tangent (I.prod I').tangent (tangentMap I (I.prod I') f) := by
      apply Smooth.tangentMap
      exact smooth_id.prod_mk smooth_const
    have B : tangentMap I (I.prod I') f = fun p ↦ ⟨(p.1, b.1), (p.2, 0)⟩ := by
      ext p : 1
      exact tangentMap_prod_left I I'
    rw [B] at A
    have C := A a
    have Z := ((contMDiffAt_totalSpace _ _).1 C).2
    simp only [modelWithCornersSelf_prod, TangentBundle.trivializationAt_apply,
      PartialHomeomorph.extend, prodChartedSpace_chartAt, PartialHomeomorph.prod_toPartialEquiv,
      PartialEquiv.prod, PartialHomeomorph.toFun_eq_coe, PartialHomeomorph.coe_coe_symm,
      modelWithCorners_prod_toPartialEquiv, ModelWithCorners.toPartialEquiv_coe,
      ModelWithCorners.toPartialEquiv_coe_symm, ModelWithCorners.source_eq, Set.univ_prod_univ,
      ModelWithCorners.target_eq, PartialEquiv.coe_trans, comp_def, PartialEquiv.coe_trans_symm,
      PartialEquiv.coe_symm_mk, modelWithCorners_prod_coe, comp_apply] at Z
    simp_rw [DifferentiableWithinAt.fderivWithin_prod sorry sorry sorry] at Z
    simp at Z
    have W : ContMDiff (𝓘(𝕜, E × E')) (𝓘(𝕜, E)) ⊤ (Prod.fst : E × E' → E) := sorry
    have U := ContMDiffAt.comp a W.contMDiffAt Z
    simp [Function.comp_def] at U
    clear Z
    let F : TangentBundle I M × TangentBundle I' M' → TangentBundle I M := Prod.fst
    have : ContMDiffAt (I.tangent.prod I'.tangent) I.tangent ⊤ F (a, b) := smoothAt_fst
    have U' := U.comp (a, b) this
    clear U
    simp [F, Function.comp_def] at U'
    convert U' using 2 with p
    clear U' this F W C B A
    let φ (x : E) := I ((chartAt H a.proj) ((chartAt H p.1.proj).symm (I.symm x)))
    change fderivWithin 𝕜 (φ ∘ Prod.fst) _ _ _ = fderivWithin 𝕜 (φ ∘ Prod.fst) _ _ _
    rw [Set.range_prod_map]
    rw [fderivWithin.comp (t := Set.range I), fderivWithin.comp (t := Set.range I)]
    simp
    rw [fderivWithin_fst, fderivWithin_fst]
    · simp
    · apply UniqueDiffWithinAt.prod
      exact ModelWithCorners.uniqueDiffWithinAt_image I















#exit

  rw [contMDiffAt_iff]
  simp only [foobar, Equiv.coe_fn_symm_mk, extChartAt, PartialHomeomorph.extend,
    modelWithCorners_prod_toPartialEquiv, modelWithCornersSelf_partialEquiv, PartialEquiv.coe_trans,
    PartialEquiv.prod_coe, ModelWithCorners.toPartialEquiv_coe, PartialEquiv.refl_coe, id_eq,
    PartialHomeomorph.toFun_eq_coe, prodChartedSpace_chartAt, PartialHomeomorph.prod_toPartialEquiv,
    PartialEquiv.coe_trans_symm, modelWithCorners_prod_coe, modelWithCornersSelf_coe, comp_apply,
    TangentBundle.coe_chartAt_fst]
  refine ⟨?_, ?_⟩
  · rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨?_, ?_⟩
    · apply Continuous.continuousAt
      apply Continuous.prod_map
      · exact FiberBundle.continuous_proj E (TangentSpace I)
      · exact FiberBundle.continuous_proj E' (TangentSpace I')
    · simp [trivializationAt, FiberBundle.trivializationAt', FiberBundleCore.localTrivAt]
      sorry
  · simp [chartAt, Function.comp_def]



#exit

/-- The invariant vector field associated to a vector in the Lie alebra. -/
def invariantVectorField (v : TangentSpace I (1 : G)) (g : G) : TangentSpace I g :=
  mfderiv I I (fun a ↦ g * a) (1 : G) v


def foo : TangentBundle I G → TangentBundle (I.prod I) (G × G) :=
  tangent_map (fun g ↦ )

theorem contMDiff_invariantVectorField (v : TangentSpace I (1 : G)) :
    ContMDiff I I.tangent ⊤
      (fun (g : G) ↦ (invariantVectorField v g : TangentBundle I G)) := by
  have Z := smooth_mul I (G := G)
  have T := ContMDiff.contMDiff_tangentMap Z (m := ⊤) le_rfl
  let f : G → TangentBundle I G := fun g ↦ TotalSpace.mk' E g 0
  have sf : Smooth I I.tangent f := smooth_zeroSection _ _
  let f' : G → TangentBundle I G := fun g ↦ TotalSpace.mk' E 1 v
  have sf' : Smooth I I.tangent f' := smooth_const
  let F : G → (TangentBundle I G × TangentBundle I G) := fun g ↦ (f g, f' g)
  have : Smooth I (I.tangent.prod I.tangent) F := by
    exact Smooth.prod_mk sf sf'







end
