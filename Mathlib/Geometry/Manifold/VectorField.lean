/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Glouglou

All this should probably be extended to `Within` versions, as we will need them when defining
things on manifolds possibly with boundary.

-/

open scoped Topology

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 :Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F]
  {G : Type*} [TopologicalSpace G] [AddCommGroup G] [Module 𝕜 G]

def IsInvertible (f : E →L[𝕜] F) : Prop :=
  ∃ (M : E ≃L[𝕜] F), M = f

/-- Given an invertible continuous linear map, choose an equiv of which it is the direct
direction. -/
def IsInvertible.toEquiv {f : E →L[𝕜] F} (hf : f.IsInvertible) : E ≃L[𝕜] F :=
  hf.choose

lemma IsInvertible.toEquiv_eq {f : E →L[𝕜] F} (hf : f.IsInvertible) :
    hf.toEquiv = f :=
  hf.choose_spec

@[simp] lemma isInvertible_equiv {f : E ≃L[𝕜] F} : IsInvertible (f : E →L[𝕜] F) := ⟨f, rfl⟩

lemma IsInvertible.comp {g : F →L[𝕜] G} {f : E →L[𝕜] F}
    (hg : g.IsInvertible) (hf : f.IsInvertible) : (g ∘L f).IsInvertible := by
  rcases hg with ⟨N, rfl⟩
  rcases hf with ⟨M, rfl⟩
  exact ⟨M.trans N, rfl⟩

lemma IsInvertible.inverse_comp {g : F →L[𝕜] G} {f : E →L[𝕜] F}
    (hg : g.IsInvertible) (hf : f.IsInvertible) : (g ∘L f).inverse = f.inverse ∘L g.inverse := by
  rcases hg with ⟨N, rfl⟩
  rcases hf with ⟨M, rfl⟩
  simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
  rfl

lemma IsInvertible.inverse_comp_apply {g : F →L[𝕜] G} {f : E →L[𝕜] F} {v : G}
    (hg : g.IsInvertible) (hf : f.IsInvertible) : (g ∘L f).inverse v = f.inverse (g.inverse v) := by
  simp only [hg.inverse_comp hf, coe_comp', Function.comp_apply]

end ContinuousLinearMap


section LieBracketVectorField

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]


/- TODO: do this in the `VectorField` namespace. And copy the whole API
of `fderiv`, `fderivWithin`. -/

/-- The Lie bracket `[V, W] (x)` of two vector fields at a point, defined as
`DW(x) (V x) - DV(x) (W x)`. -/
def lieBracket (V W : E → E) (x : E) : E :=
  fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)

def lieBracketWithin (V W : E → E) (s : Set E) (x : E) : E :=
  fderivWithin 𝕜 W s x (V x) - fderivWithin 𝕜 V s x (W x)

variable {𝕜}

lemma lieBracket_eq (V W : E → E) :
    lieBracket 𝕜 V W = fun x ↦ fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x) := rfl

lemma lieBracketWithin_eq (V W : E → E) (s : Set E) :
    lieBracketWithin 𝕜 V W s =
      fun x ↦ fderivWithin 𝕜 W s x (V x) - fderivWithin 𝕜 V s x (W x) := rfl

lemma lieBracketWithin_eq_zero_of_eq_zero (V W : E → E) (s : Set E) (x : E)
    (hV : V x = 0) (hW : W x = 0) : lieBracketWithin 𝕜 V W s x = 0 := by
  simp [lieBracketWithin, hV, hW]

lemma lieBracketWithin_eq_of_eventually_eq (V W V' W' : E → E) (s : Set E) (x : E)
    (hV : V =ᶠ[𝓝[s] x] V') (hVx : V x = V' x) (hW : W =ᶠ[𝓝[s] x] W') (hWx : W x = W' x) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V' W' s x := by
  simp only [lieBracketWithin, hVx, hWx, hW.fderivWithin_eq, hV.fderivWithin_eq]

variable (𝕜) in
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

variable (𝕜) in
/-- The pullback of a vector field under a function, defined
as `(f^* V) (x) = Df(x)^{-1} (V (f x))`. If `Df(x)` is not invertible, we use the junk value `0`.
-/
def pullback (f : E → F) (V : F → F) (x : E) : E := (fderiv 𝕜 f x).inverse (V (f x))

lemma pullback_eq_of_fderiv_eq
    {f : E → F} {M : E ≃L[𝕜] F} {x : E} (hf : M = fderiv 𝕜 f x) (V : F → F) :
    pullback 𝕜 f V x = M.symm (V (f x)) := by
  simp [pullback, ← hf]

lemma pullback_eq_of_not_exists {f : E → F} {x : E}
    (h : ¬(fderiv 𝕜 f x).IsInvertible) (V : F → F) :
    pullback 𝕜 f V x = 0 := by
  simp only [ContinuousLinearMap.IsInvertible] at h
  simp [pullback, h]

open scoped Topology Filter

/-- A variant for the derivative of a composition, written without `∘`. -/
theorem fderiv.comp'
    {f : E → F} {g : F → G} (x : E) (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun y ↦ g (f y)) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) :=
  fderiv.comp x hg hf

lemma fderiv_pullback (f : E → F) (V : F → F) (x : E) (h'f : (fderiv 𝕜 f x).IsInvertible) :
    fderiv 𝕜 f x (pullback 𝕜 f V x) = V (f x) := by
  rcases h'f with ⟨M, hM⟩
  simp [pullback_eq_of_fderiv_eq hM, ← hM]

/-- The equation `L_{f^* V} (g ∘ f) (x) = (L_V g) (f x)`, which is essentially the definition of
the pullback.
Note that `hf` can probably be removed, as it's implied by `h'f`.
-/
lemma lieDeriv_pullback (f : E → F) (V : F → F) (g : F → G) (x : E)
    (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableAt 𝕜 f x) (h'f : (fderiv 𝕜 f x).IsInvertible) :
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
    (f : E → F) (x : E) (h'f : ContDiffAt 𝕜 2 f x) (hf : (fderiv 𝕜 f x).IsInvertible) :
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
  by_cases h : (fderiv 𝕜 f x).IsInvertible; swap
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

section LieBracketManifold

open Set Function
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M']
  {H'' : Type*} [TopologicalSpace H''] {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M''] [SmoothManifoldWithCorners I'' M'']

variable (I I')

def mpullbackWithin (f : M → M') (V : Π (x : M'), TangentSpace I' x) (s : Set M) (x : M) :
    TangentSpace I x :=
  (mfderivWithin I I' f s x).inverse (V (f x))

lemma mpullbackWithin_apply (f : M → M') (V : Π (x : M'), TangentSpace I' x) (s : Set M) (x : M) :
    mpullbackWithin I I' f V s x = (mfderivWithin I I' f s x).inverse (V (f x)) := rfl

lemma mpullbackWithin_comp (g : M' → M'') (f : M → M') (V : Π (x : M''), TangentSpace I'' x)
    (s : Set M) (t : Set M') (x₀ : M) (hg : MDifferentiableWithinAt I' I'' g t (f x₀))
    (hf : MDifferentiableWithinAt I I' f s x₀) (h : Set.MapsTo f s t)
    (hu : UniqueMDiffWithinAt I s x₀)
    (hg' : (mfderivWithin I' I'' g t (f x₀)).IsInvertible)
    (hf' : (mfderivWithin I I' f s x₀).IsInvertible) :
    mpullbackWithin I I'' (g ∘ f) V s x₀ =
      mpullbackWithin I I' f (mpullbackWithin I' I'' g V t) s x₀ := by
  simp only [mpullbackWithin, comp_apply]
  rw [mfderivWithin_comp _ hg hf h hu]
  rcases hg' with ⟨N, hN⟩
  rcases hf' with ⟨M, hM⟩
  simp [← hM, ← hN]

lemma mpullbackWithin_eq_iff (f : M → M') (V W : Π (x : M'), TangentSpace I' x)
    (s : Set M) (x₀ : M) (hf : (mfderivWithin I I' f s x₀).IsInvertible) :
    mpullbackWithin I I' f V s x₀ = mpullbackWithin I I' f W s x₀ ↔ V (f x₀) = W (f x₀) := by
  rcases hf with ⟨M, hM⟩
  simp [mpullbackWithin, ← hM]

def mlieBracketWithin (V W : Π (x : M), TangentSpace I x) (s : Set M) (x₀ : M) :
     TangentSpace I x₀ := by
  let t : Set E := (extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target
  let V' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V t
  let W' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W t
  let Z := lieBracketWithin 𝕜 V' W' t
  exact mpullbackWithin I 𝓘(𝕜, E) (extChartAt I x₀) Z (s ∩ (extChartAt I x₀).source) x₀

lemma mlieBracketWithin_def (V W : Π (x : M), TangentSpace I x) (s : Set M) :
    mlieBracketWithin I V W s = fun x₀ ↦
    mpullbackWithin I 𝓘(𝕜, E) (extChartAt I x₀)
      (lieBracketWithin 𝕜
        (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V
          ((extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target))
        (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W
          ((extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target))
        ((extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target))
    (s ∩ (extChartAt I x₀).source) x₀ := rfl

/-- The Lie bracket of vector fields on manifolds is well defined, i.e., it is invariant under
diffeomorphisms.
TODO: write a version localized to sets. -/
lemma key (f : M → M') (V W : Π (x : M'), TangentSpace I' x) (x₀ : M) (s : Set M) (t : Set M')
    (hu : UniqueMDiffWithinAt I s x₀) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ =
      mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ := by
  suffices mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (mpullbackWithin I I' f (mlieBracketWithin I' V W t) s)
        ((extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target) (extChartAt I x₀ x₀) =
      mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
        (mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s)
        ((extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target) (extChartAt I x₀ x₀) by
    rw [mpullbackWithin_eq_iff] at this
    · convert this <;> simp
    · sorry
  rw [← mpullbackWithin_comp]; rotate_left
  · sorry
  · sorry
  · sorry
  · apply UniqueDiffWithinAt.uniqueMDiffWithinAt
    exact uniqueMDiffWithinAt_iff.mp hu
  · sorry
  · sorry
  rw [mpullbackWithin_apply, mpullbackWithin_apply]
  conv_rhs => rw [mlieBracketWithin, mpullbackWithin_apply]
  have Ex : (extChartAt I x₀).symm ((extChartAt I x₀) x₀) = x₀ := by simp
  simp only [comp_apply, Ex]
  rw [← ContinuousLinearMap.IsInvertible.inverse_comp_apply]; rotate_left
  · sorry
  · sorry
  rw [← mfderivWithin_comp]; rotate_left
  · sorry
  · sorry
  · sorry
  · sorry
  have : mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E)
      ((extChartAt I ((extChartAt I x₀).symm ((extChartAt I x₀) x₀))) ∘ ↑(extChartAt I x₀).symm)
      (↑(extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target) ((extChartAt I x₀) x₀) =
    ContinuousLinearMap.id _ _:= sorry
  rw [this]
  simp















#exit



end LieBracketManifold


section LieGroup

open Bundle Filter Function Set
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I G]

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
    (equivTangentBundleProd I G I G).symm
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

end LieGroup
