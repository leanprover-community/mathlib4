/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Vector fields in manifolds

We study functions of the form `V : Π (x : M) → TangentSpace I x` on a manifold, i.e.,
vector fields.

We define the pullback of a vector field under a map, as
`VectorField.mpullback I I' f V x := (mfderiv I I' f x).inverse (V (f x))`
(together with the same notion within a set). Note that the pullback uses the junk-value pattern:
if the derivative of the map is not invertible, then pullback is given the junk value zero.

We also define the Lie bracket of two vector fields, denoted with
`VectorField.mlieBracket I V W x`, as the pullback in the manifold of the corresponding notion
in the model space (through `extChartAt I x`).

In addition to comprehensive API on these two notions, the main results are the following:
* `VectorField.mpullback_mlieBracket` states that the pullback of the Lie bracket
  is the Lie bracket of the pullbacks.
* `VectorField.leibniz_identity_mlieBracket` is the Leibniz (or Jacobi)
  identity `[U, [V, W]] = [[U, V], W] + [V, [U, W]]`.

All these are given in the `VectorField` namespace because pullbacks, Lie brackets, and so on,
are notions that make sense in a variety of contexts. We also prefix the notions with `m` to
distinguish the manifold notions from the vector space notions.

For notions that come naturally in other namespaces for dot notation, we specify `vectorField` in
the name to lift ambiguities. For instance, the fact that the Lie bracket of two smooth vector
fields is smooth is `ContMDiffAt.mlieBracket_vectorField`.

Note that a smoothness assumption for a vector field is written by seeing the vector field as
a function from `M` to its tangent bundle through a coercion, as in:
`MDifferentiableWithinAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) s x`.
-/

open Set Function Filter
open scoped Topology Manifold ContDiff

noncomputable section

/- We work in the `VectorField` namespace because pullbacks, Lie brackets, and so on, are notions
that make sense in a variety of contexts. We also prefix the notions with `m` to distinguish the
manifold notions from the vector spaces notions. For instance, the Lie bracket of two vector
fields in a manifold is denoted with `VectorField.mlieBracket I V W x`, where `I` is the relevant
model with corners, `V W : Π (x : M), TangentSpace I x` are the vector fields, and `x : M` is
the basepoint.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {H'' : Type*} [TopologicalSpace H''] {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f : M → M'} {s t : Set M} {x x₀ : M}

instance {n : ℕ} [n.AtLeastTwo] [IsManifold I (minSmoothness 𝕜 (ofNat(n))) M] :
    IsManifold I (ofNat(n)) M :=
  IsManifold.of_le (n := minSmoothness 𝕜 n) le_minSmoothness

instance [IsManifold I (minSmoothness 𝕜 1) M] :
    IsManifold I 1 M :=
  IsManifold.of_le (n := minSmoothness 𝕜 1) le_minSmoothness

instance [IsManifold I (minSmoothness 𝕜 3) M] :
    IsManifold I (minSmoothness 𝕜 2) M :=
  IsManifold.of_le (n := minSmoothness 𝕜 3) (minSmoothness_monotone (by norm_cast))

instance [IsManifold I (minSmoothness 𝕜 2) M] :
    IsManifold I (minSmoothness 𝕜 1) M :=
  IsManifold.of_le (n := minSmoothness 𝕜 2) (minSmoothness_monotone (by norm_cast))

namespace VectorField

section Pullback

/-! ### Pullback of vector fields in manifolds -/

open ContinuousLinearMap

variable {V W V₁ W₁ : Π (x : M'), TangentSpace I' x}
variable {c : 𝕜} {m n : WithTop ℕ∞} {t : Set M'} {y₀ : M'}

variable (I I') in
/-- The pullback of a vector field under a map between manifolds, within a set `s`. If the
derivative of the map within `s` is not invertible, then pullback is given the junk value zero. -/
def mpullbackWithin (f : M → M') (V : Π (x : M'), TangentSpace I' x) (s : Set M) (x : M) :
    TangentSpace I x :=
  (mfderivWithin I I' f s x).inverse (V (f x))

variable (I I') in
/-- The pullback of a vector field under a map between manifolds. If the derivative of the map is
not invertible, then pullback is given the junk value zero. -/
def mpullback (f : M → M') (V : Π (x : M'), TangentSpace I' x) (x : M) :
    TangentSpace I x :=
  (mfderiv I I' f x).inverse (V (f x))

lemma mpullbackWithin_apply :
    mpullbackWithin I I' f V s x = (mfderivWithin I I' f s x).inverse (V (f x)) := rfl

lemma mpullbackWithin_smul_apply :
    mpullbackWithin I I' f (c • V) s x = c • mpullbackWithin I I' f V s x := by
  simp [mpullbackWithin_apply]

lemma mpullbackWithin_smul :
    mpullbackWithin I I' f (c • V) s = c • mpullbackWithin I I' f V s := by
  ext x
  simp [mpullbackWithin_apply]

lemma mpullbackWithin_add_apply :
    mpullbackWithin I I' f (V + V₁) s x =
      mpullbackWithin I I' f V s x + mpullbackWithin I I' f V₁ s x := by
  simp [mpullbackWithin_apply]

lemma mpullbackWithin_add :
    mpullbackWithin I I' f (V + V₁) s =
      mpullbackWithin I I' f V s + mpullbackWithin I I' f V₁ s := by
  ext x
  simp [mpullbackWithin_apply]

lemma mpullbackWithin_neg_apply :
    mpullbackWithin I I' f (-V) s x = - mpullbackWithin I I' f V s x := by
  simp [mpullbackWithin_apply]

lemma mpullbackWithin_neg :
    mpullbackWithin I I' f (-V) s = - mpullbackWithin I I' f V s := by
  ext x
  simp [mpullbackWithin_apply]

lemma mpullbackWithin_id {V : Π (x : M), TangentSpace I x} (h : UniqueMDiffWithinAt I s x) :
    mpullbackWithin I I id V s x = V x := by
  simp [mpullbackWithin_apply, mfderivWithin_id h]

lemma mpullback_apply :
    mpullback I I' f V x = (mfderiv I I' f x).inverse (V (f x)) := rfl

lemma mpullback_smul_apply :
    mpullback I I' f (c • V) x = c • mpullback I I' f V x := by
  simp [mpullback]

lemma mpullback_smul :
    mpullback I I' f (c • V) = c • mpullback I I' f V := by
  ext x
  simp [mpullback_apply]

lemma mpullback_add_apply :
    mpullback I I' f (V + V₁) x = mpullback I I' f V x + mpullback I I' f V₁ x := by
  simp [mpullback_apply]

lemma mpullback_add :
    mpullback I I' f (V + V₁) = mpullback I I' f V + mpullback I I' f V₁ := by
  ext x
  simp [mpullback_apply]

lemma mpullback_neg_apply :
    mpullback I I' f (-V) x = - mpullback I I' f V x := by
  simp [mpullback_apply]

lemma mpullback_neg :
    mpullback I I' f (-V) = - mpullback I I' f V := by
  ext x
  simp [mpullback_apply]

@[simp] lemma mpullbackWithin_univ : mpullbackWithin I I' f V univ = mpullback I I' f V := by
  ext x
  simp [mpullback_apply, mpullbackWithin_apply]

lemma mpullbackWithin_eq_pullbackWithin {f : E → E'} {V : E' → E'} {s : Set E} :
    mpullbackWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f V s = pullbackWithin 𝕜 f V s := by
  ext x
  simp only [mpullbackWithin, mfderivWithin_eq_fderivWithin, pullbackWithin]
  rfl

lemma mpullback_eq_pullback {f : E → E'} {V : E' → E'} :
    mpullback 𝓘(𝕜, E) 𝓘(𝕜, E') f V = pullback 𝕜 f V := by
  simp only [← mpullbackWithin_univ, ← pullbackWithin_univ, mpullbackWithin_eq_pullbackWithin]

@[simp] lemma mpullback_id {V : Π (x : M), TangentSpace I x} : mpullback I I id V = V := by
  ext x
  simp [mpullback]

lemma mpullbackWithin_comp_of_left
    {g : M' → M''} {f : M → M'} {V : Π (x : M''), TangentSpace I'' x} {s : Set M} {t : Set M'}
    {x₀ : M} (hf : MDifferentiableWithinAt I I' f s x₀) (h : Set.MapsTo f s t)
    (hu : UniqueMDiffWithinAt I s x₀) (hg' : (mfderivWithin I' I'' g t (f x₀)).IsInvertible) :
    mpullbackWithin I I'' (g ∘ f) V s x₀ =
      mpullbackWithin I I' f (mpullbackWithin I' I'' g V t) s x₀ := by
  simp only [mpullbackWithin, comp_apply]
  have hg : MDifferentiableWithinAt I' I'' g t (f x₀) :=
    mdifferentiableWithinAt_of_isInvertible_mfderivWithin hg'
  rw [mfderivWithin_comp _ hg hf h hu, Function.comp_apply,
    IsInvertible.inverse_comp_apply_of_left hg']

lemma mpullbackWithin_comp_of_right
    {g : M' → M''} {f : M → M'} {V : Π (x : M''), TangentSpace I'' x} {s : Set M} {t : Set M'}
    {x₀ : M} (hg : MDifferentiableWithinAt I' I'' g t (f x₀)) (h : Set.MapsTo f s t)
    (hu : UniqueMDiffWithinAt I s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible) :
    mpullbackWithin I I'' (g ∘ f) V s x₀ =
      mpullbackWithin I I' f (mpullbackWithin I' I'' g V t) s x₀ := by
  simp only [mpullbackWithin, comp_apply]
  have hf : MDifferentiableWithinAt I I' f s x₀ :=
    mdifferentiableWithinAt_of_isInvertible_mfderivWithin hf'
  rw [mfderivWithin_comp _ hg hf h hu, IsInvertible.inverse_comp_apply_of_right hf',
    Function.comp_apply]


/-! ### Regularity of pullback of vector fields

In this paragraph, we assume that the model space is complete, to ensure that the set of invertible
linear maps is open and that inversion is a smooth map there. Otherwise, the pullback of vector
fields could behave wildly, even at points where the derivative of the map is invertible.
-/

section MDifferentiability

variable [IsManifold I 2 M] [IsManifold I' 2 M'] [CompleteSpace E]

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version within a set at a point. -/
protected lemma _root_.MDifferentiableWithinAt.mpullbackWithin_vectorField_inter
    (hV : MDifferentiableWithinAt I' I'.tangent
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : 2 ≤ n) :
    MDifferentiableWithinAt I I.tangent
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f ⁻¹' t) x₀ := by
  /- We want to apply the theorem `MDifferentiableWithinAt.clm_apply_of_inCoordinates`,
  stating that applying linear maps to vector fields gives a smooth result when the linear map and
  the vector field are smooth. This theorem is general, we will apply it to
  `b₁ = f`, `b₂ = id`, `v = V ∘ f`, `ϕ = fun x ↦ (mfderivWithin I I' f s x).inverse` -/
  let b₁ := f
  let b₂ : M → M := id
  let v : Π (x : M), TangentSpace I' (f x) := V ∘ f
  let ϕ : Π (x : M), TangentSpace I' (f x) →L[𝕜] TangentSpace I x :=
    fun x ↦ (mfderivWithin I I' f s x).inverse
  have hv : MDifferentiableWithinAt I I'.tangent
      (fun x ↦ (v x : TangentBundle I' M')) (s ∩ f ⁻¹' t) x₀ := by
    apply hV.comp x₀ ((hf.mdifferentiableWithinAt (one_le_two.trans hmn)).mono inter_subset_left)
    exact MapsTo.mono_left (mapsTo_preimage _ _) inter_subset_right
  /- The only nontrivial fact, from which the conclusion follows, is
  that `ϕ` depends smoothly on `x`. -/
  suffices hϕ : MDifferentiableWithinAt I 𝓘(𝕜, E' →L[𝕜] E)
      (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E' (TangentSpace I' (M := M')) E (TangentSpace I (M := M))
        (b₁ x₀) (b₁ x) (b₂ x₀) (b₂ x) (ϕ x)) s x₀ from
    MDifferentiableWithinAt.clm_apply_of_inCoordinates (hϕ.mono inter_subset_left)
      hv mdifferentiableWithinAt_id
  /- To prove that `ϕ` depends smoothly on `x`, we use that the derivative depends smoothly on `x`
  (this is `ContMDiffWithinAt.mfderivWithin_const`), and that taking the inverse is a smooth
  operation at an invertible map. -/
  -- the derivative in coordinates depends smoothly on the point
  have : MDifferentiableWithinAt I 𝓘(𝕜, E →L[𝕜] E')
      (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
        x₀ x (f x₀) (f x) (mfderivWithin I I' f s x)) s x₀ :=
    ((hf.of_le hmn).mfderivWithin_const le_rfl hx₀ hs).mdifferentiableWithinAt le_rfl
  -- therefore, its inverse in coordinates also depends smoothly on the point
  have : MDifferentiableWithinAt I 𝓘(𝕜, E' →L[𝕜] E)
      (ContinuousLinearMap.inverse ∘ (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
        x₀ x (f x₀) (f x) (mfderivWithin I I' f s x))) s x₀ := by
    apply MDifferentiableAt.comp_mdifferentiableWithinAt _ _ this
    apply ContMDiffAt.mdifferentiableAt _ le_rfl
    apply ContDiffAt.contMDiffAt
    apply IsInvertible.contDiffAt_map_inverse
    rw [inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' x₀)
      (FiberBundle.mem_baseSet_trivializationAt' (f x₀))]
    exact isInvertible_equiv.comp (hf'.comp isInvertible_equiv)
  -- the inverse in coordinates coincides with the in-coordinate version of the inverse,
  -- therefore the previous point gives the conclusion
  apply this.congr_of_eventuallyEq_of_mem _ hx₀
  have A : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝[s] x₀ := by
    apply nhdsWithin_le_nhds
    apply (trivializationAt _ _ _).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' _
  have B : f ⁻¹' (trivializationAt E' (TangentSpace I') (f x₀)).baseSet ∈ 𝓝[s] x₀ := by
    apply hf.continuousWithinAt.preimage_mem_nhdsWithin
    apply (trivializationAt _ _ _).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' _
  filter_upwards [A, B] with x hx h'x
  simp only [Function.comp_apply]
  rw [inCoordinates_eq hx h'x, inCoordinates_eq h'x (by exact hx)]
  simp only [inverse_equiv_comp, inverse_comp_equiv, ContinuousLinearEquiv.symm_symm, ϕ]
  rfl

lemma _root_.MDifferentiableWithinAt.mpullbackWithin_vectorField_inter_of_eq
    (hV : MDifferentiableWithinAt I' I'.tangent
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : 2 ≤ n) (h : y₀ = f x₀) :
    MDifferentiableWithinAt I I.tangent
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f⁻¹' t) x₀ := by
  subst h
  exact hV.mpullbackWithin_vectorField_inter hf hf' hx₀ hs hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version on a set. -/
protected lemma _root_.MDifferentiableOn.mpullbackWithin_vectorField_inter
    (hV : MDifferentiableOn I' I'.tangent (fun (y : M') ↦ (V y : TangentBundle I' M')) t)
    (hf : ContMDiffOn I I' n f s) (hf' : ∀ x ∈ s ∩ f ⁻¹' t, (mfderivWithin I I' f s x).IsInvertible)
    (hs : UniqueMDiffOn I s) (hmn : 2 ≤ n) :
    MDifferentiableOn I I.tangent
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f ⁻¹' t) :=
  fun _ hx₀ ↦ MDifferentiableWithinAt.mpullbackWithin_vectorField_inter
    (hV _ hx₀.2) (hf _ hx₀.1) (hf' _ hx₀) hx₀.1 hs hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version within a set at a point, but with full pullback. -/
protected lemma _root_.MDifferentiableWithinAt.mpullback_vectorField_preimage
    (hV : MDifferentiableWithinAt I' I'.tangent
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : 2 ≤ n) :
    MDifferentiableWithinAt I I.tangent
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) (f ⁻¹' t) x₀ := by
  simp only [← contMDiffWithinAt_univ, ← mfderivWithin_univ, ← mpullbackWithin_univ] at hV hf hf' ⊢
  simpa using hV.mpullbackWithin_vectorField_inter hf hf' (mem_univ _) uniqueMDiffOn_univ hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version within a set at a point, but with full pullback. -/
protected lemma _root_.MDifferentiableWithinAt.mpullback_vectorField_preimage_of_eq
    (hV : MDifferentiableWithinAt I' I'.tangent (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : 2 ≤ n)
    (hy₀ : y₀ = f x₀) :
    MDifferentiableWithinAt I I.tangent
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) (f ⁻¹' t) x₀ := by
  subst hy₀
  exact hV.mpullback_vectorField_preimage hf hf' hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version on a set, but with full pullback -/
protected lemma _root_.MDifferentiableOn.mpullback_vectorField_preimage
    (hV : MDifferentiableOn I' I'.tangent (fun (y : M') ↦ (V y : TangentBundle I' M')) t)
    (hf : ContMDiff I I' n f) (hf' : ∀ x ∈ f ⁻¹' t, (mfderiv I I' f x).IsInvertible)
    (hmn : 2 ≤ n) :
    MDifferentiableOn I I.tangent
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) (f ⁻¹' t) :=
  fun x₀ hx₀ ↦ MDifferentiableWithinAt.mpullback_vectorField_preimage
    (hV _ hx₀) (hf x₀) (hf' _ hx₀) hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version at a point. -/
protected lemma _root_.MDifferentiableAt.mpullback_vectorField
    (hV : MDifferentiableAt I' I'.tangent (fun (y : M') ↦ (V y : TangentBundle I' M')) (f x₀))
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : 2 ≤ n) :
    MDifferentiableAt I I.tangent
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) x₀ := by
  simpa using MDifferentiableWithinAt.mpullback_vectorField_preimage hV hf hf' hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. -/
protected lemma _root_.MDifferentiable.mpullback_vectorField
    (hV : MDifferentiable I' I'.tangent (fun (y : M') ↦ (V y : TangentBundle I' M')))
    (hf : ContMDiff I I' n f) (hf' : ∀ x, (mfderiv I I' f x).IsInvertible) (hmn : 2 ≤ n) :
    MDifferentiable I I.tangent (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) :=
  fun x ↦ MDifferentiableAt.mpullback_vectorField (hV (f x)) (hf x) (hf' x) hmn

end MDifferentiability


section ContMDiff

variable [IsManifold I n M] [IsManifold I' n M'] [CompleteSpace E]
  -- If `1 < n` then `IsManifold.of_le` shows the following assumptions are redundant.
  -- We include them since they are necessary to make the statement.
  [IsManifold I 1 M] [IsManifold I' 1 M']

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
`m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_inter
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f ⁻¹' t) x₀ := by
  /- We want to apply the theorem `ContMDiffWithinAt.clm_apply_of_inCoordinates`, stating
  that applying linear maps to vector fields gives a smooth result when the linear map and the
  vector field are smooth. This theorem is general, we will apply it to
  `b₁ = f`, `b₂ = id`, `v = V ∘ f`, `ϕ = fun x ↦ (mfderivWithin I I' f s x).inverse` -/
  let b₁ := f
  let b₂ : M → M := id
  let v : Π (x : M), TangentSpace I' (f x) := V ∘ f
  let ϕ : Π (x : M), TangentSpace I' (f x) →L[𝕜] TangentSpace I x :=
    fun x ↦ (mfderivWithin I I' f s x).inverse
  have hv : ContMDiffWithinAt I I'.tangent m
      (fun x ↦ (v x : TangentBundle I' M')) (s ∩ f ⁻¹' t) x₀ := by
    apply hV.comp x₀ ((hf.of_le (le_trans (le_self_add) hmn)).mono inter_subset_left)
    exact MapsTo.mono_left (mapsTo_preimage _ _) inter_subset_right
  /- The only nontrivial fact, from which the conclusion follows, is
  that `ϕ` depends smoothly on `x`. -/
  suffices hϕ : ContMDiffWithinAt I 𝓘(𝕜, E' →L[𝕜] E) m
      (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E' (TangentSpace I' (M := M')) E (TangentSpace I (M := M))
        (b₁ x₀) (b₁ x) (b₂ x₀) (b₂ x) (ϕ x)) s x₀ from
    ContMDiffWithinAt.clm_apply_of_inCoordinates (hϕ.mono inter_subset_left) hv contMDiffWithinAt_id
  /- To prove that `ϕ` depends smoothly on `x`, we use that the derivative depends smoothly on `x`
  (this is `ContMDiffWithinAt.mfderivWithin_const`), and that taking the inverse is a smooth
  operation at an invertible map. -/
  -- the derivative in coordinates depends smoothly on the point
  have : ContMDiffWithinAt I 𝓘(𝕜, E →L[𝕜] E') m
      (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
        x₀ x (f x₀) (f x) (mfderivWithin I I' f s x)) s x₀ :=
    hf.mfderivWithin_const hmn hx₀ hs
  -- therefore, its inverse in coordinates also depends smoothly on the point
  have : ContMDiffWithinAt I 𝓘(𝕜, E' →L[𝕜] E) m
      (ContinuousLinearMap.inverse ∘ (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
        x₀ x (f x₀) (f x) (mfderivWithin I I' f s x))) s x₀ := by
    apply ContMDiffAt.comp_contMDiffWithinAt _ _ this
    apply ContDiffAt.contMDiffAt
    apply IsInvertible.contDiffAt_map_inverse
    rw [inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' x₀)
      (FiberBundle.mem_baseSet_trivializationAt' (f x₀))]
    exact isInvertible_equiv.comp (hf'.comp isInvertible_equiv)
  -- the inverse in coordinates coincides with the in-coordinate version of the inverse,
  -- therefore the previous point gives the conclusion
  apply this.congr_of_eventuallyEq_of_mem _ hx₀
  have A : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝[s] x₀ := by
    apply nhdsWithin_le_nhds
    apply (trivializationAt _ _ _).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' _
  have B : f ⁻¹' (trivializationAt E' (TangentSpace I') (f x₀)).baseSet ∈ 𝓝[s] x₀ := by
    apply hf.continuousWithinAt.preimage_mem_nhdsWithin
    apply (trivializationAt _ _ _).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' _
  filter_upwards [A, B] with x hx h'x
  simp only [Function.comp_apply]
  rw [inCoordinates_eq hx h'x, inCoordinates_eq h'x (by exact hx)]
  simp only [inverse_equiv_comp, inverse_comp_equiv, ContinuousLinearEquiv.symm_symm, ϕ]
  rfl

lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_inter_of_eq
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) (h : f x₀ = y₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f⁻¹' t) x₀ := by
  subst h
  exact ContMDiffWithinAt.mpullbackWithin_vectorField_inter hV hf hf' hx₀ hs hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) s x₀ := by
  apply (ContMDiffWithinAt.mpullbackWithin_vectorField_inter
    hV hf hf' hx₀ hs hmn).mono_of_mem_nhdsWithin
  exact Filter.inter_mem self_mem_nhdsWithin hst

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem_of_eq
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hy₀ : f x₀ = y₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) s x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem hV hf hf' hx₀ hs hmn hst

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) (hst : MapsTo f s t) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) s x₀ :=
  ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem hV hf hf' hx₀ hs hmn
    hst.preimage_mem_nhdsWithin

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) (hst : MapsTo f s t) (h : f x₀ = y₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) s x₀ := by
  subst h
  exact ContMDiffWithinAt.mpullbackWithin_vectorField hV hf hf' hx₀ hs hmn hst

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, with a set used for the pullback possibly larger. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField' {u : Set M}
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffWithinAt I I' n f u x₀) (hf' : (mfderivWithin I I' f u x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (hu : s ⊆ u) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V u y : TangentBundle I M)) s x₀ := by
  have hn : (1 : ℕ) ≤ n := le_trans le_add_self hmn
  have hh : (mfderivWithin I I' f s x₀).IsInvertible := by
    convert hf' using 1
    exact (hf.mdifferentiableWithinAt hn).mfderivWithin_mono (hs _ hx₀) hu
  apply (hV.mpullbackWithin_vectorField_of_mem (hf.mono hu) hh hx₀ hs hmn
    hst).congr_of_eventuallyEq_of_mem _ hx₀
  have Y := (contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin (by simp)).1 (hf.of_le hn)
  simp_rw [insert_eq_of_mem (hu hx₀)] at Y
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_mono _ hu Y] with y hy h'y
  simp only [mpullbackWithin, Bundle.TotalSpace.mk_inj]
  rw [MDifferentiableWithinAt.mfderivWithin_mono (h'y.mdifferentiableWithinAt le_rfl) (hs _ hy) hu]

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, with a set used for the pullback possibly larger. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq' {u : Set M}
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffWithinAt I I' n f u x₀) (hf' : (mfderivWithin I I' f u x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hu : s ⊆ u) (hy₀ : f x₀ = y₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V u y : TangentBundle I M)) s x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullbackWithin_vectorField' hV hf hf' hx₀ hs hmn hst hu

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version on a set. -/
protected lemma _root_.ContMDiffOn.mpullbackWithin_vectorField_inter
    (hV : ContMDiffOn I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t)
    (hf : ContMDiffOn I I' n f s) (hf' : ∀ x ∈ s ∩ f ⁻¹' t, (mfderivWithin I I' f s x).IsInvertible)
    (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) :
    ContMDiffOn I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f ⁻¹' t) :=
  fun _ hx₀ ↦ ContMDiffWithinAt.mpullbackWithin_vectorField_inter
    (hV _ hx₀.2) (hf _ hx₀.1) (hf' _ hx₀) hx₀.1 hs hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_preimage
    (hV : ContMDiffWithinAt I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : m + 1 ≤ n) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) (f ⁻¹' t) x₀ := by
  simp only [← contMDiffWithinAt_univ, ← mfderivWithin_univ, ← mpullbackWithin_univ] at hV hf hf' ⊢
  simpa using hV.mpullbackWithin_vectorField_inter hf hf' (mem_univ _) uniqueMDiffOn_univ hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_preimage_of_eq
    (hV : ContMDiffWithinAt I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : m + 1 ≤ n)
    (hy₀ : y₀ = f x₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) (f ⁻¹' t) x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullback_vectorField_preimage hV hf hf' hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin
    (hV : ContMDiffWithinAt I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : m + 1 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) s x₀ :=
  (ContMDiffWithinAt.mpullback_vectorField_preimage hV hf hf' hmn).mono_of_mem_nhdsWithin hst

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin_of_eq
    (hV : ContMDiffWithinAt I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : m + 1 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (hy₀ : y₀ = f x₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) s x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin hV hf hf' hmn hst

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version on a set, but with full pullback -/
protected lemma _root_.ContMDiffOn.mpullback_vectorField_preimage
    (hV : ContMDiffOn I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t)
    (hf : ContMDiff I I' n f) (hf' : ∀ x ∈ f ⁻¹' t, (mfderiv I I' f x).IsInvertible)
    (hmn : m + 1 ≤ n) :
    ContMDiffOn I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) (f ⁻¹' t) :=
  fun x₀ hx₀ ↦ ContMDiffWithinAt.mpullback_vectorField_preimage (hV _ hx₀) (hf x₀) (hf' _ hx₀) hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version at a point. -/
protected lemma _root_.ContMDiffAt.mpullback_vectorField_preimage
    (hV : ContMDiffAt I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) (f x₀))
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : m + 1 ≤ n) :
    ContMDiffAt I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) x₀ := by
  simp only [← contMDiffWithinAt_univ] at hV hf hf' ⊢
  simpa using ContMDiffWithinAt.mpullback_vectorField_preimage hV hf hf' hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`. -/
protected lemma _root_.ContMDiff.mpullback_vectorField
    (hV : ContMDiff I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')))
    (hf : ContMDiff I I' n f) (hf' : ∀ x, (mfderiv I I' f x).IsInvertible) (hmn : m + 1 ≤ n) :
    ContMDiff I I.tangent m (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) :=
  fun x ↦ ContMDiffAt.mpullback_vectorField_preimage (hV (f x)) (hf x) (hf' x) hmn

lemma contMDiffWithinAt_mpullbackWithin_extChartAt_symm
    {V : Π (x : M), TangentSpace I x}
    (hV : ContMDiffWithinAt I I.tangent m (fun x ↦ (V x : TangentBundle I M)) s x)
    (hs : UniqueMDiffOn I s) (hx : x ∈ s) (hmn : m + 1 ≤ n) :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent m
      (fun y ↦ (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I) y :
        TangentBundle 𝓘(𝕜, E) E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) :=
  ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq' hV
    (contMDiffWithinAt_extChartAt_symm_range (n := n) _ (mem_extChartAt_target x))
    (isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target x))
    (by simp [hx]) (UniqueMDiffOn.uniqueMDiffOn_target_inter hs x) hmn
    ((mapsTo_preimage _ _).mono_left inter_subset_right).preimage_mem_nhdsWithin
    (Subset.trans inter_subset_left (extChartAt_target_subset_range x)) (extChartAt_to_inv x)

lemma eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm
    {V : Π (x : M), TangentSpace I x}
    (hV : ContMDiffWithinAt I I.tangent m (fun x ↦ (V x : TangentBundle I M)) s x)
    (hs : UniqueMDiffOn I s) (hx : x ∈ s) (hmn : m + 1 ≤ n) (hm : m ≠ ∞) :
    ∀ᶠ y in 𝓝[s] x, ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent m
    (fun z ↦ (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I) z :
      TangentBundle 𝓘(𝕜, E) E))
    ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x y) := by
  have T := nhdsWithin_mono _ (subset_insert _ _)
    ((contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin hm).1
      (contMDiffWithinAt_mpullbackWithin_extChartAt_symm hV hs hx hmn))
  have A := (continuousAt_extChartAt (I := I) x).continuousWithinAt.preimage_mem_nhdsWithin'' T rfl
  apply (nhdsWithin_le_iff.2 _) A
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := I) x)]
    with y hy h'y
  simp only [mfld_simps] at hy h'y
  simp [hy, h'y]

omit [CompleteSpace E] in
lemma eventuallyEq_mpullback_mpullbackWithin_extChartAt (V : Π (x : M), TangentSpace I x) :
    V =ᶠ[𝓝[s] x] mpullback I 𝓘(𝕜, E) (extChartAt I x)
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)) := by
  apply nhdsWithin_le_nhds
  filter_upwards [extChartAt_source_mem_nhds (I := I) x] with y hy
  have A : (extChartAt I x).symm (extChartAt I x y) = y := (extChartAt I x).left_inv hy
  rw [mpullback_apply, mpullbackWithin_apply,
    ← (isInvertible_mfderiv_extChartAt hy).inverse_comp_apply_of_right,
    mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy, A]
  simp only [ContinuousLinearMap.inverse_id, ContinuousLinearMap.coe_id', id_eq]

end ContMDiff

end Pullback

section LieBracket

/-! ### The Lie bracket of vector fields in manifolds -/

variable {V W V₁ W₁ : Π (x : M), TangentSpace I x}

variable (I I') in
/-- The Lie bracket of two vector fields in a manifold, within a set. -/
def mlieBracketWithin (V W : Π (x : M), TangentSpace I x) (s : Set M) (x₀ : M) :
    TangentSpace I x₀ :=
  mpullback I 𝓘(𝕜, E) (extChartAt I x₀)
    (lieBracketWithin 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W (range I))
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I)) x₀

variable (I I') in
/-- The Lie bracket of two vector fields in a manifold. -/
def mlieBracket (V W : Π (x : M), TangentSpace I x) (x₀ : M) : TangentSpace I x₀ :=
  mlieBracketWithin I V W univ x₀

lemma mlieBracketWithin_def  :
    mlieBracketWithin I V W s = fun x₀ ↦
    mpullback I 𝓘(𝕜, E) (extChartAt I x₀)
    (lieBracketWithin 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W (range I))
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I)) x₀ := rfl

lemma mlieBracketWithin_apply :
    mlieBracketWithin I V W s x₀ =
    (mfderiv I 𝓘(𝕜, E) (extChartAt I x₀) x₀).inverse
    ((lieBracketWithin 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W (range I))
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I)) ((extChartAt I x₀ x₀))) := rfl

lemma mlieBracketWithin_eq_lieBracketWithin {V W : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {s : Set E} :
    mlieBracketWithin 𝓘(𝕜, E) V W s  = lieBracketWithin 𝕜 V W s := by
  ext x
  simp [mlieBracketWithin_apply]

/-********************************************************************************
Copy of the `lieBracket` API in manifolds
-/

@[simp] lemma mlieBracketWithin_univ :
    mlieBracketWithin I V W univ = mlieBracket I V W := rfl

lemma mlieBracketWithin_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) :
    mlieBracketWithin I V W s x = 0 := by
  simp only [mlieBracketWithin, mpullback_apply, comp_apply]
  rw [lieBracketWithin_eq_zero_of_eq_zero]
  · simp
  · simp only [mpullbackWithin_apply]
    have : (extChartAt I x).symm ((extChartAt I x) x) = x := by simp
    rw [this, hV]
    simp
  · simp only [mpullbackWithin_apply]
    have : (extChartAt I x).symm ((extChartAt I x) x) = x := by simp
    rw [this, hW]
    simp

lemma mlieBracketWithin_swap_apply :
    mlieBracketWithin I V W s x = - mlieBracketWithin I W V s x := by
  rw [mlieBracketWithin, lieBracketWithin_swap, mpullback_neg]
  rfl

lemma mlieBracketWithin_swap :
    mlieBracketWithin I V W s = - mlieBracketWithin I W V s := by
  ext x
  exact mlieBracketWithin_swap_apply

lemma mlieBracket_swap_apply : mlieBracket I V W x = - mlieBracket I W V x :=
  mlieBracketWithin_swap_apply

lemma mlieBracket_swap : mlieBracket I V W = - mlieBracket I W V :=
  mlieBracketWithin_swap

@[simp] lemma mlieBracketWithin_self : mlieBracketWithin I V V = 0 := by
  ext x; simp [mlieBracketWithin, mpullback]

@[simp] lemma mlieBracket_self : mlieBracket I V V = 0 := by
  ext x; simp_rw [mlieBracket, mlieBracketWithin_self, Pi.zero_apply]

/-- Variant of `mlieBracketWithin_congr_set` where one requires the sets to coincide only in
the complement of a point. -/
theorem mlieBracketWithin_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x := by
  simp only [mlieBracketWithin_apply]
  congr 1
  have : T1Space M := I.t1Space M
  suffices A : ((extChartAt I x).symm ⁻¹' s ∩ range I : Set E)
    =ᶠ[𝓝[{(extChartAt I x) x}ᶜ] (extChartAt I x x)]
      ((extChartAt I x).symm ⁻¹' t ∩ range I : Set E) by
    apply lieBracketWithin_congr_set' _ A
  obtain ⟨u, u_mem, hu⟩ : ∃ u ∈ 𝓝 x, u ∩ {x}ᶜ ⊆ {y | (y ∈ s) = (y ∈ t)} :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (nhdsWithin_compl_singleton_le x y h)
  rw [← extChartAt_to_inv (I := I) x] at u_mem
  have B : (extChartAt I x).target ∪ (range I)ᶜ ∈ 𝓝 (extChartAt I x x) := by
    rw [← nhdsWithin_univ, ← union_compl_self (range I), nhdsWithin_union]
    apply Filter.union_mem_sup (extChartAt_target_mem_nhdsWithin x) self_mem_nhdsWithin
  apply mem_nhdsWithin_iff_exists_mem_nhds_inter.2
    ⟨_, Filter.inter_mem ((continuousAt_extChartAt_symm x).preimage_mem_nhds u_mem) B, ?_⟩
  rintro z ⟨hz, h'z⟩
  simp only [eq_iff_iff, mem_setOf_eq]
  change z ∈ (extChartAt I x).symm ⁻¹' s ∩ range I ↔ z ∈ (extChartAt I x).symm ⁻¹' t ∩ range I
  by_cases hIz : z ∈ range I
  · simp [-extChartAt, hIz] at hz ⊢
    rw [← eq_iff_iff]
    apply hu ⟨hz.1, ?_⟩
    simp only [mem_compl_iff, mem_singleton_iff, ne_comm, ne_eq] at h'z ⊢
    rw [(extChartAt I x).eq_symm_apply (by simp) hz.2]
    exact Ne.symm h'z
  · simp [hIz]

theorem mlieBracketWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x :=
  mlieBracketWithin_congr_set' x <| h.filter_mono inf_le_left

theorem mlieBracketWithin_inter (ht : t ∈ 𝓝 x) :
    mlieBracketWithin I V W (s ∩ t) x = mlieBracketWithin I V W s x := by
  apply mlieBracketWithin_congr_set
  filter_upwards [ht] with y hy
  change (y ∈ s ∩ t) = (y ∈ s)
  aesop

theorem mlieBracketWithin_of_mem_nhds (h : s ∈ 𝓝 x) :
    mlieBracketWithin I V W s x = mlieBracket I V W x := by
  rw [← mlieBracketWithin_univ, ← univ_inter s, mlieBracketWithin_inter h]

theorem mlieBracketWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) :
    mlieBracketWithin I V W s x = mlieBracket I V W x :=
  mlieBracketWithin_of_mem_nhds (hs.mem_nhds hx)

/-- Variant of `mlieBracketWithin_eventually_congr_set` where one requires the sets to coincide only
in  the complement of a point. -/
theorem mlieBracketWithin_eventually_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mlieBracketWithin I V W s =ᶠ[𝓝 x] mlieBracketWithin I V W t :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => mlieBracketWithin_congr_set' y

theorem mlieBracketWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    mlieBracketWithin I V W s =ᶠ[𝓝 x] mlieBracketWithin I V W t :=
  mlieBracketWithin_eventually_congr_set' x <| h.filter_mono inf_le_left

theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_eq
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hxV : V₁ x = V x) (hW : W₁ =ᶠ[𝓝[s] x] W) (hxW : W₁ x = W x) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x := by
  simp only [mlieBracketWithin_apply]
  congr 1
  let I1 : NormedAddCommGroup (TangentSpace 𝓘(𝕜, E) (extChartAt I x x)) :=
    inferInstanceAs (NormedAddCommGroup E)
  let _I2 : NormedSpace 𝕜 (TangentSpace 𝓘(𝕜, E) (extChartAt I x x)) :=
    inferInstanceAs (NormedSpace 𝕜 E)
  apply Filter.EventuallyEq.lieBracketWithin_vectorField_eq
  · apply nhdsWithin_mono _ inter_subset_left
    filter_upwards [(continuousAt_extChartAt_symm x).continuousWithinAt.preimage_mem_nhdsWithin''
      hV (by simp)] with y hy
    simp only [mpullbackWithin_apply]
    congr 1
  · simp only [mpullbackWithin_apply]
    congr 1
    convert hxV <;> exact extChartAt_to_inv x
  · apply nhdsWithin_mono _ inter_subset_left
    filter_upwards [(continuousAt_extChartAt_symm x).continuousWithinAt.preimage_mem_nhdsWithin''
      hW (by simp)] with y hy
    simp only [mpullbackWithin_apply]
    congr 1
  · simp only [mpullbackWithin_apply]
    congr 1
    convert hxW <;> exact extChartAt_to_inv x

theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (hx : x ∈ s) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  hV.mlieBracketWithin_vectorField_eq (mem_of_mem_nhdsWithin hx hV :)
    hW (mem_of_mem_nhdsWithin hx hW :)

/-- If vector fields coincide on a neighborhood of a point within a set, then the Lie brackets
also coincide on a neighborhood of this point within this set. Version where one considers the Lie
bracket within a subset. -/
theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField'
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (ht : t ⊆ s) :
    mlieBracketWithin I V₁ W₁ t =ᶠ[𝓝[s] x] mlieBracketWithin I V W t := by
  filter_upwards [hV, hW, eventually_eventually_nhdsWithin.2 hV,
    eventually_eventually_nhdsWithin.2 hW] with y hVy hWy hVy' hWy'
  apply Filter.EventuallyEq.mlieBracketWithin_vectorField_eq
  · apply nhdsWithin_mono _ ht
    exact hVy'
  · exact hVy
  · apply nhdsWithin_mono _ ht
    exact hWy'
  · exact hWy

protected theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) :
    mlieBracketWithin I V₁ W₁ s =ᶠ[𝓝[s] x] mlieBracketWithin I V W s :=
  hV.mlieBracketWithin_vectorField' hW Subset.rfl

protected theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_of_insert
    (hV : V₁ =ᶠ[𝓝[insert x s] x] V) (hW : W₁ =ᶠ[𝓝[insert x s] x] W) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x := by
  apply mem_of_mem_nhdsWithin (mem_insert x s)
    (hV.mlieBracketWithin_vectorField' hW (subset_insert x s))

theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_nhds
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  (hV.filter_mono nhdsWithin_le_nhds).mlieBracketWithin_vectorField_eq hV.self_of_nhds
    (hW.filter_mono nhdsWithin_le_nhds) hW.self_of_nhds

theorem mlieBracketWithin_congr
    (hV : EqOn V₁ V s) (hVx : V₁ x = V x) (hW : EqOn W₁ W s) (hWx : W₁ x = W x) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  (hV.eventuallyEq.filter_mono inf_le_right).mlieBracketWithin_vectorField_eq hVx
    (hW.eventuallyEq.filter_mono inf_le_right) hWx

/-- Version of `mlieBracketWithin_congr` in which one assumes that the point belongs to the
given set. -/
theorem mlieBracketWithin_congr' (hV : EqOn V₁ V s) (hW : EqOn W₁ W s) (hx : x ∈ s) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  mlieBracketWithin_congr hV (hV hx) hW (hW hx)

theorem _root_.Filter.EventuallyEq.mlieBracket_vectorField_eq
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    mlieBracket I V₁ W₁ x = mlieBracket I V W x := by
  rw [← mlieBracketWithin_univ, ← mlieBracketWithin_univ,
    hV.mlieBracketWithin_vectorField_eq_nhds hW]

protected theorem _root_.Filter.EventuallyEq.mlieBracket_vectorField
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) : mlieBracket I V₁ W₁ =ᶠ[𝓝 x] mlieBracket I V W := by
  filter_upwards [hV.eventuallyEq_nhds, hW.eventuallyEq_nhds] with y hVy hWy
  exact hVy.mlieBracket_vectorField_eq hWy

section C2

variable {c : 𝕜}
variable [IsManifold I 2 M] [CompleteSpace E]

lemma _root_.MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField
    (hV : MDifferentiableWithinAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) s x) :
    DifferentiableWithinAt 𝕜 (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
    ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  apply MDifferentiableWithinAt.differentiableWithinAt
  have := MDifferentiableWithinAt.mpullbackWithin_vectorField_inter_of_eq hV
    (contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target x))
    (isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target x)) (mem_range_self _)
    I.uniqueMDiffOn le_rfl (extChartAt_to_inv x).symm
  rw [inter_comm]
  exact ((contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).contMDiffAt.mdifferentiableAt
    le_rfl).comp_mdifferentiableWithinAt _ this

lemma mlieBracketWithin_smul_left
    (hV : MDifferentiableWithinAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mlieBracketWithin I (c • V) W s x = c • mlieBracketWithin I V W s x := by
  simp only [mlieBracketWithin_apply]
  rw [← ContinuousLinearMap.map_smul, mpullbackWithin_smul, lieBracketWithin_smul_left]
  · exact hV.differentiableWithinAt_mpullbackWithin_vectorField
  · exact uniqueMDiffWithinAt_iff_inter_range.1 hs

lemma mlieBracket_smul_left
    (hV : MDifferentiableAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) x) :
    mlieBracket I (c • V) W  x = c • mlieBracket I V W x := by
  simp only [← mlieBracketWithin_univ, ← contMDiffWithinAt_univ] at hV ⊢
  exact mlieBracketWithin_smul_left hV (uniqueMDiffWithinAt_univ _)

lemma mlieBracketWithin_smul_right
    (hW : MDifferentiableWithinAt I I.tangent (fun x ↦ (W x : TangentBundle I M)) s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mlieBracketWithin I V (c • W) s x = c • mlieBracketWithin I V W s x := by
  simp only [mlieBracketWithin_apply]
  rw [← ContinuousLinearMap.map_smul, mpullbackWithin_smul, lieBracketWithin_smul_right]
  · exact hW.differentiableWithinAt_mpullbackWithin_vectorField
  · exact uniqueMDiffWithinAt_iff_inter_range.1 hs

lemma mlieBracket_smul_right
    (hW : MDifferentiableAt I I.tangent (fun x ↦ (W x : TangentBundle I M)) x) :
    mlieBracket I V (c • W) x = c • mlieBracket I V W x := by
  simp only [← mlieBracketWithin_univ, ← contMDiffWithinAt_univ] at hW ⊢
  exact mlieBracketWithin_smul_right hW (uniqueMDiffWithinAt_univ _)

lemma mlieBracketWithin_add_left
    (hV : MDifferentiableWithinAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) s x)
    (hV₁ : MDifferentiableWithinAt I I.tangent (fun x ↦ (V₁ x : TangentBundle I M)) s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mlieBracketWithin I (V + V₁) W s x =
      mlieBracketWithin I V W s x + mlieBracketWithin I V₁ W s x := by
  simp only [mlieBracketWithin_apply]
  rw [← ContinuousLinearMap.map_add, mpullbackWithin_add, lieBracketWithin_add_left]
  · exact hV.differentiableWithinAt_mpullbackWithin_vectorField
  · exact hV₁.differentiableWithinAt_mpullbackWithin_vectorField
  · exact uniqueMDiffWithinAt_iff_inter_range.1 hs

lemma mlieBracket_add_left
    (hV : MDifferentiableAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) x)
    (hV₁ : MDifferentiableAt I I.tangent (fun x ↦ (V₁ x : TangentBundle I M)) x) :
    mlieBracket I (V + V₁) W  x =
      mlieBracket I V W x + mlieBracket I V₁ W x := by
  simp only [← mlieBracketWithin_univ, ← contMDiffWithinAt_univ] at hV hV₁ ⊢
  exact mlieBracketWithin_add_left hV hV₁ (uniqueMDiffWithinAt_univ _)

lemma mlieBracketWithin_add_right
    (hW : MDifferentiableWithinAt I I.tangent (fun x ↦ (W x : TangentBundle I M)) s x)
    (hW₁ : MDifferentiableWithinAt I I.tangent (fun x ↦ (W₁ x : TangentBundle I M)) s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mlieBracketWithin I V (W + W₁) s x =
      mlieBracketWithin I V W s x + mlieBracketWithin I V W₁ s x := by
  rw [mlieBracketWithin_swap, Pi.neg_apply, mlieBracketWithin_add_left hW hW₁ hs,
    mlieBracketWithin_swap (V := V), mlieBracketWithin_swap (V := V), Pi.neg_apply, Pi.neg_apply]
  abel

lemma mlieBracket_add_right
    (hW : MDifferentiableAt I I.tangent (fun x ↦ (W x : TangentBundle I M)) x)
    (hW₁ : MDifferentiableAt I I.tangent (fun x ↦ (W₁ x : TangentBundle I M)) x) :
    mlieBracket I V (W + W₁) x =
      mlieBracket I V W x + mlieBracket I V W₁ x := by
  simp only [← mlieBracketWithin_univ, ← contMDiffWithinAt_univ] at hW hW₁ ⊢
  exact mlieBracketWithin_add_right hW hW₁ (uniqueMDiffWithinAt_univ _)

theorem mlieBracketWithin_of_mem_nhdsWithin
    (st : t ∈ 𝓝[s] x) (hs : UniqueMDiffWithinAt I s x)
    (hV : MDifferentiableWithinAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) t x)
    (hW : MDifferentiableWithinAt I I.tangent (fun x ↦ (W x : TangentBundle I M)) t x) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x := by
  simp only [mlieBracketWithin_apply]
  congr 1
  rw [lieBracketWithin_of_mem_nhdsWithin]
  · apply Filter.inter_mem
    · apply nhdsWithin_mono _ inter_subset_left
      exact (continuousAt_extChartAt_symm x).continuousWithinAt.preimage_mem_nhdsWithin''
        st (by simp)
    · exact nhdsWithin_mono _ inter_subset_right self_mem_nhdsWithin
  · exact uniqueMDiffWithinAt_iff_inter_range.1 hs
  · exact hV.differentiableWithinAt_mpullbackWithin_vectorField
  · exact hW.differentiableWithinAt_mpullbackWithin_vectorField

theorem mlieBracketWithin_subset (st : s ⊆ t) (ht : UniqueMDiffWithinAt I s x)
    (hV : MDifferentiableWithinAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) t x)
    (hW : MDifferentiableWithinAt I I.tangent (fun x ↦ (W x : TangentBundle I M)) t x) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x :=
  mlieBracketWithin_of_mem_nhdsWithin (nhdsWithin_mono _ st self_mem_nhdsWithin) ht hV hW

theorem mlieBracketWithin_eq_mlieBracket (hs : UniqueMDiffWithinAt I s x)
    (hV : MDifferentiableAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) x)
    (hW : MDifferentiableAt I I.tangent (fun x ↦ (W x : TangentBundle I M)) x) :
    mlieBracketWithin I V W s x = mlieBracket I V W x := by
  simp only [← mlieBracketWithin_univ, ← mdifferentiableWithinAt_univ] at hV hW ⊢
  exact mlieBracketWithin_subset (subset_univ _) hs hV hW

theorem _root_.DifferentiableWithinAt.mlieBracketWithin_congr_mono
    (hV : MDifferentiableWithinAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) s x)
    (hVs : EqOn V₁ V t) (hVx : V₁ x = V x)
    (hW : MDifferentiableWithinAt I I.tangent (fun x ↦ (W x : TangentBundle I M)) s x)
    (hWs : EqOn W₁ W t) (hWx : W₁ x = W x)
    (hxt : UniqueMDiffWithinAt I t x) (h₁ : t ⊆ s) :
    mlieBracketWithin I V₁ W₁ t x = mlieBracketWithin I V W s x := by
  rw [mlieBracketWithin_congr hVs hVx hWs hWx]
  exact mlieBracketWithin_subset h₁ hxt hV hW

end C2

section Invariance_IsSymmSndFDerivWithinAt

variable [IsManifold I 2 M] [IsManifold I' 2 M'] [CompleteSpace E]

/- The Lie bracket of vector fields on manifolds is well defined, i.e., it is invariant under
diffeomorphisms. Auxiliary version where one assumes that all relevant sets are contained
in chart domains. -/
private lemma mpullbackWithin_mlieBracketWithin_aux [CompleteSpace E']
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (V x : TangentBundle I' M')) t (f x₀))
    (hW : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (W x : TangentBundle I' M')) t (f x₀))
    (hu : UniqueMDiffOn I s) (hf : ContMDiffOn I I' 2 f s) (hx₀ : x₀ ∈ s)
    (ht : t ⊆ (extChartAt I' (f x₀)).source) (hst : MapsTo f s t)
    (hsymm : IsSymmSndFDerivWithinAt 𝕜 ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I) (extChartAt I x₀ x₀)) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ =
      mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ := by
  have A : (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ := by simp
  have A' : x₀ = (extChartAt I x₀).symm (extChartAt I x₀ x₀) := by simp
  have h'f : MDifferentiableWithinAt I I' f s x₀ := (hf x₀ hx₀).mdifferentiableWithinAt one_le_two
  simp only [mlieBracketWithin_apply, mpullbackWithin_apply]
  -- first, rewrite the pullback of the Lie bracket as a pullback in `E` under the map
  -- `F = extChartAt I' (f x₀) ∘ f ∘ (extChartAt I x₀).symm` of a Lie bracket computed in `E'`,
  -- of two vector fields `V'` and `W'`.
  rw [← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_left
    (isInvertible_mfderiv_extChartAt (mem_extChartAt_source (f x₀)))]
  rw [← mfderiv_comp_mfderivWithin _ (mdifferentiableAt_extChartAt
    (ChartedSpace.mem_chart_source (f x₀))) h'f (hu x₀ hx₀)]
  rw [eq_comm, (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x₀)).inverse_apply_eq]
  have : (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) (extChartAt I x₀ x₀)).inverse =
      mfderiv I 𝓘(𝕜, E) (extChartAt I x₀) x₀ := by
    apply ContinuousLinearMap.inverse_eq
    · convert mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) (x := x₀)
        (y := extChartAt I x₀ x₀) (by simp)
    · convert mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x₀)
        (y := extChartAt I x₀ x₀) (by simp)
  rw [← this, ← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_right]; swap
  · exact isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target x₀)
  have : mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) (extChartAt I x₀ x₀) =
      mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm ((extChartAt I x₀).symm ⁻¹' s ∩ range I)
      (extChartAt I x₀ x₀) :=
    (MDifferentiableWithinAt.mfderivWithin_mono
      (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x₀))
      (UniqueDiffWithinAt.uniqueMDiffWithinAt (hu x₀ hx₀)) inter_subset_right).symm
  rw [this]; clear this
  rw [← mfderivWithin_comp_of_eq]; rotate_left
  · apply MDifferentiableAt.comp_mdifferentiableWithinAt (I' := I') _ _ h'f
    exact mdifferentiableAt_extChartAt (ChartedSpace.mem_chart_source (f x₀))
  · exact (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x₀)).mono
      inter_subset_right
  · exact inter_subset_left
  · exact UniqueDiffWithinAt.uniqueMDiffWithinAt (hu x₀ hx₀)
  · simp
  set V' := mpullbackWithin 𝓘(𝕜, E') I' (extChartAt I' (f x₀)).symm V (range I') with hV'
  set W' := mpullbackWithin 𝓘(𝕜, E') I' (extChartAt I' (f x₀)).symm W (range I') with hW'
  set F := ((extChartAt I' (f x₀)) ∘ f) ∘ ↑(extChartAt I x₀).symm with hF
  have hFx₀ : extChartAt I' (f x₀) (f x₀) = F (extChartAt I x₀ x₀) := by simp [F]
  rw [hFx₀, ← mpullbackWithin_apply]
  -- second rewrite, the Lie bracket of the pullback as the Lie bracket of the pullback of the
  -- vector fields `V'` and `W'` in `E'`.
  have P (Y : (x : M') → TangentSpace I' x) :
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (mpullbackWithin I I' f Y s)
      (range I)) =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' s ∩ range I] (extChartAt I x₀ x₀)]
        mpullbackWithin 𝓘(𝕜, E) 𝓘(𝕜, E') F
          (mpullbackWithin 𝓘(𝕜, E') I' ((extChartAt I' (f x₀)).symm) Y (range I'))
          ((extChartAt I x₀).symm ⁻¹' s ∩ range I) := by
    have : (extChartAt I x₀).target
        ∈ 𝓝[(extChartAt I x₀).symm ⁻¹' s ∩ range I] (extChartAt I x₀ x₀) :=
      nhdsWithin_mono _ inter_subset_right (extChartAt_target_mem_nhdsWithin x₀)
    filter_upwards [self_mem_nhdsWithin, this] with y hy h'''y
    have h'y : f ((extChartAt I x₀).symm y) ∈ (extChartAt I' (f x₀)).source := ht (hst hy.1)
    have h''y : f ((extChartAt I x₀).symm y) ∈ (chartAt H' (f x₀)).source := by simpa using h'y
    have huy : UniqueMDiffWithinAt 𝓘(𝕜, E) ((extChartAt I x₀).symm ⁻¹' s ∩ range I) y := by
      apply UniqueDiffWithinAt.uniqueMDiffWithinAt
      rw [inter_comm]
      apply hu.uniqueDiffWithinAt_range_inter
      exact ⟨h'''y, hy.1⟩
    simp only [mpullbackWithin_apply, hF, comp_apply, ← mfderivWithin_eq_fderivWithin]
    rw [mfderivWithin_comp (I' := I) (u := s)]; rotate_left
    · apply (mdifferentiableAt_extChartAt h''y).comp_mdifferentiableWithinAt (I' := I')
      exact (hf _ hy.1).mdifferentiableWithinAt one_le_two
    · exact (mdifferentiableWithinAt_extChartAt_symm h'''y).mono inter_subset_right
    · exact inter_subset_left
    · exact huy
    rw [mfderiv_comp_mfderivWithin (I' := I')]; rotate_left
    · exact mdifferentiableAt_extChartAt h''y
    · exact (hf _ hy.1).mdifferentiableWithinAt one_le_two
    · exact hu _ hy.1
    rw [← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_right]; swap
    · exact isInvertible_mfderivWithin_extChartAt_symm h'''y
    rw [← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_left]; swap
    · exact isInvertible_mfderivWithin_extChartAt_symm (PartialEquiv.map_source _ h'y)
    have : f ((extChartAt I x₀).symm y)
        = (extChartAt I' (f x₀)).symm ((extChartAt I' (f x₀)) (f ((extChartAt I x₀).symm y))) :=
      (PartialEquiv.left_inv (extChartAt I' (f x₀)) h'y).symm
    congr 2
    have : (mfderivWithin 𝓘(𝕜, E') I' ((extChartAt I' (f x₀)).symm) (range I')
        (extChartAt I' (f x₀) (f ((extChartAt I x₀).symm y)))) ∘L
        (mfderiv I' 𝓘(𝕜, E') (↑(extChartAt I' (f x₀))) (f ((extChartAt I x₀).symm y))) =
        ContinuousLinearMap.id _ _ := by
      convert mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
        ((PartialEquiv.map_source _ h'y))
    simp only [← ContinuousLinearMap.comp_assoc, this, ContinuousLinearMap.id_comp]
    congr 1
    exact ((mdifferentiableWithinAt_extChartAt_symm h'''y).mfderivWithin_mono huy
      inter_subset_right).symm
  rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem (P V) (P W) (by simp [hx₀]),
    ← hV', ← hW']
  simp only [mpullbackWithin_eq_pullbackWithin]
  -- finally, use the fact that for `C^2` maps between vector spaces with symmetric second
  -- derivative, the pullback and the Lie bracket commute.
  rw [pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt_of_eventuallyEq
      (u := (extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target)]
  · exact hsymm
  · rw [hF, comp_assoc]
    apply ContMDiffWithinAt.contDiffWithinAt
    apply ContMDiffAt.comp_contMDiffWithinAt (I' := I')
    · exact contMDiffAt_extChartAt' (by simp)
    apply ContMDiffWithinAt.comp_of_eq (I' := I) (hf _ hx₀) _ _ A
    · exact (contMDiffWithinAt_extChartAt_symm_range _ (mem_extChartAt_target x₀)).mono
        inter_subset_right
    · exact (mapsTo_preimage _ _).mono_left inter_subset_left
  · rw [← hFx₀]
    exact hV.differentiableWithinAt_mpullbackWithin_vectorField
  · rw [← hFx₀]
    exact hW.differentiableWithinAt_mpullbackWithin_vectorField
  · rw [inter_comm]
    exact UniqueMDiffOn.uniqueDiffOn_target_inter hu x₀
  · simp [hx₀]
  · intro z hz
    simp only [comp_apply, mem_inter_iff, mem_preimage, mem_range, F]
    refine ⟨?_, mem_range_self _⟩
    convert hst hz.1
    exact PartialEquiv.left_inv (extChartAt I' (f x₀)) (ht (hst hz.1))
  · rw [← nhdsWithin_eq_iff_eventuallyEq]
    apply le_antisymm
    · exact nhdsWithin_mono _ (inter_subset_inter_right _ (extChartAt_target_subset_range x₀))
    · rw [nhdsWithin_le_iff, nhdsWithin_inter]
      exact Filter.inter_mem_inf self_mem_nhdsWithin (extChartAt_target_mem_nhdsWithin x₀)

/- The Lie bracket of vector fields on manifolds is well defined, i.e., it is invariant under
diffeomorphisms. -/
lemma mpullbackWithin_mlieBracketWithin_of_isSymmSndFDerivWithinAt
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (V x : TangentBundle I' M')) t (f x₀))
    (hW : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (W x : TangentBundle I' M')) t (f x₀))
    (hu : UniqueMDiffOn I s) (hf : ContMDiffWithinAt I I' 2 f s x₀) (hx₀ : x₀ ∈ s)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hsymm : IsSymmSndFDerivWithinAt 𝕜 ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I) (extChartAt I x₀ x₀)) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ =
      mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ := by
  have A : (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ := by simp
  by_cases hfi : (mfderivWithin I I' f s x₀).IsInvertible; swap
  · simp only [mlieBracketWithin_apply, mpullbackWithin_apply,
      ContinuousLinearMap.inverse_of_not_isInvertible hfi, ContinuousLinearMap.zero_apply]
    rw [lieBracketWithin_eq_zero_of_eq_zero]
    · simp [-extChartAt]
    · simp only [mpullbackWithin_apply]
      rw [A, ContinuousLinearMap.inverse_of_not_isInvertible hfi]
      simp [-extChartAt]
    · simp only [mpullbackWithin_apply]
      rw [A, ContinuousLinearMap.inverse_of_not_isInvertible hfi]
      simp [-extChartAt]
  -- Now, interesting case where the derivative of `f` is invertible
  have : CompleteSpace E' := by
    rcases hfi with ⟨M, -⟩
    let M' : E ≃L[𝕜] E' := M
    exact (completeSpace_congr (e := M'.toEquiv) M'.isUniformEmbedding).1 (by assumption)
  -- choose a small open set `v` around `x₀` where `f` is `C^2`
  obtain ⟨u, u_open, x₀u, ut, maps_u, u_smooth⟩ :
      ∃ u, IsOpen u ∧ x₀ ∈ u ∧ s ∩ u ⊆ f ⁻¹' t ∧
        s ∩ u ⊆ f ⁻¹' (extChartAt I' (f x₀)).source ∧ ContMDiffOn I I' 2 f (s ∩ u) := by
    obtain ⟨u, u_open, x₀u, hu⟩ :
        ∃ u, IsOpen u ∧ x₀ ∈ u ∧ ContMDiffOn I I' 2 f (insert x₀ s ∩ u) :=
      hf.contMDiffOn' le_rfl (by simp)
    have : f ⁻¹' (extChartAt I' (f x₀)).source ∈ 𝓝[s] x₀ :=
      hf.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (f x₀))
    rcases mem_nhdsWithin.1 (Filter.inter_mem hst this) with ⟨w, w_open, x₀w, hw⟩
    refine ⟨u ∩ w, u_open.inter w_open, by simp [x₀u, x₀w], ?_, ?_, ?_⟩
    · apply Subset.trans _ (hw.trans inter_subset_left)
      exact fun y hy ↦ ⟨hy.2.2, hy.1⟩
    · apply Subset.trans _ (hw.trans inter_subset_right)
      exact fun y hy ↦ ⟨hy.2.2, hy.1⟩
    · apply hu.mono
      exact fun y hy ↦ ⟨subset_insert _ _ hy.1, hy.2.1⟩
  have u_mem : u ∈ 𝓝 x₀ := u_open.mem_nhds x₀u
  -- apply the auxiliary version to `s ∩ u`
  set s' := s ∩ u with hs'
  have s'_eq : s' =ᶠ[𝓝 x₀] s := by
    filter_upwards [u_mem] with y hy
    change (y ∈ s ∩ u) = (y ∈ s)
    simp [hy]
  set t' := t ∩ (extChartAt I' (f x₀)).source with ht'
  calc mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀
  _ = mpullbackWithin I I' f (mlieBracketWithin I' V W t) s' x₀ := by
    simp only [mpullbackWithin, hs', mfderivWithin_inter u_mem]
  _ = mpullbackWithin I I' f (mlieBracketWithin I' V W t') s' x₀ := by
    simp only [mpullbackWithin, ht', mlieBracketWithin_inter (extChartAt_source_mem_nhds (f x₀))]
  _ = mlieBracketWithin I (mpullbackWithin I I' f V s') (mpullbackWithin I I' f W s') s' x₀ := by
    apply mpullbackWithin_mlieBracketWithin_aux (t := t') (hV.mono inter_subset_left)
      (hW.mono inter_subset_left) (hu.inter u_open) u_smooth ⟨hx₀, x₀u⟩ inter_subset_right
      (fun y hy ↦ ⟨ut hy, maps_u hy⟩)
    apply hsymm.congr_set
    have : (extChartAt I x₀).symm ⁻¹' u ∈ 𝓝 (extChartAt I x₀ x₀) := by
      apply (continuousAt_extChartAt_symm x₀).preimage_mem_nhds
      apply u_open.mem_nhds (by simpa using x₀u)
    filter_upwards [this] with y hy
    change (y ∈ (extChartAt I x₀).symm ⁻¹' s ∩ range I) =
      (y ∈ (extChartAt I x₀).symm ⁻¹' (s ∩ u) ∩ range I)
    simp [-extChartAt, hy]
  _ = mlieBracketWithin I (mpullbackWithin I I' f V s') (mpullbackWithin I I' f W s') s x₀ := by
    simp only [hs', mlieBracketWithin_inter u_mem]
  _ = mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ := by
    apply Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem _ _ hx₀
    · apply nhdsWithin_le_nhds
      filter_upwards [mfderivWithin_eventually_congr_set (I := I) (I' := I') (f := f) s'_eq]
        with y hy using by simp [mpullbackWithin, hy]
    · apply nhdsWithin_le_nhds
      filter_upwards [mfderivWithin_eventually_congr_set (I := I) (I' := I') (f := f) s'_eq]
        with y hy using by simp [mpullbackWithin, hy]

end Invariance_IsSymmSndFDerivWithinAt

section Invariance

variable [IsManifold I (minSmoothness 𝕜 2) M] [IsManifold I' (minSmoothness 𝕜 2) M']
  [CompleteSpace E] {n : WithTop ℕ∞}

/-- The pullback commutes with the Lie bracket of vector fields on manifolds. Version where one
assumes that the map is smooth on a larget set `u` (so that the
condition `x₀ ∈ closure (interior u)`, needed to guarantee the symmetry of the second derivative,
becomes easier to check.) -/
lemma mpullbackWithin_mlieBracketWithin'
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s u : Set M} {t : Set M'}
    (hV : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (V x : TangentBundle I' M')) t (f x₀))
    (hW : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (W x : TangentBundle I' M')) t (f x₀))
    (hs : UniqueMDiffOn I s) (hu : UniqueMDiffOn I u)
    (hf : ContMDiffWithinAt I I' n f u x₀) (hx₀ : x₀ ∈ s) (hn : minSmoothness 𝕜 2 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (h'x₀ : x₀ ∈ closure (interior u)) (hsu : s ⊆ u) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ =
      mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ := by
  have B : ContDiffWithinAt 𝕜 n ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).symm ⁻¹' u ∩ (extChartAt I x₀).target) (extChartAt I x₀ x₀) := by
    apply (contMDiffWithinAt_iff.1 hf).2.congr_set
    exact EventuallyEq.inter (by rfl) extChartAt_target_eventuallyEq.symm
  apply mpullbackWithin_mlieBracketWithin_of_isSymmSndFDerivWithinAt hV hW hs
    ((hf.mono hsu).of_le (le_minSmoothness.trans hn)) hx₀ hst
  have : ((extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target : Set E)
      =ᶠ[𝓝 (extChartAt I x₀ x₀)] ((extChartAt I x₀).symm ⁻¹' s ∩ range I : Set E) :=
    EventuallyEq.inter (by rfl) extChartAt_target_eventuallyEq
  apply IsSymmSndFDerivWithinAt.congr_set _ this
  have : IsSymmSndFDerivWithinAt 𝕜 ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).symm ⁻¹' u ∩ (extChartAt I x₀).target) (extChartAt I x₀ x₀) := by
    apply ContDiffWithinAt.isSymmSndFDerivWithinAt (n := minSmoothness 𝕜 2) _ le_rfl
    · rw [inter_comm]
      exact UniqueMDiffOn.uniqueDiffOn_target_inter hu x₀
    · apply extChartAt_mem_closure_interior h'x₀ (mem_extChartAt_source x₀)
    · simp [hsu hx₀]
    · exact B.of_le hn
  apply IsSymmSndFDerivWithinAt.mono_of_mem_nhdsWithin this
  · apply mem_of_superset self_mem_nhdsWithin (inter_subset_inter_left _ (preimage_mono hsu))
  · exact (B.of_le hn).of_le le_minSmoothness
  · rw [inter_comm]
    exact UniqueMDiffOn.uniqueDiffOn_target_inter hs x₀
  · rw [inter_comm]
    exact UniqueMDiffOn.uniqueDiffOn_target_inter hu x₀
  · simp [hx₀]

/-- The pullback commutes with the Lie bracket of vector fields on manifolds. -/
lemma mpullbackWithin_mlieBracketWithin
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (V x : TangentBundle I' M')) t (f x₀))
    (hW : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (W x : TangentBundle I' M')) t (f x₀))
    (hu : UniqueMDiffOn I s) (hf : ContMDiffWithinAt I I' n f s x₀) (hx₀ : x₀ ∈ s)
    (hn : minSmoothness 𝕜 2 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (h'x₀ : x₀ ∈ closure (interior s)) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ =
      mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ :=
  mpullbackWithin_mlieBracketWithin' hV hW hu hu hf hx₀ hn hst h'x₀ Subset.rfl

/-- The pullback commutes with the Lie bracket of vector fields on manifolds. -/
lemma mpullback_mlieBracketWithin
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (V x : TangentBundle I' M')) t (f x₀))
    (hW : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (W x : TangentBundle I' M')) t (f x₀))
    (hu : UniqueMDiffOn I s) (hf : ContMDiffAt I I' n f x₀) (hx₀ : x₀ ∈ s)
    (hn : minSmoothness 𝕜 2 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀) :
    mpullback I I' f (mlieBracketWithin I' V W t) x₀ =
      mlieBracketWithin I (mpullback I I' f V) (mpullback I I' f W) s x₀ := by
  have : mpullback I I' f (mlieBracketWithin I' V W t) x₀ =
      mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ := by
    simp only [mpullback, mpullbackWithin]
    congr
    apply (mfderivWithin_eq_mfderiv (hu _ hx₀) _).symm
    exact hf.mdifferentiableAt (one_le_two.trans (le_minSmoothness.trans hn))
  rw [this, mpullbackWithin_mlieBracketWithin' hV hW hu uniqueMDiffOn_univ hf.contMDiffWithinAt
    hx₀ hn hst (by simp) (subset_univ _)]
  apply Filter.EventuallyEq.mlieBracketWithin_vectorField_of_insert
  · rw [insert_eq_of_mem hx₀]
    filter_upwards [nhdsWithin_le_nhds ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1
      (hf.of_le (le_minSmoothness.trans hn))), self_mem_nhdsWithin] with y hy h'y
    simp only [mpullback, mpullbackWithin]
    congr
    apply mfderivWithin_eq_mfderiv (hu _ h'y)
    exact hy.mdifferentiableAt one_le_two
  · rw [insert_eq_of_mem hx₀]
    filter_upwards [nhdsWithin_le_nhds ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1
      (hf.of_le (le_minSmoothness.trans hn))), self_mem_nhdsWithin] with y hy h'y
    simp only [mpullback, mpullbackWithin]
    congr
    apply mfderivWithin_eq_mfderiv (hu _ h'y)
    exact hy.mdifferentiableAt one_le_two

lemma mpullback_mlieBracket
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M}
    (hV : MDifferentiableAt I' I'.tangent (fun x ↦ (V x : TangentBundle I' M')) (f x₀))
    (hW : MDifferentiableAt I' I'.tangent (fun x ↦ (W x : TangentBundle I' M')) (f x₀))
    (hf : ContMDiffAt I I' n f x₀) (hn : minSmoothness 𝕜 2 ≤ n) :
    mpullback I I' f (mlieBracket I' V W) x₀ =
      mlieBracket I (mpullback I I' f V) (mpullback I I' f W) x₀ := by
  simp only [← mlieBracketWithin_univ, ← mdifferentiableWithinAt_univ] at hV hW ⊢
  exact mpullback_mlieBracketWithin hV hW uniqueMDiffOn_univ hf (mem_univ _) hn (by simp)

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
protected lemma _root_.ContMDiffWithinAt.mlieBracketWithin_vectorField
    [IsManifold I (n + 1) M] {m : WithTop ℕ∞}
    {U V : Π (x : M), TangentSpace I x} {s : Set M} {x : M}
    (hU : ContMDiffWithinAt I I.tangent n (fun x ↦ (U x : TangentBundle I M)) s x)
    (hV : ContMDiffWithinAt I I.tangent n (fun x ↦ (V x : TangentBundle I M)) s x)
    (hs : UniqueMDiffOn I s) (hx : x ∈ s) (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    ContMDiffWithinAt I I.tangent m
      (fun x ↦ (mlieBracketWithin I U V s x : TangentBundle I M)) s x := by
  /- The statement is not obvious, since at different points the Lie bracket is defined using
  different charts. However, since we know that the Lie bracket is invariant under diffeos, we can
  use a single chart to prove the statement. Let `U'` and `V'` denote the pullbacks of `U` and `V`
  in the chart around `x`. Then the Lie bracket there is smooth (as it coincides with the vector
  space Lie bracket, given by an explicit formula). Pulling back this Lie bracket in `M` gives
  locally a smooth function, which coincides with the initial Lie bracket by invariance
  under diffeos. -/
  have min2 : minSmoothness 𝕜 2 ≤ n + 1 := by
    apply le_trans _ (add_le_add_right hmn 1)
    rw [← minSmoothness_add, add_assoc]
    exact minSmoothness_monotone le_add_self
  apply contMDiffWithinAt_iff_le_ne_infty.2 (fun m' hm' h'm' ↦ ?_)
  have hn : 1 ≤ m' + 1 := le_add_self
  have hm'n : m' + 1 ≤ n := le_trans (add_le_add_right hm' 1) (le_minSmoothness.trans hmn)
  have : IsManifold I (m' + 1) M := IsManifold.of_le (n := n + 1) (hm'n.trans le_self_add)
  have pre_mem : (extChartAt I x) ⁻¹' ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)
      ∈ 𝓝[s] x := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := I) x)] with y hy h'y
    exact ⟨(extChartAt I x).map_source h'y,
      by simpa only [mem_preimage, (extChartAt I x).left_inv h'y] using hy⟩
  let U' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm U (range I)
  let V' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)
  have A : ContDiffWithinAt 𝕜 m' (lieBracketWithin 𝕜 U' V'
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) :=
    ContDiffWithinAt.lieBracketWithin_vectorField
      (contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.1
        (contMDiffWithinAt_mpullbackWithin_extChartAt_symm hU hs hx le_rfl))
      (contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.1
        (contMDiffWithinAt_mpullbackWithin_extChartAt_symm hV hs hx le_rfl))
      (hs.uniqueDiffOn_target_inter x) hm'n (by simp [hx])
  have B : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent m' (fun y ↦ (mlieBracketWithin 𝓘(𝕜, E) U' V'
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) y : TangentBundle 𝓘(𝕜, E) E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) := by
    rw [← mlieBracketWithin_eq_lieBracketWithin] at A
    exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.2 A
  have C : ContMDiffWithinAt I I.tangent m' (fun y ↦ (mpullback I 𝓘(𝕜, E) (extChartAt I x)
      ((mlieBracketWithin 𝓘(𝕜, E) U' V'
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s))) y : TangentBundle I M)) s x :=
    ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin_of_eq B (n := m' + 1)
      contMDiffAt_extChartAt
      (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)) le_rfl pre_mem rfl
  apply C.congr_of_eventuallyEq_of_mem _ hx
  filter_upwards [eventually_eventually_nhdsWithin.2 pre_mem,
    eventually_eventually_nhdsWithin.2 (eventuallyEq_mpullback_mpullbackWithin_extChartAt U),
    eventually_eventually_nhdsWithin.2 (eventuallyEq_mpullback_mpullbackWithin_extChartAt V),
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm (hU.of_le hm'n) hs hx
      (add_le_add_right hm'n 1) (by simp [h'm']),
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm (hV.of_le hm'n) hs hx
      (add_le_add_right hm'n 1) (by simp [h'm']),
    nhdsWithin_le_nhds (chart_source_mem_nhds H x), self_mem_nhdsWithin]
    with y hy hyU hyV h'yU h'yV hy_chart hys
  simp only [Bundle.TotalSpace.mk_inj]
  rw [mpullback_mlieBracketWithin (h'yU.mdifferentiableWithinAt hn)
    (h'yV.mdifferentiableWithinAt hn) hs (contMDiffAt_extChartAt' hy_chart) hys min2 hy]
  exact Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem hyU hyV hys

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
lemma _root_.ContMDiffAt.mlieBracket_vectorField {m n : ℕ∞}
    [IsManifold I (n + 1) M] {U V : Π (x : M), TangentSpace I x} {x : M}
    (hU : ContMDiffAt I I.tangent n (fun x ↦ (U x : TangentBundle I M)) x)
    (hV : ContMDiffAt I I.tangent n (fun x ↦ (V x : TangentBundle I M)) x)
    (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    ContMDiffAt I I.tangent m (fun x ↦ (mlieBracket I U V x : TangentBundle I M)) x := by
  simp only [← contMDiffWithinAt_univ, ← mlieBracketWithin_univ] at hU hV ⊢
  exact hU.mlieBracketWithin_vectorField hV uniqueMDiffOn_univ (mem_univ _) hmn

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
lemma _root_.ContMDiffOn.mlieBracketWithin_vectorField {m n : ℕ∞}
    [IsManifold I (n + 1) M] {U V : Π (x : M), TangentSpace I x}
    (hU : ContMDiffOn I I.tangent n (fun x ↦ (U x : TangentBundle I M)) s)
    (hV : ContMDiffOn I I.tangent n (fun x ↦ (V x : TangentBundle I M)) s)
    (hs : UniqueMDiffOn I s) (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    ContMDiffOn I I.tangent m (fun x ↦ (mlieBracketWithin I U V s x : TangentBundle I M)) s :=
  fun x hx ↦ (hU x hx).mlieBracketWithin_vectorField (hV x hx) hs hx hmn

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
lemma _root_.ContDiff.mlieBracket_vectorField {m n : ℕ∞}
    [IsManifold I (n + 1) M] {U V : Π (x : M), TangentSpace I x}
    (hU : ContMDiff I I.tangent n (fun x ↦ (U x : TangentBundle I M)))
    (hV : ContMDiff I I.tangent n (fun x ↦ (V x : TangentBundle I M)))
    (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    ContMDiff I I.tangent m (fun x ↦ (mlieBracket I U V x : TangentBundle I M)) := by
  simp only [← contMDiffOn_univ, mlieBracketWithin_univ] at hU hV ⊢
  exact hU.mlieBracketWithin_vectorField hV uniqueMDiffOn_univ hmn

end Invariance

section Leibniz

variable [IsManifold I (minSmoothness 𝕜 3) M] [CompleteSpace E]

/-- The Lie bracket of vector fields in manifolds satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]` (also called Jacobi identity). -/
theorem leibniz_identity_mlieBracketWithin_apply
    {U V W : Π (x : M), TangentSpace I x} {s : Set M} {x : M}
    (hs : UniqueMDiffOn I s) (h's : x ∈ closure (interior s)) (hx : x ∈ s)
    (hU : ContMDiffWithinAt I I.tangent (minSmoothness 𝕜 2)
      (fun x ↦ (U x : TangentBundle I M)) s x)
    (hV : ContMDiffWithinAt I I.tangent (minSmoothness 𝕜 2)
      (fun x ↦ (V x : TangentBundle I M)) s x)
    (hW : ContMDiffWithinAt I I.tangent (minSmoothness 𝕜 2)
      (fun x ↦ (W x : TangentBundle I M)) s x) :
    mlieBracketWithin I U (mlieBracketWithin I V W s) s x =
      mlieBracketWithin I (mlieBracketWithin I U V s) W s x
      + mlieBracketWithin I V (mlieBracketWithin I U W s) s x := by
  have A : minSmoothness 𝕜 2 + 1 ≤ minSmoothness 𝕜 3 := by
    simp only [← minSmoothness_add]
    exact le_rfl
  have s_inter_mem : s ∩ (extChartAt I x).source ∈ 𝓝[s] x :=
    inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (extChartAt_source_mem_nhds x))
  have pre_mem : (extChartAt I x) ⁻¹' ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)
      ∈ 𝓝[s] x := by
    filter_upwards [s_inter_mem] with y hy
    exact ⟨(extChartAt I x).map_source hy.2,
      by simpa only [mem_preimage, (extChartAt I x).left_inv hy.2] using hy.1⟩
  -- write everything as pullbacks of vector fields in `E` (denoted with primes), for which
  -- the identity can be checked via direct calculation.
  let U' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm U (range I)
  let V' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)
  let W' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (range I)
  -- register basic facts on the pullbacks in the vector space
  have J0U : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent (minSmoothness 𝕜 2)
      (fun y ↦ (U' y : TangentBundle 𝓘(𝕜, E) E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) :=
    contMDiffWithinAt_mpullbackWithin_extChartAt_symm hU hs hx A
  have J0V : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent (minSmoothness 𝕜 2)
      (fun y ↦ (V' y : TangentBundle 𝓘(𝕜, E) E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) :=
    contMDiffWithinAt_mpullbackWithin_extChartAt_symm hV hs hx A
  have J0W : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent (minSmoothness 𝕜 2)
      (fun y ↦ (W' y : TangentBundle 𝓘(𝕜, E) E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) :=
    contMDiffWithinAt_mpullbackWithin_extChartAt_symm hW hs hx A
  have J1U : ∀ᶠ y in 𝓝[s] x, ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent (minSmoothness 𝕜 2)
      (fun y ↦ (U' y : TangentBundle 𝓘(𝕜, E) E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x y) :=
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm hU hs hx A (by simp)
  have J1V : ∀ᶠ y in 𝓝[s] x, ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent (minSmoothness 𝕜 2)
      (fun y ↦ (V' y : TangentBundle 𝓘(𝕜, E) E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x y) :=
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm hV hs hx A (by simp)
  have J1W : ∀ᶠ y in 𝓝[s] x, ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent (minSmoothness 𝕜 2)
      (fun y ↦ (W' y : TangentBundle 𝓘(𝕜, E) E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x y) :=
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm hW hs hx A (by simp)
  have JU : U =ᶠ[𝓝[s] x] mpullback I 𝓘(𝕜, E) (extChartAt I x) U' :=
    eventuallyEq_mpullback_mpullbackWithin_extChartAt U
  have JV : V =ᶠ[𝓝[s] x] mpullback I 𝓘(𝕜, E) (extChartAt I x) V' :=
    eventuallyEq_mpullback_mpullbackWithin_extChartAt V
  have JW : W =ᶠ[𝓝[s] x] mpullback I 𝓘(𝕜, E) (extChartAt I x) W' :=
    eventuallyEq_mpullback_mpullbackWithin_extChartAt W
  rw [JU.mlieBracketWithin_vectorField_eq_of_mem (JV.mlieBracketWithin_vectorField JW) hx,
    (JU.mlieBracketWithin_vectorField JV).mlieBracketWithin_vectorField_eq_of_mem JW hx,
    JV.mlieBracketWithin_vectorField_eq_of_mem (JU.mlieBracketWithin_vectorField JW) hx]
  /- Rewrite the first term as a pullback-/
  have : ∀ᶠ y in 𝓝[s] x, mlieBracketWithin I
        (mpullback I 𝓘(𝕜, E) (extChartAt I x) V') (mpullback I 𝓘(𝕜, E) (extChartAt I x) W') s y
      = mpullback I 𝓘(𝕜, E) (extChartAt I x) (mlieBracketWithin 𝓘(𝕜, E) V' W'
        ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)) y := by
    filter_upwards [eventually_eventually_nhdsWithin.2 pre_mem, J1V, J1W,
      nhdsWithin_le_nhds (chart_source_mem_nhds H x), self_mem_nhdsWithin] with y hy hyV hyW h'y ys
    symm
    exact mpullback_mlieBracketWithin (n := minSmoothness 𝕜 2)
      (hyV.mdifferentiableWithinAt (one_le_two.trans le_minSmoothness))
      (hyW.mdifferentiableWithinAt (one_le_two.trans le_minSmoothness)) hs
      (contMDiffAt_extChartAt' h'y) ys le_rfl hy
  rw [Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem EventuallyEq.rfl this hx,
    ← mpullback_mlieBracketWithin (J0U.mdifferentiableWithinAt (one_le_two.trans le_minSmoothness))
      _ hs contMDiffAt_extChartAt hx le_rfl pre_mem]; swap
  · apply ContMDiffWithinAt.mdifferentiableWithinAt _ le_rfl
    apply J0V.mlieBracketWithin_vectorField J0W (m := 1)
    · exact hs.uniqueMDiffOn_target_inter x
    · exact ⟨mem_extChartAt_target x, by simp [hx]⟩
    · exact le_rfl
  /- Rewrite the second term as a pullback-/
  have : ∀ᶠ y in 𝓝[s] x, mlieBracketWithin I
        (mpullback I 𝓘(𝕜, E) (extChartAt I x) U') (mpullback I 𝓘(𝕜, E) (extChartAt I x) V') s y
      = mpullback I 𝓘(𝕜, E) (extChartAt I x) (mlieBracketWithin 𝓘(𝕜, E) U' V'
        ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)) y := by
    filter_upwards [eventually_eventually_nhdsWithin.2 pre_mem, J1U, J1V,
      nhdsWithin_le_nhds (chart_source_mem_nhds H x), self_mem_nhdsWithin] with y hy hyU hyV h'y ys
    symm
    exact mpullback_mlieBracketWithin (n := minSmoothness 𝕜 2)
      (hyU.mdifferentiableWithinAt (one_le_two.trans le_minSmoothness))
      (hyV.mdifferentiableWithinAt (one_le_two.trans le_minSmoothness)) hs
      (contMDiffAt_extChartAt' h'y) ys le_rfl hy
  rw [Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem this EventuallyEq.rfl hx,
    ← mpullback_mlieBracketWithin _ (J0W.mdifferentiableWithinAt
      (one_le_two.trans le_minSmoothness)) hs contMDiffAt_extChartAt hx le_rfl pre_mem]; swap
  · apply ContMDiffWithinAt.mdifferentiableWithinAt _ le_rfl
    apply J0U.mlieBracketWithin_vectorField J0V (m := 1)
    · exact hs.uniqueMDiffOn_target_inter x
    · exact ⟨mem_extChartAt_target x, by simp [hx]⟩
    · exact le_rfl
  /- Rewrite the third term as a pullback-/
  have : ∀ᶠ y in 𝓝[s] x, mlieBracketWithin I
        (mpullback I 𝓘(𝕜, E) (extChartAt I x) U') (mpullback I 𝓘(𝕜, E) (extChartAt I x) W') s y
      = mpullback I 𝓘(𝕜, E) (extChartAt I x) (mlieBracketWithin 𝓘(𝕜, E) U' W'
        ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)) y := by
    filter_upwards [eventually_eventually_nhdsWithin.2 pre_mem, J1U, J1W,
      nhdsWithin_le_nhds (chart_source_mem_nhds H x), self_mem_nhdsWithin] with y hy hyU hyW h'y ys
    symm
    exact mpullback_mlieBracketWithin (n := minSmoothness 𝕜 2)
      (hyU.mdifferentiableWithinAt (one_le_two.trans le_minSmoothness))
      (hyW.mdifferentiableWithinAt (one_le_two.trans le_minSmoothness)) hs
      (contMDiffAt_extChartAt' h'y) ys le_rfl hy
  rw [Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem EventuallyEq.rfl this hx,
    ← mpullback_mlieBracketWithin (J0V.mdifferentiableWithinAt (one_le_two.trans le_minSmoothness))
      _ hs contMDiffAt_extChartAt hx le_rfl pre_mem]; swap
  · apply ContMDiffWithinAt.mdifferentiableWithinAt _ le_rfl
    apply J0U.mlieBracketWithin_vectorField J0W (m := 1)
    · exact hs.uniqueMDiffOn_target_inter x
    · exact ⟨mem_extChartAt_target x, by simp [hx]⟩
    · exact le_rfl
  /- Now that everything is in pullback form, use the leibniz identity in the vector space -/
  rw [← mpullback_add_apply, mpullback_apply, mpullback_apply]
  congr 1
  simp_rw [mlieBracketWithin_eq_lieBracketWithin]
  apply leibniz_identity_lieBracketWithin (E := E) le_rfl
  · exact hs.uniqueDiffOn_target_inter x
  · rw [inter_comm]
    exact extChartAt_mem_closure_interior h's (mem_extChartAt_source x)
  · exact ⟨mem_extChartAt_target x, by simp [hx]⟩
  · exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp J0U
  · exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp J0V
  · exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp J0W

/-- The Lie bracket of vector fields in manifolds satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]` (also called Jacobi identity). -/
lemma leibniz_identity_mlieBracket_apply
    {U V W : Π (x : M), TangentSpace I x} {x : M}
    (hU : ContMDiffAt I I.tangent (minSmoothness 𝕜 2) (fun x ↦ (U x : TangentBundle I M)) x)
    (hV : ContMDiffAt I I.tangent (minSmoothness 𝕜 2) (fun x ↦ (V x : TangentBundle I M)) x)
    (hW : ContMDiffAt I I.tangent (minSmoothness 𝕜 2) (fun x ↦ (W x : TangentBundle I M)) x) :
    mlieBracket I U (mlieBracket I V W) x =
      mlieBracket I (mlieBracket I U V) W x + mlieBracket I V (mlieBracket I U W) x := by
  simp only [← mlieBracketWithin_univ, ← contMDiffWithinAt_univ] at hU hV hW ⊢
  exact leibniz_identity_mlieBracketWithin_apply uniqueMDiffOn_univ (by simp) (mem_univ _) hU hV hW

/-- The Lie bracket of vector fields in manifolds satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]` (also called Jacobi identity). -/
lemma leibniz_identity_mlieBracket
    {U V W : Π (x : M), TangentSpace I x}
    (hU : ContMDiff I I.tangent (minSmoothness 𝕜 2) (fun x ↦ (U x : TangentBundle I M)))
    (hV : ContMDiff I I.tangent (minSmoothness 𝕜 2) (fun x ↦ (V x : TangentBundle I M)))
    (hW : ContMDiff I I.tangent (minSmoothness 𝕜 2) (fun x ↦ (W x : TangentBundle I M))) :
    mlieBracket I U (mlieBracket I V W) =
      mlieBracket I (mlieBracket I U V) W + mlieBracket I V (mlieBracket I U W) := by
  ext x
  exact leibniz_identity_mlieBracket_apply (hU x) (hV x) (hW x)

end Leibniz

end LieBracket

end VectorField

set_option linter.style.longFile 1700
