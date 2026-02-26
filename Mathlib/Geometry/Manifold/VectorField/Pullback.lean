/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Vector fields in manifolds

We study functions of the form `V : Π (x : M) → TangentSpace I x` on a manifold, i.e.,
vector fields.

We define the pullback of a vector field under a map, as
`VectorField.mpullback I I' f V x := (mfderiv I I' f x).inverse (V (f x))`
(together with the same notion within a set). Note that the pullback uses the junk-value pattern:
if the derivative of the map is not invertible, then pullback is given the junk value zero.

See `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean` for the Lie bracket of two vector
fields.

These definitions are given in the `VectorField` namespace because pullbacks, Lie brackets,
and so on, are notions that make sense in a variety of contexts.
We also prefix the notions with `m` to distinguish the manifold notions from the vector space
notions.

For notions that come naturally in other namespaces for dot notation, we specify `vectorField` in
the name to lift ambiguities. For instance, the fact that the Lie bracket of two smooth vector
fields is smooth is `ContMDiffAt.mlieBracket_vectorField`.

Note that a smoothness assumption for a vector field is written by seeing the vector field as
a function from `M` to its tangent bundle through a coercion, as in:
`MDifferentiableWithinAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) s x`.
-/

@[expose] public section

open Set Function Filter
open scoped Topology Manifold ContDiff

noncomputable section

/- We work in the `VectorField` namespace because pullbacks, Lie brackets, and so on, are notions
that make sense in a variety of contexts. We also prefix the notions with `m` to distinguish the
manifold notions from the vector space notions. For instance, the Lie bracket of two vector
fields in a manifold is denoted with `VectorField.mlieBracket I V W x`, where `I` is the relevant
model with corners, `V W : Π (x : M), TangentSpace I x` are the vector fields, and `x : M` is
the basepoint.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [AddCommGroup E] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [AddCommGroup E'] [NormedAddCommGroup E']
    [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {H'' : Type*} [TopologicalSpace H''] {E'' : Type*} [AddCommGroup E''] [NormedAddCommGroup E'']
    [NormedSpace 𝕜 E'']
  {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f : M → M'} {s t : Set M} {x x₀ : M}

instance {n : ℕ} [n.AtLeastTwo] [IsManifold I (minSmoothness 𝕜 (ofNat(n))) M] :
    IsManifold I (ofNat(n)) M :=
  IsManifold.of_le (n := minSmoothness 𝕜 n) le_minSmoothness

instance [IsManifold I (minSmoothness 𝕜 1) M] :
    IsManifold I 1 M :=
  IsManifold.of_le (n := minSmoothness 𝕜 1) le_minSmoothness

set_option backward.isDefEq.respectTransparency false in
instance [IsManifold I (minSmoothness 𝕜 3) M] :
    IsManifold I (minSmoothness 𝕜 2) M :=
  IsManifold.of_le (n := minSmoothness 𝕜 3) (minSmoothness_monotone (by norm_cast))

set_option backward.isDefEq.respectTransparency false in
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

@[simp]
lemma mpullbackWithin_zero : mpullbackWithin I I' f 0 s = 0 := by
  ext x
  simp [mpullbackWithin_apply]

lemma mpullbackWithin_neg_apply :
    mpullbackWithin I I' f (-V) s x = - mpullbackWithin I I' f V s x := by
  simp [mpullbackWithin_apply]

lemma mpullbackWithin_neg :
    mpullbackWithin I I' f (-V) s = - mpullbackWithin I I' f V s := by
  ext x
  simp [mpullbackWithin_apply]

set_option backward.isDefEq.respectTransparency false in
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

@[simp]
lemma mpullback_zero : mpullback I I' f 0 = 0 := by simp [← mpullbackWithin_univ]

lemma mpullbackWithin_eq_pullbackWithin {f : E → E'} {V : E' → E'} {s : Set E} :
    mpullbackWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f V s = pullbackWithin 𝕜 f V s := by
  ext x
  simp only [mpullbackWithin, mfderivWithin_eq_fderivWithin, pullbackWithin]
  rfl

lemma mpullback_eq_pullback {f : E → E'} {V : E' → E'} :
    mpullback 𝓘(𝕜, E) 𝓘(𝕜, E') f V = pullback 𝕜 f V := by
  simp only [← mpullbackWithin_univ, ← pullbackWithin_univ, mpullbackWithin_eq_pullbackWithin]

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma mpullback_id {V : Π (x : M), TangentSpace I x} : mpullback I I id V = V := by
  ext x
  simp [mpullback]

lemma mpullbackWithin_comp_of_left
    {g : M' → M''} {f : M → M'} {V : Π (x : M''), TangentSpace I'' x} {s : Set M} {t : Set M'}
    {x₀ : M} (hf : MDifferentiableWithinAt I I' f s x₀) (h : Set.MapsTo f s t)
    (hu : UniqueMDiffWithinAt I s x₀) (hg' : (mfderivWithin I' I'' g t (f x₀)).IsInvertible) :
    mpullbackWithin I I'' (g ∘ f) V s x₀ =
      mpullbackWithin I I' f (mpullbackWithin I' I'' g V t) s x₀ := by
  simp only [mpullbackWithin]
  have hg : MDifferentiableWithinAt I' I'' g t (f x₀) :=
    mdifferentiableWithinAt_of_isInvertible_mfderivWithin hg'
  rw [mfderivWithin_comp _ hg hf h hu, Function.comp_apply,
    IsInvertible.inverse_comp_apply_of_left hg']

set_option backward.isDefEq.respectTransparency false in
lemma mpullbackWithin_comp_of_right
    {g : M' → M''} {f : M → M'} {V : Π (x : M''), TangentSpace I'' x} {s : Set M} {t : Set M'}
    {x₀ : M} (hg : MDifferentiableWithinAt I' I'' g t (f x₀)) (h : Set.MapsTo f s t)
    (hu : UniqueMDiffWithinAt I s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible) :
    mpullbackWithin I I'' (g ∘ f) V s x₀ =
      mpullbackWithin I I' f (mpullbackWithin I' I'' g V t) s x₀ := by
  simp only [mpullbackWithin]
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
    apply hV.comp x₀ ((hf.mdifferentiableWithinAt (by positivity)).mono inter_subset_left)
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
    ((hf.of_le hmn).mfderivWithin_const le_rfl hx₀ hs).mdifferentiableWithinAt one_ne_zero
  -- therefore, its inverse in coordinates also depends smoothly on the point
  have : MDifferentiableWithinAt I 𝓘(𝕜, E' →L[𝕜] E)
      (ContinuousLinearMap.inverse ∘ (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
        x₀ x (f x₀) (f x) (mfderivWithin I I' f s x))) s x₀ := by
    apply MDifferentiableAt.comp_mdifferentiableWithinAt _ _ this
    apply ContMDiffAt.mdifferentiableAt _ one_ne_zero
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
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f ⁻¹' t) x₀ := by
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

variable [CompleteSpace E] [IsManifold I 1 M] [IsManifold I' 1 M']

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
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f ⁻¹' t) x₀ := by
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
  have hn : 1 ≤ n := le_trans (by simp) hmn
  have hh : (mfderivWithin I I' f s x₀).IsInvertible := by
    convert hf' using 1
    exact (hf.mdifferentiableWithinAt <| by positivity).mfderivWithin_mono (hs _ hx₀) hu
  apply (hV.mpullbackWithin_vectorField_of_mem (hf.mono hu) hh hx₀ hs hmn
    hst).congr_of_eventuallyEq_of_mem _ hx₀
  have Y := (contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin (by simp)).1 (hf.of_le hn)
  simp_rw [insert_eq_of_mem (hu hx₀)] at Y
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_mono _ hu Y] with y hy h'y
  simp only [mpullbackWithin, Bundle.TotalSpace.mk_inj]
  rw [MDifferentiableWithinAt.mfderivWithin_mono (h'y.mdifferentiableWithinAt one_ne_zero)
    (hs _ hy) hu]

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
    (contMDiffWithinAt_extChartAt_symm_range_self (n := n) x)
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

end VectorField
