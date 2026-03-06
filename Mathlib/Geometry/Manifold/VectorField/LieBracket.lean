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
public import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.Notation

/-!
# Lie brackets of vector fields on manifolds

We define the Lie bracket of two vector fields, denoted with
`VectorField.mlieBracket I V W x`, as the pullback in the manifold of the corresponding notion
in the model space (through `extChartAt I x`).

The main results are the following:
* `VectorField.mpullback_mlieBracket` states that the pullback of the Lie bracket
  is the Lie bracket of the pullbacks.
* `VectorField.leibniz_identity_mlieBracket` is the Leibniz (or Jacobi)
  identity `[U, [V, W]] = [[U, V], W] + [V, [U, W]]`.

-/

@[expose] public section

open Set Function Filter NormedSpace
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

namespace VectorField

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

lemma mlieBracketWithin_def :
    mlieBracketWithin I V W s = fun x₀ ↦
    mpullback I 𝓘(𝕜, E) (extChartAt I x₀)
    (lieBracketWithin 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W (range I))
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I)) x₀ := rfl

lemma mlieBracketWithin_apply :
    mlieBracketWithin I V W s x₀ = (mfderiv% (extChartAt I x₀) x₀).inverse
    ((lieBracketWithin 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W (range I))
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I)) ((extChartAt I x₀ x₀))) := rfl

set_option backward.isDefEq.respectTransparency false in
lemma mlieBracketWithin_eq_lieBracketWithin {V W : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {s : Set E} :
    mlieBracketWithin 𝓘(𝕜, E) V W s = lieBracketWithin 𝕜 V W s := by
  ext x
  simp [mlieBracketWithin_apply]

/- Copy of the `lieBracket` API to manifolds -/

@[simp] lemma mlieBracketWithin_univ :
    mlieBracketWithin I V W univ = mlieBracket I V W := rfl

set_option backward.isDefEq.respectTransparency false in
lemma mlieBracketWithin_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) :
    mlieBracketWithin I V W s x = 0 := by
  simp only [mlieBracketWithin, mpullback_apply]
  rw [lieBracketWithin_eq_zero_of_eq_zero]
  · simp
  · simp only [mpullbackWithin_apply]
    have : (extChartAt I x).symm ((extChartAt I x) x) = x := by simp
    rw [this, hV]
    simp +instances
  · simp only [mpullbackWithin_apply]
    have : (extChartAt I x).symm ((extChartAt I x) x) = x := by simp
    rw [this, hW]
    simp +instances

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma mlieBracketWithin_self : mlieBracketWithin I V V = 0 := by
  ext x; simp [mlieBracketWithin, mpullback]

@[simp] lemma mlieBracket_self : mlieBracket I V V = 0 := by
  ext x; simp_rw [mlieBracket, mlieBracketWithin_self, Pi.zero_apply]

set_option backward.isDefEq.respectTransparency false in
/-- We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set. -/
@[simp]
lemma mlieBracketWithin_zero_left : mlieBracketWithin I 0 W s = 0 := by
  ext x
  simp [mlieBracketWithin]

/-- We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set. -/
@[simp]
lemma mlieBracketWithin_zero_right : mlieBracketWithin I W 0 s = 0 := by
  rw [mlieBracketWithin_swap]; simp

/-- We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. -/
@[simp]
lemma mlieBracket_zero_left : mlieBracket I 0 W = 0 := by simp [← mlieBracketWithin_univ]

/-- We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. -/
@[simp]
lemma mlieBracket_zero_right : mlieBracket I W 0 = 0 := by simp [← mlieBracketWithin_univ]

/-- Variant of `mlieBracketWithin_congr_set` where one requires the sets to coincide only in
the complement of a point. -/
theorem mlieBracketWithin_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x := by
  simp only [mlieBracketWithin_apply]
  congr 1
  suffices A : ((extChartAt I x).symm ⁻¹' s ∩ range I : Set E)
    =ᶠ[𝓝[{(extChartAt I x) x}ᶜ] (extChartAt I x x)]
      ((extChartAt I x).symm ⁻¹' t ∩ range I : Set E) by
    apply lieBracketWithin_congr_set' _ A
  exact preimage_extChartAt_eventuallyEq_compl_singleton y h

theorem mlieBracketWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x :=
  mlieBracketWithin_congr_set' x <| h.filter_mono inf_le_left

theorem mlieBracketWithin_inter (ht : t ∈ 𝓝 x) :
    mlieBracketWithin I V W (s ∩ t) x = mlieBracketWithin I V W s x := by
  apply mlieBracketWithin_congr_set
  filter_upwards [ht] with y hy
  change (y ∈ s ∩ t) = (y ∈ s)
  simp_all

theorem mlieBracketWithin_of_mem_nhds (h : s ∈ 𝓝 x) :
    mlieBracketWithin I V W s x = mlieBracket I V W x := by
  rw [← mlieBracketWithin_univ, ← univ_inter s, mlieBracketWithin_inter h]

theorem mlieBracketWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) :
    mlieBracketWithin I V W s x = mlieBracket I V W x :=
  mlieBracketWithin_of_mem_nhds (hs.mem_nhds hx)

/-- Variant of `mlieBracketWithin_eventually_congr_set` where one requires the sets to coincide only
in the complement of a point. -/
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

section

variable {c : 𝕜}
variable [IsManifold I 2 M]

lemma _root_.MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField
    [CompleteSpace E]
    (hV : MDiffAt[s] (fun x ↦ (V x : TangentBundle I M)) x) :
    DifferentiableWithinAt 𝕜 (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  apply MDifferentiableWithinAt.differentiableWithinAt
  have := MDifferentiableWithinAt.mpullbackWithin_vectorField_inter_of_eq hV
    (contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target x))
    (isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target x)) (mem_range_self _)
    I.uniqueMDiffOn le_rfl (extChartAt_to_inv x).symm
  rw [inter_comm]
  exact (contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).contMDiffAt.mdifferentiableAt one_ne_zero
    |>.comp_mdifferentiableWithinAt _ this

set_option backward.isDefEq.respectTransparency false in
lemma mfderiv_extChartAt_inverse_comp_mfderivWithin_extChartAT_symm (Y : TangentSpace I x) :
    letI φ := extChartAt I x
    ((mfderiv% φ x).inverse.comp ((mfderiv[range I] φ.symm (φ x)).inverse) Y) = Y := by
  set φ := extChartAt I x
  trans (ContinuousLinearMap.id 𝕜 _) Y; swap; · simp
  rw [extChartAt_to_inv x, ← ContinuousLinearMap.IsInvertible.inverse_comp_of_left,
    ← ContinuousLinearMap.inverse_id,
    mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (mem_extChartAt_source x)]
  exact isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target x)

variable (x W) in
private lemma mfderiv_extChart_inverse_comp_aux :
    letI φ := extChartAt I x
    (mfderiv% φ x).inverse.comp
      ((mfderiv[range I] φ.symm (φ x)).inverse) (W (φ.symm (φ x))) = W x := by
  rw [mfderiv_extChartAt_inverse_comp_mfderivWithin_extChartAT_symm, extChartAt_to_inv]

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back through `extChartAt` the scalar multiplication of a vector field by
the derivative of a scalar function equals the scalar multiplication by the manifold derivative. -/
lemma mpullback_mfderivWithin_apply_smul {f : M → 𝕜}
    (hf : MDiffAt[s] f x) :
    let V' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)
    let W' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (range I)
    letI s' : Set E := (extChartAt I x).symm ⁻¹' s ∩ range I
    mpullback I 𝓘(𝕜, E) (extChartAt I x)
        (fun x₀ ↦ (fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) s' x₀) (V' x₀) • W' x₀) x =
      (mfderiv[s] f x) (V x) • W x := by
  simp only [mpullback, mfderivWithin, hf, map_smul, ← mfderiv_extChart_inverse_comp_aux x W,
    mpullbackWithin]
  congr 2
  rw [extChartAt_to_inv]
  exact mfderivWithin_extChartAt_symm_inverse_apply (v := V x)

variable [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in
/--
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a function
`f : M → 𝕜`, we have `[V, f • W] = (df V) • W + f • [V, W]`. Version within a set.
-/
lemma mlieBracketWithin_smul_right {f : M → 𝕜} (hf : MDiffAt[s] f x)
    (hW : MDiffAt[s] (fun x ↦ (W x : TangentBundle I M)) x)
    (hs : UniqueMDiffWithinAt I s x) :
    mlieBracketWithin I V (f • W) s x =
      (fromTangentSpace (f x) (mfderiv[s] f x (V x))) • (W x)
      + (f x) • mlieBracketWithin I V W s x := by
  simp only [mlieBracketWithin, mpullbackWithin_smul]
  -- Simplify local notation a bit.
  set V' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)
  set W' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (range I)
  set f' := f ∘ (extChartAt I x).symm
  set s' := (extChartAt I x).symm ⁻¹' s ∩ range I
  -- We begin by rewriting using `lieBracketWithin_smul_right`.
  -- We need the coercion since on the nose `B` is a map `E → E`,
  -- whereas we need a map between tangent spaces.
  let A (x₀) := (fderivWithin 𝕜 f' s' x₀) (V' x₀) • W' x₀
  let B (x₀) : TangentSpace 𝓘(𝕜, E) x₀ := f' x₀ • lieBracketWithin 𝕜 V' W' s' x₀
  trans mpullback I 𝓘(𝕜, E) ((extChartAt I x)) (fun y ↦ A y + B y) x
  · simp only [mpullback_apply]
    congr
    exact lieBracketWithin_smul_right (V := V') hf.differentiableWithinAt_comp_extChartAt_symm
      hW.differentiableWithinAt_mpullbackWithin_vectorField hs
  -- We prove the equality of each summand separately.
  rw [← Pi.add_def, mpullback_add_apply]; congr
  · simpa only [A] using mpullback_mfderivWithin_apply_smul hf
  · simp [B, ← Pi.smul_def', mpullback_smul (V := lieBracketWithin 𝕜 V' W' s'), f']

set_option backward.isDefEq.respectTransparency false in
/--
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a function
`f : M → 𝕜`, we have `[V, f • W] = (df V) • W + f • [V, W]`.
-/
lemma mlieBracket_smul_right {f : M → 𝕜} (hf : MDiffAt f x)
    (hW : MDiffAt (fun x ↦ (W x : TangentBundle I M)) x) :
    mlieBracket I V (f • W) x =
      (fromTangentSpace (f x) (mfderiv% f x (V x))) • (W x)
      + (f x) • mlieBracket I V W x := by
  rw [← mdifferentiableWithinAt_univ] at hf hW
  rw [← mlieBracketWithin_univ, ← mfderivWithin_univ]
  exact mlieBracketWithin_smul_right hf hW (uniqueMDiffWithinAt_univ I)

set_option backward.isDefEq.respectTransparency false in
/--
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a function
`f : M → 𝕜`, we have `[f • V, W] = -(df W) • V + f • [V, W]`. Version within a set.
-/
lemma mlieBracketWithin_smul_left {f : M → 𝕜} (hf : MDiffAt[s] f x)
    (hV : MDiffAt[s] (fun x ↦ (V x : TangentBundle I M)) x)
    (hs : UniqueMDiffWithinAt I s x) :
    mlieBracketWithin I (f • V) W s x =
      -(fromTangentSpace (f x) (mfderiv[s] f x (W x))) • (V x)
      + (f x) • mlieBracketWithin I V W s x := by
  rw [mlieBracketWithin_swap, Pi.neg_apply, mlieBracketWithin_smul_right hf hV (V := W) hs,
    mlieBracketWithin_swap]
  simp; abel

set_option backward.isDefEq.respectTransparency false in
/--
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a function
`f : M → 𝕜`, we have `[f • V, W] = -(df W) • V + f • [V, W]`.
-/
lemma mlieBracket_smul_left {f : M → 𝕜} (hf : MDiffAt f x)
    (hV : MDiffAt (fun x ↦ (V x : TangentBundle I M)) x) :
    mlieBracket I (f • V) W x =
      - (fromTangentSpace (f x) (mfderiv% f x (W x))) • (V x)
      + (f x) • mlieBracket I V W x := by
  rw [← mdifferentiableWithinAt_univ] at hf hV
  rw [← mlieBracketWithin_univ, ← mfderivWithin_univ]
  exact mlieBracketWithin_smul_left hf hV (uniqueMDiffWithinAt_univ I)

set_option backward.isDefEq.respectTransparency false in
lemma mlieBracketWithin_const_smul_left
    (hV : MDiffAt[s] (T% V) x) (hs : UniqueMDiffWithinAt I s x) :
    mlieBracketWithin I (c • V) W s x = c • mlieBracketWithin I V W s x := by
  simpa [mfderivWithin_const] using
    mlieBracketWithin_smul_left (mdifferentiableWithinAt_const (c := c)) (W := W) hV hs

lemma mlieBracket_const_smul_left (hV : MDiffAt (T% V) x) :
    mlieBracket I (c • V) W x = c • mlieBracket I V W x := by
  simp only [← mlieBracketWithin_univ] at hV ⊢
  exact mlieBracketWithin_const_smul_left hV (uniqueMDiffWithinAt_univ _)

set_option backward.isDefEq.respectTransparency false in
lemma mlieBracketWithin_const_smul_right
    (hW : MDiffAt[s] (T% W) x) (hs : UniqueMDiffWithinAt I s x) :
    mlieBracketWithin I V (c • W) s x = c • mlieBracketWithin I V W s x := by
  simpa [mfderivWithin_const] using
    mlieBracketWithin_smul_right (mdifferentiableWithinAt_const (c := c)) (V := V) hW hs

lemma mlieBracket_const_smul_right (hW : MDiffAt (T% W) x) :
    mlieBracket I V (c • W) x = c • mlieBracket I V W x := by
  simp only [← mlieBracketWithin_univ] at hW ⊢
  exact mlieBracketWithin_const_smul_right hW (uniqueMDiffWithinAt_univ _)

set_option backward.isDefEq.respectTransparency false in
lemma mlieBracketWithin_add_left
    (hV : MDiffAt[s] (T% V) x) (hV₁ : MDiffAt[s] (T% V₁) x) (hs : UniqueMDiffWithinAt I s x) :
    mlieBracketWithin I (V + V₁) W s x =
      mlieBracketWithin I V W s x + mlieBracketWithin I V₁ W s x := by
  simp only [mlieBracketWithin_apply]
  rw [← map_add, mpullbackWithin_add, lieBracketWithin_add_left]
  · exact hV.differentiableWithinAt_mpullbackWithin_vectorField
  · exact hV₁.differentiableWithinAt_mpullbackWithin_vectorField
  · exact uniqueMDiffWithinAt_iff_inter_range.1 hs

lemma mlieBracket_add_left (hV : MDiffAt (T% V) x) (hV₁ : MDiffAt (T% V₁) x) :
    mlieBracket I (V + V₁) W x = mlieBracket I V W x + mlieBracket I V₁ W x := by
  simp only [← mlieBracketWithin_univ] at hV hV₁ ⊢
  exact mlieBracketWithin_add_left hV hV₁ (uniqueMDiffWithinAt_univ _)

lemma mlieBracketWithin_add_right
    (hW : MDiffAt[s] (T% W) x) (hW₁ : MDiffAt[s] (T% W₁) x) (hs : UniqueMDiffWithinAt I s x) :
    mlieBracketWithin I V (W + W₁) s x =
      mlieBracketWithin I V W s x + mlieBracketWithin I V W₁ s x := by
  rw [mlieBracketWithin_swap, Pi.neg_apply, mlieBracketWithin_add_left hW hW₁ hs,
    mlieBracketWithin_swap (V := V), mlieBracketWithin_swap (V := V), Pi.neg_apply, Pi.neg_apply]
  abel

lemma mlieBracket_add_right (hW : MDiffAt (T% W) x) (hW₁ : MDiffAt (T% W₁) x) :
    mlieBracket I V (W + W₁) x = mlieBracket I V W x + mlieBracket I V W₁ x := by
  simp only [← mlieBracketWithin_univ] at hW hW₁ ⊢
  exact mlieBracketWithin_add_right hW hW₁ (uniqueMDiffWithinAt_univ _)

theorem mlieBracketWithin_of_mem_nhdsWithin (st : t ∈ 𝓝[s] x) (hs : UniqueMDiffWithinAt I s x)
    (hV : MDiffAt[t] (T% V) x) (hW : MDiffAt[t] (T% W) x) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x := by
  simp only [mlieBracketWithin_apply]
  congr 1
  rw [lieBracketWithin_of_mem_nhdsWithin]
  · apply Filter.inter_mem
    · apply nhdsWithin_mono _ inter_subset_left <|
        (continuousAt_extChartAt_symm x).continuousWithinAt.preimage_mem_nhdsWithin'' st (by simp)
    · exact nhdsWithin_mono _ inter_subset_right self_mem_nhdsWithin
  · exact uniqueMDiffWithinAt_iff_inter_range.1 hs
  · exact hV.differentiableWithinAt_mpullbackWithin_vectorField
  · exact hW.differentiableWithinAt_mpullbackWithin_vectorField

theorem mlieBracketWithin_subset (st : s ⊆ t) (ht : UniqueMDiffWithinAt I s x)
    (hV : MDiffAt[t] (T% V) x) (hW : MDiffAt[t] (T% W) x) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x :=
  mlieBracketWithin_of_mem_nhdsWithin (nhdsWithin_mono _ st self_mem_nhdsWithin) ht hV hW

theorem mlieBracketWithin_eq_mlieBracket (hs : UniqueMDiffWithinAt I s x)
    (hV : MDiffAt (T% V) x) (hW : MDiffAt (T% W) x) :
    mlieBracketWithin I V W s x = mlieBracket I V W x := by
  simp only [← mlieBracketWithin_univ, ← mdifferentiableWithinAt_univ] at hV hW ⊢
  exact mlieBracketWithin_subset (subset_univ _) hs hV hW

theorem _root_.DifferentiableWithinAt.mlieBracketWithin_congr_mono
    (hV : MDiffAt[s] (T% V) x) (hVs : EqOn V₁ V t) (hVx : V₁ x = V x)
    (hW : MDiffAt[s] (T% W) x) (hWs : EqOn W₁ W t) (hWx : W₁ x = W x)
    (hxt : UniqueMDiffWithinAt I t x) (h₁ : t ⊆ s) :
    mlieBracketWithin I V₁ W₁ t x = mlieBracketWithin I V W s x := by
  rw [mlieBracketWithin_congr hVs hVx hWs hWx]
  exact mlieBracketWithin_subset h₁ hxt hV hW

end

section Invariance_IsSymmSndFDerivWithinAt

variable [IsManifold I 2 M] [IsManifold I' 2 M'] [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in
/- The Lie bracket of vector fields on manifolds is well defined, i.e., it is invariant under
diffeomorphisms. Auxiliary version where one assumes that all relevant sets are contained
in chart domains. -/
private lemma mpullbackWithin_mlieBracketWithin_aux [CompleteSpace E']
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀))
    (hu : UniqueMDiffOn I s) (hf : CMDiff[s] 2 f) (hx₀ : x₀ ∈ s)
    (ht : t ⊆ (extChartAt I' (f x₀)).source) (hst : MapsTo f s t)
    (hsymm : IsSymmSndFDerivWithinAt 𝕜 ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I) (extChartAt I x₀ x₀)) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ =
      mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ := by
  have A : (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ := by simp
  have A' : x₀ = (extChartAt I x₀).symm (extChartAt I x₀ x₀) := by simp
  have h'f : MDiffAt[s] f x₀ := (hf x₀ hx₀).mdifferentiableWithinAt two_ne_zero
  simp only [mlieBracketWithin_apply, mpullbackWithin_apply]
  -- first, rewrite the pullback of the Lie bracket as a pullback in `E` under the map
  -- `F = extChartAt I' (f x₀) ∘ f ∘ (extChartAt I x₀).symm` of a Lie bracket computed in `E'`,
  -- of two vector fields `V'` and `W'`.
  rw [← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_left
    (isInvertible_mfderiv_extChartAt (mem_extChartAt_source (f x₀)))]
  rw [← mfderiv_comp_mfderivWithin _ (mdifferentiableAt_extChartAt
    (ChartedSpace.mem_chart_source (f x₀))) h'f (hu x₀ hx₀)]
  rw [eq_comm, (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x₀)).inverse_apply_eq]
  have : (mfderiv[range I] (extChartAt I x₀).symm (extChartAt I x₀ x₀)).inverse =
      mfderiv% (extChartAt I x₀) x₀ := by
    apply ContinuousLinearMap.inverse_eq
    · convert mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) (x := x₀)
        (y := extChartAt I x₀ x₀) (by simp)
    · convert mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x₀)
        (y := extChartAt I x₀ x₀) (by simp)
  rw [← this, ← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_right]; swap
  · exact isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target x₀)
  have : mfderiv[range I] (extChartAt I x₀).symm (extChartAt I x₀ x₀) =
      mfderiv[(extChartAt I x₀).symm ⁻¹' s ∩ range I] (extChartAt I x₀).symm (extChartAt I x₀ x₀) :=
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
    simp only [mpullbackWithin_apply, hF, comp_apply]
    rw [mfderivWithin_comp (I' := I) (u := s)]; rotate_left
    · apply (mdifferentiableAt_extChartAt h''y).comp_mdifferentiableWithinAt (I' := I')
      exact (hf _ hy.1).mdifferentiableWithinAt two_ne_zero
    · exact (mdifferentiableWithinAt_extChartAt_symm h'''y).mono inter_subset_right
    · exact inter_subset_left
    · exact huy
    rw [mfderiv_comp_mfderivWithin (I' := I')]; rotate_left
    · exact mdifferentiableAt_extChartAt h''y
    · exact (hf _ hy.1).mdifferentiableWithinAt two_ne_zero
    · exact hu _ hy.1
    rw [← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_right]; swap
    · exact isInvertible_mfderivWithin_extChartAt_symm h'''y
    rw [← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_left]; swap
    · exact isInvertible_mfderivWithin_extChartAt_symm (PartialEquiv.map_source _ h'y)
    have : f ((extChartAt I x₀).symm y)
        = (extChartAt I' (f x₀)).symm ((extChartAt I' (f x₀)) (f ((extChartAt I x₀).symm y))) :=
      (PartialEquiv.left_inv (extChartAt I' (f x₀)) h'y).symm
    congr 2
    have : (mfderiv[range I'] ((extChartAt I' (f x₀)).symm)
        (extChartAt I' (f x₀) (f ((extChartAt I x₀).symm y)))) ∘L
        (mfderiv% (extChartAt I' (f x₀)) (f ((extChartAt I x₀).symm y))) =
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

set_option backward.isDefEq.respectTransparency false in
/- The Lie bracket of vector fields on manifolds is well defined, i.e., it is invariant under
diffeomorphisms. -/
lemma mpullbackWithin_mlieBracketWithin_of_isSymmSndFDerivWithinAt
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀))
    (hu : UniqueMDiffOn I s) (hf : CMDiffAt[s] 2 f x₀) (hx₀ : x₀ ∈ s)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hsymm : IsSymmSndFDerivWithinAt 𝕜 ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I) (extChartAt I x₀ x₀)) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ =
      mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ := by
  have A : (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ := by simp
  by_cases hfi : (mfderiv[s] f x₀).IsInvertible; swap
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
        s ∩ u ⊆ f ⁻¹' (extChartAt I' (f x₀)).source ∧ CMDiff[s ∩ u] 2 f := by
    obtain ⟨u, u_open, x₀u, hu⟩ : ∃ u, IsOpen u ∧ x₀ ∈ u ∧ CMDiff[insert x₀ s ∩ u] 2 f  :=
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
assumes that the map is smooth on a larger set `u` (so that the
condition `x₀ ∈ closure (interior u)`, needed to guarantee the symmetry of the second derivative,
becomes easier to check.) -/
lemma mpullbackWithin_mlieBracketWithin'
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s u : Set M} {t : Set M'}
    (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀))
    (hs : UniqueMDiffOn I s) (hu : UniqueMDiffOn I u)
    (hf : CMDiffAt[u] n f x₀) (hx₀ : x₀ ∈ s) (hn : minSmoothness 𝕜 2 ≤ n)
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
    (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀))
    (hu : UniqueMDiffOn I s) (hf : CMDiffAt[s] n f x₀) (hx₀ : x₀ ∈ s)
    (hn : minSmoothness 𝕜 2 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (h'x₀ : x₀ ∈ closure (interior s)) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ =
      mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ :=
  mpullbackWithin_mlieBracketWithin' hV hW hu hu hf hx₀ hn hst h'x₀ Subset.rfl

/-- The pullback commutes with the Lie bracket of vector fields on manifolds. -/
lemma mpullback_mlieBracketWithin
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀))
    (hu : UniqueMDiffOn I s) (hf : CMDiffAt n f x₀) (hx₀ : x₀ ∈ s)
    (hn : minSmoothness 𝕜 2 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀) :
    mpullback I I' f (mlieBracketWithin I' V W t) x₀ =
      mlieBracketWithin I (mpullback I I' f V) (mpullback I I' f W) s x₀ := by
  have : mpullback I I' f (mlieBracketWithin I' V W t) x₀ =
      mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ := by
    simp only [mpullback, mpullbackWithin]
    congr
    apply (mfderivWithin_eq_mfderiv (hu _ hx₀) _).symm
    exact hf.mdifferentiableAt (two_pos.trans_le (le_minSmoothness.trans hn)).ne'
  rw [this, mpullbackWithin_mlieBracketWithin' hV hW hu uniqueMDiffOn_univ hf.contMDiffWithinAt
    hx₀ hn hst (by simp) (subset_univ _)]
  apply Filter.EventuallyEq.mlieBracketWithin_vectorField_of_insert
  · rw [insert_eq_of_mem hx₀]
    filter_upwards [nhdsWithin_le_nhds ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1
      (hf.of_le (le_minSmoothness.trans hn))), self_mem_nhdsWithin] with y hy h'y
    simp only [mpullback, mpullbackWithin]
    congr
    apply mfderivWithin_eq_mfderiv (hu _ h'y)
    exact hy.mdifferentiableAt two_ne_zero
  · rw [insert_eq_of_mem hx₀]
    filter_upwards [nhdsWithin_le_nhds ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1
      (hf.of_le (le_minSmoothness.trans hn))), self_mem_nhdsWithin] with y hy h'y
    simp only [mpullback, mpullbackWithin]
    congr
    apply mfderivWithin_eq_mfderiv (hu _ h'y)
    exact hy.mdifferentiableAt two_ne_zero

lemma mpullback_mlieBracket
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M}
    (hV : MDiffAt (T% V) (f x₀)) (hW : MDiffAt (T% W) (f x₀))
    (hf : CMDiffAt n f x₀) (hn : minSmoothness 𝕜 2 ≤ n) :
    mpullback I I' f (mlieBracket I' V W) x₀ =
      mlieBracket I (mpullback I I' f V) (mpullback I I' f W) x₀ := by
  simp only [← mlieBracketWithin_univ, ← mdifferentiableWithinAt_univ] at hV hW ⊢
  exact mpullback_mlieBracketWithin hV hW uniqueMDiffOn_univ hf (mem_univ _) hn (by simp)

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
protected lemma _root_.ContMDiffWithinAt.mlieBracketWithin_vectorField
    [IsManifold I (n + 1) M] {m : WithTop ℕ∞}
    {U V : Π (x : M), TangentSpace I x} {s : Set M} {x : M}
    (hU : CMDiffAt[s] n (T% U) x) (hV : CMDiffAt[s] n (T% V) x)
    (hs : UniqueMDiffOn I s) (hx : x ∈ s) (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    CMDiffAt[s] m (T% (mlieBracketWithin I U V s)) x := by
  /- The statement is not obvious, since at different points the Lie bracket is defined using
  different charts. However, since we know that the Lie bracket is invariant under diffeos, we can
  use a single chart to prove the statement. Let `U'` and `V'` denote the pullbacks of `U` and `V`
  in the chart around `x`. Then the Lie bracket there is smooth (as it coincides with the vector
  space Lie bracket, given by an explicit formula). Pulling back this Lie bracket in `M` gives
  locally a smooth function, which coincides with the initial Lie bracket by invariance
  under diffeos. -/
  have min2 : minSmoothness 𝕜 2 ≤ n + 1 := by
    grw [← hmn, ← minSmoothness_add, add_assoc]
    exact minSmoothness_monotone le_add_self
  apply contMDiffWithinAt_iff_le_ne_infty.2 (fun m' hm' h'm' ↦ ?_)
  have hn : 1 ≤ m' + 1 := le_add_self
  have hm'n : m' + 1 ≤ n := by grw [hm', ← hmn, ← le_minSmoothness]
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
  have B : CMDiffAt[((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)] m'
      (T% (mlieBracketWithin 𝓘(𝕜, E) U' V' ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)))
      (extChartAt I x x) := by
    rw [← mlieBracketWithin_eq_lieBracketWithin] at A
    exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.2 A
  have C : CMDiffAt[s] m' (T% ((mpullback I 𝓘(𝕜, E) (extChartAt I x)
      ((mlieBracketWithin 𝓘(𝕜, E) U' V'
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)))))) x :=
    ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin_of_eq B (n := m' + 1)
      contMDiffAt_extChartAt
      (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)) le_rfl pre_mem rfl
  apply C.congr_of_eventuallyEq_of_mem _ hx
  filter_upwards [eventually_eventually_nhdsWithin.2 pre_mem,
    eventually_eventually_nhdsWithin.2 (eventuallyEq_mpullback_mpullbackWithin_extChartAt U),
    eventually_eventually_nhdsWithin.2 (eventuallyEq_mpullback_mpullbackWithin_extChartAt V),
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm (hU.of_le hm'n) hs hx
      (by gcongr) (by simp [h'm']),
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm (hV.of_le hm'n) hs hx
      (by gcongr) (by simp [h'm']),
    nhdsWithin_le_nhds (chart_source_mem_nhds H x), self_mem_nhdsWithin]
    with y hy hyU hyV h'yU h'yV hy_chart hys
  simp only [Bundle.TotalSpace.mk_inj]
  rw [mpullback_mlieBracketWithin (h'yU.mdifferentiableWithinAt <| by positivity)
    (h'yV.mdifferentiableWithinAt <| by positivity) hs (contMDiffAt_extChartAt' hy_chart)
    hys min2 hy]
  exact Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem hyU hyV hys

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
lemma _root_.ContMDiffAt.mlieBracket_vectorField {m n : ℕ∞}
    [IsManifold I (n + 1) M] {U V : Π (x : M), TangentSpace I x} {x : M}
    (hU : CMDiffAt n (T% U) x) (hV : CMDiffAt n (T% V) x)
    (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    CMDiffAt m (T% (mlieBracket I U V)) x := by
  simp only [← contMDiffWithinAt_univ, ← mlieBracketWithin_univ] at hU hV ⊢
  exact hU.mlieBracketWithin_vectorField hV uniqueMDiffOn_univ (mem_univ _) hmn

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
lemma _root_.ContMDiffOn.mlieBracketWithin_vectorField {m n : ℕ∞}
    [IsManifold I (n + 1) M] {U V : Π (x : M), TangentSpace I x}
    (hU : CMDiff[s] n (T% U)) (hV : CMDiff[s] n (T% V))
    (hs : UniqueMDiffOn I s) (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    CMDiff[s] m (T% (mlieBracketWithin I U V s)) :=
  fun x hx ↦ (hU x hx).mlieBracketWithin_vectorField (hV x hx) hs hx hmn

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
lemma _root_.ContDiff.mlieBracket_vectorField {m n : ℕ∞}
    [IsManifold I (n + 1) M] {U V : Π (x : M), TangentSpace I x}
    (hU : CMDiff n (T% U)) (hV : CMDiff n (T% V)) (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    CMDiff m (T% (mlieBracket I U V)) := by
  simp only [← contMDiffOn_univ] at hU hV ⊢
  exact hU.mlieBracketWithin_vectorField hV uniqueMDiffOn_univ hmn

end Invariance

section Leibniz

variable [IsManifold I (minSmoothness 𝕜 3) M] [CompleteSpace E]

/-- The Lie bracket of vector fields in manifolds satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]` (also called Jacobi identity). -/
theorem leibniz_identity_mlieBracketWithin_apply
    {U V W : Π (x : M), TangentSpace I x} {s : Set M} {x : M}
    (hs : UniqueMDiffOn I s) (h's : x ∈ closure (interior s)) (hx : x ∈ s)
    (hU : CMDiffAt[s] (minSmoothness 𝕜 2) (T% U) x)
    (hV : CMDiffAt[s] (minSmoothness 𝕜 2) (T% V) x)
    (hW : CMDiffAt[s] (minSmoothness 𝕜 2) (T% W) x) :
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
  have J0U : CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s] (minSmoothness 𝕜 2)
      (T% U') (extChartAt I x x) :=
    contMDiffWithinAt_mpullbackWithin_extChartAt_symm hU hs hx A
  have J0V : CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s] (minSmoothness 𝕜 2)
      (T% V') (extChartAt I x x) :=
    contMDiffWithinAt_mpullbackWithin_extChartAt_symm hV hs hx A
  have J0W : CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s] (minSmoothness 𝕜 2)
      (T% W') (extChartAt I x x) :=
    contMDiffWithinAt_mpullbackWithin_extChartAt_symm hW hs hx A
  have J1U : ∀ᶠ y in 𝓝[s] x, CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s]
      (minSmoothness 𝕜 2) (T% U') (extChartAt I x y) :=
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm hU hs hx A (by simp)
  have J1V : ∀ᶠ y in 𝓝[s] x, CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s]
      (minSmoothness 𝕜 2) (T% V') (extChartAt I x y) :=
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm hV hs hx A (by simp)
  have J1W : ∀ᶠ y in 𝓝[s] x, CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s]
      (minSmoothness 𝕜 2) (T% W') (extChartAt I x y) :=
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
      (hyV.mdifferentiableWithinAt (two_pos.trans_le le_minSmoothness).ne')
      (hyW.mdifferentiableWithinAt (two_pos.trans_le le_minSmoothness).ne') hs
      (contMDiffAt_extChartAt' h'y) ys le_rfl hy
  rw [Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem EventuallyEq.rfl this hx,
    ← mpullback_mlieBracketWithin (J0U.mdifferentiableWithinAt
      (two_pos.trans_le le_minSmoothness).ne') _ hs contMDiffAt_extChartAt hx le_rfl pre_mem]; swap
  · apply ContMDiffWithinAt.mdifferentiableWithinAt _ one_ne_zero
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
      (hyU.mdifferentiableWithinAt (two_pos.trans_le le_minSmoothness).ne')
      (hyV.mdifferentiableWithinAt (two_pos.trans_le le_minSmoothness).ne') hs
      (contMDiffAt_extChartAt' h'y) ys le_rfl hy
  rw [Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem this EventuallyEq.rfl hx,
    ← mpullback_mlieBracketWithin _ (J0W.mdifferentiableWithinAt
      (two_pos.trans_le le_minSmoothness).ne') hs contMDiffAt_extChartAt hx le_rfl pre_mem]; swap
  · apply ContMDiffWithinAt.mdifferentiableWithinAt _ one_ne_zero
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
      (hyU.mdifferentiableWithinAt (two_pos.trans_le le_minSmoothness).ne')
      (hyW.mdifferentiableWithinAt (two_pos.trans_le le_minSmoothness).ne') hs
      (contMDiffAt_extChartAt' h'y) ys le_rfl hy
  rw [Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem EventuallyEq.rfl this hx,
    ← mpullback_mlieBracketWithin (J0V.mdifferentiableWithinAt
      (two_pos.trans_le le_minSmoothness).ne') _ hs contMDiffAt_extChartAt hx le_rfl pre_mem]; swap
  · apply ContMDiffWithinAt.mdifferentiableWithinAt _ one_ne_zero
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
    (hU : CMDiffAt (minSmoothness 𝕜 2) (T% U) x)
    (hV : CMDiffAt (minSmoothness 𝕜 2) (T% V) x)
    (hW : CMDiffAt (minSmoothness 𝕜 2) (T% W) x) :
    mlieBracket I U (mlieBracket I V W) x =
      mlieBracket I (mlieBracket I U V) W x + mlieBracket I V (mlieBracket I U W) x := by
  simp only [← mlieBracketWithin_univ, ← contMDiffWithinAt_univ] at hU hV hW ⊢
  exact leibniz_identity_mlieBracketWithin_apply uniqueMDiffOn_univ (by simp) (mem_univ _) hU hV hW

/-- The Lie bracket of vector fields in manifolds satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]` (also called Jacobi identity). -/
lemma leibniz_identity_mlieBracket
    {U V W : Π (x : M), TangentSpace I x}
    (hU : CMDiff (minSmoothness 𝕜 2) (T% U))
    (hV : CMDiff (minSmoothness 𝕜 2) (T% V))
    (hW : CMDiff (minSmoothness 𝕜 2) (T% W)) :
    mlieBracket I U (mlieBracket I V W) =
      mlieBracket I (mlieBracket I U V) W + mlieBracket I V (mlieBracket I U W) := by
  ext x
  exact leibniz_identity_mlieBracket_apply (hU x) (hV x) (hW x)

end Leibniz

end LieBracket

end VectorField
