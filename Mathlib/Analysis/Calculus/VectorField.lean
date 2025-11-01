/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Vector fields in vector spaces

We study functions of the form `V : E → E` on a vector space, thinking of these as vector fields.
We define several notions in this context, with the aim to generalize them to vector fields on
manifolds.

Notably, we define the pullback of a vector field under a map, as
`VectorField.pullback 𝕜 f V x := (fderiv 𝕜 f x).inverse (V (f x))` (together with the same notion
within a set).

We also define the Lie bracket of two vector fields as
`VectorField.lieBracket 𝕜 V W x := fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)`
(together with the same notion within a set).

In addition to comprehensive API on these two notions, the main results are the following:
* `VectorField.pullback_lieBracket` states that the pullback of the Lie bracket
  is the Lie bracket of the pullbacks, when the second derivative is symmetric.
* `VectorField.leibniz_identity_lieBracket` is the Leibniz
  identity `[U, [V, W]] = [[U, V], W] + [V, [U, W]]`.

-/

open Set
open scoped Topology

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V W V₁ W₁ : E → E} {s t : Set E} {x : E}

/-!
### The Lie bracket of vector fields in a vector space

We define the Lie bracket of two vector fields, and call it `lieBracket 𝕜 V W x`. We also define
a version localized to sets, `lieBracketWithin 𝕜 V W s x`. We copy the relevant API
of `fderivWithin` and `fderiv` for these notions to get a comprehensive API.
-/

namespace VectorField

variable (𝕜) in
/-- The Lie bracket `[V, W] (x)` of two vector fields at a point, defined as
`DW(x) (V x) - DV(x) (W x)`. -/
def lieBracket (V W : E → E) (x : E) : E :=
  fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)

variable (𝕜) in
/-- The Lie bracket `[V, W] (x)` of two vector fields within a set at a point, defined as
`DW(x) (V x) - DV(x) (W x)` where the derivatives are taken inside `s`. -/
def lieBracketWithin (V W : E → E) (s : Set E) (x : E) : E :=
  fderivWithin 𝕜 W s x (V x) - fderivWithin 𝕜 V s x (W x)

lemma lieBracket_eq :
    lieBracket 𝕜 V W = fun x ↦ fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x) := rfl

lemma lieBracketWithin_eq :
    lieBracketWithin 𝕜 V W s =
      fun x ↦ fderivWithin 𝕜 W s x (V x) - fderivWithin 𝕜 V s x (W x) := rfl

@[simp]
theorem lieBracketWithin_univ : lieBracketWithin 𝕜 V W univ = lieBracket 𝕜 V W := by
  ext1 x
  simp [lieBracketWithin, lieBracket]

lemma lieBracketWithin_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) :
    lieBracketWithin 𝕜 V W s x = 0 := by
  simp [lieBracketWithin, hV, hW]

lemma lieBracket_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) :
    lieBracket 𝕜 V W x = 0 := by
  simp [lieBracket, hV, hW]

lemma lieBracketWithin_swap : lieBracketWithin 𝕜 V W s = - lieBracketWithin 𝕜 W V s := by
  ext x; simp [lieBracketWithin]

lemma lieBracket_swap : lieBracket 𝕜 V W x = - lieBracket 𝕜 W V x := by
  simp [lieBracket]

@[simp] lemma lieBracketWithin_self : lieBracketWithin 𝕜 V V s = 0 := by
  ext x; simp [lieBracketWithin]

@[simp] lemma lieBracket_self : lieBracket 𝕜 V V = 0 := by
  ext x; simp [lieBracket]

lemma lieBracketWithin_const_smul_left {c : 𝕜} (hV : DifferentiableWithinAt 𝕜 V s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 (c • V) W s x =
      c • lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, smul_sub, fderivWithin_const_smul hs hV]

lemma lieBracket_const_smul_left {c : 𝕜} (hV : DifferentiableAt 𝕜 V x) :
    lieBracket 𝕜 (c • V) W x = c • lieBracket 𝕜 V W x := by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ] at hV ⊢
  exact lieBracketWithin_const_smul_left hV uniqueDiffWithinAt_univ

lemma lieBracketWithin_const_smul_right {c : 𝕜} (hW : DifferentiableWithinAt 𝕜 W s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (c • W) s x =
      c • lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, smul_sub, fderivWithin_const_smul hs hW]

lemma lieBracket_const_smul_right {c : 𝕜} (hW : DifferentiableAt 𝕜 W x) :
    lieBracket 𝕜 V (c • W) x = c • lieBracket 𝕜 V W x := by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ] at hW ⊢
  exact lieBracketWithin_const_smul_right hW uniqueDiffWithinAt_univ

/--
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a function `f : E → 𝕜`,
we have `[V, f • W] = (df V) • W + f • [V, W]`
-/
lemma lieBracketWithin_smul_right {f : E → 𝕜} (hf : DifferentiableWithinAt 𝕜 f s x)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (fun y ↦ f y • W y) s x =
      (fderivWithin 𝕜 f s x) (V x) • (W x) + (f x) • lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, fderivWithin_fun_smul hs hf hW, map_smul, add_comm, smul_sub,
    add_sub_assoc]

/--
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a function `f : E → 𝕜`,
we have `[V, f • W] = (df V) • W + f • [V, W]`
-/
lemma lieBracket_smul_right {f : E → 𝕜} (hf : DifferentiableAt 𝕜 f x)
    (hW : DifferentiableAt 𝕜 W x) :
    lieBracket 𝕜 V (fun y ↦ f y • W y) x =
      (fderiv 𝕜 f x) (V x) • (W x) + (f x) • lieBracket 𝕜 V W x := by
  simp_rw [← differentiableWithinAt_univ, ← lieBracketWithin_univ, fderiv] at hW hf ⊢
  exact lieBracketWithin_smul_right hf hW uniqueDiffWithinAt_univ

/--
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a function `f : E → 𝕜`,
we have `[f • V, W] = - (df W) • V + f • [V, W]`
-/
lemma lieBracketWithin_smul_left {f : E → 𝕜} (hf : DifferentiableWithinAt 𝕜 f s x)
    (hV : DifferentiableWithinAt 𝕜 V s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 (fun y ↦ f y • V y) W s x =
      - (fderivWithin 𝕜 f s x) (W x) • (V x)  + (f x) • lieBracketWithin 𝕜 V W s x := by
  rw [lieBracketWithin_swap, Pi.neg_apply, lieBracketWithin_smul_right hf hV hs,
    lieBracketWithin_swap, add_comm]
  simp

/--
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a function `f : E → 𝕜`,
we have `[f • V, W] = - (df W) • V + f • [V, W]`
-/
lemma lieBracket_fmul_left {f : E → 𝕜} (hf : DifferentiableAt 𝕜 f x)
    (hV : DifferentiableAt 𝕜 V x) :
    lieBracket 𝕜 (fun y ↦ f y • V y) W x =
      - (fderiv 𝕜 f x) (W x) • (V x)  + (f x) • lieBracket 𝕜 V W x := by
  rw [lieBracket_swap, lieBracket_smul_right hf hV, lieBracket_swap, add_comm]
  simp

lemma lieBracketWithin_add_left (hV : DifferentiableWithinAt 𝕜 V s x)
    (hV₁ : DifferentiableWithinAt 𝕜 V₁ s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 (V + V₁) W s x =
      lieBracketWithin 𝕜 V W s x + lieBracketWithin 𝕜 V₁ W s x := by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add hs hV hV₁, ContinuousLinearMap.add_apply]
  abel

lemma lieBracket_add_left (hV : DifferentiableAt 𝕜 V x) (hV₁ : DifferentiableAt 𝕜 V₁ x) :
    lieBracket 𝕜 (V + V₁) W  x =
      lieBracket 𝕜 V W x + lieBracket 𝕜 V₁ W x := by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add hV hV₁, ContinuousLinearMap.add_apply]
  abel

/-- We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set. -/
@[simp]
lemma lieBracketWithin_zero_left : lieBracketWithin 𝕜 0 W s = 0 := by ext; simp [lieBracketWithin]

/-- We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set. -/
@[simp]
lemma lieBracketWithin_zero_right : lieBracketWithin 𝕜 W 0 s = 0 := by ext; simp [lieBracketWithin]

/-- We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. -/
@[simp]
lemma lieBracket_zero_left : lieBracket 𝕜 0 W = 0 := by simp [← lieBracketWithin_univ]

/-- We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. -/
@[simp]
lemma lieBracket_zero_right : lieBracket 𝕜 W 0 = 0 := by simp [← lieBracketWithin_univ]

lemma lieBracketWithin_add_right (hW : DifferentiableWithinAt 𝕜 W s x)
    (hW₁ : DifferentiableWithinAt 𝕜 W₁ s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (W + W₁) s x =
      lieBracketWithin 𝕜 V W s x + lieBracketWithin 𝕜 V W₁ s x := by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add hs hW hW₁, ContinuousLinearMap.add_apply]
  abel

lemma lieBracket_add_right (hW : DifferentiableAt 𝕜 W x) (hW₁ : DifferentiableAt 𝕜 W₁ x) :
    lieBracket 𝕜 V (W + W₁) x =
      lieBracket 𝕜 V W x + lieBracket 𝕜 V W₁ x := by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add hW hW₁, ContinuousLinearMap.add_apply]
  abel

lemma _root_.ContDiffWithinAt.lieBracketWithin_vectorField
    {m n : WithTop ℕ∞} (hV : ContDiffWithinAt 𝕜 n V s x)
    (hW : ContDiffWithinAt 𝕜 n W s x) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 m (lieBracketWithin 𝕜 V W s) s x := by
  apply ContDiffWithinAt.sub
  · exact ContDiffWithinAt.clm_apply (hW.fderivWithin_right hs hmn hx)
      (hV.of_le (le_trans le_self_add hmn))
  · exact ContDiffWithinAt.clm_apply (hV.fderivWithin_right hs hmn hx)
      (hW.of_le (le_trans le_self_add hmn))

lemma _root_.ContDiffAt.lieBracket_vectorField {m n : WithTop ℕ∞} (hV : ContDiffAt 𝕜 n V x)
    (hW : ContDiffAt 𝕜 n W x) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (lieBracket 𝕜 V W) x := by
  rw [← contDiffWithinAt_univ] at hV hW ⊢
  simp_rw [← lieBracketWithin_univ]
  exact hV.lieBracketWithin_vectorField hW uniqueDiffOn_univ hmn (mem_univ _)

lemma _root_.ContDiffOn.lieBracketWithin_vectorField {m n : WithTop ℕ∞} (hV : ContDiffOn 𝕜 n V s)
    (hW : ContDiffOn 𝕜 n W s) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (lieBracketWithin 𝕜 V W s) s :=
  fun x hx ↦ (hV x hx).lieBracketWithin_vectorField (hW x hx) hs hmn hx

lemma _root_.ContDiff.lieBracket_vectorField {m n : WithTop ℕ∞} (hV : ContDiff 𝕜 n V)
    (hW : ContDiff 𝕜 n W) (hmn : m + 1 ≤ n) :
    ContDiff 𝕜 m (lieBracket 𝕜 V W) :=
  contDiff_iff_contDiffAt.2 (fun _ ↦ hV.contDiffAt.lieBracket_vectorField hW.contDiffAt hmn)

theorem lieBracketWithin_of_mem_nhdsWithin (st : t ∈ 𝓝[s] x) (hs : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableWithinAt 𝕜 V t x) (hW : DifferentiableWithinAt 𝕜 W t x) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x := by
  simp [lieBracketWithin, fderivWithin_of_mem_nhdsWithin st hs hV,
    fderivWithin_of_mem_nhdsWithin st hs hW]

theorem lieBracketWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableWithinAt 𝕜 V t x) (hW : DifferentiableWithinAt 𝕜 W t x) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x :=
  lieBracketWithin_of_mem_nhdsWithin (nhdsWithin_mono _ st self_mem_nhdsWithin) ht hV hW

theorem lieBracketWithin_inter (ht : t ∈ 𝓝 x) :
    lieBracketWithin 𝕜 V W (s ∩ t) x = lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, fderivWithin_inter, ht]

theorem lieBracketWithin_of_mem_nhds (h : s ∈ 𝓝 x) :
    lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x := by
  rw [← lieBracketWithin_univ, ← univ_inter s, lieBracketWithin_inter h]

theorem lieBracketWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) :
    lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x :=
  lieBracketWithin_of_mem_nhds (hs.mem_nhds hx)

theorem lieBracketWithin_eq_lieBracket (hs : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableAt 𝕜 V x) (hW : DifferentiableAt 𝕜 W x) :
    lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x := by
  simp [lieBracketWithin, lieBracket, fderivWithin_eq_fderiv, hs, hV, hW]

/-- Variant of `lieBracketWithin_congr_set` where one requires the sets to coincide only in
the complement of a point. -/
theorem lieBracketWithin_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x := by
  simp [lieBracketWithin, fderivWithin_congr_set' _ h]

theorem lieBracketWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x :=
  lieBracketWithin_congr_set' x <| h.filter_mono inf_le_left

/-- Variant of `lieBracketWithin_eventually_congr_set` where one requires the sets to coincide only
in the complement of a point. -/
theorem lieBracketWithin_eventually_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    lieBracketWithin 𝕜 V W s =ᶠ[𝓝 x] lieBracketWithin 𝕜 V W t :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => lieBracketWithin_congr_set' y

theorem lieBracketWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    lieBracketWithin 𝕜 V W s =ᶠ[𝓝 x] lieBracketWithin 𝕜 V W t :=
  lieBracketWithin_eventually_congr_set' x <| h.filter_mono inf_le_left

theorem _root_.DifferentiableWithinAt.lieBracketWithin_congr_mono
    (hV : DifferentiableWithinAt 𝕜 V s x) (hVs : EqOn V₁ V t) (hVx : V₁ x = V x)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hWs : EqOn W₁ W t) (hWx : W₁ x = W x)
    (hxt : UniqueDiffWithinAt 𝕜 t x) (h₁ : t ⊆ s) :
    lieBracketWithin 𝕜 V₁ W₁ t x = lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, hV.fderivWithin_congr_mono, hW.fderivWithin_congr_mono, hVs, hVx,
    hWs, hWx, hxt, h₁]

theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hxV : V₁ x = V x) (hW : W₁ =ᶠ[𝓝[s] x] W) (hxW : W₁ x = W x) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x := by
  simp only [lieBracketWithin, hV.fderivWithin_eq hxV, hW.fderivWithin_eq hxW, hxV, hxW]

theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (hx : x ∈ s) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  hV.lieBracketWithin_vectorField_eq (mem_of_mem_nhdsWithin hx hV :)
    hW (mem_of_mem_nhdsWithin hx hW :)

/-- If vector fields coincide on a neighborhood of a point within a set, then the Lie brackets
also coincide on a neighborhood of this point within this set. Version where one considers the Lie
bracket within a subset. -/
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField'
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (ht : t ⊆ s) :
    lieBracketWithin 𝕜 V₁ W₁ t =ᶠ[𝓝[s] x] lieBracketWithin 𝕜 V W t := by
  filter_upwards [hV.fderivWithin' ht (𝕜 := 𝕜), hW.fderivWithin' ht (𝕜 := 𝕜), hV, hW]
    with x hV' hW' hV hW
  simp [lieBracketWithin, hV', hW', hV, hW]

protected theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s =ᶠ[𝓝[s] x] lieBracketWithin 𝕜 V W s :=
  hV.lieBracketWithin_vectorField' hW Subset.rfl

protected theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_insert
    (hV : V₁ =ᶠ[𝓝[insert x s] x] V) (hW : W₁ =ᶠ[𝓝[insert x s] x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x := by
  apply mem_of_mem_nhdsWithin (mem_insert x s) (hV.lieBracketWithin_vectorField' hW
    (subset_insert x s))

theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_nhds
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  (hV.filter_mono nhdsWithin_le_nhds).lieBracketWithin_vectorField_eq hV.self_of_nhds
    (hW.filter_mono nhdsWithin_le_nhds) hW.self_of_nhds

theorem lieBracketWithin_congr
    (hV : EqOn V₁ V s) (hVx : V₁ x = V x) (hW : EqOn W₁ W s) (hWx : W₁ x = W x) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  (hV.eventuallyEq.filter_mono inf_le_right).lieBracketWithin_vectorField_eq hVx
    (hW.eventuallyEq.filter_mono inf_le_right) hWx

/-- Version of `lieBracketWithin_congr` in which one assumes that the point belongs to the
given set. -/
theorem lieBracketWithin_congr' (hV : EqOn V₁ V s) (hW : EqOn W₁ W s) (hx : x ∈ s) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  lieBracketWithin_congr hV (hV hx) hW (hW hx)

theorem _root_.Filter.EventuallyEq.lieBracket_vectorField_eq
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    lieBracket 𝕜 V₁ W₁ x = lieBracket 𝕜 V W x := by
  rw [← lieBracketWithin_univ, ← lieBracketWithin_univ, hV.lieBracketWithin_vectorField_eq_nhds hW]

protected theorem _root_.Filter.EventuallyEq.lieBracket_vectorField
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) : lieBracket 𝕜 V₁ W₁ =ᶠ[𝓝 x] lieBracket 𝕜 V W := by
  filter_upwards [hV.eventuallyEq_nhds, hW.eventuallyEq_nhds] with y hVy hWy
  exact hVy.lieBracket_vectorField_eq hWy

/-- The Lie bracket of vector fields in vector spaces satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]`. -/
lemma leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt
    {U V W : E → E} {s : Set E} {x : E} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s)
    (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x)
    (hW : ContDiffWithinAt 𝕜 2 W s x)
    (h'U : IsSymmSndFDerivWithinAt 𝕜 U s x) (h'V : IsSymmSndFDerivWithinAt 𝕜 V s x)
    (h'W : IsSymmSndFDerivWithinAt 𝕜 W s x) :
    lieBracketWithin 𝕜 U (lieBracketWithin 𝕜 V W s) s x =
      lieBracketWithin 𝕜 (lieBracketWithin 𝕜 U V s) W s x
      + lieBracketWithin 𝕜 V (lieBracketWithin 𝕜 U W s) s x := by
  simp only [lieBracketWithin_eq, map_sub]
  have aux₁ {U V : E → E} (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x) :
      DifferentiableWithinAt 𝕜 (fun x ↦ (fderivWithin 𝕜 V s x) (U x)) s x :=
    have := hV.fderivWithin_right_apply (hU.of_le one_le_two) hs le_rfl hx
    this.differentiableWithinAt le_rfl
  have aux₂ {U V : E → E} (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x) :
      fderivWithin 𝕜 (fun y ↦ (fderivWithin 𝕜 U s y) (V y)) s x =
        (fderivWithin 𝕜 U s x).comp (fderivWithin 𝕜 V s x) +
        (fderivWithin 𝕜 (fderivWithin 𝕜 U s) s x).flip (V x) := by
    refine fderivWithin_clm_apply (hs x hx) ?_ (hV.differentiableWithinAt one_le_two)
    exact (hU.fderivWithin_right hs le_rfl hx).differentiableWithinAt le_rfl
  rw [fderivWithin_fun_sub (hs x hx) (aux₁ hV hW) (aux₁ hW hV)]
  rw [fderivWithin_fun_sub (hs x hx) (aux₁ hU hV) (aux₁ hV hU)]
  rw [fderivWithin_fun_sub (hs x hx) (aux₁ hU hW) (aux₁ hW hU)]
  rw [aux₂ hW hV, aux₂ hV hW, aux₂ hV hU, aux₂ hU hV, aux₂ hW hU, aux₂ hU hW]
  simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.flip_apply, h'V.eq,
    h'U.eq, h'W.eq]
  abel

/-- The Lie bracket of vector fields in vector spaces satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]`. -/
lemma leibniz_identity_lieBracketWithin (hn : minSmoothness 𝕜 2 ≤ n)
    {U V W : E → E} {s : Set E} {x : E}
    (hs : UniqueDiffOn 𝕜 s) (h'x : x ∈ closure (interior s)) (hx : x ∈ s)
    (hU : ContDiffWithinAt 𝕜 n U s x) (hV : ContDiffWithinAt 𝕜 n V s x)
    (hW : ContDiffWithinAt 𝕜 n W s x) :
    lieBracketWithin 𝕜 U (lieBracketWithin 𝕜 V W s) s x =
      lieBracketWithin 𝕜 (lieBracketWithin 𝕜 U V s) W s x
      + lieBracketWithin 𝕜 V (lieBracketWithin 𝕜 U W s) s x := by
  apply leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt hs hx
    (hU.of_le (le_minSmoothness.trans hn)) (hV.of_le (le_minSmoothness.trans hn))
    (hW.of_le (le_minSmoothness.trans hn))
  · exact hU.isSymmSndFDerivWithinAt hn hs h'x hx
  · exact hV.isSymmSndFDerivWithinAt hn hs h'x hx
  · exact hW.isSymmSndFDerivWithinAt hn hs h'x hx

/-- The Lie bracket of vector fields in vector spaces satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]`. -/
lemma leibniz_identity_lieBracket (hn : minSmoothness 𝕜 2 ≤ n) {U V W : E → E} {x : E}
    (hU : ContDiffAt 𝕜 n U x) (hV : ContDiffAt 𝕜 n V x) (hW : ContDiffAt 𝕜 n W x) :
    lieBracket 𝕜 U (lieBracket 𝕜 V W) x =
      lieBracket 𝕜 (lieBracket 𝕜 U V) W x + lieBracket 𝕜 V (lieBracket 𝕜 U W) x := by
  simp only [← lieBracketWithin_univ, ← contDiffWithinAt_univ] at hU hV hW ⊢
  exact leibniz_identity_lieBracketWithin hn uniqueDiffOn_univ (by simp) (mem_univ _) hU hV hW


/-!
### The pullback of vector fields in a vector space
-/

variable (𝕜) in
/-- The pullback of a vector field under a function, defined
as `(f^* V) (x) = Df(x)^{-1} (V (f x))`. If `Df(x)` is not invertible, we use the junk value `0`.
-/
def pullback (f : E → F) (V : F → F) (x : E) : E := (fderiv 𝕜 f x).inverse (V (f x))

variable (𝕜) in
/-- The pullback within a set of a vector field under a function, defined
as `(f^* V) (x) = Df(x)^{-1} (V (f x))` where `Df(x)` is the derivative of `f` within `s`.
If `Df(x)` is not invertible, we use the junk value `0`.
-/
def pullbackWithin (f : E → F) (V : F → F) (s : Set E) (x : E) : E :=
  (fderivWithin 𝕜 f s x).inverse (V (f x))

lemma pullbackWithin_eq {f : E → F} {V : F → F} {s : Set E} :
    pullbackWithin 𝕜 f V s = fun x ↦ (fderivWithin 𝕜 f s x).inverse (V (f x)) := rfl

lemma pullback_eq_of_fderiv_eq
    {f : E → F} {M : E ≃L[𝕜] F} {x : E} (hf : M = fderiv 𝕜 f x) (V : F → F) :
    pullback 𝕜 f V x = M.symm (V (f x)) := by
  simp [pullback, ← hf]

lemma pullback_eq_of_not_isInvertible {f : E → F} {x : E}
    (h : ¬(fderiv 𝕜 f x).IsInvertible) (V : F → F) :
    pullback 𝕜 f V x = 0 := by
  simp [pullback, h]

lemma pullbackWithin_eq_of_not_isInvertible {f : E → F} {x : E}
    (h : ¬(fderivWithin 𝕜 f s x).IsInvertible) (V : F → F) :
    pullbackWithin 𝕜 f V s x = 0 := by
  simp [pullbackWithin, h]

lemma pullbackWithin_eq_of_fderivWithin_eq
    {f : E → F} {M : E ≃L[𝕜] F} {x : E} (hf : M = fderivWithin 𝕜 f s x) (V : F → F) :
    pullbackWithin 𝕜 f V s x = M.symm (V (f x)) := by
  simp [pullbackWithin, ← hf]

@[simp] lemma pullbackWithin_univ {f : E → F} {V : F → F} :
    pullbackWithin 𝕜 f V univ = pullback 𝕜 f V := by
  ext x
  simp [pullbackWithin, pullback]

open scoped Topology Filter

lemma fderiv_pullback (f : E → F) (V : F → F) (x : E) (h'f : (fderiv 𝕜 f x).IsInvertible) :
    fderiv 𝕜 f x (pullback 𝕜 f V x) = V (f x) := by
  rcases h'f with ⟨M, hM⟩
  simp [pullback_eq_of_fderiv_eq hM, ← hM]

lemma fderivWithin_pullbackWithin {f : E → F} {V : F → F} {x : E}
    (h'f : (fderivWithin 𝕜 f s x).IsInvertible) :
    fderivWithin 𝕜 f s x (pullbackWithin 𝕜 f V s x) = V (f x) := by
  rcases h'f with ⟨M, hM⟩
  simp [pullbackWithin_eq_of_fderivWithin_eq hM, ← hM]

open Set

variable [CompleteSpace E]

/-- If a `C^2` map has an invertible derivative within a set at a point, then nearby derivatives
can be written as continuous linear equivs, which depend in a `C^1` way on the point, as well as
their inverse, and moreover one can compute the derivative of the inverse. -/
lemma _root_.exists_continuousLinearEquiv_fderivWithin_symm_eq
    {f : E → F} {s : Set E} {x : E} (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hf : (fderivWithin 𝕜 f s x).IsInvertible) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    ∃ N : E → (E ≃L[𝕜] F), ContDiffWithinAt 𝕜 1 (fun y ↦ (N y : E →L[𝕜] F)) s x
    ∧ ContDiffWithinAt 𝕜 1 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x
    ∧ (∀ᶠ y in 𝓝[s] x, N y = fderivWithin 𝕜 f s y)
    ∧ ∀ v, fderivWithin 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x v
      = - (N x).symm  ∘L ((fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x v)) ∘L (N x).symm := by
  classical
  rcases hf with ⟨M, hM⟩
  let U := {y | ∃ (N : E ≃L[𝕜] F), N = fderivWithin 𝕜 f s y}
  have hU : U ∈ 𝓝[s] x := by
    have I : range ((↑) : (E ≃L[𝕜] F) → E →L[𝕜] F) ∈ 𝓝 (fderivWithin 𝕜 f s x) := by
      rw [← hM]
      exact M.nhds
    have : ContinuousWithinAt (fderivWithin 𝕜 f s) s x :=
      (h'f.fderivWithin_right (m := 1) hs le_rfl hx).continuousWithinAt
    exact this I
  let N : E → (E ≃L[𝕜] F) := fun x ↦ if h : x ∈ U then h.choose else M
  have eN : (fun y ↦ (N y : E →L[𝕜] F)) =ᶠ[𝓝[s] x] fun y ↦ fderivWithin 𝕜 f s y := by
    filter_upwards [hU] with y hy
    simpa only [hy, ↓reduceDIte, N] using Exists.choose_spec hy
  have e'N : N x = fderivWithin 𝕜 f s x := by apply mem_of_mem_nhdsWithin hx eN
  have hN : ContDiffWithinAt 𝕜 1 (fun y ↦ (N y : E →L[𝕜] F)) s x := by
    have : ContDiffWithinAt 𝕜 1 (fun y ↦ fderivWithin 𝕜 f s y) s x :=
      h'f.fderivWithin_right (m := 1) hs le_rfl hx
    apply this.congr_of_eventuallyEq eN e'N
  have hN' : ContDiffWithinAt 𝕜 1 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x := by
    have : ContDiffWithinAt 𝕜 1 (ContinuousLinearMap.inverse ∘ (fun y ↦ (N y : E →L[𝕜] F))) s x :=
      (contDiffAt_map_inverse (N x)).comp_contDiffWithinAt x hN
    convert this with y
    simp only [Function.comp_apply, ContinuousLinearMap.inverse_equiv]
  refine ⟨N, hN, hN', eN, fun v ↦ ?_⟩
  have A' y : ContinuousLinearMap.compL 𝕜 F E F (N y : E →L[𝕜] F) ((N y).symm : F →L[𝕜] E)
      = ContinuousLinearMap.id 𝕜 F := by ext; simp
  have : fderivWithin 𝕜 (fun y ↦ ContinuousLinearMap.compL 𝕜 F E F (N y : E →L[𝕜] F)
      ((N y).symm : F →L[𝕜] E)) s x v = 0 := by
    simp [A', fderivWithin_const_apply]
  have I : (N x : E →L[𝕜] F) ∘L (fderivWithin 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x v) =
      - (fderivWithin 𝕜 (fun y ↦ (N y : E →L[𝕜] F)) s x v) ∘L ((N x).symm : F →L[𝕜] E) := by
    rw [ContinuousLinearMap.fderivWithin_of_bilinear _ (hN.differentiableWithinAt le_rfl)
      (hN'.differentiableWithinAt le_rfl) (hs x hx)] at this
    simpa [eq_neg_iff_add_eq_zero] using this
  have B (M : F →L[𝕜] E) : M = ((N x).symm : F →L[𝕜] E) ∘L ((N x) ∘L M) := by
    ext; simp
  rw [B (fderivWithin 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x v), I]
  simp only [ContinuousLinearMap.comp_neg, eN.fderivWithin_eq e'N]

lemma DifferentiableWithinAt.pullbackWithin {f : E → F} {V : F → F} {s : Set E} {t : Set F} {x : E}
    (hV : DifferentiableWithinAt 𝕜 V t (f x))
    (hf : ContDiffWithinAt 𝕜 2 f s x) (hf' : (fderivWithin 𝕜 f s x).IsInvertible)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    DifferentiableWithinAt 𝕜 (pullbackWithin 𝕜 f V s) s x := by
  rcases exists_continuousLinearEquiv_fderivWithin_symm_eq hf hf' hs hx
    with ⟨M, -, M_symm_smooth, hM, -⟩
  simp only [pullbackWithin_eq]
  have : DifferentiableWithinAt 𝕜 (fun y ↦ ((M y).symm : F →L[𝕜] E) (V (f y))) s x := by
    apply DifferentiableWithinAt.clm_apply
    · exact M_symm_smooth.differentiableWithinAt le_rfl
    · exact hV.comp _ (hf.differentiableWithinAt one_le_two) hst
  apply this.congr_of_eventuallyEq
  · filter_upwards [hM] with y hy using by simp [← hy]
  · have hMx : M x = fderivWithin 𝕜 f s x := by apply mem_of_mem_nhdsWithin hx hM
    simp [← hMx]

/-- If a `C^2` map has an invertible derivative at a point, then nearby derivatives can be written
as continuous linear equivs, which depend in a `C^1` way on the point, as well as their inverse, and
moreover one can compute the derivative of the inverse. -/
lemma _root_.exists_continuousLinearEquiv_fderiv_symm_eq
    {f : E → F} {x : E} (h'f : ContDiffAt 𝕜 2 f x) (hf : (fderiv 𝕜 f x).IsInvertible) :
    ∃ N : E → (E ≃L[𝕜] F), ContDiffAt 𝕜 1 (fun y ↦ (N y : E →L[𝕜] F)) x
    ∧ ContDiffAt 𝕜 1 (fun y ↦ ((N y).symm : F →L[𝕜] E)) x
    ∧ (∀ᶠ y in 𝓝 x, N y = fderiv 𝕜 f y)
    ∧ ∀ v, fderiv 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) x v
      = - (N x).symm  ∘L ((fderiv 𝕜 (fderiv 𝕜 f) x v)) ∘L (N x).symm := by
  simp only [← fderivWithin_univ, ← contDiffWithinAt_univ, ← nhdsWithin_univ] at hf h'f ⊢
  exact exists_continuousLinearEquiv_fderivWithin_symm_eq h'f hf uniqueDiffOn_univ (mem_univ _)

/-- The Lie bracket commutes with taking pullbacks. This requires the function to have symmetric
second derivative. Version in a complete space. One could also give a version avoiding
completeness but requiring that `f` is a local diffeo. -/
lemma pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
    {f : E → F} {V W : F → F} {x : E} {t : Set F}
    (hf : IsSymmSndFDerivWithinAt 𝕜 f s x) (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x))
    (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
      = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x := by
  by_cases h : (fderivWithin 𝕜 f s x).IsInvertible; swap
  · simp [pullbackWithin_eq_of_not_isInvertible h, lieBracketWithin_eq]
  rcases exists_continuousLinearEquiv_fderivWithin_symm_eq h'f h hu hx
    with ⟨M, -, M_symm_smooth, hM, M_diff⟩
  have hMx : M x = fderivWithin 𝕜 f s x := (mem_of_mem_nhdsWithin hx hM :)
  have AV : fderivWithin 𝕜 (pullbackWithin 𝕜 f V s) s x =
      fderivWithin 𝕜 (fun y ↦ ((M y).symm : F →L[𝕜] E) (V (f y))) s x := by
    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx
    filter_upwards [hM] with y hy using pullbackWithin_eq_of_fderivWithin_eq hy _
  have AW : fderivWithin 𝕜 (pullbackWithin 𝕜 f W s) s x =
      fderivWithin 𝕜 (fun y ↦ ((M y).symm : F →L[𝕜] E) (W (f y))) s x := by
    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx
    filter_upwards [hM] with y hy using pullbackWithin_eq_of_fderivWithin_eq hy _
  have Af : DifferentiableWithinAt 𝕜 f s x := h'f.differentiableWithinAt one_le_two
  simp only [lieBracketWithin_eq, pullbackWithin_eq_of_fderivWithin_eq hMx, map_sub, AV, AW]
  rw [fderivWithin_clm_apply, fderivWithin_clm_apply]
  · simp [fderivWithin_comp' x hW Af hst (hu x hx), ← hMx,
      fderivWithin_comp' x hV Af hst (hu x hx), M_diff, hf.eq]
  · exact hu x hx
  · exact M_symm_smooth.differentiableWithinAt le_rfl
  · exact hV.comp x Af hst
  · exact hu x hx
  · exact M_symm_smooth.differentiableWithinAt le_rfl
  · exact hW.comp x Af hst

/-- The Lie bracket commutes with taking pullbacks. This requires the function to have symmetric
second derivative. Version in a complete space. One could also give a version avoiding
completeness but requiring that `f` is a local diffeo. Variant where unique differentiability and
the invariance property are only required in a smaller set `u`. -/
lemma pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt_of_eventuallyEq
    {f : E → F} {V W : F → F} {x : E} {t : Set F} {u : Set E}
    (hf : IsSymmSndFDerivWithinAt 𝕜 f s x) (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x))
    (hu : UniqueDiffOn 𝕜 u) (hx : x ∈ u) (hst : MapsTo f u t) (hus : u =ᶠ[𝓝 x] s) :
    pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
      = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x := calc
  pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
  _ = pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) u x := by
    simp only [pullbackWithin]
    congr 2
    exact fderivWithin_congr_set hus.symm
  _ = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V u) (pullbackWithin 𝕜 f W u) u x :=
    pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
      (hf.congr_set hus.symm) (h'f.congr_set hus.symm) hV hW hu hx hst
  _ = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) u x := by
    apply Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem _ _ hx
    · apply nhdsWithin_le_nhds
      filter_upwards [fderivWithin_eventually_congr_set (𝕜 := 𝕜) (f := f) hus] with y hy
      simp [pullbackWithin, hy]
    · apply nhdsWithin_le_nhds
      filter_upwards [fderivWithin_eventually_congr_set (𝕜 := 𝕜) (f := f) hus] with y hy
      simp [pullbackWithin, hy]
  _ = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x :=
    lieBracketWithin_congr_set hus

/-- The Lie bracket commutes with taking pullbacks. This requires the function to have symmetric
second derivative. Version in a complete space. One could also give a version avoiding
completeness but requiring that `f` is a local diffeo. -/
lemma pullback_lieBracket_of_isSymmSndFDerivAt {f : E → F} {V W : F → F} {x : E}
    (hf : IsSymmSndFDerivAt 𝕜 f x) (h'f : ContDiffAt 𝕜 2 f x)
    (hV : DifferentiableAt 𝕜 V (f x)) (hW : DifferentiableAt 𝕜 W (f x)) :
    pullback 𝕜 f (lieBracket 𝕜 V W) x = lieBracket 𝕜 (pullback 𝕜 f V) (pullback 𝕜 f W) x := by
  simp only [← lieBracketWithin_univ, ← pullbackWithin_univ, ← isSymmSndFDerivWithinAt_univ,
    ← differentiableWithinAt_univ] at hf h'f hV hW ⊢
  exact pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt hf h'f hV hW uniqueDiffOn_univ
    (mem_univ _) (mapsTo_univ _ _)

/-- The Lie bracket commutes with taking pullbacks. This requires the function to have symmetric
second derivative. Version in a complete space. One could also give a version avoiding
completeness but requiring that `f` is a local diffeo. -/
lemma pullbackWithin_lieBracketWithin
    {f : E → F} {V W : F → F} {x : E} {t : Set F} (hn : minSmoothness 𝕜 2 ≤ n)
    (h'f : ContDiffWithinAt 𝕜 n f s x)
    (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x))
    (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (h'x : x ∈ closure (interior s)) (hst : MapsTo f s t) :
    pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
      = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x :=
  pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
  (h'f.isSymmSndFDerivWithinAt hn hu h'x hx) (h'f.of_le (le_minSmoothness.trans hn)) hV hW hu hx hst

/-- The Lie bracket commutes with taking pullbacks. One could also give a version avoiding
completeness but requiring that `f` is a local diffeo. -/
lemma pullback_lieBracket (hn : minSmoothness 𝕜 2 ≤ n)
    {f : E → F} {V W : F → F} {x : E} (h'f : ContDiffAt 𝕜 n f x)
    (hV : DifferentiableAt 𝕜 V (f x)) (hW : DifferentiableAt 𝕜 W (f x)) :
    pullback 𝕜 f (lieBracket 𝕜 V W) x = lieBracket 𝕜 (pullback 𝕜 f V) (pullback 𝕜 f W) x :=
  pullback_lieBracket_of_isSymmSndFDerivAt (h'f.isSymmSndFDerivAt hn)
    (h'f.of_le (le_minSmoothness.trans hn)) hV hW

end VectorField
