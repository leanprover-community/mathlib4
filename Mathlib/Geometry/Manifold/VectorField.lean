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

open Set
open scoped Topology

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 :Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F]
  {G : Type*} [TopologicalSpace G] [AddCommGroup G] [Module 𝕜 G]

/-- A continuous linear map is invertible if it is the forward direction of a continuous linear
equivalence. -/
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

lemma IsInvertible.of_inverse {f : E →L[𝕜] F} {g : F →L[𝕜] E}
    (hf : f ∘L g = id 𝕜 F) (hg : g ∘L f = id 𝕜 E) :
    f.IsInvertible := by
  let M : E ≃L[𝕜] F :=
  { f with
    invFun := g
    left_inv := by
      intro x
      have : (g ∘L f) x = x := by simp [hg]
      simpa using this
    right_inv := by
      intro x
      have : (f ∘L g) x = x := by simp [hf]
      simpa using this }
  exact ⟨M, rfl⟩

/-- At an invertible map `e : E →L[𝕜] F` between Banach spaces, the operation of
inversion is `C^n`, for all `n`. -/
theorem IsInvertible.contDiffAt_map_inverse {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] (e : E →L[𝕜] F)
    (he : e.IsInvertible) {n : ℕ∞} :
    ContDiffAt 𝕜 n inverse e := by
  rcases he with ⟨M, rfl⟩
  exact _root_.contDiffAt_map_inverse M

lemma inverse_of_not_isInvertible {f : E →L[𝕜] F} (hf : ¬ f.IsInvertible) : f.inverse = 0 :=
  inverse_non_equiv _ hf

@[simp] lemma isInvertible_equiv_comp {e : F ≃L[𝕜] G} {f : E →L[𝕜] F} :
    ((e : F →L[𝕜] G) ∘L f).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨M, hM⟩
    have : f = e.symm ∘L ((e : F →L[𝕜] G) ∘L f) := by ext; simp
    rw [this, ← hM]
    simp
  · rintro ⟨M, rfl⟩
    simp

@[simp] lemma isInvertible_comp_equiv {e : G ≃L[𝕜] E} {f : E →L[𝕜] F} :
    (f ∘L (e : G →L[𝕜] E)).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨M, hM⟩
    have : f = (f ∘L (e : G →L[𝕜] E)) ∘L e.symm := by ext; simp
    rw [this, ← hM]
    simp
  · rintro ⟨M, rfl⟩
    simp

@[simp] lemma inverse_equiv_comp {e : F ≃L[𝕜] G} {f : E →L[𝕜] F} :
    (e ∘L f).inverse = f.inverse ∘L (e.symm : G →L[𝕜] F) := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨M, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf]
    rfl

@[simp] lemma inverse_comp_equiv {e : G ≃L[𝕜] E} {f : E →L[𝕜] F} :
    (f ∘L e).inverse = (e.symm : E →L[𝕜] G) ∘L f.inverse := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨M, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf]
    simp

end ContinuousLinearMap


section LieBracketVectorField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
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

lemma lieBracketWithin_add_left (hV : DifferentiableWithinAt 𝕜 V s x)
    (hV₁ : DifferentiableWithinAt 𝕜 V₁ s x) (hs :  UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 (V + V₁) W s x =
      lieBracketWithin 𝕜 V W s x + lieBracketWithin 𝕜 V₁ W s x := by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add' hs hV hV₁, ContinuousLinearMap.add_apply]
  abel

lemma lieBracket_add_left (hV : DifferentiableAt 𝕜 V x) (hV₁ : DifferentiableAt 𝕜 V₁ x) :
    lieBracket 𝕜 (V + V₁) W  x =
      lieBracket 𝕜 V W x + lieBracket 𝕜 V₁ W x := by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add' hV hV₁, ContinuousLinearMap.add_apply]
  abel

lemma lieBracketWithin_add_right (hW : DifferentiableWithinAt 𝕜 W s x)
    (hW₁ : DifferentiableWithinAt 𝕜 W₁ s x) (hs :  UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (W + W₁) s x =
      lieBracketWithin 𝕜 V W s x + lieBracketWithin 𝕜 V W₁ s x := by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add' hs hW hW₁, ContinuousLinearMap.add_apply]
  abel

lemma lieBracket_add_right (hW : DifferentiableAt 𝕜 W x) (hW₁ : DifferentiableAt 𝕜 W₁ x) :
    lieBracket 𝕜 V (W + W₁) x =
      lieBracket 𝕜 V W x + lieBracket 𝕜 V W₁ x := by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add' hW hW₁, ContinuousLinearMap.add_apply]
  abel

lemma lieBracketWithin_swap : lieBracketWithin 𝕜 V W s = - lieBracketWithin 𝕜 W V s := by
  ext x; simp [lieBracketWithin]

lemma lieBracket_swap : lieBracket 𝕜 V W x = - lieBracket 𝕜 W V x := by
  simp [lieBracket]

lemma _root_.ContDiffWithinAt.lieBracketWithin {m n : ℕ∞} (hV : ContDiffWithinAt 𝕜 n V s x)
    (hW : ContDiffWithinAt 𝕜 n W s x) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 m (lieBracketWithin 𝕜 V W s) s x := by
  apply ContDiffWithinAt.sub
  · exact ContDiffWithinAt.clm_apply (hW.fderivWithin_right hs hmn hx)
      (hV.of_le (le_trans le_self_add hmn))
  · exact ContDiffWithinAt.clm_apply (hV.fderivWithin_right hs hmn hx)
      (hW.of_le (le_trans le_self_add hmn))

lemma _root_.ContDiffAt.lieBracket {m n : ℕ∞} (hV : ContDiffAt 𝕜 n V x)
    (hW : ContDiffAt 𝕜 n W x) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (lieBracket 𝕜 V W) x := by
  rw [← contDiffWithinAt_univ] at hV hW ⊢
  simp_rw [← lieBracketWithin_univ]
  exact hV.lieBracketWithin hW uniqueDiffOn_univ hmn (mem_univ _)

lemma _root_.ContDiffOn.lieBracketWithin {m n : ℕ∞} (hV : ContDiffOn 𝕜 n V s)
    (hW : ContDiffOn 𝕜 n W s) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (lieBracketWithin 𝕜 V W s) s :=
  fun x hx ↦ (hV x hx).lieBracketWithin (hW x hx) hs hmn hx

lemma _root_.ContDiff.lieBracket {m n : ℕ∞} (hV : ContDiff 𝕜 n V)
    (hW : ContDiff 𝕜 n W) (hmn : m + 1 ≤ n) :
    ContDiff 𝕜 m (lieBracket 𝕜 V W) :=
  contDiff_iff_contDiffAt.2 (fun _ ↦ hV.contDiffAt.lieBracket hW.contDiffAt hmn)

theorem lieBracketWithin_of_mem (st : t ∈ 𝓝[s] x) (hs : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableWithinAt 𝕜 V t x) (hW : DifferentiableWithinAt 𝕜 W t x) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x := by
  simp [lieBracketWithin, fderivWithin_of_mem st hs hV, fderivWithin_of_mem st hs hW]

theorem lieBracketWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableWithinAt 𝕜 V t x) (hW : DifferentiableWithinAt 𝕜 W t x) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x :=
  lieBracketWithin_of_mem (nhdsWithin_mono _ st self_mem_nhdsWithin) ht hV hW

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
in  the complement of a point. -/
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

theorem _root_.Filter.EventuallyEq.lieBracketWithin_eq
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hxV : V₁ x = V x) (hW : W₁ =ᶠ[𝓝[s] x] W) (hxW : W₁ x = W x) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x := by
  simp only [lieBracketWithin, hV.fderivWithin_eq hxV, hW.fderivWithin_eq hxW, hxV, hxW]

/-- If vector fields coincide on a neighborhood of a point within a set, then the Lie brackets
also coincide on a neighborhood of this point within this set. Version where one considers the Lie
bracket within a subset. -/
theorem _root_.Filter.EventuallyEq.lieBracketWithin'
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (ht : t ⊆ s) :
    lieBracketWithin 𝕜 V₁ W₁ t =ᶠ[𝓝[s] x] lieBracketWithin 𝕜 V W t := by
  filter_upwards [hV.fderivWithin' ht (𝕜 := 𝕜), hW.fderivWithin' ht (𝕜 := 𝕜), hV, hW]
    with x hV' hW' hV hW
  simp [lieBracketWithin, hV', hW', hV, hW]

protected theorem _root_.Filter.EventuallyEq.lieBracketWithin
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s =ᶠ[𝓝[s] x] lieBracketWithin 𝕜 V W s :=
  hV.lieBracketWithin' hW Subset.rfl

theorem _root_.Filter.EventuallyEq.lieBracketWithin_eq_nhds
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  (hV.filter_mono nhdsWithin_le_nhds).lieBracketWithin_eq hV.self_of_nhds
    (hW.filter_mono nhdsWithin_le_nhds) hW.self_of_nhds

theorem lieBracketWithin_congr
    (hV : EqOn V₁ V s) (hVx : V₁ x = V x) (hW : EqOn W₁ W s) (hWx : W₁ x = W x) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  (hV.eventuallyEq.filter_mono inf_le_right).lieBracketWithin_eq hVx
    (hW.eventuallyEq.filter_mono inf_le_right) hWx

/-- Version of `lieBracketWithin_congr` in which one assumes that the point belongs to the
given set. -/
theorem lieBracketWithin_congr' (hV : EqOn V₁ V s) (hW : EqOn W₁ W s) (hx : x ∈ s) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  lieBracketWithin_congr hV (hV hx) hW (hW hx)

theorem _root_.Filter.EventuallyEq.lieBracket_eq (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    lieBracket 𝕜 V₁ W₁ x = lieBracket 𝕜 V W x := by
  rw [← lieBracketWithin_univ, ← lieBracketWithin_univ, hV.lieBracketWithin_eq_nhds hW]

protected theorem _root_.Filter.EventuallyEq.lieBracket
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) : lieBracket 𝕜 V₁ W₁ =ᶠ[𝓝 x] lieBracket 𝕜 V W := by
  filter_upwards [hV.eventuallyEq_nhds, hW.eventuallyEq_nhds] with y hVy hWy
  exact hVy.lieBracket_eq hWy

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

variable (𝕜) in
/-- The pullback of a vector field under a function, defined
as `(f^* V) (x) = Df(x)^{-1} (V (f x))`. If `Df(x)` is not invertible, we use the junk value `0`.
-/
def pullbackWithin (f : E → F) (V : F → F) (s : Set E) (x : E) : E :=
  (fderivWithin 𝕜 f s x).inverse (V (f x))

lemma pullbackWithin_eq {f : E → F} {V : F → F} {s : Set E} :
    pullbackWithin 𝕜 f V s = fun x ↦ (fderivWithin 𝕜 f s x).inverse (V (f x)) := rfl

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

/- TODO: move me -/

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
    simp [A', fderivWithin_const_apply, hs x hx]
  have I : (N x : E →L[𝕜] F) ∘L (fderivWithin 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x v) =
      - (fderivWithin 𝕜 (fun y ↦ (N y : E →L[𝕜] F)) s x v) ∘L ((N x).symm : F →L[𝕜] E) := by
    rw [ContinuousLinearMap.fderivWithin_of_bilinear _ (hN.differentiableWithinAt le_rfl)
      (hN'.differentiableWithinAt le_rfl) (hs x hx)] at this
    simpa [eq_neg_iff_add_eq_zero] using this
  have B (M : F →L[𝕜] E) : M = ((N x).symm : F →L[𝕜] E) ∘L ((N x) ∘L M) := by
    ext; simp
  rw [B (fderivWithin 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x v), I]
  simp only [ContinuousLinearMap.comp_neg, neg_inj, eN.fderivWithin_eq e'N]

/-- If a `C^2` map has an invertible derivative at a point, then nearby derivatives can be written
as continuous linear equivs, which depend in a `C^1` way on the point, as well as their inverse, and
moreover one can compute the derivative of the inverse. -/
lemma _root_.exists_continuousLinearEquiv_fderiv_symm_eq
    (f : E → F) (x : E) (h'f : ContDiffAt 𝕜 2 f x) (hf : (fderiv 𝕜 f x).IsInvertible) :
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

end VectorField

end LieBracketVectorField

section LieBracketManifold

open Set Function
open scoped Manifold

/- We work in the `VectorField` namespace because pullbacks, Lie brackets, and so on, are notions
that make sense in a variety of contexts. We also prefix the notions with `m` to distinguish the
manifold notions from the vector spaces notions. For instance, the Lie bracket of two vector
fields in a manifold is denoted with `mlieBracket I V W x`, where `I` is the relevant model with
corners, `V W : Π (x : M), TangentSpace I x` are the vector fields, and `x : M` is the basepoint.
-/
namespace VectorField


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

variable {f : M → M'} {s t : Set M} {x x₀ : M}

section

variable {V W V₁ W₁ : Π (x : M'), TangentSpace I' x}
variable {m n : ℕ∞} {t : Set M'} {y₀ : M'}

variable (I I') in
/-- The pullback of a vector field under a map between manifolds, within a set `s`. -/
def mpullbackWithin (f : M → M') (V : Π (x : M'), TangentSpace I' x) (s : Set M) (x : M) :
    TangentSpace I x :=
  (mfderivWithin I I' f s x).inverse (V (f x))

variable (I I') in
/-- The pullback of a vector field under a map between manifolds. -/
def mpullback (f : M → M') (V : Π (x : M'), TangentSpace I' x) (x : M) :
    TangentSpace I x :=
  (mfderiv I I' f x).inverse (V (f x))

lemma mpullbackWithin_apply :
    mpullbackWithin I I' f V s x = (mfderivWithin I I' f s x).inverse (V (f x)) := rfl

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

lemma mpullback_apply :
    mpullback I I' f V x = (mfderiv I I' f x).inverse (V (f x)) := rfl

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

open ContinuousLinearMap

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
protected lemma ContMDiffWithinAt.mpullbackWithin [CompleteSpace E]
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f ⁻¹' t) x₀ := by
  /- We want to apply the general theorem `ContMDiffWithinAt.clm_apply_of_inCoordinates`, stating
  that applying linear maps to vector fields gives a smooth result when the linear map and the
  vector field are smooth. This theorem is general, we will apply it to
  `b₁ = f`, `b₂ = id`, `v = V ∘ f`, `ϕ = fun x ↦ (mfderivWithin I I' f s x).inverse`-/
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

lemma ContMDiffWithinAt.mpullbackWithin_of_eq [CompleteSpace E]
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) (h : y₀ = f x₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f⁻¹' t) x₀ := by
  subst h
  exact ContMDiffWithinAt.mpullbackWithin hV hf hf' hx₀ hs hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version on a set. -/
protected lemma ContMDiffOn.mpullbackWithin [CompleteSpace E]
    (hV : ContMDiffOn I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t)
    (hf : ContMDiffOn I I' n f s) (hf' : ∀ x ∈ s ∩ f ⁻¹' t, (mfderivWithin I I' f s x).IsInvertible)
    (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) :
    ContMDiffOn I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f ⁻¹' t) :=
  fun _ hx₀ ↦ ContMDiffWithinAt.mpullbackWithin
    (hV _ hx₀.2) (hf _ hx₀.1) (hf' _ hx₀) hx₀.1 hs hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
protected lemma ContMDiffWithinAt.mpullback [CompleteSpace E]
    (hV : ContMDiffWithinAt I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : m + 1 ≤ n) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) (f ⁻¹' t) x₀ := by
  simp only [← contMDiffWithinAt_univ, ← mfderivWithin_univ, ← mpullbackWithin_univ] at hV hf hf' ⊢
  simpa using ContMDiffWithinAt.mpullbackWithin hV hf hf' (mem_univ _) uniqueMDiffOn_univ hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
protected lemma ContMDiffWithinAt.mpullback_of_eq [CompleteSpace E]
    (hV : ContMDiffWithinAt I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : m + 1 ≤ n)
    (hy₀ : y₀ = f x₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) (f ⁻¹' t) x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullback hV hf hf' hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version on a set, but with full pullback -/
protected lemma ContMDiffOn.mpullback [CompleteSpace E]
    (hV : ContMDiffOn I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t)
    (hf : ContMDiff I I' n f) (hf' : ∀ x ∈ f ⁻¹' t, (mfderiv I I' f x).IsInvertible)
    (hmn : m + 1 ≤ n) :
    ContMDiffOn I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) (f ⁻¹' t) :=
  fun x₀ hx₀ ↦ ContMDiffWithinAt.mpullback (hV _ hx₀) (hf x₀) (hf' _ hx₀) hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version at a point. -/
protected lemma ContMDiffAt.mpullback [CompleteSpace E]
    (hV : ContMDiffAt I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) (f x₀))
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : m + 1 ≤ n) :
    ContMDiffAt I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) x₀ := by
  simp only [← contMDiffWithinAt_univ] at hV hf hf' ⊢
  simpa using ContMDiffWithinAt.mpullback hV hf hf' hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`. -/
protected lemma ContMDiff.mpullback [CompleteSpace E]
    (hV : ContMDiff I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')))
    (hf : ContMDiff I I' n f) (hf' : ∀ x, (mfderiv I I' f x).IsInvertible) (hmn : m + 1 ≤ n) :
    ContMDiff I I.tangent m (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) :=
  fun x ↦ ContMDiffAt.mpullback (hV (f x)) (hf x) (hf' x) hmn

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

end

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

open FiberBundle

variable (H I) in
/-- In the tangent bundle to the model space, the second projection is smooth. -/
lemma contMDiff_snd_tangentBundle_modelSpace {n : ℕ∞} :
    ContMDiff I.tangent 𝓘(𝕜, E) n (fun (p : TangentBundle I H) ↦ p.2) := by
  change ContMDiff I.tangent 𝓘(𝕜, E) n
    ((id Prod.snd : ModelProd H E → E) ∘ (tangentBundleModelSpaceHomeomorph H I))
  apply ContMDiff.comp (I' := I.prod 𝓘(𝕜, E))
  · convert contMDiff_snd
    rw [chartedSpaceSelf_prod]
    rfl
  · exact contMDiff_tangentBundleModelSpaceHomeomorph H I

lemma mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
    {y : E} (hy : y ∈ (extChartAt I x).target) :
    (mfderiv I 𝓘(𝕜, E) (extChartAt I x) ((extChartAt I x).symm y)) ∘L
      (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) y) = ContinuousLinearMap.id _ _ := by
  have U : UniqueMDiffWithinAt 𝓘(𝕜, E) (range ↑I) y := by
    apply I.uniqueMDiffOn
    exact extChartAt_target_subset_range I x hy
  have h'y : (extChartAt I x).symm y ∈ (extChartAt I x).source := (extChartAt I x).map_target hy
  have h''y : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rwa [← extChartAt_source (I := I)]
  rw [← mfderiv_comp_mfderivWithin]; rotate_left
  · apply mdifferentiableAt_extChartAt _ h''y
  · exact mdifferentiableWithinAt_extChartAt_symm _ hy
  · exact U
  rw [← mfderivWithin_id _ U]
  apply Filter.EventuallyEq.mfderivWithin_eq U
  · filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem _ hy] with z hz
    simp only [comp_def, PartialEquiv.right_inv (extChartAt I x) hz, id_eq]
  · simp only [comp_def, PartialEquiv.right_inv (extChartAt I x) hy, id_eq]

lemma mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
    {y : E} (hy : y ∈ (extChartAt I x).target) :
    (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) y) ∘L
      (mfderiv I 𝓘(𝕜, E) (extChartAt I x) ((extChartAt I x).symm y))
      = ContinuousLinearMap.id _ _ := by
  have h'y : (extChartAt I x).symm y ∈ (extChartAt I x).source := (extChartAt I x).map_target hy
  have h''y : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    rwa [← extChartAt_source (I := I)]
  have U' : UniqueMDiffWithinAt I (extChartAt I x).source ((extChartAt I x).symm y) :=
    (isOpen_extChartAt_source I x).uniqueMDiffWithinAt h'y
  have : mfderiv I 𝓘(𝕜, E) (extChartAt I x) ((extChartAt I x).symm y)
      = mfderivWithin I 𝓘(𝕜, E) (extChartAt I x) (extChartAt I x).source
      ((extChartAt I x).symm y) := by
    rw [mfderivWithin_eq_mfderiv U']
    exact mdifferentiableAt_extChartAt _ h''y
  rw [this, ← mfderivWithin_comp_of_eq]; rotate_left
  · exact mdifferentiableWithinAt_extChartAt_symm _ hy
  · exact (mdifferentiableAt_extChartAt _ h''y).mdifferentiableWithinAt
  · intro z hz
    apply extChartAt_target_subset_range I x
    exact PartialEquiv.map_source (extChartAt I x) hz
  · exact U'
  · exact PartialEquiv.right_inv (extChartAt I x) hy
  rw [← mfderivWithin_id _ U']
  apply Filter.EventuallyEq.mfderivWithin_eq U'
  · filter_upwards [extChartAt_source_mem_nhdsWithin' _ h'y] with z hz
    simp only [comp_def, PartialEquiv.left_inv (extChartAt I x) hz, id_eq]
  · simp only [comp_def, PartialEquiv.right_inv (extChartAt I x) hy, id_eq]

lemma isInvertible_mfderivWithin_extChartAt_symm {y : E} (hy : y ∈ (extChartAt I x).target) :
    (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) y).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hy)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hy)

lemma isInvertible_mfderiv_extChartAt {y : M} (hy : y ∈ (extChartAt I x).source) :
    (mfderiv I 𝓘(𝕜, E) (extChartAt I x) y).IsInvertible := by
  have h'y : extChartAt I x y ∈ (extChartAt I x).target := (extChartAt I x).map_source hy
  have Z := ContinuousLinearMap.IsInvertible.of_inverse
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm h'y)
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt h'y)
  have : (extChartAt I x).symm ((extChartAt I x) y) = y := (extChartAt I x).left_inv hy
  rwa [this] at Z

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

#check UniqueMDiffWithinAt

lemma mlieBracketWithin_add_left [CompleteSpace E]
    (hV : ContMDiffWithinAt I I.tangent 1 (fun x ↦ (V x : TangentBundle I M)) s x)
    (hV₁ : ContMDiffWithinAt I I.tangent 1 (fun x ↦ (V₁ x : TangentBundle I M)) s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mlieBracketWithin I (V + V₁) W s x =
      mlieBracketWithin I V W s x + mlieBracketWithin I V₁ W s x := by
  simp only [mlieBracketWithin, Pi.add_apply, map_add, mpullback_apply]
  rw [← ContinuousLinearMap.map_add, mpullbackWithin_add]
  congr 1
  rw [lieBracketWithin_add_left]
  · apply MDifferentiableWithinAt.differentiableWithinAt
    apply ContMDiffWithinAt.mdifferentiableWithinAt _ le_rfl
    have Z := ContMDiffWithinAt.mpullbackWithin_of_eq hV
      (contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target I x))
      (isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target I x)) (mem_range_self _)
      I.uniqueMDiffOn le_rfl (extChartAt_to_inv I x).symm
    rw [inter_comm]
    exact (contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).contMDiffAt.comp_contMDiffWithinAt _ Z
  · apply MDifferentiableWithinAt.differentiableWithinAt
    apply ContMDiffWithinAt.mdifferentiableWithinAt _ le_rfl
    have Z := ContMDiffWithinAt.mpullbackWithin_of_eq hV₁
      (contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target I x))
      (isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target I x)) (mem_range_self _)
      I.uniqueMDiffOn le_rfl (extChartAt_to_inv I x).symm
    rw [inter_comm]
    exact (contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).contMDiffAt.comp_contMDiffWithinAt _ Z
  · exact uniqueMDiffWithinAt_iff_inter_range.1 hs

lemma mlieBracket_add_left [CompleteSpace E]
    (hV : ContMDiffAt I I.tangent 1 (fun x ↦ (V x : TangentBundle I M)) x)
    (hV₁ : ContMDiffAt I I.tangent 1 (fun x ↦ (V₁ x : TangentBundle I M)) x) :
    mlieBracket I (V + V₁) W  x =
      mlieBracket I V W x + mlieBracket I V₁ W x := by
  simp only [← mlieBracketWithin_univ, ← contMDiffWithinAt_univ] at hV hV₁ ⊢
  exact mlieBracketWithin_add_left hV hV₁ (uniqueMDiffWithinAt_univ _)

lemma mlieBracketWithin_add_right [CompleteSpace E]
    (hW : ContMDiffWithinAt I I.tangent 1 (fun x ↦ (W x : TangentBundle I M)) s x)
    (hW₁ : ContMDiffWithinAt I I.tangent 1 (fun x ↦ (W₁ x : TangentBundle I M)) s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mlieBracketWithin I V (W + W₁) s x =
      mlieBracketWithin I V W s x + mlieBracketWithin I V W₁ s x := by
  rw [mlieBracketWithin_swap, Pi.neg_apply, mlieBracketWithin_add_left hW hW₁ hs,
    mlieBracketWithin_swap (V := V), mlieBracketWithin_swap (V := V), Pi.neg_apply, Pi.neg_apply]
  abel

lemma mlieBracket_add_right [CompleteSpace E]
    (hW : ContMDiffAt I I.tangent 1 (fun x ↦ (W x : TangentBundle I M)) x)
    (hW₁ : ContMDiffAt I I.tangent 1 (fun x ↦ (W₁ x : TangentBundle I M)) x) :
    mlieBracket I V (W + W₁) x =
      mlieBracket I V W x + mlieBracket I V W₁ x := by
  simp only [← mlieBracketWithin_univ, ← contMDiffWithinAt_univ] at hW hW₁ ⊢
  exact mlieBracketWithin_add_right hW hW₁ (uniqueMDiffWithinAt_univ _)

/-
lemma _root_.ContDiffWithinAt.mlieBracketWithin {m n : ℕ∞} (hV : ContDiffWithinAt 𝕜 n V s x)
    (hW : ContDiffWithinAt 𝕜 n W s x) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 m (mlieBracketWithin I V W s) s x := by
  apply ContDiffWithinAt.sub
  · exact ContDiffWithinAt.clm_apply (hW.fderivWithin_right hs hmn hx)
      (hV.of_le (le_trans le_self_add hmn))
  · exact ContDiffWithinAt.clm_apply (hV.fderivWithin_right hs hmn hx)
      (hW.of_le (le_trans le_self_add hmn))

lemma _root_.ContDiffAt.mlieBracket {m n : ℕ∞} (hV : ContDiffAt 𝕜 n V x)
    (hW : ContDiffAt 𝕜 n W x) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (mlieBracket I V W) x := by
  rw [← contDiffWithinAt_univ] at hV hW ⊢
  simp_rw [← mlieBracketWithin_univ]
  exact hV.mlieBracketWithin hW uniqueDiffOn_univ hmn (mem_univ _)

lemma _root_.ContDiffOn.mlieBracketWithin {m n : ℕ∞} (hV : ContDiffOn 𝕜 n V s)
    (hW : ContDiffOn 𝕜 n W s) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (mlieBracketWithin I V W s) s :=
  fun x hx ↦ (hV x hx).mlieBracketWithin (hW x hx) hs hmn hx

lemma _root_.ContDiff.mlieBracket {m n : ℕ∞} (hV : ContDiff 𝕜 n V)
    (hW : ContDiff 𝕜 n W) (hmn : m + 1 ≤ n) :
    ContDiff 𝕜 m (mlieBracket I V W) :=
  contDiff_iff_contDiffAt.2 (fun _ ↦ hV.contDiffAt.mlieBracket hW.contDiffAt hmn)
-/

theorem mlieBracketWithin_of_mem [CompleteSpace E]
    (st : t ∈ 𝓝[s] x) (hs : UniqueMDiffWithinAt I s x)
    (hV : ContMDiffWithinAt I I.tangent 1 (fun x ↦ (V x : TangentBundle I M)) t x)
    (hW : ContMDiffWithinAt I I.tangent 1 (fun x ↦ (W x : TangentBundle I M)) t x) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x := by
  simp only [mlieBracketWithin, fderivWithin_of_mem, mpullback_apply]
  congr 1
  rw [lieBracketWithin_of_mem]
  ·
  · exact uniqueMDiffWithinAt_iff_inter_range.1 hs
  · apply MDifferentiableWithinAt.differentiableWithinAt
    apply ContMDiffWithinAt.mdifferentiableWithinAt _ le_rfl
    have Z := ContMDiffWithinAt.mpullbackWithin_of_eq hV
      (contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target I x))
      (isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target I x)) (mem_range_self _)
      I.uniqueMDiffOn le_rfl (extChartAt_to_inv I x).symm
    rw [inter_comm]
    exact (contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).contMDiffAt.comp_contMDiffWithinAt _ Z
  · apply MDifferentiableWithinAt.differentiableWithinAt
    apply ContMDiffWithinAt.mdifferentiableWithinAt _ le_rfl
    have Z := ContMDiffWithinAt.mpullbackWithin_of_eq hW
      (contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target I x))
      (isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target I x)) (mem_range_self _)
      I.uniqueMDiffOn le_rfl (extChartAt_to_inv I x).symm
    rw [inter_comm]
    exact (contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).contMDiffAt.comp_contMDiffWithinAt _ Z




#exit

theorem mlieBracketWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableWithinAt 𝕜 V t x) (hW : DifferentiableWithinAt 𝕜 W t x) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x :=
  mlieBracketWithin_of_mem (nhdsWithin_mono _ st self_mem_nhdsWithin) ht hV hW

theorem mlieBracketWithin_inter (ht : t ∈ 𝓝 x) :
    mlieBracketWithin I V W (s ∩ t) x = mlieBracketWithin I V W s x := by
  simp [mlieBracketWithin, fderivWithin_inter, ht]

theorem mlieBracketWithin_of_mem_nhds (h : s ∈ 𝓝 x) :
    mlieBracketWithin I V W s x = mlieBracket I V W x := by
  rw [← mlieBracketWithin_univ, ← univ_inter s, mlieBracketWithin_inter h]

theorem mlieBracketWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) :
    mlieBracketWithin I V W s x = mlieBracket I V W x :=
  mlieBracketWithin_of_mem_nhds (hs.mem_nhds hx)

theorem mlieBracketWithin_eq_mlieBracket (hs : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableAt 𝕜 V x) (hW : DifferentiableAt 𝕜 W x) :
    mlieBracketWithin I V W s x = mlieBracket I V W x := by
  simp [mlieBracketWithin, mlieBracket, fderivWithin_eq_fderiv, hs, hV, hW]

/-- Variant of `mlieBracketWithin_congr_set` where one requires the sets to coincide only in
the complement of a point. -/
theorem mlieBracketWithin_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x := by
  simp [mlieBracketWithin, fderivWithin_congr_set' _ h]

theorem mlieBracketWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x :=
  mlieBracketWithin_congr_set' x <| h.filter_mono inf_le_left

/-- Variant of `mlieBracketWithin_eventually_congr_set` where one requires the sets to coincide only
in  the complement of a point. -/
theorem mlieBracketWithin_eventually_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mlieBracketWithin I V W s =ᶠ[𝓝 x] mlieBracketWithin I V W t :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => mlieBracketWithin_congr_set' y

theorem mlieBracketWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    mlieBracketWithin I V W s =ᶠ[𝓝 x] mlieBracketWithin I V W t :=
  mlieBracketWithin_eventually_congr_set' x <| h.filter_mono inf_le_left

theorem _root_.DifferentiableWithinAt.mlieBracketWithin_congr_mono
    (hV : DifferentiableWithinAt 𝕜 V s x) (hVs : EqOn V₁ V t) (hVx : V₁ x = V x)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hWs : EqOn W₁ W t) (hWx : W₁ x = W x)
    (hxt : UniqueDiffWithinAt 𝕜 t x) (h₁ : t ⊆ s) :
    mlieBracketWithin I V₁ W₁ t x = mlieBracketWithin I V W s x := by
  simp [mlieBracketWithin, hV.fderivWithin_congr_mono, hW.fderivWithin_congr_mono, hVs, hVx,
    hWs, hWx, hxt, h₁]

theorem _root_.Filter.EventuallyEq.mlieBracketWithin_eq
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hxV : V₁ x = V x) (hW : W₁ =ᶠ[𝓝[s] x] W) (hxW : W₁ x = W x) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x := by
  simp only [mlieBracketWithin, hV.fderivWithin_eq hxV, hW.fderivWithin_eq hxW, hxV, hxW]

/-- If vector fields coincide on a neighborhood of a point within a set, then the Lie brackets
also coincide on a neighborhood of this point within this set. Version where one considers the Lie
bracket within a subset. -/
theorem _root_.Filter.EventuallyEq.mlieBracketWithin'
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (ht : t ⊆ s) :
    mlieBracketWithin I V₁ W₁ t =ᶠ[𝓝[s] x] mlieBracketWithin I V W t := by
  filter_upwards [hV.fderivWithin' ht (𝕜 := 𝕜), hW.fderivWithin' ht (𝕜 := 𝕜), hV, hW]
    with x hV' hW' hV hW
  simp [mlieBracketWithin, hV', hW', hV, hW]

protected theorem _root_.Filter.EventuallyEq.mlieBracketWithin
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) :
    mlieBracketWithin I V₁ W₁ s =ᶠ[𝓝[s] x] mlieBracketWithin I V W s :=
  hV.mlieBracketWithin' hW Subset.rfl

theorem _root_.Filter.EventuallyEq.mlieBracketWithin_eq_nhds
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  (hV.filter_mono nhdsWithin_le_nhds).mlieBracketWithin_eq hV.self_of_nhds
    (hW.filter_mono nhdsWithin_le_nhds) hW.self_of_nhds

theorem mlieBracketWithin_congr
    (hV : EqOn V₁ V s) (hVx : V₁ x = V x) (hW : EqOn W₁ W s) (hWx : W₁ x = W x) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  (hV.eventuallyEq.filter_mono inf_le_right).mlieBracketWithin_eq hVx
    (hW.eventuallyEq.filter_mono inf_le_right) hWx

/-- Version of `mlieBracketWithin_congr` in which one assumes that the point belongs to the
given set. -/
theorem mlieBracketWithin_congr' (hV : EqOn V₁ V s) (hW : EqOn W₁ W s) (hx : x ∈ s) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  mlieBracketWithin_congr hV (hV hx) hW (hW hx)

theorem _root_.Filter.EventuallyEq.mlieBracket_eq (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    mlieBracket I V₁ W₁ x = mlieBracket I V W x := by
  rw [← mlieBracketWithin_univ, ← mlieBracketWithin_univ, hV.mlieBracketWithin_eq_nhds hW]

protected theorem _root_.Filter.EventuallyEq.mlieBracket
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) : mlieBracket I V₁ W₁ =ᶠ[𝓝 x] mlieBracket I V W := by
  filter_upwards [hV.eventuallyEq_nhds, hW.eventuallyEq_nhds] with y hVy hWy
  exact hVy.mlieBracket_eq hWy
#exit

/-******************************************************************************-/


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

end VectorField

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
