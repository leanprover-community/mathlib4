/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

#align_import analysis.calculus.inverse from "leanprover-community/mathlib"@"2c1d8ca2812b64f88992a5294ea3dba144755cd1"

/-!
# Inverse function theorem

In this file we prove the inverse function theorem. It says that if a map `f : E → F`
has an invertible strict derivative `f'` at `a`, then it is locally invertible,
and the inverse function has derivative `f' ⁻¹`.

We define `HasStrictFDerivAt.toLocalHomeomorph` that repacks a function `f`
with a `hf : HasStrictFDerivAt f f' a`, `f' : E ≃L[𝕜] F`, into a `LocalHomeomorph`.
The `toFun` of this `LocalHomeomorph` is defeq to `f`, so one can apply theorems
about `LocalHomeomorph` to `hf.toLocalHomeomorph f`, and get statements about `f`.

Then we define `HasStrictFDerivAt.localInverse` to be the `invFun` of this `LocalHomeomorph`,
and prove two versions of the inverse function theorem:

* `HasStrictFDerivAt.to_localInverse`: if `f` has an invertible derivative `f'` at `a` in the
  strict sense (`hf`), then `hf.localInverse f f' a` has derivative `f'.symm` at `f a` in the
  strict sense;

* `HasStrictFDerivAt.to_local_left_inverse`: if `f` has an invertible derivative `f'` at `a` in
  the strict sense and `g` is locally left inverse to `f` near `a`, then `g` has derivative
  `f'.symm` at `f a` in the strict sense.

Some related theorems, providing the derivative and higher regularity assuming that we already know
the inverse function, are formulated in the `Analysis/Calculus/FDeriv` and `Analysis/Calculus/Deriv`
folders, and in `ContDiff.lean`.

## Tags

derivative, strictly differentiable, continuously differentiable, smooth, inverse function
-/

open Function Set Filter Metric

open scoped Topology Classical NNReal

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

variable {ε : ℝ}

open Asymptotics Filter Metric Set

open ContinuousLinearMap (id)


/-!
### Inverse function theorem

Let `f : E → F` be a map defined on a complete vector
space `E`. Assume that `f` has an invertible derivative `f' : E ≃L[𝕜] F` at `a : E` in the strict
sense. Then `f` approximates `f'` in the sense of `ApproximatesLinearOn` on an open neighborhood
of `a`, and we can apply `ApproximatesLinearOn.toLocalHomeomorph` to construct the inverse
function. -/

namespace HasStrictFDerivAt

/-- If `f` has derivative `f'` at `a` in the strict sense and `c > 0`, then `f` approximates `f'`
with constant `c` on some neighborhood of `a`. -/
theorem approximates_deriv_on_nhds {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) {c : ℝ≥0} (hc : Subsingleton E ∨ 0 < c) :
    ∃ s ∈ 𝓝 a, ApproximatesLinearOn f f' s c := by
  cases' hc with hE hc
  · refine' ⟨univ, IsOpen.mem_nhds isOpen_univ trivial, fun x _ y _ => _⟩
    simp [@Subsingleton.elim E hE x y]
  have := hf.def hc
  rw [nhds_prod_eq, Filter.Eventually, mem_prod_same_iff] at this
  rcases this with ⟨s, has, hs⟩
  exact ⟨s, has, fun x hx y hy => hs (mk_mem_prod hx hy)⟩
#align has_strict_fderiv_at.approximates_deriv_on_nhds HasStrictFDerivAt.approximates_deriv_on_nhds

theorem map_nhds_eq_of_surj [CompleteSpace E] [CompleteSpace F] {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) (h : LinearMap.range f' = ⊤) :
    map f (𝓝 a) = 𝓝 (f a) := by
  let f'symm := f'.nonlinearRightInverseOfSurjective h
  set c : ℝ≥0 := f'symm.nnnorm⁻¹ / 2 with hc
  have f'symm_pos : 0 < f'symm.nnnorm := f'.nonlinearRightInverseOfSurjective_nnnorm_pos h
  have cpos : 0 < c := by simp [hc, half_pos, inv_pos, f'symm_pos]
  obtain ⟨s, s_nhds, hs⟩ : ∃ s ∈ 𝓝 a, ApproximatesLinearOn f f' s c :=
    hf.approximates_deriv_on_nhds (Or.inr cpos)
  apply hs.map_nhds_eq f'symm s_nhds (Or.inr (NNReal.half_lt_self _))
  simp [ne_of_gt f'symm_pos]
#align has_strict_fderiv_at.map_nhds_eq_of_surj HasStrictFDerivAt.map_nhds_eq_of_surj

variable [CompleteSpace E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}

theorem approximates_deriv_on_open_nhds (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∃ s : Set E, a ∈ s ∧ IsOpen s ∧
      ApproximatesLinearOn f (f' : E →L[𝕜] F) s (‖(f'.symm : F →L[𝕜] E)‖₊⁻¹ / 2) := by
  simp only [← and_assoc]
  refine ((nhds_basis_opens a).exists_iff fun s t => ApproximatesLinearOn.mono_set).1 ?_
  exact
    hf.approximates_deriv_on_nhds <|
      f'.subsingleton_or_nnnorm_symm_pos.imp id fun hf' => half_pos <| inv_pos.2 hf'
#align has_strict_fderiv_at.approximates_deriv_on_open_nhds HasStrictFDerivAt.approximates_deriv_on_open_nhds

variable (f)

/-- Given a function with an invertible strict derivative at `a`, returns a `LocalHomeomorph`
with `to_fun = f` and `a ∈ source`. This is a part of the inverse function theorem.
The other part `HasStrictFDerivAt.to_localInverse` states that the inverse function
of this `LocalHomeomorph` has derivative `f'.symm`. -/
def toLocalHomeomorph (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) : LocalHomeomorph E F :=
  ApproximatesLinearOn.toLocalHomeomorph f (Classical.choose hf.approximates_deriv_on_open_nhds)
    (Classical.choose_spec hf.approximates_deriv_on_open_nhds).2.2
    (f'.subsingleton_or_nnnorm_symm_pos.imp id fun hf' =>
      NNReal.half_lt_self <| ne_of_gt <| inv_pos.2 hf')
    (Classical.choose_spec hf.approximates_deriv_on_open_nhds).2.1
#align has_strict_fderiv_at.to_local_homeomorph HasStrictFDerivAt.toLocalHomeomorph

variable {f}

@[simp]
theorem toLocalHomeomorph_coe (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    (hf.toLocalHomeomorph f : E → F) = f :=
  rfl
#align has_strict_fderiv_at.to_local_homeomorph_coe HasStrictFDerivAt.toLocalHomeomorph_coe

theorem mem_toLocalHomeomorph_source (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    a ∈ (hf.toLocalHomeomorph f).source :=
  (Classical.choose_spec hf.approximates_deriv_on_open_nhds).1
#align has_strict_fderiv_at.mem_to_local_homeomorph_source HasStrictFDerivAt.mem_toLocalHomeomorph_source

theorem image_mem_toLocalHomeomorph_target (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    f a ∈ (hf.toLocalHomeomorph f).target :=
  (hf.toLocalHomeomorph f).map_source hf.mem_toLocalHomeomorph_source
#align has_strict_fderiv_at.image_mem_to_local_homeomorph_target HasStrictFDerivAt.image_mem_toLocalHomeomorph_target

theorem map_nhds_eq_of_equiv (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    map f (𝓝 a) = 𝓝 (f a) :=
  (hf.toLocalHomeomorph f).map_nhds_eq hf.mem_toLocalHomeomorph_source
#align has_strict_fderiv_at.map_nhds_eq_of_equiv HasStrictFDerivAt.map_nhds_eq_of_equiv

variable (f f' a)

/-- Given a function `f` with an invertible derivative, returns a function that is locally inverse
to `f`. -/
def localInverse (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) : F → E :=
  (hf.toLocalHomeomorph f).symm
#align has_strict_fderiv_at.local_inverse HasStrictFDerivAt.localInverse

variable {f f' a}

theorem localInverse_def (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    hf.localInverse f _ _ = (hf.toLocalHomeomorph f).symm :=
  rfl
#align has_strict_fderiv_at.local_inverse_def HasStrictFDerivAt.localInverse_def

theorem eventually_left_inverse (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 a, hf.localInverse f f' a (f x) = x :=
  (hf.toLocalHomeomorph f).eventually_left_inverse hf.mem_toLocalHomeomorph_source
#align has_strict_fderiv_at.eventually_left_inverse HasStrictFDerivAt.eventually_left_inverse

@[simp]
theorem localInverse_apply_image (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    hf.localInverse f f' a (f a) = a :=
  hf.eventually_left_inverse.self_of_nhds
#align has_strict_fderiv_at.local_inverse_apply_image HasStrictFDerivAt.localInverse_apply_image

theorem eventually_right_inverse (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ y in 𝓝 (f a), f (hf.localInverse f f' a y) = y :=
  (hf.toLocalHomeomorph f).eventually_right_inverse' hf.mem_toLocalHomeomorph_source
#align has_strict_fderiv_at.eventually_right_inverse HasStrictFDerivAt.eventually_right_inverse

theorem localInverse_continuousAt (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ContinuousAt (hf.localInverse f f' a) (f a) :=
  (hf.toLocalHomeomorph f).continuousAt_symm hf.image_mem_toLocalHomeomorph_target
#align has_strict_fderiv_at.local_inverse_continuous_at HasStrictFDerivAt.localInverse_continuousAt

theorem localInverse_tendsto (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    Tendsto (hf.localInverse f f' a) (𝓝 <| f a) (𝓝 a) :=
  (hf.toLocalHomeomorph f).tendsto_symm hf.mem_toLocalHomeomorph_source
#align has_strict_fderiv_at.local_inverse_tendsto HasStrictFDerivAt.localInverse_tendsto

theorem localInverse_unique (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) {g : F → E}
    (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) : ∀ᶠ y in 𝓝 (f a), g y = localInverse f f' a hf y :=
  eventuallyEq_of_left_inv_of_right_inv hg hf.eventually_right_inverse <|
    (hf.toLocalHomeomorph f).tendsto_symm hf.mem_toLocalHomeomorph_source
#align has_strict_fderiv_at.local_inverse_unique HasStrictFDerivAt.localInverse_unique

/-- If `f` has an invertible derivative `f'` at `a` in the sense of strict differentiability `(hf)`,
then the inverse function `hf.localInverse f` has derivative `f'.symm` at `f a`. -/
theorem to_localInverse (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    HasStrictFDerivAt (hf.localInverse f f' a) (f'.symm : F →L[𝕜] E) (f a) :=
  (hf.toLocalHomeomorph f).hasStrictFDerivAt_symm hf.image_mem_toLocalHomeomorph_target <| by
    simpa [← localInverse_def] using hf
#align has_strict_fderiv_at.to_local_inverse HasStrictFDerivAt.to_localInverse

/-- If `f : E → F` has an invertible derivative `f'` at `a` in the sense of strict differentiability
and `g (f x) = x` in a neighborhood of `a`, then `g` has derivative `f'.symm` at `f a`.

For a version assuming `f (g y) = y` and continuity of `g` at `f a` but not `[CompleteSpace E]`
see `of_local_left_inverse`.  -/
theorem to_local_left_inverse (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) {g : F → E}
    (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) : HasStrictFDerivAt g (f'.symm : F →L[𝕜] E) (f a) :=
  hf.to_localInverse.congr_of_eventuallyEq <| (hf.localInverse_unique hg).mono fun _ => Eq.symm
#align has_strict_fderiv_at.to_local_left_inverse HasStrictFDerivAt.to_local_left_inverse

end HasStrictFDerivAt

/-- If a function has an invertible strict derivative at all points, then it is an open map. -/
theorem open_map_of_strict_fderiv_equiv [CompleteSpace E] {f : E → F} {f' : E → E ≃L[𝕜] F}
    (hf : ∀ x, HasStrictFDerivAt f (f' x : E →L[𝕜] F) x) : IsOpenMap f :=
  isOpenMap_iff_nhds_le.2 fun x => (hf x).map_nhds_eq_of_equiv.ge
#align open_map_of_strict_fderiv_equiv open_map_of_strict_fderiv_equiv
