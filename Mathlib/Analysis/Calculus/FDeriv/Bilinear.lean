/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# The derivative of bounded bilinear maps

For detailed documentation of the Fréchet derivative,
see the module docstring of `Analysis/Calculus/Fderiv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
bounded bilinear maps.
-/


open Asymptotics Topology

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

section BilinearMap

/-! ### Derivative of a bounded bilinear map -/

variable {b : E × F → G} {u : Set (E × F)}

open NormedField

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: rewrite/golf using analytic functions?
@[fun_prop]
theorem IsBoundedBilinearMap.hasStrictFDerivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    HasStrictFDerivAt b (h.deriv p) p := by
  simp only [hasStrictFDerivAt_iff_isLittleO]
  simp only [← map_add_left_nhds_zero (p, p), isLittleO_map]
  set T := (E × F) × E × F
  calc
    _ = fun x ↦ h.deriv (x.1 - x.2) (x.2.1, x.1.2) := by
      ext ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
      rcases p with ⟨x, y⟩
      simp only [map_sub, deriv_apply, Function.comp_apply, Prod.mk_add_mk, h.add_right, h.add_left,
        Prod.mk_sub_mk, h.map_sub_left, h.map_sub_right, sub_add_sub_cancel]
      abel
    -- _ =O[𝓝 (0 : T)] fun x ↦ ‖x.1 - x.2‖ * ‖(x.2.1, x.1.2)‖ :=
    --     h.toContinuousLinearMap.deriv₂.isBoundedBilinearMap.isBigO_comp
    -- _ = o[𝓝 0] fun x ↦ ‖x.1 - x.2‖ * 1 := _
    _ =o[𝓝 (0 : T)] fun x ↦ x.1 - x.2 := by
      -- TODO : add 2 `calc` steps instead of the next 3 lines
      refine h.toContinuousLinearMap.deriv₂.isBoundedBilinearMap.isBigO_comp.trans_isLittleO ?_
      suffices (fun x : T ↦ ‖x.1 - x.2‖ * ‖(x.2.1, x.1.2)‖) =o[𝓝 0] fun x ↦ ‖x.1 - x.2‖ * 1 by
        simpa only [mul_one, isLittleO_norm_right] using this
      refine (isBigO_refl _ _).mul_isLittleO ((isLittleO_one_iff _).2 ?_)
      -- TODO: `continuity` fails
      exact (continuous_snd.fst.prod_mk continuous_fst.snd).norm.tendsto' _ _ (by simp +zetaDelta)
    _ = _ := by simp [T, Function.comp_def]

@[fun_prop]
theorem IsBoundedBilinearMap.hasFDerivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    HasFDerivAt b (h.deriv p) p :=
  (h.hasStrictFDerivAt p).hasFDerivAt

@[fun_prop]
theorem IsBoundedBilinearMap.hasFDerivWithinAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    HasFDerivWithinAt b (h.deriv p) u p :=
  (h.hasFDerivAt p).hasFDerivWithinAt

@[fun_prop]
theorem IsBoundedBilinearMap.differentiableAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    DifferentiableAt 𝕜 b p :=
  (h.hasFDerivAt p).differentiableAt

@[fun_prop]
theorem IsBoundedBilinearMap.differentiableWithinAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    DifferentiableWithinAt 𝕜 b u p :=
  (h.differentiableAt p).differentiableWithinAt

protected theorem IsBoundedBilinearMap.fderiv (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    fderiv 𝕜 b p = h.deriv p :=
  HasFDerivAt.fderiv (h.hasFDerivAt p)

protected theorem IsBoundedBilinearMap.fderivWithin (h : IsBoundedBilinearMap 𝕜 b) (p : E × F)
    (hxs : UniqueDiffWithinAt 𝕜 u p) : fderivWithin 𝕜 b u p = h.deriv p := by
  rw [DifferentiableAt.fderivWithin (h.differentiableAt p) hxs]
  exact h.fderiv p

@[fun_prop]
theorem IsBoundedBilinearMap.differentiable (h : IsBoundedBilinearMap 𝕜 b) : Differentiable 𝕜 b :=
  fun x => h.differentiableAt x

@[fun_prop]
theorem IsBoundedBilinearMap.differentiableOn (h : IsBoundedBilinearMap 𝕜 b) :
    DifferentiableOn 𝕜 b u :=
  h.differentiable.differentiableOn

variable (B : E →L[𝕜] F →L[𝕜] G)

#adaptation_note /-- https://github.com/leanprover/lean4/pull/6024
  need `by exact` to deal with tricky unification -/
@[fun_prop]
theorem ContinuousLinearMap.hasFDerivWithinAt_of_bilinear {f : G' → E} {g : G' → F}
    {f' : G' →L[𝕜] E} {g' : G' →L[𝕜] F} {x : G'} {s : Set G'} (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt g g' s x) :
    HasFDerivWithinAt (fun y => B (f y) (g y))
      (B.precompR G' (f x) g' + B.precompL G' f' (g x)) s x := by
  exact (B.isBoundedBilinearMap.hasFDerivAt (f x, g x)).comp_hasFDerivWithinAt x (hf.prod hg)

#adaptation_note /-- https://github.com/leanprover/lean4/pull/6024
  need `by exact` to deal with tricky unification -/
@[fun_prop]
theorem ContinuousLinearMap.hasFDerivAt_of_bilinear {f : G' → E} {g : G' → F} {f' : G' →L[𝕜] E}
    {g' : G' →L[𝕜] F} {x : G'} (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun y => B (f y) (g y)) (B.precompR G' (f x) g' + B.precompL G' f' (g x)) x := by
  exact (B.isBoundedBilinearMap.hasFDerivAt (f x, g x)).comp x (hf.prod hg)

@[fun_prop]
theorem ContinuousLinearMap.hasStrictFDerivAt_of_bilinear
    {f : G' → E} {g : G' → F} {f' : G' →L[𝕜] E}
    {g' : G' →L[𝕜] F} {x : G'} (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x) :
    HasStrictFDerivAt (fun y => B (f y) (g y))
      (B.precompR G' (f x) g' + B.precompL G' f' (g x)) x :=
  (B.isBoundedBilinearMap.hasStrictFDerivAt (f x, g x)).comp x (hf.prod hg)

theorem ContinuousLinearMap.fderivWithin_of_bilinear {f : G' → E} {g : G' → F} {x : G'} {s : Set G'}
    (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y => B (f y) (g y)) s x =
      B.precompR G' (f x) (fderivWithin 𝕜 g s x) + B.precompL G' (fderivWithin 𝕜 f s x) (g x) :=
  (B.hasFDerivWithinAt_of_bilinear hf.hasFDerivWithinAt hg.hasFDerivWithinAt).fderivWithin hs

theorem ContinuousLinearMap.fderiv_of_bilinear {f : G' → E} {g : G' → F} {x : G'}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => B (f y) (g y)) x =
      B.precompR G' (f x) (fderiv 𝕜 g x) + B.precompL G' (fderiv 𝕜 f x) (g x) :=
  (B.hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt).fderiv

end BilinearMap

end
