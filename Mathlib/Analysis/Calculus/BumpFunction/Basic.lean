/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.NormedSpace.FiniteDimension

#align_import analysis.calculus.bump_function_inner from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Infinitely smooth "bump" functions

A smooth bump function is an infinitely smooth function `f : E → ℝ` supported on a ball
that is equal to `1` on a ball of smaller radius.

These functions have many uses in real analysis. E.g.,

- they can be used to construct a smooth partition of unity which is a very useful tool;
- they can be used to approximate a continuous function by infinitely smooth functions.

There are two classes of spaces where bump functions are guaranteed to exist:
inner product spaces and finite dimensional spaces.

In this file we define a typeclass `HasContDiffBump`
saying that a normed space has a family of smooth bump functions with certain properties.

We also define a structure `ContDiffBump` that holds the center and radii of the balls from above.
An element `f : ContDiffBump c` can be coerced to a function which is an infinitely smooth function
such that

- `f` is equal to `1` in `Metric.closedBall c f.rIn`;
- `support f = Metric.ball c f.rOut`;
- `0 ≤ f x ≤ 1` for all `x`.

## Main Definitions

- `ContDiffBump (c : E)`: a structure holding data needed to construct
  an infinitely smooth bump function.
- `ContDiffBumpBase (E : Type*)`: a family of infinitely smooth bump functions
  that can be used to construct coercion of a `ContDiffBump (c : E)`
  to a function.
- `HasContDiffBump (E : Type*)`: a typeclass saying that `E` has a `ContDiffBumpBase`.
  Two instances of this typeclass (for inner product spaces and for finite dimensional spaces)
  are provided elsewhere.

## Keywords

smooth function, smooth bump function
-/
noncomputable section

open Function Set Filter
open scoped Topology Filter

variable {E X : Type*}

/-- `f : ContDiffBump c`, where `c` is a point in a normed vector space, is a
bundled smooth function such that

- `f` is equal to `1` in `Metric.closedBall c f.rIn`;
- `support f = Metric.ball c f.rOut`;
- `0 ≤ f x ≤ 1` for all `x`.

The structure `ContDiffBump` contains the data required to construct the function:
real numbers `rIn`, `rOut`, and proofs of `0 < rIn < rOut`. The function itself is available through
`CoeFun` when the space is nice enough, i.e., satisfies the `HasContDiffBump` typeclass. -/
structure ContDiffBump (c : E) where
  /-- real numbers `0 < rIn < rOut` -/
  (rIn rOut : ℝ)
  rIn_pos : 0 < rIn
  rIn_lt_rOut : rIn < rOut
#align cont_diff_bump ContDiffBump
#align cont_diff_bump.r ContDiffBump.rIn
set_option linter.uppercaseLean3 false in
#align cont_diff_bump.R ContDiffBump.rOut
#align cont_diff_bump.r_pos ContDiffBump.rIn_pos
set_option linter.uppercaseLean3 false in
#align cont_diff_bump.r_lt_R ContDiffBump.rIn_lt_rOut

/-- The base function from which one will construct a family of bump functions. One could
add more properties if they are useful and satisfied in the examples of inner product spaces
and finite dimensional vector spaces, notably derivative norm control in terms of `R - 1`.

TODO: do we ever need `f x = 1 ↔ ‖x‖ ≤ 1`? -/
-- Porting note(#5171): linter not yet ported; was @[nolint has_nonempty_instance]
structure ContDiffBumpBase (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The function underlying this family of bump functions -/
  toFun : ℝ → E → ℝ
  mem_Icc : ∀ (R : ℝ) (x : E), toFun R x ∈ Icc (0 : ℝ) 1
  symmetric : ∀ (R : ℝ) (x : E), toFun R (-x) = toFun R x
  smooth : ContDiffOn ℝ ⊤ (uncurry toFun) (Ioi (1 : ℝ) ×ˢ (univ : Set E))
  eq_one : ∀ R : ℝ, 1 < R → ∀ x : E, ‖x‖ ≤ 1 → toFun R x = 1
  support : ∀ R : ℝ, 1 < R → Function.support (toFun R) = Metric.ball (0 : E) R
#align cont_diff_bump_base ContDiffBumpBase

/-- A class registering that a real vector space admits bump functions. This will be instantiated
first for inner product spaces, and then for finite-dimensional normed spaces.
We use a specific class instead of `Nonempty (ContDiffBumpBase E)` for performance reasons. -/
class HasContDiffBump (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop where
  out : Nonempty (ContDiffBumpBase E)
#align has_cont_diff_bump HasContDiffBump

/-- In a space with `C^∞` bump functions, register some function that will be used as a basis
to construct bump functions of arbitrary size around any point. -/
def someContDiffBumpBase (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [hb : HasContDiffBump E] : ContDiffBumpBase E :=
  Nonempty.some hb.out
#align some_cont_diff_bump_base someContDiffBumpBase

namespace ContDiffBump

theorem rOut_pos {c : E} (f : ContDiffBump c) : 0 < f.rOut :=
  f.rIn_pos.trans f.rIn_lt_rOut
set_option linter.uppercaseLean3 false in
#align cont_diff_bump.R_pos ContDiffBump.rOut_pos

theorem one_lt_rOut_div_rIn {c : E} (f : ContDiffBump c) : 1 < f.rOut / f.rIn := by
  rw [one_lt_div f.rIn_pos]
  exact f.rIn_lt_rOut
set_option linter.uppercaseLean3 false in
#align cont_diff_bump.one_lt_R_div_r ContDiffBump.one_lt_rOut_div_rIn

instance (c : E) : Inhabited (ContDiffBump c) :=
  ⟨⟨1, 2, zero_lt_one, one_lt_two⟩⟩

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [HasContDiffBump E] {c : E} (f : ContDiffBump c) {x : E} {n : ℕ∞}

/-- The function defined by `f : ContDiffBump c`. Use automatic coercion to
function instead. -/
@[coe] def toFun {c : E} (f : ContDiffBump c) : E → ℝ :=
  (someContDiffBumpBase E).toFun (f.rOut / f.rIn) ∘ fun x ↦ (f.rIn⁻¹ • (x - c))
#align cont_diff_bump.to_fun ContDiffBump.toFun

instance : CoeFun (ContDiffBump c) fun _ => E → ℝ :=
  ⟨toFun⟩

protected theorem apply (x : E) :
    f x = (someContDiffBumpBase E).toFun (f.rOut / f.rIn) (f.rIn⁻¹ • (x - c)) :=
  rfl
#align cont_diff_bump.def ContDiffBump.apply

protected theorem sub (x : E) : f (c - x) = f (c + x) := by
  simp [f.apply, ContDiffBumpBase.symmetric]
#align cont_diff_bump.sub ContDiffBump.sub

protected theorem neg (f : ContDiffBump (0 : E)) (x : E) : f (-x) = f x := by
  simp_rw [← zero_sub, f.sub, zero_add]
#align cont_diff_bump.neg ContDiffBump.neg

open Metric

theorem one_of_mem_closedBall (hx : x ∈ closedBall c f.rIn) : f x = 1 := by
  apply ContDiffBumpBase.eq_one _ _ f.one_lt_rOut_div_rIn
  simpa only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg f.rIn_pos.le, ← div_eq_inv_mul,
    div_le_one f.rIn_pos] using mem_closedBall_iff_norm.1 hx
#align cont_diff_bump.one_of_mem_closed_ball ContDiffBump.one_of_mem_closedBall

theorem nonneg : 0 ≤ f x :=
  (ContDiffBumpBase.mem_Icc (someContDiffBumpBase E) _ _).1
#align cont_diff_bump.nonneg ContDiffBump.nonneg

/-- A version of `ContDiffBump.nonneg` with `x` explicit -/
theorem nonneg' (x : E) : 0 ≤ f x := f.nonneg
#align cont_diff_bump.nonneg' ContDiffBump.nonneg'

theorem le_one : f x ≤ 1 :=
  (ContDiffBumpBase.mem_Icc (someContDiffBumpBase E) _ _).2
#align cont_diff_bump.le_one ContDiffBump.le_one

theorem support_eq : Function.support f = Metric.ball c f.rOut := by
  simp only [toFun, support_comp_eq_preimage, ContDiffBumpBase.support _ _ f.one_lt_rOut_div_rIn]
  ext x
  simp only [mem_ball_iff_norm, sub_zero, norm_smul, mem_preimage, Real.norm_eq_abs, abs_inv,
    abs_of_pos f.rIn_pos, ← div_eq_inv_mul, div_lt_div_right f.rIn_pos]
#align cont_diff_bump.support_eq ContDiffBump.support_eq

theorem tsupport_eq : tsupport f = closedBall c f.rOut := by
  simp_rw [tsupport, f.support_eq, closure_ball _ f.rOut_pos.ne']
#align cont_diff_bump.tsupport_eq ContDiffBump.tsupport_eq

theorem pos_of_mem_ball (hx : x ∈ ball c f.rOut) : 0 < f x :=
  f.nonneg.lt_of_ne' <| by rwa [← support_eq, mem_support] at hx
#align cont_diff_bump.pos_of_mem_ball ContDiffBump.pos_of_mem_ball

theorem zero_of_le_dist (hx : f.rOut ≤ dist x c) : f x = 0 := by
  rwa [← nmem_support, support_eq, mem_ball, not_lt]
#align cont_diff_bump.zero_of_le_dist ContDiffBump.zero_of_le_dist

protected theorem hasCompactSupport [FiniteDimensional ℝ E] : HasCompactSupport f := by
  simp_rw [HasCompactSupport, f.tsupport_eq, isCompact_closedBall]
#align cont_diff_bump.has_compact_support ContDiffBump.hasCompactSupport

theorem eventuallyEq_one_of_mem_ball (h : x ∈ ball c f.rIn) : f =ᶠ[𝓝 x] 1 :=
  mem_of_superset (closedBall_mem_nhds_of_mem h) fun _ ↦ f.one_of_mem_closedBall
#align cont_diff_bump.eventually_eq_one_of_mem_ball ContDiffBump.eventuallyEq_one_of_mem_ball

theorem eventuallyEq_one : f =ᶠ[𝓝 c] 1 :=
  f.eventuallyEq_one_of_mem_ball (mem_ball_self f.rIn_pos)
#align cont_diff_bump.eventually_eq_one ContDiffBump.eventuallyEq_one

/-- `ContDiffBump` is `𝒞ⁿ` in all its arguments. -/
protected theorem _root_.ContDiffWithinAt.contDiffBump {c g : X → E} {s : Set X}
    {f : ∀ x, ContDiffBump (c x)} {x : X} (hc : ContDiffWithinAt ℝ n c s x)
    (hr : ContDiffWithinAt ℝ n (fun x => (f x).rIn) s x)
    (hR : ContDiffWithinAt ℝ n (fun x => (f x).rOut) s x)
    (hg : ContDiffWithinAt ℝ n g s x) :
    ContDiffWithinAt ℝ n (fun x => f x (g x)) s x := by
  change ContDiffWithinAt ℝ n (uncurry (someContDiffBumpBase E).toFun ∘ fun x : X =>
    ((f x).rOut / (f x).rIn, (f x).rIn⁻¹ • (g x - c x))) s x
  refine (((someContDiffBumpBase E).smooth.contDiffAt ?_).of_le le_top).comp_contDiffWithinAt x ?_
  · exact prod_mem_nhds (Ioi_mem_nhds (f x).one_lt_rOut_div_rIn) univ_mem
  · exact (hR.div hr (f x).rIn_pos.ne').prod ((hr.inv (f x).rIn_pos.ne').smul (hg.sub hc))

/-- `ContDiffBump` is `𝒞ⁿ` in all its arguments. -/
protected nonrec theorem _root_.ContDiffAt.contDiffBump {c g : X → E} {f : ∀ x, ContDiffBump (c x)}
    {x : X} (hc : ContDiffAt ℝ n c x) (hr : ContDiffAt ℝ n (fun x => (f x).rIn) x)
    (hR : ContDiffAt ℝ n (fun x => (f x).rOut) x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun x => f x (g x)) x :=
  hc.contDiffBump hr hR hg
#align cont_diff_at.cont_diff_bump ContDiffAt.contDiffBump

theorem _root_.ContDiff.contDiffBump {c g : X → E} {f : ∀ x, ContDiffBump (c x)}
    (hc : ContDiff ℝ n c) (hr : ContDiff ℝ n fun x => (f x).rIn)
    (hR : ContDiff ℝ n fun x => (f x).rOut) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n fun x => f x (g x) := by
  rw [contDiff_iff_contDiffAt] at *
  exact fun x => (hc x).contDiffBump (hr x) (hR x) (hg x)
#align cont_diff.cont_diff_bump ContDiff.contDiffBump

protected theorem contDiff : ContDiff ℝ n f :=
  contDiff_const.contDiffBump contDiff_const contDiff_const contDiff_id
#align cont_diff_bump.cont_diff ContDiffBump.contDiff

protected theorem contDiffAt : ContDiffAt ℝ n f x :=
  f.contDiff.contDiffAt
#align cont_diff_bump.cont_diff_at ContDiffBump.contDiffAt

protected theorem contDiffWithinAt {s : Set E} : ContDiffWithinAt ℝ n f s x :=
  f.contDiffAt.contDiffWithinAt
#align cont_diff_bump.cont_diff_within_at ContDiffBump.contDiffWithinAt

protected theorem continuous : Continuous f :=
  contDiff_zero.mp f.contDiff
#align cont_diff_bump.continuous ContDiffBump.continuous

end ContDiffBump
