/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log -- move lemmas, drop `public`
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Complex exponential is a covering map

In this file we show that the complex exponential function is a covering map over `{0}ᶜ`.

## TODO

Prove a similar theorem about polynomials (over the complement to the set of critical values),
especially for `x ^ n` (over `{0}ᶜ`).
-/

open scoped Real
open Set

@[expose] public noncomputable section

namespace Complex

/-- Complex exponential function is a branched covering map.

This partial homeomorph gives an explicit trivialization of this covering over `slitPlane`. -/
def expOpenPartialHomeomorphProd : OpenPartialHomeomorph ℂ (ℂ × ℤ) where
  toPartialEquiv := expPartialEquivProd
  open_source := isOpen_slitPlane.preimage continuous_exp
  open_target := isOpen_slitPlane.prod isOpen_univ
  continuousOn_toFun := by
    refine .prodMk (by fun_prop) <| .neg <| ?_
    refine (continuousOn_toIocDiv Real.two_pi_pos _).comp continuous_im.continuousOn ?_
    suffices ∀ z, exp z ∈ slitPlane → ¬z.im ≡ -π [PMOD (2 * π)] by
      simpa [MapsTo, AddCommGroup.modEq_iff_eq_mod_zmultiples] using this
    intro z hz₁ hz₂
    apply slitPlane_arg_ne_pi hz₁
    rw [AddCommGroup.ModEq, ← toIocMod_eq_toIocMod Real.two_pi_pos] at hz₂
    rw [arg_exp, hz₂, toIocMod_apply_left, two_mul, neg_add_cancel_left]
  continuousOn_invFun :=
    continuousOn_fst.clog (by simp) |>.sub (Continuous.continuousOn <| by fun_prop)

theorem isEvenlyCovered_exp {x : ℂ} (hx : x ≠ 0) :
    IsEvenlyCovered exp x ℤ := by
  -- We have an explicit trivialization over `slitPlane`.
  -- Make a change of coordinates to move our point there.
  -- We can move to any nonzero point, so we move to `1`.
  suffices IsEvenlyCovered exp 1 ℤ by
    convert this.comp_homeomorph (.addLeft (-x.log)) |>.homeomorph_comp (.mulLeft₀ x hx)
    · ext z
      simp [exp_add, exp_neg, exp_log, hx]
    · simp
  exact ⟨inferInstance, slitPlane, one_mem_slitPlane, isOpen_slitPlane,
    isOpen_slitPlane.preimage continuous_exp,
    expOpenPartialHomeomorphProd.toHomeomorphSourceTarget.trans <|
      (Homeomorph.Set.prod _ _).trans <| .prodCongr (.refl _) (Homeomorph.Set.univ _), fun _ ↦ rfl⟩

/-- Complex exponential function is a covering map on `{0}ᶜ`. -/
theorem isCoveringMapOn_exp : IsCoveringMapOn exp {0}ᶜ := fun _x hx ↦
  (isEvenlyCovered_exp hx).to_isEvenlyCovered_preimage

end Complex
