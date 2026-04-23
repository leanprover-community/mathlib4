/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Lemmas about asymptotics and the natural embedding `ℝ → ℂ`

In this file we prove several trivial lemmas about `Asymptotics.IsBigO` etc. and `(↑) : ℝ → ℂ`.
-/

public section

namespace Complex

variable {α E : Type*} [Norm E] {l : Filter α}

theorem isTheta_ofReal (f : α → ℝ) (l : Filter α) : (f · : α → ℂ) =Θ[l] f :=
  .of_norm_left <| by simpa using (Asymptotics.isTheta_rfl (f := f)).norm_left

@[simp, norm_cast]
theorem isLittleO_ofReal_left {f : α → ℝ} {g : α → E} : (f · : α → ℂ) =o[l] g ↔ f =o[l] g :=
  (isTheta_ofReal f l).isLittleO_congr_left

@[simp, norm_cast]
theorem isLittleO_ofReal_right {f : α → E} {g : α → ℝ} : f =o[l] (g · : α → ℂ) ↔ f =o[l] g :=
  (isTheta_ofReal g l).isLittleO_congr_right

@[simp, norm_cast]
theorem isBigO_ofReal_left {f : α → ℝ} {g : α → E} : (f · : α → ℂ) =O[l] g ↔ f =O[l] g :=
  (isTheta_ofReal f l).isBigO_congr_left

@[simp, norm_cast]
theorem isBigO_ofReal_right {f : α → E} {g : α → ℝ} : f =O[l] (g · : α → ℂ) ↔ f =O[l] g :=
  (isTheta_ofReal g l).isBigO_congr_right

@[simp, norm_cast]
theorem isTheta_ofReal_left {f : α → ℝ} {g : α → E} : (f · : α → ℂ) =Θ[l] g ↔ f =Θ[l] g :=
  (isTheta_ofReal f l).isTheta_congr_left

@[simp, norm_cast]
theorem isTheta_ofReal_right {f : α → E} {g : α → ℝ} : f =Θ[l] (g · : α → ℂ) ↔ f =Θ[l] g :=
  (isTheta_ofReal g l).isTheta_congr_right

open Topology

lemma isBigO_comp_ofReal_nhds {f g : ℂ → ℂ} {x : ℝ} (h : f =O[𝓝 (x : ℂ)] g) :
    (fun y : ℝ ↦ f y) =O[𝓝 x] (fun y : ℝ ↦ g y) :=
  h.comp_tendsto <| continuous_ofReal.tendsto x

lemma isBigO_comp_ofReal_nhds_ne {f g : ℂ → ℂ} {x : ℝ} (h : f =O[𝓝[≠] (x : ℂ)] g) :
    (fun y : ℝ ↦ f y) =O[𝓝[≠] x] (fun y : ℝ ↦ g y) :=
  h.comp_tendsto <| continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun _ _ ↦ by simp_all

lemma isBigO_re_sub_re {z : ℂ} : (fun (w : ℂ) ↦ w.re - z.re) =O[𝓝 z] fun w ↦ w - z :=
  Asymptotics.isBigO_of_le _ fun w ↦ abs_re_le_norm (w - z)

lemma isBigO_im_sub_im {z : ℂ} : (fun (w : ℂ) ↦ w.im - z.im) =O[𝓝 z] fun w ↦ w - z :=
  Asymptotics.isBigO_of_le _ fun w ↦ abs_im_le_norm (w - z)

end Complex

section Int

open Filter in
lemma Int.cast_complex_isTheta_cast_real : Int.cast (R := ℂ) =Θ[cofinite] Int.cast (R := ℝ) := by
  apply Asymptotics.IsTheta.of_norm_eventuallyEq_norm
  filter_upwards with n using by simp

end Int
