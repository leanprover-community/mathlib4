/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.NumberTheory.Height.Basic

/-!
# Heights of points in projective space

We define the multiplicative (`Projectivization.mulHeight`) and the logarithmic
(`Projectivization.logHeight`) height of a point in a (finite-dimensional) projective space
over a field that has a `Height.AdmissibleAbsValues` instance.

The height is defined to be the height of any representative tuple; it does not depend
on which representative is chosen.
-/

public section

namespace Projectivization

open Height AdmissibleAbsValues Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Finite ι]

private lemma mulHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K) (h : a.val = t • b.val) :
    mulHeight a.val = mulHeight b.val :=
  have ht : t ≠ 0 := by
    contrapose! h
    simpa [h] using a.prop
  h ▸ mulHeight_smul_eq_mulHeight _ ht

private lemma logHeight_aux (a b : { v : ι → K // v ≠ 0 }) (t : K) (h : a.val = t • b.val) :
    logHeight a.val = logHeight b.val :=
  congrArg log <| mod_cast mulHeight_aux a b t h

-- We do not expose the bodies of these definitions so that we can keep the "_aux" lemmas
-- above private.

/-- The multiplicative height of a point on a finite-dimensional projective space over `K`
with a given basis. -/
noncomputable def mulHeight (x : Projectivization K (ι → K)) : ℝ :=
  x.lift (fun r ↦ Height.mulHeight r.val) mulHeight_aux

/-- The logarithmic height of a point on a finite-dimensional projective space over `K`
with a given basis. -/
noncomputable def logHeight (x : Projectivization K (ι → K)) : ℝ :=
  x.lift (fun r ↦ Height.logHeight r.val) logHeight_aux

lemma mulHeight_mk {x : ι → K} (hx : x ≠ 0) : mulHeight (mk K x hx) = Height.mulHeight x := by
  rfl

lemma logHeight_mk {x : ι → K} (hx : x ≠ 0) : logHeight (mk K x hx) = Height.logHeight x := by
  rfl

lemma logHeight_eq_log_mulHeight (x : Projectivization K (ι → K)) :
    logHeight x = log (mulHeight x) := by
  rw [← x.mk_rep, mulHeight_mk, logHeight_mk, Height.logHeight]

lemma one_le_mulHeight (x : Projectivization K (ι → K)) : 1 ≤ mulHeight x := by
  rw [← x.mk_rep, mulHeight_mk]
  exact Height.one_le_mulHeight _

lemma mulHeight_pos (x : Projectivization K (ι → K)) : 0 < mulHeight x :=
  zero_lt_one.trans_le <| one_le_mulHeight x

lemma mulHeight_ne_zero (x : Projectivization K (ι → K)) : mulHeight x ≠ 0 :=
  (mulHeight_pos x).ne'

lemma logHeight_nonneg (x : Projectivization K (ι → K)) : 0 ≤ logHeight x := by
  rw [logHeight_eq_log_mulHeight]
  exact log_nonneg <| x.one_le_mulHeight

end Projectivization

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq Projectivization

/-- Extension for the `positivity` tactic: `Projectivization.mulHeight` is always positive. -/
@[positivity Projectivization.mulHeight _]
meta def evalProjMulHeight : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@mulHeight $K $KF $KA $ι $ιF $a) =>
    assertInstancesCommute
    pure (.positive q(mulHeight_pos $a))
  | _, _, _ => throwError "not Projectivization.mulHeight"

/-- Extension for the `positivity` tactic: `Projectivization.logHeight` is always nonnegative. -/
@[positivity Projectivization.logHeight _]
meta def evalProjLogHeight : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@logHeight $K $KF $KA $ι $ιF $a) =>
    assertInstancesCommute
    pure (.nonnegative q(logHeight_nonneg $a))
  | _, _, _ => throwError "not Projectivization.logHeight"

end Mathlib.Meta.Positivity
