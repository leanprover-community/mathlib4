/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Adomas Baliuka
-/
import Mathlib.Tactic.Differentiability.Init
import Mathlib.Algebra.Group.Defs

/-!
# Differentiability

We define the `differentiability` tactic using `aesop`.
The approach is copied from how the tactic `continuity` is implemented.
-/

attribute [aesop (rule_sets [Differentiable]) unfold norm] Function.comp

-- copied over (from `continuity`) but it was decided that this should not be used
-- neither here, nor for `continuity`.
-- attribute [aesop (rule_sets [Differentiable]) unfold norm] npowRec

/--
The `differentiability` attribute used to tag differentiability statements for the
 `differentiability` tactic. -/
macro "differentiability" : attr =>
  `(attr|aesop safe apply (rule_sets [$(Lean.mkIdent `Differentiable):ident]))

/--
The tactic `differentiability` solves goals of the form `Differentiable _ f` by applying lemmas
tagged with the `differentiability` user attribute. -/
macro "differentiability" : tactic =>
  `(tactic| aesop (options := { terminal := true })
  (rule_sets [$(Lean.mkIdent `Differentiable):ident]))

/--
The tactic `differentiability` solves goals of the form `Differentiable _ f` by applying lemmas
tagged with the `differentiability` user attribute. -/
macro "differentiability?" : tactic =>
  `(tactic| aesop? (options := { terminal := true })
    (rule_sets [$(Lean.mkIdent `Differentiable):ident]))

-- Todo: implement `differentiability!` and `differentiability!?` and add configuration, original
-- syntax was (same for the missing `differentiability` variants):
-- syntax (name := differentiability) "differentiability" (config)? : tactic


/-- attribute to use with `solve_by_elim`. TODO delete either aesop tactic or this? -/
register_label_attr differentiabilitySBE
