module

public import Mathlib.Algebra.Group.Defs
public meta import Mathlib.Lean.Exception
public import Mathlib.Tactic.ReduceModChar.Ext
public import Mathlib.Tactic.Translate.ToDifferentiable
public import Qq.MetaM

import all Init.Prelude
import all Mathlib.Tactic.Translate.Expr

open Qq Lean Meta Elab Command Mathlib Tactic Translate ToDifferentiable

public section

-- work in a namespace so that it doesn't matter if names clash
namespace Test

variable {R : Type*} [Group R] {E F : Type*} [Group E] [Group F]

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

-- Artificially simplified definitions (which hence contain unused variables).
def ContDiff (n : ℕ) (f : E → F) : Prop := True

def Differentiable (f : E → F) : Prop := True

attribute [to_differentiable existing (omit := 3) Differentiable] ContDiff

lemma ContDiff.add [Add F] (f g : E → F) (hf : ContDiff 2 f) (hg : ContDiff 2 g) :
  ContDiff 2 (fun x ↦ f x + g x) := trivial

lemma Differentiable.add [Add F] (f g : E → F) (hf : Differentiable f) (hg : Differentiable g) :
  Differentiable (fun x ↦ f x + g x) := trivial

attribute [to_differentiable existing] ContDiff.add
