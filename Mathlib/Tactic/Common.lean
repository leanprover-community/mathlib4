/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

-- First import Aesop, Qq, and Plausible
module  -- shake: keep-all, shake: keep-downstream

public import Aesop
public import Qq
public import Plausible

-- Tools for analysing imports, like `#find_home`, `#minimize_imports`, ...
public import ImportGraph.Imports

-- Import common Batteries tactics and commands
public import Batteries.Tactic.Basic
public import Batteries.Tactic.Case
public import Batteries.Tactic.HelpCmd
public import Batteries.Tactic.Alias
public import Batteries.Tactic.GeneralizeProofs

-- Import Batteries code actions
public import Batteries.CodeAction

-- Import syntax for leansearch
public import LeanSearchClient

-- Import Mathlib-specific linters.
public import Mathlib.Tactic.Linter.Lint

-- Now import all tactics defined in Mathlib that do not require theory files.
public import Mathlib.Tactic.ApplyCongr
-- ApplyFun imports `Mathlib/Order/Monotone/Basic.lean`
-- import Mathlib.Tactic.ApplyFun
public import Mathlib.Tactic.ApplyAt
public import Mathlib.Tactic.ApplyWith
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.ByCases
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.CasesM
public import Mathlib.Tactic.Check
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.ClearExclamation
public import Mathlib.Tactic.ClearExcept
public import Mathlib.Tactic.Clear_
public import Mathlib.Tactic.Coe
public import Mathlib.Tactic.CongrExclamation
public import Mathlib.Tactic.CongrM
public import Mathlib.Tactic.Constructor
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Conv
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.DefEqTransformations
public import Mathlib.Tactic.DeprecateTo
public import Mathlib.Tactic.ErwQuestion
public import Mathlib.Tactic.Eqns
public import Mathlib.Tactic.ExistsI
public import Mathlib.Tactic.ExtractGoal
public import Mathlib.Tactic.FailIfNoProgress
public import Mathlib.Tactic.Find
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.GuardGoalNums
public import Mathlib.Tactic.GuardHypNums
public import Mathlib.Tactic.HigherOrder
public import Mathlib.Tactic.Hint
public import Mathlib.Tactic.InferParam
public import Mathlib.Tactic.Inhabit
public import Mathlib.Tactic.IrreducibleDef
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.Linter
public import Mathlib.Tactic.MkIffOfInductiveProp
-- NormNum imports `Algebra.Order.Invertible`, `Data.Int.Basic`, `Data.Nat.Cast.Commute`
-- import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NthRewrite
public import Mathlib.Tactic.Observe
public import Mathlib.Tactic.OfNat
-- `positivity` imports `Data.Nat.Factorial.Basic`, but hopefully this can be rearranged.
-- import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.RSuffices
public import Mathlib.Tactic.Recover
public import Mathlib.Tactic.Relation.Rfl
public import Mathlib.Tactic.Rename
public import Mathlib.Tactic.RenameBVar
public import Mathlib.Tactic.Says
public import Mathlib.Tactic.ScopedNS
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SimpIntro
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.Simps.Basic
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Spread
public import Mathlib.Tactic.Subsingleton
public import Mathlib.Tactic.Substs
public import Mathlib.Tactic.SuccessIfFailWithMsg
public import Mathlib.Tactic.SudoSetOption
public import Mathlib.Tactic.SwapVar
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.ToFun
public import Mathlib.Tactic.TermCongr
-- TFAE imports `Mathlib/Data/List/TFAE.lean` and thence `Mathlib/Data/List/Basic.lean`.
-- import Mathlib.Tactic.TFAE
public import Mathlib.Tactic.ToExpr
public import Mathlib.Tactic.ToLevel
public import Mathlib.Tactic.Trace
public import Mathlib.Tactic.TypeCheck
public import Mathlib.Tactic.UnsetOption
public import Mathlib.Tactic.Use
public import Mathlib.Tactic.Variable
public import Mathlib.Tactic.Widget.Calc
public import Mathlib.Tactic.Widget.CongrM
public import Mathlib.Tactic.Widget.Conv
public import Mathlib.Tactic.Widget.LibraryRewrite
public import Mathlib.Tactic.WLOG
public import Mathlib.Util.AssertExists
public import Mathlib.Util.CountHeartbeats
public import Mathlib.Util.PrintSorries
public import Mathlib.Util.TransImports
public import Mathlib.Util.WhatsNew

/-!
This file imports all tactics which do not have significant theory imports,
and hence can be imported very low in the theory import hierarchy,
thereby making tactics widely available without needing specific imports.

We include some commented out imports here, with an explanation of their theory requirements,
to save some time for anyone wondering why they are not here.

We also import theory-free linters, commands, and utilities which are useful to have low in the
import hierarchy.
-/

public meta section

/-!
# Register tactics with `hint`. Tactics with larger priority run first.
-/

section Hint

register_hint 200 grind
register_hint 1000 trivial
register_hint 500 tauto
register_hint 1000 split
register_hint 1000 intro
register_hint 80 aesop
register_hint 800 simp_all?
register_hint 600 exact?
register_hint 1000 decide
register_hint 200 omega
register_hint 200 fun_prop

end Hint

/-!
# Register tactics with `try?`. Tactics with larger priority run first.
-/

section Try

register_try?_tactic (priority := 500) tauto
register_try?_tactic (priority := 80) aesop
register_try?_tactic (priority := 200) fun_prop

end Try
