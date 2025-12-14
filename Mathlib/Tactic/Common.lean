/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

-- First import Aesop, Qq, and Plausible
module

public meta import Aesop
public meta import Qq
public meta import Plausible

-- Tools for analysing imports, like `#find_home`, `#minimize_imports`, ...
public meta import ImportGraph.Imports

-- Import common Batteries tactics and commands
public meta import Batteries.Tactic.Basic
public meta import Batteries.Tactic.Case
public meta import Batteries.Tactic.HelpCmd
public meta import Batteries.Tactic.Alias
public meta import Batteries.Tactic.GeneralizeProofs

-- Import syntax for leansearch
public meta import LeanSearchClient

-- Import Mathlib-specific linters.
public meta import Mathlib.Tactic.Linter.Lint

-- Now import all tactics defined in Mathlib that do not require theory files.
public meta import Mathlib.Tactic.ApplyCongr
-- ApplyFun imports `Mathlib/Order/Monotone/Basic.lean`
-- import Mathlib.Tactic.ApplyFun
public meta import Mathlib.Tactic.ApplyAt
public meta import Mathlib.Tactic.ApplyWith
public meta import Mathlib.Tactic.Basic
public meta import Mathlib.Tactic.ByCases
public meta import Mathlib.Tactic.ByContra
public meta import Mathlib.Tactic.CasesM
public meta import Mathlib.Tactic.Check
public meta import Mathlib.Tactic.Choose
public meta import Mathlib.Tactic.ClearExclamation
public meta import Mathlib.Tactic.ClearExcept
public meta import Mathlib.Tactic.Clear_
public meta import Mathlib.Tactic.Coe
public meta import Mathlib.Tactic.CongrExclamation
public meta import Mathlib.Tactic.CongrM
public meta import Mathlib.Tactic.Constructor
public meta import Mathlib.Tactic.Contrapose
public meta import Mathlib.Tactic.Conv
public meta import Mathlib.Tactic.Convert
public meta import Mathlib.Tactic.DefEqTransformations
public meta import Mathlib.Tactic.DeprecateTo
public meta import Mathlib.Tactic.ErwQuestion
public meta import Mathlib.Tactic.Eqns
public meta import Mathlib.Tactic.ExistsI
public meta import Mathlib.Tactic.ExtractGoal
public meta import Mathlib.Tactic.FailIfNoProgress
public meta import Mathlib.Tactic.Find
public meta import Mathlib.Tactic.FunProp
public meta import Mathlib.Tactic.GCongr
public meta import Mathlib.Tactic.GRewrite
public meta import Mathlib.Tactic.GuardGoalNums
public meta import Mathlib.Tactic.GuardHypNums
public meta import Mathlib.Tactic.HigherOrder
public meta import Mathlib.Tactic.Hint
public meta import Mathlib.Tactic.InferParam
public meta import Mathlib.Tactic.Inhabit
public meta import Mathlib.Tactic.IrreducibleDef
public meta import Mathlib.Tactic.Lift
public meta import Mathlib.Tactic.Linter
public meta import Mathlib.Tactic.MkIffOfInductiveProp
-- NormNum imports `Algebra.Order.Invertible`, `Data.Int.Basic`, `Data.Nat.Cast.Commute`
-- import Mathlib.Tactic.NormNum.Basic
public meta import Mathlib.Tactic.NthRewrite
public meta import Mathlib.Tactic.Observe
public meta import Mathlib.Tactic.OfNat
-- `positivity` imports `Data.Nat.Factorial.Basic`, but hopefully this can be rearranged.
-- import Mathlib.Tactic.Positivity
public meta import Mathlib.Tactic.Push
public meta import Mathlib.Tactic.RSuffices
public meta import Mathlib.Tactic.Recover
public meta import Mathlib.Tactic.Relation.Rfl
public meta import Mathlib.Tactic.Rename
public meta import Mathlib.Tactic.RenameBVar
public meta import Mathlib.Tactic.Says
public meta import Mathlib.Tactic.ScopedNS
public meta import Mathlib.Tactic.Set
public meta import Mathlib.Tactic.SimpIntro
public meta import Mathlib.Tactic.SimpRw
public meta import Mathlib.Tactic.Simps.Basic
public meta import Mathlib.Tactic.SplitIfs
public meta import Mathlib.Tactic.Spread
public meta import Mathlib.Tactic.Subsingleton
public meta import Mathlib.Tactic.Substs
public meta import Mathlib.Tactic.SuccessIfFailWithMsg
public meta import Mathlib.Tactic.SudoSetOption
public meta import Mathlib.Tactic.SwapVar
public meta import Mathlib.Tactic.Tauto
public meta import Mathlib.Tactic.TermCongr
-- TFAE imports `Mathlib/Data/List/TFAE.lean` and thence `Mathlib/Data/List/Basic.lean`.
-- import Mathlib.Tactic.TFAE
public meta import Mathlib.Tactic.ToExpr
public meta import Mathlib.Tactic.ToLevel
public meta import Mathlib.Tactic.Trace
public meta import Mathlib.Tactic.TypeCheck
public meta import Mathlib.Tactic.UnsetOption
public meta import Mathlib.Tactic.Use
public meta import Mathlib.Tactic.Variable
public meta import Mathlib.Tactic.Widget.Calc
public meta import Mathlib.Tactic.Widget.CongrM
public meta import Mathlib.Tactic.Widget.Conv
public meta import Mathlib.Tactic.Widget.LibraryRewrite
public meta import Mathlib.Tactic.WLOG
public meta import Mathlib.Util.AssertExists
public meta import Mathlib.Util.CountHeartbeats
public meta import Mathlib.Util.PrintSorries
public meta import Mathlib.Util.TransImports
public meta import Mathlib.Util.WhatsNew

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
