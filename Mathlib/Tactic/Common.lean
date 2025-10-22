/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

-- First import Aesop, Qq, and Plausible
import Aesop
import Qq
import Plausible

-- Tools for analysing imports, like `#find_home`, `#minimize_imports`, ...
import ImportGraph.Imports

-- Import common Batteries tactics and commands
import Batteries.Tactic.Basic
import Batteries.Tactic.Case
import Batteries.Tactic.HelpCmd
import Batteries.Tactic.Alias

-- Import syntax for leansearch
import LeanSearchClient

-- Import Mathlib-specific linters.
import Mathlib.Tactic.Linter.Lint

-- Now import all tactics defined in Mathlib that do not require theory files.
import Mathlib.Tactic.ApplyCongr
-- ApplyFun imports `Mathlib/Order/Monotone/Basic.lean`
-- import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.ApplyWith
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.Check
import Mathlib.Tactic.Choose
import Mathlib.Tactic.ClearExclamation
import Mathlib.Tactic.ClearExcept
import Mathlib.Tactic.Clear_
import Mathlib.Tactic.Coe
import Mathlib.Tactic.CongrExclamation
import Mathlib.Tactic.CongrM
import Mathlib.Tactic.Constructor
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.DefEqTransformations
import Mathlib.Tactic.DefaultNumeralType
import Mathlib.Tactic.DeprecateTo
import Mathlib.Tactic.ErwQuestion
import Mathlib.Tactic.Eqns
import Mathlib.Tactic.ExistsI
import Mathlib.Tactic.ExtractGoal
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Tactic.Find
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.GeneralizeProofs
import Mathlib.Tactic.GuardGoalNums
import Mathlib.Tactic.GuardHypNums
import Mathlib.Tactic.HigherOrder
import Mathlib.Tactic.Hint
import Mathlib.Tactic.InferParam
import Mathlib.Tactic.Inhabit
import Mathlib.Tactic.IrreducibleDef
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Linter
import Mathlib.Tactic.MkIffOfInductiveProp
-- NormNum imports `Algebra.Order.Invertible`, `Data.Int.Basic`, `Data.Nat.Cast.Commute`
-- import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Observe
import Mathlib.Tactic.OfNat
-- `positivity` imports `Data.Nat.Factorial.Basic`, but hopefully this can be rearranged.
-- import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Propose
import Mathlib.Tactic.Push
import Mathlib.Tactic.RSuffices
import Mathlib.Tactic.Recover
import Mathlib.Tactic.Relation.Rfl
import Mathlib.Tactic.Rename
import Mathlib.Tactic.RenameBVar
import Mathlib.Tactic.Says
import Mathlib.Tactic.ScopedNS
import Mathlib.Tactic.Set
import Mathlib.Tactic.SimpIntro
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Spread
import Mathlib.Tactic.Subsingleton
import Mathlib.Tactic.Substs
import Mathlib.Tactic.SuccessIfFailWithMsg
import Mathlib.Tactic.SudoSetOption
import Mathlib.Tactic.SwapVar
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.TermCongr
-- TFAE imports `Mathlib/Data/List/TFAE.lean` and thence `Mathlib/Data/List/Basic.lean`.
-- import Mathlib.Tactic.TFAE
import Mathlib.Tactic.ToExpr
import Mathlib.Tactic.ToLevel
import Mathlib.Tactic.Trace
import Mathlib.Tactic.TypeCheck
import Mathlib.Tactic.UnsetOption
import Mathlib.Tactic.Use
import Mathlib.Tactic.Variable
import Mathlib.Tactic.Widget.Calc
import Mathlib.Tactic.Widget.CongrM
import Mathlib.Tactic.Widget.Conv
import Mathlib.Tactic.Widget.LibraryRewrite
import Mathlib.Tactic.WLOG
import Mathlib.Util.AssertExists
import Mathlib.Util.CountHeartbeats
import Mathlib.Util.PrintSorries
import Mathlib.Util.TransImports
import Mathlib.Util.WhatsNew

/-!
This file imports all tactics which do not have significant theory imports,
and hence can be imported very low in the theory import hierarchy,
thereby making tactics widely available without needing specific imports.

We include some commented out imports here, with an explanation of their theory requirements,
to save some time for anyone wondering why they are not here.

We also import theory-free linters, commands, and utilities which are useful to have low in the
import hierarchy.
-/

/-!
# Register tactics with `hint`. Tactics with larger priority run first.
-/

section Hint

register_hint (priority := 200) grind
register_hint (priority := 1000) trivial
register_hint (priority := 500) tauto
register_hint (priority := 1000) split
register_hint (priority := 1000) intro
register_hint (priority := 80) aesop
register_hint (priority := 800) simp_all?
register_hint (priority := 600) exact?
register_hint (priority := 1000) decide
register_hint (priority := 200) omega
register_hint (priority := 200) fun_prop

end Hint
