/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

-- First import Aesop and Qq
import Aesop
import Qq

-- Tools for analysing imports, like `#find_home`, `#minimize_imports`, ...
import ImportGraph.Imports

-- Currently we don't need to import all of ProofWidgets,
-- but without this, if you don't run `lake build ProofWidgets` then `make test` will fail.
-- Hopefully `lake` will be able to handle tests later.
import ProofWidgets

-- Import Mathlib-specific linters.
import Mathlib.Tactic.Linter.Lint

-- Now import all tactics defined in Mathlib that do not require theory files.
import Mathlib.Mathport.Rename
import Mathlib.Tactic.ApplyCongr
-- ApplyFun imports `Mathlib.Order.Monotone.Basic`
-- import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.ApplyWith
import Mathlib.Tactic.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Cases
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.Check
import Mathlib.Tactic.Choose
import Mathlib.Tactic.ClearExclamation
import Mathlib.Tactic.ClearExcept
import Mathlib.Tactic.Clear_
import Mathlib.Tactic.Coe
import Mathlib.Tactic.Congr!
import Mathlib.Tactic.Congrm
import Mathlib.Tactic.Constructor
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.DefEqTransformations
import Mathlib.Tactic.DeprecateMe
import Mathlib.Tactic.DeriveToExpr
import Mathlib.Tactic.Eqns
import Mathlib.Tactic.Existsi
import Mathlib.Tactic.ExtractGoal
import Mathlib.Tactic.ExtractLets
import Mathlib.Tactic.FailIfNoProgress
import Mathlib.Tactic.Find
-- `gcongr` currently imports `Algebra.Order.Field.Power` and thence `Algebra.CharZero.Lemmas`
-- Hopefully this can be rearranged.
-- import Mathlib.Tactic.GCongr
import Mathlib.Tactic.GeneralizeProofs
import Mathlib.Tactic.GuardGoalNums
import Mathlib.Tactic.GuardHypNums
import Mathlib.Tactic.HelpCmd
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
-- `positivity` imports `Data.Nat.Factorial.Basic`, but hopefully this can be rearranged.
-- import Mathlib.Tactic.Positivity
import Mathlib.Tactic.ProjectionNotation
import Mathlib.Tactic.Propose
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.RSuffices
import Mathlib.Tactic.Recover
import Mathlib.Tactic.Relation.Rfl
import Mathlib.Tactic.Relation.Trans
import Mathlib.Tactic.Rename
import Mathlib.Tactic.RenameBVar
import Mathlib.Tactic.Says
import Mathlib.Tactic.ScopedNS
import Mathlib.Tactic.Set
import Mathlib.Tactic.SimpIntro
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Simps.Basic
-- SlimCheck has unnecessarily complicated imports, and could be streamlined.
-- `Gen` / `Testable` / `Sampleable` instances for types should be out in the library,
-- rather than the theory for those types being imported into `SlimCheck`.
-- import Mathlib.Tactic.SlimCheck
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Spread
import Mathlib.Tactic.Substs
import Mathlib.Tactic.SuccessIfFailWithMsg
import Mathlib.Tactic.SudoSetOption
import Mathlib.Tactic.SwapVar
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.TermCongr
-- TFAE imports `Mathlib.Data.List.TFAE` and thence `Mathlib.Data.List.Basic`.
-- import Mathlib.Tactic.TFAE
import Mathlib.Tactic.ToExpr
import Mathlib.Tactic.ToLevel
import Mathlib.Tactic.Trace
import Mathlib.Tactic.TypeCheck
import Mathlib.Tactic.UnsetOption
import Mathlib.Tactic.Use
import Mathlib.Tactic.Variable
import Mathlib.Tactic.Widget.Calc
import Mathlib.Tactic.Widget.Congrm
import Mathlib.Tactic.Widget.Conv
import Mathlib.Tactic.WLOG
import Mathlib.Util.AssertExists
import Mathlib.Util.CountHeartbeats
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
# Register tactics with `hint`.
-/

section Hint

register_hint split
register_hint intro
register_hint aesop
register_hint simp_all?
register_hint exact?
register_hint decide
register_hint omega

end Hint
