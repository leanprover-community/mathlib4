/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.GCongr.Core
import Mathlib.Tactic.PushNeg
import Mathlib.Util.AssertExists

/-!
# Basic operations on the natural numbers
-/

/- We don't want to import the algebraic hierarchy in this file. -/
assert_not_exists Monoid
