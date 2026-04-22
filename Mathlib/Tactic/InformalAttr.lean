/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

import Mathlib.Tactic.DatabaseAttributes
import Batteries.Data.MLList.Basic
import Batteries.Data.RBMap.Basic
import Batteries.Data.DList.Basic

/-!
# Upstream attributes for `@[informal]`
-/

-- Generated with `#imported_informal?` after importing `Lean`, `Batteries`, `Std`
attribute [informal "array"] Array
attribute [informal "integer"] Int
attribute [informal "list"] List
attribute [informal "lazy list"] MLList
attribute [informal "natural number"] Nat
attribute [informal "rational number"] Rat
attribute [informal "difference list"] Batteries.DList
attribute [informal "red-black map"] Batteries.RBMap
attribute [informal "red-black tree"] Batteries.RBSet
attribute [informal "hash map"] Std.HashMap
