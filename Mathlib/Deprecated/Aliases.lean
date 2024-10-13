/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Init
import Batteries.Tactic.Alias
import Batteries.Data.String.Basic

/-!
Deprecated aliases can be dumped here if they are no longer used in Mathlib,
to avoid needing their imports if they are otherwise unnecessary.
-/
namespace String

@[deprecated (since := "2024-06-04")] alias getRest := dropPrefix?

end String
