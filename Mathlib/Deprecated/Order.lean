/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.Defs.LinearOrder

/-!
# Deprecated instances about order structures.
-/

variable {α : Type*}

@[deprecated "This was a leftover from Lean 3, and has not been needed." (since := "2024-11-26")]
instance isStrictTotalOrder_of_linearOrder [LinearOrder α] : IsStrictTotalOrder α (· < ·) where
  irrefl := lt_irrefl
  trichotomous := lt_trichotomy
