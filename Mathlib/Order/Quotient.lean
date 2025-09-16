/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.Interval.Set.Defs

/-!
### Quotient of linear order is linear order

Let `α` be a linear order, and consider a quotient such that every equivalence class is
`Set.OrdConnected`. We show that we can linearly order the quotient, such that 
-/

variable {α : Type*} [LinearOrder α] [Setoid α]
