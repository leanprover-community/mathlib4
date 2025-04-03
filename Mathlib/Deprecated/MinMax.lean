/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Deprecated.Logic
import Mathlib.Order.MinMax
/-!
# Note about deprecated files

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.
-/

universe u

variable {α : Type u} [LinearOrder α]

set_option linter.deprecated false

@[deprecated instCommutativeMax (since := "2024-09-12")]
theorem max_commutative : Commutative (α := α) max := max_comm
@[deprecated instAssociativeMax (since := "2024-09-12")]
theorem max_associative : Associative (α := α) max := max_assoc
@[deprecated instCommutativeMin (since := "2024-09-12")]
theorem min_commutative : Commutative (α := α) min := min_comm
@[deprecated instAssociativeMin (since := "2024-09-12")]
theorem min_associative : Associative (α := α) min := min_assoc
