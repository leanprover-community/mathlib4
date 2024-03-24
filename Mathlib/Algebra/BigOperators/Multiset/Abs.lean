/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Rob Lewis
-/
import Mathlib.Algebra.BigOperators.Multiset.Basic
import Mathlib.Algebra.Order.Group.Abs

#align_import algebra.big_operators.multiset.basic from "leanprover-community/mathlib"@"6c5f73fd6f6cc83122788a80a27cdd54663609f4"

/-!
# Absolute values and sums/products over multisets

This file contains lemmas on the relation between `Multiset.prod`/`Multiset.sum` and `abs`.

## Main declarations

* `Multiset.abs_sum_le_sum_abs`: the multiset version of the triangle inequality.
-/

namespace Multiset

variable {α : Type*}

theorem abs_sum_le_sum_abs [LinearOrderedAddCommGroup α] {s : Multiset α} :
    abs s.sum ≤ (s.map abs).sum :=
  le_sum_of_subadditive _ abs_zero abs_add s
#align multiset.abs_sum_le_sum_abs Multiset.abs_sum_le_sum_abs

end Multiset
