/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.LinearAlgebra.Dimension.DivisionRing

#align_import linear_algebra.free_module.rank from "leanprover-community/mathlib"@"465d4301d8da5945ef1dc1b29fb34c2f2b315ac4"

/-!

# Extra results about `Module.rank`

This file contains some extra results not in `LinearAlgebra.Dimension`.

It also contains a proof of the Erdős-Kaplansky theorem (`rank_dual_eq_card_dual_of_aleph0_le_rank`)
which says that the dimension of an infinite-dimensional dual space over a division ring
has dimension equal to its cardinality.

-/
