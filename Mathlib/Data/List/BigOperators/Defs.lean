/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Data.List.Defs
import Mathlib.Algebra.Group.Defs

#align_import data.list.defs from "leanprover-community/mathlib"@"d2d8742b0c21426362a9dacebc6005db895ca963"

/-!
## Products and sums over lists

-/

namespace List

/-- Product of a list.

`List.prod [a, b, c] = ((1 * a) * b) * c` -/
@[to_additive "Sum of a list.\n\n`List.sum [a, b, c] = ((0 + a) + b) + c`"]
def prod {α} [Mul α] [One α] : List α → α :=
  foldl (· * ·) 1
#align list.prod List.prod
#align list.sum List.sum

/-- The alternating sum of a list. -/
def alternatingSum {G : Type*} [Zero G] [Add G] [Neg G] : List G → G
  | [] => 0
  | g :: [] => g
  | g :: h :: t => g + -h + alternatingSum t
#align list.alternating_sum List.alternatingSum

/-- The alternating product of a list. -/
@[to_additive existing]
def alternatingProd {G : Type*} [One G] [Mul G] [Inv G] : List G → G
  | [] => 1
  | g :: [] => g
  | g :: h :: t => g * h⁻¹ * alternatingProd t
#align list.alternating_prod List.alternatingProd

end List
