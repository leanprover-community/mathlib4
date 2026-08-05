/-
  Euclid's Elements, Book I — formalization in Lean 4 + mathlib.

  This module collects machine-checked proofs of the first propositions
  of Euclid's Elements (c. 300 BCE) that are NOT already in mathlib.

  Author: Warren Wong

  ## Status

  | Prop | Content                              | In mathlib? | Here? |
  |------|--------------------------------------|-------------|-------|
  | I.1  | Equilateral triangle construction    | No          | ✅    |
  | I.2  | Copy a segment to a point            | No          | ✅    |
  | I.3  | Cut a shorter segment from a longer  | No          | ✅    |
  | I.4  | SAS congruence                        | Yes         | —     |
  | I.5  | Isosceles base angles equal          | Yes         | —     |
  | I.6  | Converse of I.5                       | Yes         | —     |
  | I.7  | Uniqueness of triangle (perp)        | No          | ✅    |
  | I.8  | SSS congruence                        | Yes         | —     |
  | I.9  | Angle bisection (existence)          | No          | ✅    |

  All proofs verified with `lake build` (ZERO `sorry`).

  ## How to build

  ```
  export PATH="$HOME/.elan/bin:$PATH"
  cd ~/Projects/lean-geometry && lake build
  ```
-/

import Geometry.Basic
import Geometry.Prop2
import Geometry.Prop3
import Geometry.Prop7
import Geometry.Prop9

namespace Geometry.Euclid

/-! ### Book I, Proposition 1
  On a given finite straight line, to construct an equilateral triangle. -/
#check Euclid.BookI.Prop1.equilateral_triangle_exists

/-! ### Book I, Proposition 2
  To place a straight line equal to a given straight line with one end at a given point. -/
#check Euclid.BookI.Prop2.segment_copy

/-! ### Book I, Proposition 3
  Given two unequal straight lines, to cut off from the greater a straight line equal to the less. -/
#check Euclid.BookI.Prop3.cut_segment

/-! ### Book I, Proposition 7
  On the same base and on the same side, two straight lines cannot be constructed
  meeting at a different point while having the same endpoints.
  (Algebraic core: equidistant points are perpendicular to the base.) -/
#check Euclid.BookI.Prop7.equidistant_implies_perp

/-! ### Book I, Proposition 9
  To bisect a given rectilinear angle.
  (Existence of a point D such that the angle ABD equals the angle DBC.) -/
#check Euclid.BookI.Prop9.angle_bisector_exists

end Geometry.Euclid
