import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finsupp.Notation
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
# Testing computability (and runtime) of antidiagonal
-/

open Finset

section
-- set_option trace.profiler true

-- `antidiagonalTuple` is faster than `finAntidiagonal` by a small constant factor
/-- info: 23426 -/
#guard_msgs in #eval (finAntidiagonal 4 50).card
/-- info: 23426 -/
#guard_msgs in #eval (Finset.Nat.antidiagonalTuple 4 50).card

end

/--
info: {fun₀ | "C" => 3,
 fun₀ | "B" => 1 | "C" => 2,
 fun₀ | "B" => 2 | "C" => 1,
 fun₀ | "B" => 3,
 fun₀ | "A" => 1 | "C" => 2,
 fun₀ | "A" => 1 | "B" => 1 | "C" => 1,
 fun₀ | "A" => 1 | "B" => 2,
 fun₀ | "A" => 2 | "C" => 1,
 fun₀ | "A" => 2 | "B" => 1,
 fun₀ | "A" => 3}
-/
#guard_msgs in
#eval finsuppAntidiag {"A", "B", "C"} 3
