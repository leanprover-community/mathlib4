import Mathlib.LinearAlgebra.Multilinear.DFinsupp
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.Data.DFinsupp.Notation

/--
info: fun₀
  | !["hello", "complicated", "world"] => 20
  | !["hello", "complicated", "test file"] => 30
  | !["goodbye", "complicated", "world"] => -20
  | !["goodbye", "complicated", "test file"] => -30
-/
#guard_msgs in
#eval MultilinearMap.dfinsuppFamily
  (κ := fun _ => String)
  (M := fun _ _ => ℤ)
  (N := fun _ => ℤ)
  (R := ℤ)
  (f := fun _ => MultilinearMap.mkPiAlgebra ℤ (Fin 3) ℤ) ![
    fun₀ | "hello" => 1 | "goodbye" => -1,
    fun₀ | "complicated" => 10,
    fun₀ | "world" => 2 | "test file" => 3]
