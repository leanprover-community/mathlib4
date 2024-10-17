import Mathlib.Data.DFinsupp.Multilinear
import Mathlib.Data.DFinsupp.Notation

/--
info: fun₀
| !["hello", "complicated", "world"] => 20
| !["hello", "complicated", "test file"] => 30
| !["goodbye", "complicated", "world"] => -20
| !["goodbye", "complicated", "test file"] => -30
-/
#guard_msgs in
#eval DFinsupp.piMultilinear
  (κ := fun _ => String)
  (M := fun _ _ => ℤ)
  (N := fun _ => ℤ)
  (R := ℤ)
  (f := fun _ => MultilinearMap.mkPiAlgebra ℤ (Fin 3) ℤ) <|
    Fin.cons (fun₀ | "hello" => 1 | "goodbye" => -1) <|
    Fin.cons (fun₀ | "complicated" => 10) <|
    Fin.cons (fun₀ | "world" => 2 | "test file" => 3) <|
    IsEmpty.elim inferInstance
