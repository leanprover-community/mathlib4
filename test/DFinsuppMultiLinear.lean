import Mathlib.Data.DFinsupp.Multilinear
import Mathlib.Data.DFinsupp.Notation

/--
info:
fun₀
| !["hello", "complicated", "world"] => 231
| !["hello", "complicated", "test file"] => 273
| !["goodbye", "complicated", "world"] => 385
| !["goodbye", "complicated", "test file"] => 455
-/
#guard_msgs in
#eval DFinsupp.piMultilinear
  (κ := fun _ => String)
  (M := fun _ _ => ℤ)
  (N := fun _ => ℤ)
  (R := ℤ)
  (f := fun _ => MultilinearMap.mkPiAlgebra ℤ (Fin 3) ℤ)
  (x :=
    Fin.cons (fun₀ | "hello" => 3 | "goodbye" => 5) <|
    Fin.cons (fun₀ | "complicated" => 7) <|
    Fin.cons (fun₀ | "world" => 11 | "test file" => 13) <|
    IsEmpty.elim inferInstance)
