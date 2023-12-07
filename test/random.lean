import Mathlib.Control.Random
import Mathlib.Tactic.NormNum

open Random

section Rand

/--
info: 44
-/
#guard_msgs in
#eval do
  IO.runRandWith 257 (show Rand _ from do
    let i ← randBound Int 3 30 (by norm_num)
    let j ← randBound Int 4 40 (by norm_num)
    return i.1 + j.1)

-- using higher universes
/--
info: ULift.up 17
-/
#guard_msgs in
#eval do
  IO.runRandWith 257 (show Rand _ from do
    let i ← rand (ULift.{3} (Fin 20))
    return i)

end Rand

section RandT

-- using the monad transformer
/--
info: Got 15
Got 29
44
-/
#guard_msgs in
#eval do
  IO.runRandWith 257 (show RandT IO _ from do
    let i ← randBound Int 3 30 (by norm_num)
    IO.println s!"Got {i}"
    let j ← randBound Int 4 40 (by norm_num)
    IO.println s!"Got {j}"
    return i.1 + j.1)

end RandT
