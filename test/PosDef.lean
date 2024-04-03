import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix
open scoped ComplexOrder

variable {n 𝕜 : Type*} [Fintype n] [IsROrC 𝕜] [DecidableEq n]
  {A : Matrix n n 𝕜} (hA : PosSemidef A)

-- test for custom elaborator
/--
info: (_ : PosSemidef A).sqrt : Matrix n n 𝕜
-/
#guard_msgs in
#check (id hA).sqrt
