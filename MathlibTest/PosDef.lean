import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix
open scoped ComplexOrder

variable {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜] [DecidableEq n]
  {A : Matrix n n 𝕜} (hA : PosSemidef A)

-- test for custom elaborator
/--
info: (⋯ : A.PosSemidef).sqrt : Matrix n n 𝕜
-/
#guard_msgs in
#check (id hA).sqrt
