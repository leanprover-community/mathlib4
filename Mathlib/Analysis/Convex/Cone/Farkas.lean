import Mathlib.Analysis.Convex.Cone.Caratheodory
import Mathlib.Analysis.Convex.Cone.Proper
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

variable {𝕜 : Type*} {E : Type*} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable {m n : Type*} [Fintype m] [Fintype n]

-- STEPS:
-- 1. Define {A x | x ≥ 0} as a cone
-- 2. Show this cone is spanned by the columns of A
-- 3. Show this cone is spanned by linearly independent columns of A
-- 4. Show this is union of cones spanned by subsets of linearly independent columns of A
-- 5. Show this is union of {B x | x ≥ 0} where B is a square matrix with linearly independent columns
-- 6. Show this is union of {B x | x ≥ 0} where B is invertible
-- 7. Show multiplication by invertible matrix is a proper map
-- 8. Show {B x | x ≥ 0} is a proper cone
-- 9. Conclude {A x | x ≥ 0} is a proper cone
