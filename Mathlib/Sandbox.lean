import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Algebra.Rat

variable (a b : ℚ) [Fact (∀ r, r ^ 2 ≠ a + b * r)]

-- Le diamant résiduel : échoue à transparence d'instances…
example : @DivisionRing.toRatAlgebra (QuadraticAlgebra ℚ a b) _ _ =
    QuadraticAlgebra.instAlgebra := by
  with_implicit rfl

-- …mais tient à transparence par défaut (c'est le « crush » de #38818) :
example : @DivisionRing.toRatAlgebra (QuadraticAlgebra ℚ a b) _ _ =
    QuadraticAlgebra.instAlgebra := rfl   -- ✓ attendu : succès
