import Mathlib.CategoryTheory.Monoidal.Internal.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

open CategoryTheory Limits

noncomputable section

-- We verify that we have successfully created special shapes of limits in `Mon_ C`,
-- assuming that only those special shapes existed in `C`.

-- To avoid unnecessarily adding imports in `Mathlib/CategoryTheory/Monoidal/Internal/Limits.lean`
-- this check lives in the test suite.

example (D : Type u) [Category.{v} D] [MonoidalCategory D] [HasTerminal D] :
  (⊤_ (Mon_ D)).X ≅ (⊤_ D) := PreservesTerminal.iso (Mon_.forget D)

example (D : Type u) [Category.{v} D] [MonoidalCategory D] [HasBinaryProducts D] (A B : Mon_ D) :
  (prod A B).X ≅ prod A.X B.X := PreservesLimitPair.iso (Mon_.forget D) A B
