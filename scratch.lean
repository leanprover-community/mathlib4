import Mathlib.Data.Pi.Algebra
-- import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Real.Basic

-- Example 1: succeeds
example {α R : Type*} [CommRing R] (f : α → R) (r : R) (a : α) :
    (r • f) a = r • (f a) := by
  simp only [Pi.smul_apply] -- succeeds

-- Example 2: fails!
example {α R : Type*} [CommRing R] (f : α → R) (r : R) (a : α) :
    (r • f) a = r • (f a) := by
  let bar : SMul R R := SMulZeroClass.toSMul
  simp only [Pi.smul_apply] -- Fails!

set_option trace.Meta.synthInstance true in
def foo : Algebra.toSMul = SMulZeroClass.toSMul (M := ℝ) (A := ℝ) := by with_reducible_and_instances rfl
def bar : Algebra.toSMul = SMulZeroClass.toSMul (M := ℝ) (A := ℝ) := rfl

set_option pp.all true in
#print foo

set_option pp.all true in
#print bar

/-
@rfl.{1} (SMul.{0, 0} Real Real)
  (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiringReal Real.semiring
    (@NormedAlgebra.toAlgebra.{0, 0} Real Real Real.normedField
      (@SeminormedCommRing.toSeminormedRing.{0} Real
        (@NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing))
      (@NormedAlgebra.id.{0} Real Real.normedField)))

@rfl.{1} (SMul.{0, 0} Real Real)
  (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiringReal Real.semiring
    (@Algebra.id.{0} Real Real.instCommSemiringReal))
-/
