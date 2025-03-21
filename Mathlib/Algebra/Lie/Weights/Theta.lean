import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.LinearAlgebra.RootSystem.Basic
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.Algebra.Algebra.Rat

/-!
# Theta maps of Lie algebras

Text here please.

## Main definitions

  * `Theta`

## Tags

Tags here please.
-/

namespace LieAlgebra

namespace Theta

open LieModule

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  (H : LieSubalgebra K L) [LieRing.IsNilpotent H]
  [IsTriangularizable K H L] [FiniteDimensional K L]


--lemma exists_isSl2Triple_of_weight_isNonZero {α : Weight K H L} (hα : α.IsNonZero) :
--    ∃ h e f : L, IsSl2Triple h e f ∧ e ∈ rootSpace H α ∧ f ∈ rootSpace H (- α) :=


/-- In characteristic zero, the exponential of a nilpotent derivation is a Lie algebra
automorphism. -/
noncomputable def theta [IsTriangularizable K H L] {α : Weight K H L} {h e f : L} (hα : α.IsNonZero) (ht : IsSl2Triple h e f)
    (he : e ∈ rootSpace H α)  (hf : f ∈ rootSpace H (- α)) : L ≃ₗ⁅K⁆ L := by
  let D := LieDerivation.instDerivation K L e
  have n2 : IsNilpotent D.toLinearMap := by
    dsimp [D]
    apply LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hα he
  exact LieEquiv.trans (LieDerivation.exp D n2) (LieDerivation.exp D n2)


/-
lemma exp_apply [Module ℚ L] (h : IsNilpotent D.toLinearMap) :
    exp D h = IsNilpotent.exp D.toLinearMap := by
  ext x
  dsimp [exp]
  convert rfl
  subsingleton
-/

end Theta

end LieAlgebra
