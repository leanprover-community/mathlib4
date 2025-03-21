import Mathlib.Algebra.Lie.Weights.Killing
import Mathlib.LinearAlgebra.RootSystem.Basic
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import Mathlib.Algebra.Algebra.Rat
import LeanCopilot

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
noncomputable def theta {α : Weight K H L} {h e f : L} (hα : α.IsNonZero) (ht : IsSl2Triple h e f)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (- α)) (t : Kˣ) : L ≃ₗ⁅K⁆ L := by
  let D1 := LieDerivation.instDerivation K L (t • e)
  let D2 := LieDerivation.instDerivation K L (t⁻¹ • f)
  have he' : t • e ∈ rootSpace H α := by
    apply Submodule.smul_mem
    exact he
  have hf' : t⁻¹ • f ∈ rootSpace H (- α) := by
    apply Submodule.smul_mem
    exact hf
  have n₀ : ((- α) : H → K) ≠ 0 := neg_ne_zero.mpr hα
  have n₁ : IsNilpotent D1.toLinearMap := LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hα he'
  have n₂ : IsNilpotent D2.toLinearMap := LieAlgebra.isNilpotent_ad_of_mem_rootSpace H n₀ hf'
  exact LieEquiv.trans (LieEquiv.trans (LieDerivation.exp D1 n₁) (LieDerivation.exp D2 n₂))
    (LieDerivation.exp D1 n₁)

/-
lemma theta_apply {α : Weight K H L} {h e f : L} (hα : α.IsNonZero) (ht : IsSl2Triple h e f)
    (he : e ∈ rootSpace H α) (hf : f ∈ rootSpace H (- α)) (t : Kˣ) : theta H hα ht he hf t =
      LieDerivation.exp (LieDerivation.instDerivation K L e) (LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hα he) ∘
      LieDerivation.exp (LieDerivation.instDerivation K L f) (LieAlgebra.isNilpotent_ad_of_mem_rootSpace H (neg_ne_zero.mpr hα) hf) ∘
      LieDerivation.exp (LieDerivation.instDerivation K L e) (LieAlgebra.isNilpotent_ad_of_mem_rootSpace H hα he) := by
  ext x
  dsimp [theta]
-/

end Theta

end LieAlgebra
