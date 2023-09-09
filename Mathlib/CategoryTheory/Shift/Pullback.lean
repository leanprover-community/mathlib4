import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

namespace CategoryTheory

open Limits

variable (C : Type*) [Category C] {A B : Type*} [AddMonoid A] [AddMonoid B]
  (φ : A →+ B) [HasShift C B]

attribute [local instance] endofunctorMonoidalCategory

namespace HasShift

noncomputable def pullback : HasShift C A where
  shift := (Discrete.addMonoidalFunctor φ).comp HasShift.shift

end HasShift

@[nolint unusedArguments]
def PullbackShift (_ : A →+ B) [HasShift C B]:= C

instance : Category (PullbackShift C φ) := by
  dsimp only [PullbackShift]
  infer_instance

noncomputable instance : HasShift (PullbackShift C φ) A := HasShift.pullback C φ

instance [HasZeroObject C] : HasZeroObject (PullbackShift C φ) := by
  dsimp [PullbackShift]
  infer_instance

instance [Preadditive C] : Preadditive (PullbackShift C φ) := by
  dsimp [PullbackShift]
  infer_instance

instance [Preadditive C] (a : A) [(shiftFunctor C (φ a)).Additive] :
    (shiftFunctor (PullbackShift C φ) a).Additive := by
  change (shiftFunctor C (φ a)).Additive
  infer_instance

end CategoryTheory
