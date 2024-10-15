import Mathlib.Deprecated.AlgebraClasses
import Mathlib.Logic.Equiv.Basic

variable {α₁ β₁ : Type*} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁)

set_option linter.deprecated false

@[deprecated (since := "2024-09-11")]
instance [IsLeftCancel α₁ f] : IsLeftCancel β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  ⟨e.surjective.forall₃.2 fun x y z => by simpa using @IsLeftCancel.left_cancel _ f _ x y z⟩

@[deprecated (since := "2024-09-11")]
instance [IsRightCancel α₁ f] : IsRightCancel β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  ⟨e.surjective.forall₃.2 fun x y z => by simpa using @IsRightCancel.right_cancel _ f _ x y z⟩
