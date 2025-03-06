/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Deprecated.AlgebraClasses
import Mathlib.Logic.Equiv.Defs
/-!
# Note about deprecated files

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

# Unbundled algebra classes and `Equiv`

This file contains a few deprecated results on the `Is*` classes introduced in
`Mathlib/Deprecated/AlgebraClasses.lean` that involve the `Equiv` type.
-/

variable {α₁ β₁ : Type*} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁)

set_option linter.deprecated false

@[deprecated "No deprecation message was provided." (since := "2024-09-11")]
instance [IsLeftCancel α₁ f] : IsLeftCancel β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  ⟨e.surjective.forall₃.2 fun x y z => by simpa using @IsLeftCancel.left_cancel _ f _ x y z⟩

@[deprecated "No deprecation message was provided." (since := "2024-09-11")]
instance [IsRightCancel α₁ f] : IsRightCancel β₁ (e.arrowCongr (e.arrowCongr e) f) :=
  ⟨e.surjective.forall₃.2 fun x y z => by simpa using @IsRightCancel.right_cancel _ f _ x y z⟩
