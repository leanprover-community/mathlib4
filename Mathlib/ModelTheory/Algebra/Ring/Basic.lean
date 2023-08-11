/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

namespace FirstOrder

namespace Language

inductive RingFunctions : ℕ → Type
  | add : RingFunctions 2
  | mul : RingFunctions 2
  | neg : RingFunctions 1
  | zero : RingFunctions 0
  | one : RingFunctions 0

protected def ring : Language :=
  { Functions := RingFunctions
    Relations := fun _ => Empty }

end Language

end FirstOrder
