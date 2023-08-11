/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

namespace FirstOrder

namespace Language

inductive RingFunc : ℕ → Type
  | add : RingFunc 2
  | mul : RingFunc 2
  | neg : RingFunc 1
  | zero : RingFunc 0
  | one : RingFunc 0

def ring : Language :=
  { Functions := RingFunc
    Relations := fun _ => Empty }

end Language

end FirstOrder
