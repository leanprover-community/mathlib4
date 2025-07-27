/-
Copyright (c) 2017 Pierre Quinton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Quinton
-/
import Mathlib.Order.SetNotation
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.Defs.PartialOrder

variable {α β : Type*}

class LawfulSupPreorder (α) extends Preorder α, SupSet α where
  isLUB_sSup_of_exists_isLUB (s : Set α) : ∃ x, IsLUB s x → IsLUB s (sSup s)

class LawfulInfPreorder (α) extends Preorder α, InfSet α where
  isGLB_sInf_of_exists_isGLB (s : Set α) : ∃ x, IsGLB s x → IsGLB s (sInf s)

class LawfulPreorder (α) extends LawfulSupPreorder α, LawfulInfPreorder α
