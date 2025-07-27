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
  isLUB_sSup_of_exists_isLUB (s : Set α) : (∃ x, IsLUB s x) → IsLUB s (sSup s)

open Classical in
noncomputable instance Preorder.toLawfulSupPreorder [Preorder α] [Inhabited α] :
    LawfulSupPreorder α where
  sSup s := if hs : ∃ x, IsLUB s x then Classical.choose hs else default
  isLUB_sSup_of_exists_isLUB s := by
    intro ⟨x, hs⟩
    rw [dif_pos]
    exact Classical.choose_spec ⟨x, hs⟩

class LawfulInfPreorder (α) extends Preorder α, InfSet α where
  isGLB_sInf_of_exists_isGLB (s : Set α) : (∃ x, IsGLB s x) → IsGLB s (sInf s)

open Classical in
noncomputable instance Preorder.toLawfulInfPreorder [Preorder α] [Inhabited α] :
    LawfulInfPreorder α where
  sInf s := if hs : ∃ x, IsGLB s x then Classical.choose hs else default
  isGLB_sInf_of_exists_isGLB s := by
    intro ⟨x, hs⟩
    rw [dif_pos]
    exact Classical.choose_spec ⟨x, hs⟩

class LawfulPreorder (α) extends LawfulSupPreorder α, LawfulInfPreorder α

open Classical in
noncomputable instance Preorder.toLawfulPreorder [Preorder α] [Inhabited α] :
    LawfulPreorder α where
