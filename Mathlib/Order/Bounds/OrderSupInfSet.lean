/-
Copyright (c) 2026 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.SetNotation

/-!

-/

@[expose] public section

variable {α : Type*} [LE α]

class OrderSupInfSet (α : Type*) [LE α] extends SupSet α, InfSet α where
  protected isLUB_sSup_of_isLUB s a : IsLUB s a → IsLUB s (sSup s)
  protected isGLB_sInf_of_isGLB s a : IsGLB s a → IsGLB s (sInf s)

attribute [to_dual self (reorder := 3 4, 5 6)] OrderSupInfSet.mk
attribute [to_dual existing] OrderSupInfSet.toSupSet
attribute [to_dual existing] OrderSupInfSet.isLUB_sSup_of_isLUB

@[to_dual]
abbrev OrderSupInfSet.ofSupSet {α : Type*} [SupSet α] [LE α]
    (isLUB_sSup_of_isLUB : ∀ (s : Set α) a, IsLUB s a → IsLUB s (sSup s)) :
    OrderSupInfSet α where
  isLUB_sSup_of_isLUB := isLUB_sSup_of_isLUB
  sInf s := sSup (lowerBounds s)
  isGLB_sInf_of_isGLB _ _ h := isLUB_lowerBounds.mp (isLUB_sSup_of_isLUB _ _ h.isLUB)

open Classical in
noncomputable abbrev OrderSupInfSet.choose {α : Type*} [LE α] (d : α) :
    OrderSupInfSet α where
  sSup s := if h : ∃ x, IsLUB s x then h.choose else d
  sInf s := if h : ∃ x, IsGLB s x then h.choose else d
  isLUB_sSup_of_isLUB _ _ h := dif_pos (Exists.intro _ h) ▸ choose_spec _
  isGLB_sInf_of_isGLB _ _ h := dif_pos (Exists.intro _ h) ▸ choose_spec _

@[to_dual]
theorem isLUB_sSup_of_isLUB [OrderSupInfSet α] {s : Set α} {a : α} :
    IsLUB s a → IsLUB s (sSup s) :=
  OrderSupInfSet.isLUB_sSup_of_isLUB _ _

@[to_dual] protected alias IsLUB.isLUB_sSup := isLUB_sSup_of_isLUB

@[to_dual]
theorem exists_isLUB_iff_isLUB_sSup [OrderSupInfSet α] {s : Set α} :
    (∃ a, IsLUB s a) ↔ IsLUB s (sSup s) :=
  ⟨fun ⟨_, h⟩ ↦ h.isLUB_sSup, fun h ↦ ⟨_, h⟩⟩
