/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Prod.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Nontrivial.Defs
public import Mathlib.Logic.Unique
public import Mathlib.Order.Defs.LinearOrder

import Mathlib.Tactic.Attr.Register

/-!
# Nontrivial types

Results about `Nontrivial`.
-/

@[expose] public section

variable {α : Type*} {β : Type*}

-- `x` and `y` are explicit here, as they are often needed to guide typechecking of `h`.
theorem nontrivial_of_lt [Preorder α] (x y : α) (h : x < y) : Nontrivial α :=
  ⟨⟨x, y, ne_of_lt h⟩⟩

theorem exists_pair_lt (α : Type*) [Nontrivial α] [LinearOrder α] : ∃ x y : α, x < y := by
  rcases exists_pair_ne α with ⟨x, y, hxy⟩
  cases lt_or_gt_of_ne hxy <;> exact ⟨_, _, ‹_›⟩

theorem nontrivial_iff_lt [LinearOrder α] : Nontrivial α ↔ ∃ x y : α, x < y :=
  ⟨fun h ↦ @exists_pair_lt α h _, fun ⟨x, y, h⟩ ↦ nontrivial_of_lt x y h⟩

theorem Subtype.nontrivial_iff_exists_ne (p : α → Prop) (x : Subtype p) :
    Nontrivial (Subtype p) ↔ ∃ (y : α) (_ : p y), y ≠ x := by
  simp only [_root_.nontrivial_iff_exists_ne x, Subtype.exists, Ne, Subtype.ext_iff]

open Classical in
/-- An inhabited type is either nontrivial, or has a unique element. -/
noncomputable def nontrivialPSumUnique (α : Type*) [Inhabited α] :
    Nontrivial α ⊕' Unique α :=
  if h : Nontrivial α then PSum.inl h
  else
    PSum.inr
      { default := default,
        uniq := fun x : α ↦ by
          by_contra H
          exact h ⟨_, _, H⟩ }

instance Option.nontrivial [Nonempty α] : Nontrivial (Option α) := by
  inhabit α
  exact ⟨none, some default, nofun⟩

instance nontrivial_prod_right [Nonempty α] [Nontrivial β] : Nontrivial (α × β) :=
  Prod.snd_surjective.nontrivial

instance nontrivial_prod_left [Nontrivial α] [Nonempty β] : Nontrivial (α × β) :=
  Prod.fst_surjective.nontrivial

namespace Pi

variable {I : Type*} {f : I → Type*}

open Classical in
/-- A pi type is nontrivial if it's nonempty everywhere and nontrivial somewhere. -/
theorem nontrivial_at (i' : I) [inst : ∀ i, Nonempty (f i)] [Nontrivial (f i')] :
    Nontrivial (∀ i : I, f i) := by
  letI := Classical.decEq (∀ i : I, f i)
  exact (Function.update_injective (fun i ↦ Classical.choice (inst i)) i').nontrivial

/-- As a convenience, provide an instance automatically if `(f default)` is nontrivial.

If a different index has the non-trivial type, then use `haveI := nontrivial_at that_index`.
-/
instance nontrivial [Inhabited I] [∀ i, Nonempty (f i)] [Nontrivial (f default)] :
    Nontrivial (∀ i : I, f i) :=
  nontrivial_at default

end Pi

instance Function.nontrivial [h : Nonempty α] [Nontrivial β] : Nontrivial (α → β) :=
  h.elim fun a ↦ Pi.nontrivial_at a

@[nontriviality]
protected theorem Subsingleton.le [Preorder α] [Subsingleton α] (x y : α) : x ≤ y :=
  le_of_eq (Subsingleton.elim x y)
