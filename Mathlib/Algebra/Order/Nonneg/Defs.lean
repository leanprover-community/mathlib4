/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Logic.Function.Defs
public import Mathlib.Tactic.Ext

/-!
# The type of nonnegative elements

This file defines the type `Nonneg α` of nonnegative elements of a type `α` equipped with a zero
and a `≤`.

The order structure on `Nonneg α` is set up in `Mathlib/Algebra/Order/Nonneg/Lattice.lean`, and
the algebraic structure in `Mathlib/Algebra/Order/Nonneg/Basic.lean`.

## Implementation notes

`Nonneg α` is a structure rather than a type synonym for the subtype `{x : α // 0 ≤ x}`, so that
the two are not definitionally equal and `Subtype`'s instances do not leak to `Nonneg α` (and
therefore to `ℝ≥0`, `ℚ≥0`).

Note that we could instead use `Set.Ici (0 : α)`. However, using an explicit structure has a big
advantage: when writing an element explicitly with a proof of nonnegativity as `⟨x, hx⟩`, the `hx`
is expected to have type `0 ≤ x`. If we used `Ici 0`, then it would be expected to have type
`x ∈ Ici 0`. Although these types are definitionally equal, this often confuses the elaborator.
Similar problems arise when doing cases on an element.
-/

@[expose] public section

variable {α : Type*}

/-- The type of nonnegative elements of `α`. -/
@[ext]
structure Nonneg (α : Type*) [Zero α] [LE α] where
  /-- The underlying element of `α` of a nonnegative element. -/
  val : α
  /-- The underlying element of a nonnegative element is nonnegative. -/
  val_nonneg : 0 ≤ val

namespace Nonneg

attribute [coe] val

variable [Zero α] [LE α] {a b : Nonneg α} {x : α}

instance : CoeOut (Nonneg α) α := ⟨val⟩

@[simp, norm_cast] lemma coe_mk (hx : 0 ≤ x) : ((⟨x, hx⟩ : Nonneg α) : α) = x := rfl

@[simp] lemma mk_val (a : Nonneg α) : (⟨a.val, a.val_nonneg⟩ : Nonneg α) = a := rfl

lemma val_injective : Function.Injective (val : Nonneg α → α) := fun _ _ ↦ Nonneg.ext

@[simp, norm_cast] lemma coe_inj : (a : α) = b ↔ a = b :=
  ⟨fun h ↦ val_injective h, congrArg val⟩

@[norm_cast] lemma coe_ne_coe : (a : α) ≠ b ↔ a ≠ b := not_congr coe_inj

protected lemma «forall» {p : Nonneg α → Prop} : (∀ a, p a) ↔ ∀ x hx, p ⟨x, hx⟩ :=
  ⟨fun h _ _ ↦ h _, fun h ⟨_, hx⟩ ↦ h _ hx⟩

protected lemma «exists» {p : Nonneg α → Prop} : (∃ a, p a) ↔ ∃ x hx, p ⟨x, hx⟩ :=
  ⟨fun ⟨⟨_, hx⟩, h⟩ ↦ ⟨_, hx, h⟩, fun ⟨_, hx, h⟩ ↦ ⟨⟨_, hx⟩, h⟩⟩

end Nonneg
