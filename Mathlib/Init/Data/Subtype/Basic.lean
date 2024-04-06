/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Std.Logic
import Mathlib.Mathport.Rename

#align_import init.data.subtype.basic from "leanprover-community/lean"@"855e5b74e3a52a40552e8f067169d747d48743fd"

/-! # Subtypes

These are ported from the Lean 3 standard library file `init/data/subtype/basic.lean`.
-/

open Decidable

universe u

namespace Subtype

theorem exists_of_subtype {α : Type u} {p : α → Prop} : { x // p x } → ∃ x, p x
  | ⟨a, h⟩ => ⟨a, h⟩
#align subtype.exists_of_subtype Subtype.exists_of_subtype

variable {α : Type u} {p : α → Prop}

theorem tag_irrelevant {a : α} (h1 h2 : p a) : mk a h1 = mk a h2 :=
  rfl
#align subtype.tag_irrelevant Subtype.tag_irrelevant

#align subtype.eq Subtype.eq

theorem ne_of_val_ne {a1 a2 : { x // p x }} : val a1 ≠ val a2 → a1 ≠ a2 :=
  mt <| congr_arg _
#align subtype.ne_of_val_ne Subtype.ne_of_val_ne

#align subtype.eta Subtype.eta

end Subtype

open Subtype

/-- If there is some element satisfying the predicate, then the subtype is inhabited. -/
def Subtype.inhabited {α : Type u} {p : α → Prop} {a : α} (h : p a) : Inhabited { x // p x } :=
  ⟨⟨a, h⟩⟩
#align subtype.inhabited Subtype.inhabited
