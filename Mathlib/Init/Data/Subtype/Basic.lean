/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad

! This file was ported from Lean 3 source module init.data.subtype.basic
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Leanbin.Init.Logic

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

#print Subtype.eq /-
protected theorem eq : ∀ {a1 a2 : { x // p x }}, val a1 = val a2 → a1 = a2
  | ⟨x, h1⟩, ⟨x, h2⟩, rfl => rfl
#align subtype.eq Subtype.eq
-/

theorem ne_of_val_ne {a1 a2 : { x // p x }} : val a1 ≠ val a2 → a1 ≠ a2 :=
  mt <| congr_arg _
#align subtype.ne_of_val_ne Subtype.ne_of_val_ne

#print Subtype.eta /-
theorem eta (a : { x // p x }) (h : p (val a)) : mk (val a) h = a :=
  Subtype.eq rfl
#align subtype.eta Subtype.eta
-/

end Subtype

open Subtype

def Subtype.inhabited {α : Type u} {p : α → Prop} {a : α} (h : p a) : Inhabited { x // p x } :=
  ⟨⟨a, h⟩⟩
#align subtype.inhabited Subtype.inhabited

