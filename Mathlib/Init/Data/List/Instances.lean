/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mathport.Rename

#align_import init.data.list.instances from "leanprover-community/lean"@"9af482290ef68e8aaa5ead01aa7b09b7be7019fd"

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

`#align` statements without corresponding declarations
(i.e. because the declaration is in Batteries or Lean) can be left here.
These will be deleted soon so will not significantly delay deleting otherwise empty `Init` files.

# Decidable and Monad instances for `List` not (yet) in `Batteries`
-/

universe u v w

namespace List

variable {α : Type u} {β : Type v} {γ : Type w}

#align list.bind_singleton List.bind_singleton
#align list.bind_singleton' List.bind_singleton'
#align list.map_eq_bind List.map_eq_bind
#align list.bind_assoc List.bind_assoc

instance instMonad : Monad List.{u} where
  pure := @List.pure
  bind := @List.bind
  map := @List.map
#align list.monad List.instMonad

@[simp] theorem pure_def (a : α) : pure a = [a] := rfl

instance instLawfulMonad : LawfulMonad List.{u} := LawfulMonad.mk'
  (id_map := map_id)
  (pure_bind := fun _ _ => List.append_nil _)
  (bind_assoc := List.bind_assoc)
  (bind_pure_comp := fun _ _ => (map_eq_bind _ _).symm)
#align list.is_lawful_monad List.instLawfulMonad

instance instAlternative : Alternative List.{u} where
  failure := @List.nil
  orElse l l' := List.append l (l' ())
#align list.alternative List.instAlternative

#noalign list.bin_tree_to_list

#align list.decidable_bex List.decidableBEx

#align list.decidable_ball List.decidableBAll

end List
