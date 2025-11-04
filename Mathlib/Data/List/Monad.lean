/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Mathlib.Init
import Batteries.Control.AlternativeMonad
/-!
# Monad instances for `List`
-/

universe u

namespace List

variable {α : Type u}

instance instMonad : Monad List.{u} where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f

@[simp] theorem pure_def (a : α) : pure a = [a] := rfl

instance instLawfulMonad : LawfulMonad List.{u} := LawfulMonad.mk'
  (id_map := map_id)
  (pure_bind := fun _ _ => List.append_nil _)
  (bind_assoc := fun _ _ _ => List.flatMap_assoc)
  (bind_pure_comp := fun _ _ => map_eq_flatMap.symm)

instance : AlternativeMonad List.{u} where
  failure := @List.nil
  orElse l l' := List.append l (l' ())

instance : LawfulAlternative List where
  map_failure _ := List.map_nil
  failure_seq _ := List.flatMap_nil
  orElse_failure _ := List.append_nil _
  failure_orElse _ := List.nil_append _
  orElse_assoc _ _ _ := List.append_assoc _ _ _ |>.symm
  map_orElse _ _ _ := List.map_append

end List
