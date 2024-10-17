/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Mathlib.Init
/-!
# Monad instances for `List`
-/

universe u

namespace List

variable {α : Type u}

instance instMonad : Monad List.{u} where
  pure := @List.singleton
  bind := @List.flatMap
  map := @List.map

@[simp] theorem pure_def (a : α) : pure a = [a] := rfl

instance instLawfulMonad : LawfulMonad List.{u} := LawfulMonad.mk'
  (id_map := map_id)
  (pure_bind := fun _ _ => List.append_nil _)
  (bind_assoc := List.flatMap_assoc)
  (bind_pure_comp := fun _ _ => (map_eq_flatMap _ _).symm)

instance instAlternative : Alternative List.{u} where
  failure := @List.nil
  orElse l l' := List.append l (l' ())

end List
