/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

instance : LawfulFunctor Option where
  map_const := rfl
  id_map x := by cases x <;> rfl
  comp_map f g x := by cases x <;> rfl
