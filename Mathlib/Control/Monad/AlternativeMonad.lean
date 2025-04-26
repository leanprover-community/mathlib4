/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Eric Wieser
-/
import Mathlib.Control.Lawful
import Mathlib.Control.Monad.Basic
import Mathlib.Data.Finset.Functor
import Batteries.Control.AlternativeMonad

/-!
# Instances of `LawfulAlternative`

## Tags

monad, alternative, failure
-/

universe u v w


namespace Finset

variable [∀ P, Decidable P]

instance : AlternativeMonad Finset where

instance : LawfulAlternative Finset where
  map_failure _ := Finset.image_empty _
  failure_seq _ := Finset.sup_empty
  orElse_failure _ := Finset.union_empty _
  failure_orElse _ := Finset.empty_union _
  orElse_assoc _ _ _ := Finset.union_assoc _ _ _ |>.symm
  map_orElse _ _ _ := Finset.image_union _ _

end Finset

namespace Set

attribute [local instance] Set.monad

instance : AlternativeMonad Set where

instance : LawfulAlternative Set where
  map_failure _ := Set.image_empty _
  failure_seq _ := Set.image2_empty_left
  orElse_failure _ := Set.union_empty _
  failure_orElse _ := Set.empty_union _
  orElse_assoc _ _ _ := Set.union_assoc _ _ _ |>.symm
  map_orElse _ _ _ := Set.image_union _ _ _

end Set

namespace List

instance : AlternativeMonad List where

instance : LawfulAlternative List where
  map_failure _ := List.map_nil
  failure_seq _ := List.flatMap_nil
  orElse_failure _ := List.append_nil _
  failure_orElse _ := List.nil_append _
  orElse_assoc _ _ _ := List.append_assoc _ _ _ |>.symm
  map_orElse _ _ _ := List.map_append

end List
