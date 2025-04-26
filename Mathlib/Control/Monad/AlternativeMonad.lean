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
# Laws for Monads with Failure

Definitions for monads that also have an `Alternative` instance while sharing the underlying
`Applicative` instance, and a class `LawfulAlternative` for types where the failure and monad
structures are compatible in a natural way. More specifically they satisfy:

* `failure >>= g = failure`
* `x <|> failure = x`
* `failure <|> y = y`

`Option`/`OptionT` are the most basic examples, but transformers like `StateT` also preserve
the lawfullness of this on the underlying monad.

We also include an additional condition for `mapConst`, as it is not necessarilly equal to the
composition of map with a constant function, and is used in definitions like `success`.
The law `do _ ← x; failure = failure` is true for monads like `Option` and `List` that don't
have any "side effects" to execution, but not for something like `OptionT` on some monads,
so we don't include this condition.

## Tags

monad, alternative, failure
-/

universe u v w


namespace StateT

variable {m : Type u → Type v} [AlternativeMonad m] {σ : Type u}

instance  [LawfulMonad m] [LawfulAlternative m] : LawfulAlternative (StateT σ m) where
  map_failure _ := StateT.ext fun _ => by rw [map_failure _]
  failure_seq _ := StateT.ext fun _ => by rw [failure_seq _]
  orElse_failure _ := StateT.ext fun _ => orElse_failure _
  failure_orElse _ := StateT.ext fun _ => failure_orElse _
  orElse_assoc _ _ _ := StateT.ext fun _ => orElse_assoc _ _ _
  map_orElse _ _ _ := StateT.ext fun _ => by rw [map_orElse _ _ _]

end StateT

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
