/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Lawful
import Mathlib.Control.Monad.Basic
import Mathlib.Data.Finset.Functor

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

/-- `AlternativeMonad m` means that `m` has both a `Monad` and `Alternative` instance,
which both share the same underlying `Applicative` instance.
The main example is `Option`, but many monad transformers also preserve or add this structure. -/
class AlternativeMonad (m : Type u → Type v) extends Alternative m, Monad m

/-- `LawfulAlternative m` means that the `failure` operation on `m` behaves naturally
with respect to the `bind` and `orElse` operators. -/
class LawfulAlternative (m : Type u → Type v) [AlternativeMonad m] extends LawfulMonad m where
  failure_bind {α β : Type u} (g : α → m β) : failure >>= g = failure
  mapConst_failure {α β : Type u} (y : β) : Functor.mapConst y (failure : m α) = failure
  orElse_failure {α : Type u} (x : m α) : (x <|> failure) = x
  failure_orElse {α : Type u} (y : m α) : (failure <|> y) = y

export LawfulAlternative (failure_bind mapConst_failure orElse_failure failure_orElse)
attribute [simp] failure_bind mapConst_failure orElse_failure failure_orElse

section LawfulAlternative

variable {m : Type u → Type v} [AlternativeMonad m] [LawfulAlternative m]
    {n : Type → Type v} [AlternativeMonad n] [LawfulAlternative n]


@[simp] lemma map_failure {α β} (f : α → β) : f <$> (failure : m α) = failure := by
  rw [map_eq_bind_pure_comp, failure_bind]

@[simp] lemma failure_seq {α β} (x : m α) : (failure : m (α → β)) <*> x = failure := by
  rw [seq_eq_bind, failure_bind]

@[simp] lemma succeeds_failure {α} : (succeeds (failure : n α)) = pure false := by
  rw [succeeds, mapConst_failure, failure_orElse]

@[simp] lemma tryM_failure {α} : tryM (failure : n α) = pure () := by
  rw [tryM, mapConst_failure, failure_orElse]

@[simp] lemma try?_failure {α} : try? (failure : n α) = pure none := by
  rw [try?, map_failure, failure_orElse]

end LawfulAlternative

namespace Option

instance : AlternativeMonad Option.{u} where

instance : LawfulAlternative Option.{u} where
  failure_bind _ := rfl
  mapConst_failure _ := rfl
  orElse_failure := Option.orElse_none
  failure_orElse := Option.none_orElse

end Option

namespace OptionT

variable {m : Type u → Type v} [Monad m] {α β : Type u}

@[simp] lemma run_failure : (failure : OptionT m α).run = pure none := rfl

@[simp] lemma run_orElse (x : OptionT m α) (y : OptionT m α) : (x <|> y).run =
    (do match ← x.run with | some a => pure (some a) | _  => y.run) := rfl

instance : AlternativeMonad (OptionT m) where

instance [LawfulMonad m] : LawfulAlternative (OptionT m) where
  failure_bind _ := OptionT.ext (pure_bind _ _)
  mapConst_failure y := OptionT.ext (by simp)
  orElse_failure x := OptionT.ext
    ((bind_congr (fun | some _ => rfl | none => rfl)).trans (bind_pure x))
  failure_orElse _ := pure_bind _ _

end OptionT

namespace StateT

variable {m : Type u → Type v} [AlternativeMonad m] {σ : Type u}

instance : AlternativeMonad (StateT σ m) where

instance [LawfulAlternative m] : LawfulAlternative (StateT σ m) where
  failure_bind _ := StateT.ext fun _ => failure_bind _
  mapConst_failure _ := StateT.ext fun _ => (run_mapConst _ _ _).trans (map_failure _)
  orElse_failure _ := StateT.ext fun _ => orElse_failure _
  failure_orElse _ := StateT.ext fun _ => failure_orElse _

end StateT

namespace Finset

variable [∀ P, Decidable P]

instance : AlternativeMonad Finset where

instance : LawfulAlternative Finset where
  failure_bind _ := rfl
  mapConst_failure _ := rfl
  orElse_failure := Finset.union_empty
  failure_orElse := Finset.empty_union

end Finset

namespace Set

attribute [local instance] Set.monad

instance : AlternativeMonad Set where

instance : LawfulAlternative Set where
  failure_bind := biUnion_empty
  mapConst_failure _ := image_eq_empty.mpr rfl
  orElse_failure := union_empty
  failure_orElse := empty_union

end Set

namespace List

instance : AlternativeMonad List where

instance : LawfulAlternative List where
  failure_bind _ := rfl
  mapConst_failure _ := rfl
  orElse_failure := List.append_nil
  failure_orElse := List.nil_append

end List
