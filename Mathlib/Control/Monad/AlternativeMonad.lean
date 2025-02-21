/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Lawful
import Mathlib.Control.Monad.Basic

/-!
# Laws for Monads with Failure

Definitions for monads that also have an `Aleternative` instance while sharing the underlying
`Applicative` instance, and a class `LawfulAlternative` for types where the failure and monad
structures are compatible in a natural way.

`Option`/`OptionT` are the most basic examples, but transformers like `StateT` also preserve
the lawfullness of the underlying monad.

## Tags

functor, applicative, monad, simp

-/

universe u v w

/-- `AlternativeMonad m` means that `m` has both a `Monad` and `Alternative` instance which share
are equal as `Applicative` instances. -/
class AlternativeMonad (m : Type u → Type v) extends Alternative m, Monad m

class LawfulAlternative (m : Type u → Type v) [AlternativeMonad m] extends LawfulMonad m where
  failure_bind {α β : Type u} (g : α → m β) : failure >>= g = failure
  orElse_failure {α : Type u} (x : m α) : (x <|> failure) = x
  failure_orElse {α : Type u} (y : m α) : (failure <|> y) = y

export LawfulAlternative (failure_bind orElse_failure failure_orElse)
attribute [simp] failure_bind orElse_failure failure_orElse

variable {m : Type u → Type v} {α β σ : Type u}

@[simp] lemma map_failure [AlternativeMonad m] [LawfulAlternative m] (f : α → β) :
    f <$> (failure : m α) = failure := by
  rw [map_eq_bind_pure_comp, failure_bind]

@[simp] lemma failure_seq [AlternativeMonad m] [LawfulAlternative m] (x : m α) :
    (failure : m (α → β)) <*> x = failure := by
  rw [seq_eq_bind, failure_bind]

section move

lemma bind_eq_self [Monad m] [LawfulMonad m] (x : m α) {f : α → m α}
    (h : ∀ a, f a = pure a) : x >>= f = x := by
  refine (bind_congr h).trans (bind_pure x)

end move

namespace Option

instance : AlternativeMonad Option.{u} where

instance : LawfulAlternative Option.{u} where
  failure_bind _ := rfl
  orElse_failure := Option.orElse_none
  failure_orElse := Option.none_orElse

end Option

namespace OptionT

@[simp] lemma run_failure [Monad m] : (failure : OptionT m α).run = pure none := rfl

protected lemma orElse_def [Monad m] (x : OptionT m α) (y : Unit → OptionT m α) :
    @HOrElse.hOrElse _ _ _ _ x y = OptionT.orElse x y := rfl

@[simp] lemma run_orElse [Monad m] (x : OptionT m α) (y : Unit → OptionT m α) :
    OptionT.run (OptionT.orElse x y) =
      (do match (← x.run) with | some a => pure (some a) | _  => (y ()).run) := rfl

@[simp] lemma orElse_failure [Monad m] [LawfulMonad m] (x : OptionT m α) :
    OptionT.orElse x (fun _ => failure) = x :=
  bind_eq_self x.run fun | some _ => rfl | none => rfl

@[simp] lemma failure_orElse [Monad m] [LawfulMonad m] (y : Unit → OptionT m α) :
    OptionT.orElse failure y = y () := by
  simp [OptionT.ext_iff]

instance [Monad m] : AlternativeMonad (OptionT m) where

instance [Monad m] [LawfulMonad m] : LawfulAlternative (OptionT m) where
  failure_bind g := by simp_rw [OptionT.ext_iff, run_bind, run_failure, pure_bind]
  orElse_failure := OptionT.orElse_failure
  failure_orElse y := OptionT.failure_orElse (fun _ => y)

end OptionT

namespace StateT

@[simp] lemma run_failure [AlternativeMonad m] :
    (failure : StateT σ m α).run = fun _ => failure := rfl

instance [AlternativeMonad m] {σ : Type u} : AlternativeMonad (StateT σ m) where

instance [AlternativeMonad m] [LawfulAlternative m] : LawfulAlternative (StateT σ m) where
  failure_bind g := by sorry
  orElse_failure := sorry
  failure_orElse := sorry

end StateT
