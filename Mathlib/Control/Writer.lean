/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, E.W.Ayers

The writer monad transformer for passing immutable state.
-/

def WriterT (ω : Type u) (M : Type u → Type v) (α : Type u) : Type v :=
  M (α × ω)

@[reducible]
def Writer ω := WriterT ω Id

class MonadWriter (ω : outParam (Type u)) (M : Type u → Type v) where
  tell : ω → M PUnit
  listen {α} : M α → M (α × ω)
  pass {α} : M (α × (ω → ω)) → M α

export MonadWriter (tell listen pass)

namespace WriterT

protected def mk {ω : Type u} (cmd :  M (α × ω)) : WriterT ω M α:= cmd
protected def run {ω : Type u} (cmd : WriterT ω M α) : M (α × ω) := cmd
protected def runThe (ω : Type u) (cmd : WriterT ω M α) : M (α × ω) := cmd

variable {ω : Type u} {α β : Type u}

/-- Creates an instance of Monad, with an explicitly given empty and append operation.

Previously, this would have used an instance of `[Monoid ω]` as input.
In practice, however, WriterT is used for logging and creating lists so restricting to
monoids with `Mul` and `One` can make `WriterT` cumbersome to use.

This is used to derive instances for both `[EmptyCollection ω] [Append ω]` and `[Monoid ω]`.
-/
def monad (empty : ω) (append : ω → ω → ω) : Monad (WriterT ω M) where
  map := fun f (cmd : M _) => WriterT.mk $ (fun (a,w) => (f a, w)) <$> cmd
  pure := fun a => pure (f := M) (a, empty)
  bind := fun (cmd : M _) f =>
    WriterT.mk $ cmd >>= fun (a, w₁) =>
      (fun (b, w₂) => (b, append w₁ w₂)) <$> (f a)

/-- Lift an `M` to a `WriterT ω M`, using the given `empty` as the monoid unit. -/
protected def liftTell (empty : ω) : MonadLift M (WriterT ω M) where
  monadLift := fun cmd => WriterT.mk $ (fun a => (a, empty)) <$> cmd

instance [EmptyCollection ω] [Append ω] : Monad (WriterT ω M) := monad ∅ (· ++ ·)
instance [EmptyCollection ω] : MonadLift M (WriterT ω M) := WriterT.liftTell ∅
instance [Monoid ω] : Monad (WriterT ω M) := monad 1 (· * ·)
instance [Monoid ω] : MonadLift M (WriterT ω M) := WriterT.liftTell 1

instance : MonadWriter ω (WriterT ω M) where
  tell := fun w => WriterT.mk $ pure (⟨⟩, w)
  listen := fun cmd => WriterT.mk $ (fun (a,w) => ((a,w), w)) <$> cmd
  pass := fun cmd => WriterT.mk $ (fun ((a,f), w) => (a, f w)) <$> cmd

instance [MonadExcept ε M] : MonadExcept ε (WriterT ω M) where
  throw := fun e => WriterT.mk $ throw e
  tryCatch := fun cmd c => WriterT.mk $ tryCatch cmd fun e => (c e).run


end WriterT
