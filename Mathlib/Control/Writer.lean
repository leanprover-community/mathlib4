/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, E.W.Ayers

The writer monad transformer for passing immutable state.
-/

structure WriterT (ω : Type u) (M : Type u → Type v) (α : Type u) : Type (max u v) where
  run : M (α × ω)

@[reducible]
def Writer ω := WriterT ω Id

class MonadWriter (ω : outParam (Type u)) (M : Type u → Type v) where
  tell : ω → M PUnit
  listen {α} : M α → M (α × ω)
  pass {α} : M (α × (ω → ω)) → M α

export MonadWriter (tell listen pass)

namespace WriterT

protected def runThe (ω : Type u) {M : Type u → Type v} (cmd : WriterT ω M α) : M (α × ω) := WriterT.run cmd

variable {ω : Type u} {M : Type u → Type v} [Monad M] {α β : Type u}

def monad (empty : ω) (append : ω → ω → ω) : Monad (WriterT ω M) where
  map := fun f ⟨cmd⟩ => ⟨(fun (a,w) => (f a, w)) <$> cmd⟩
  pure := fun a => ⟨pure (a, empty)⟩
  bind := fun ⟨cmd⟩ f => ⟨cmd >>= fun (a, w₁) => (fun (b, w₂) => (b, append w₁ w₂)) <$> (f a).run⟩

protected def liftTell (item : ω) : MonadLift M (WriterT ω M) where
  monadLift := fun cmd => ⟨(fun a => (a, item)) <$> cmd⟩

instance [EmptyCollection ω] [Append ω] : Monad (WriterT ω M) := monad ∅ (· ++ ·)
-- instance [Monoid ω] : Monad (WriterT ω M) := monad 1 (· * ·)
instance [EmptyCollection ω] : MonadLift M (WriterT ω M) := WriterT.liftTell ∅

instance : MonadWriter ω (WriterT ω M) where
  tell := fun w => ⟨pure (⟨⟩, w)⟩
  listen := fun ⟨cmd⟩ => ⟨(fun (a,w) => ((a,w), w)) <$> cmd⟩
  pass := fun ⟨cmd⟩ => ⟨(fun ((a,f), w) => (a, f w)) <$> cmd⟩

instance [MonadExcept ε M] : MonadExcept ε (WriterT ω M) where
  throw := fun e => ⟨throw e⟩
  tryCatch := fun ⟨cmd⟩ c => ⟨tryCatch cmd fun e => (c e).run⟩

end WriterT
