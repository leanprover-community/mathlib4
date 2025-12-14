/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

public import Mathlib.Tactic.Basic

/-!
# Functor Laws, applicative laws, and monad Laws
-/

@[expose] public section

universe u v

namespace StateT

section

variable {σ : Type u} {m : Type u → Type v} {α β : Type u}

/-- A copy of `LawfulFunctor.map_const` for `StateT` that holds even if `m` is not lawful. -/
protected lemma map_const [Monad m] :
    (Functor.mapConst : α → StateT σ m β → StateT σ m α) = Functor.map ∘ Function.const β :=
  rfl

@[simp] lemma run_mapConst [Monad m] [LawfulMonad m] (x : StateT σ m α) (y : β) (st : σ) :
    (Functor.mapConst y x).run st = Prod.map (Function.const α y) id <$> x.run st := run_map _ _ _

end

end StateT

namespace ExceptT

variable {α ε : Type u} {m : Type u → Type v} (x : ExceptT ε m α)

attribute [simp] run_bind

@[simp]
theorem run_monadLift {n} [Monad m] [MonadLiftT n m] (x : n α) :
    (monadLift x : ExceptT ε m α).run = Except.ok <$> (monadLift x : m α) :=
  rfl

end ExceptT
