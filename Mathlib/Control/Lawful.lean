/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

import Mathlib.Tactic.Basic

/-!
# Functor Laws, applicative laws, and monad Laws
-/

universe u v

namespace StateT

section

variable {σ : Type u} {m : Type u → Type v} {α β : Type u}

/--
`StateT` doesn't require a constructor, but it appears confusing to declare the
following theorem as a simp theorem.
```lean
@[simp]
theorem run_fun (f : σ → m (α × σ)) (st : σ) : StateT.run (fun s => f s) st = f st :=
  rfl
```
If we declare this theorem as a simp theorem, `StateT.run f st` is simplified to `f st` by eta
reduction. This breaks the structure of `StateT`.
So, we declare a constructor-like definition `StateT.mk` and a simp theorem for it.
-/
protected def mk (f : σ → m (α × σ)) : StateT σ m α := f

@[simp]
theorem run_mk (f : σ → m (α × σ)) (st : σ) : StateT.run (StateT.mk f) st = f st :=
  rfl

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

@[simp]
theorem run_monadMap {n} [MonadFunctorT n m] (f : ∀ {α}, n α → n α) :
    (monadMap (@f) x : ExceptT ε m α).run = monadMap (@f) x.run :=
  rfl

end ExceptT

namespace ReaderT

section

variable {m : Type u → Type v}
variable {α σ : Type u}

/--
`ReaderT` doesn't require a constructor, but it appears confusing to declare the
following theorem as a simp theorem.
```lean
@[simp]
theorem run_fun (f : σ → m α) (r : σ) : ReaderT.run (fun r' => f r') r = f r :=
  rfl
```
If we declare this theorem as a simp theorem, `ReaderT.run f st` is simplified to `f st` by eta
reduction. This breaks the structure of `ReaderT`.
So, we declare a constructor-like definition `ReaderT.mk` and a simp theorem for it.
-/
protected def mk (f : σ → m α) : ReaderT σ m α := f

@[simp]
theorem run_mk (f : σ → m α) (r : σ) : ReaderT.run (ReaderT.mk f) r = f r :=
  rfl

end

end ReaderT
