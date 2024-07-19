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

variable {σ : Type u}
variable {m : Type u → Type v}
variable {α : Type u}

/-
Porting note:
In Lean 4, `StateT` doesn't require a constructor, but it appears confusing to declare the
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

-- Porting note: `StateT.adapt` is removed.

end

end StateT

namespace ExceptT

variable {α β ε : Type u} {m : Type u → Type v} (x : ExceptT ε m α)

-- Porting note: This is proven by proj reduction in Lean 3.
@[simp]
theorem run_mk (x : m (Except ε α)) : ExceptT.run (ExceptT.mk x) = x :=
  rfl

variable [Monad m]

attribute [simp] run_bind

@[simp]
theorem run_monadLift {n} [MonadLiftT n m] (x : n α) :
    (monadLift x : ExceptT ε m α).run = Except.ok <$> (monadLift x : m α) :=
  rfl

@[simp]
theorem run_monadMap {n} [MonadFunctorT n m] (f : ∀ {α}, n α → n α) :
    (monadMap (@f) x : ExceptT ε m α).run = monadMap (@f) x.run :=
  rfl

end ExceptT

namespace ReaderT

section

variable {ρ : Type u}
variable {m : Type u → Type v}
variable {α σ : Type u}

/-
Porting note:
In Lean 4, `ReaderT` doesn't require a constructor, but it appears confusing to declare the
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

namespace OptionT

variable {α β : Type u} {m : Type u → Type v} (x : OptionT m α)

@[ext] theorem ext {x x' : OptionT m α} (h : x.run = x'.run) : x = x' :=
  h

-- Porting note: This is proven by proj reduction in Lean 3.
@[simp]
theorem run_mk (x : m (Option α)) : OptionT.run (OptionT.mk x) = x :=
  rfl

variable [Monad m]

@[simp]
theorem run_pure (a) : (pure a : OptionT m α).run = pure (some a) :=
  rfl

@[simp]
theorem run_bind (f : α → OptionT m β) :
    (x >>= f).run = x.run >>= fun
                              | some a => OptionT.run (f a)
                              | none   => pure none :=
  rfl

@[simp]
theorem run_map (f : α → β) [LawfulMonad m] : (f <$> x).run = Option.map f <$> x.run := by
  rw [← bind_pure_comp _ x.run]
  change x.run >>= (fun
                     | some a => OptionT.run (pure (f a))
                     | none   => pure none) = _
  apply bind_congr
  intro a; cases a <;> simp [Option.map, Option.bind]

@[simp]
theorem run_monadLift {n} [MonadLiftT n m] (x : n α) :
    (monadLift x : OptionT m α).run = (monadLift x : m α) >>= fun a => pure (some a) :=
  rfl

@[simp]
theorem run_monadMap {n} [MonadFunctorT n m] (f : ∀ {α}, n α → n α) :
    (monadMap (@f) x : OptionT m α).run = monadMap (@f) x.run :=
  rfl

end OptionT

instance (m : Type u → Type v) [Monad m] [LawfulMonad m] : LawfulMonad (OptionT m) :=
  LawfulMonad.mk'
    (id_map := by
      intros; apply OptionT.ext; simp only [OptionT.run_map]
      rw [map_congr, id_map]
      intro a; cases a <;> rfl)
    (bind_assoc := by
      intros; apply OptionT.ext; simp only [OptionT.run_bind, bind_assoc]
      rw [bind_congr]
      intro a; cases a <;> simp)
    (pure_bind := by intros; apply OptionT.ext; simp)

/-! ### Lawfulness of `IO`

At some point core intends to make `IO` opaque, which would break these proofs
As discussed in https://github.com/leanprover/std4/pull/416,
it should be possible for core to expose the lawfulness of `IO` as part of the opaque interface,
which would remove the need for these proofs anyway.

These are not in Batteries because Batteries does not want to deal with the churn from such a core
refactor.
-/

variable {ε σ : Type}
instance : LawfulMonad (EIO ε) := inferInstanceAs <| LawfulMonad (EStateM _ _)
instance : LawfulMonad BaseIO := inferInstanceAs <| LawfulMonad (EIO _)
instance : LawfulMonad IO := inferInstance

instance : LawfulMonad (EST ε σ) := inferInstanceAs <| LawfulMonad (EStateM _ _)
instance : LawfulMonad (ST ε) := inferInstance
