/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/

import Mathlib.Mathport.Rename
import Mathlib.Tactic.Basic

#align_import init.control.lawful from "leanprover-community/lean"@"9af482290ef68e8aaa5ead01aa7b09b7be7019fd"

/-! ## Functor Laws, applicative laws, and monad Laws -/

set_option autoImplicit true

universe u v

#align is_lawful_functor LawfulFunctor
#align is_lawful_functor.map_const_eq LawfulFunctor.map_const
#align is_lawful_functor.id_map LawfulFunctor.id_map
#align is_lawful_functor.comp_map LawfulFunctor.comp_map

#align is_lawful_applicative LawfulApplicative
#align is_lawful_applicative.seq_left_eq LawfulApplicative.seqLeft_eq
#align is_lawful_applicative.seq_right_eq LawfulApplicative.seqRight_eq
#align is_lawful_applicative.pure_seq_eq_map LawfulApplicative.pure_seq
#align is_lawful_applicative.map_pure LawfulApplicative.map_pure
#align is_lawful_applicative.seq_pure LawfulApplicative.seq_pure
#align is_lawful_applicative.seq_assoc LawfulApplicative.seq_assoc

#align pure_id_seq pure_id_seq

#align is_lawful_monad LawfulMonad
#align is_lawful_monad.bind_pure_comp_eq_map LawfulMonad.bind_pure_comp
#align is_lawful_monad.bind_map_eq_seq LawfulMonad.bind_map
#align is_lawful_monad.pure_bind LawfulMonad.pure_bind
#align is_lawful_monad.bind_assoc LawfulMonad.bind_assoc

#align bind_pure bind_pure

#align bind_ext_congr bind_congr

#align map_ext_congr map_congr

#align id.map_eq Id.map_eq

#align id.bind_eq Id.bind_eq

#align id.pure_eq Id.pure_eq

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
#align state_t.mk StateT.mk

@[simp]
theorem run_mk (f : σ → m (α × σ)) (st : σ) : StateT.run (StateT.mk f) st = f st :=
  rfl

#align state_t.ext StateTₓ.ext

#align state_t.run_pure StateTₓ.run_pure

#align state_t.run_bind StateTₓ.run_bind

#align state_t.run_map StateTₓ.run_map

#align state_t.run_monad_lift StateTₓ.run_monadLift

#align state_t.run_monad_map StateTₓ.run_monadMap

-- Porting note: `StateT.adapt` is removed.
#noalign state_t.run_adapt

#align state_t.run_get StateTₓ.run_get

#align state_t.run_put StateTₓ.run_set

end

end StateT

namespace ExceptT

variable {α β ε : Type u} {m : Type u → Type v} (x : ExceptT ε m α)

#align except_t.ext ExceptTₓ.ext

-- Porting note: This is proven by proj reduction in Lean 3.
@[simp]
theorem run_mk (x : m (Except ε α)) : ExceptT.run (ExceptT.mk x) = x :=
  rfl

variable [Monad m]

#align except_t.run_pure ExceptTₓ.run_pure

attribute [simp] run_bind
#align except_t.run_bind ExceptTₓ.run_bind

#align except_t.run_map ExceptTₓ.run_map

@[simp]
theorem run_monadLift {n} [MonadLiftT n m] (x : n α) :
    (monadLift x : ExceptT ε m α).run = Except.ok <$> (monadLift x : m α) :=
  rfl
#align except_t.run_monad_lift ExceptTₓ.run_monadLift

@[simp]
theorem run_monadMap {n} [MonadFunctorT n m] (f : ∀ {α}, n α → n α) :
    (monadMap (@f) x : ExceptT ε m α).run = monadMap (@f) x.run :=
  rfl
#align except_t.run_monad_map ExceptTₓ.run_monadMap

end ExceptT

namespace ReaderT

section

variable {ρ : Type u}
variable {m : Type u → Type v}
variable {α : Type u}

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
#align reader_t.mk ReaderT.mk

@[simp]
theorem run_mk (f : σ → m α) (r : σ) : ReaderT.run (ReaderT.mk f) r = f r :=
  rfl

#align reader_t.ext ReaderTₓ.ext

#align reader_t.run_pure ReaderTₓ.run_pure

#align reader_t.run_bind ReaderTₓ.run_bind

#align reader_t.run_map ReaderTₓ.run_map

#align reader_t.run_monad_lift ReaderTₓ.run_monadLift

#align reader_t.run_monad_map ReaderTₓ.run_monadMap

#align reader_t.run_read ReaderTₓ.run_read

end

end ReaderT

namespace OptionT

variable {α β : Type u} {m : Type u → Type v} (x : OptionT m α)

@[ext] theorem ext {x x' : OptionT m α} (h : x.run = x'.run) : x = x' :=
  h
#align option_t.ext OptionTₓ.ext

-- Porting note: This is proven by proj reduction in Lean 3.
@[simp]
theorem run_mk (x : m (Option α)) : OptionT.run (OptionT.mk x) = x :=
  rfl

variable [Monad m]

@[simp]
theorem run_pure (a) : (pure a : OptionT m α).run = pure (some a) :=
  rfl
#align option_t.run_pure OptionTₓ.run_pure

@[simp]
theorem run_bind (f : α → OptionT m β) :
    (x >>= f).run = x.run >>= fun
                              | some a => OptionT.run (f a)
                              | none   => pure none :=
  rfl
#align option_t.run_bind OptionTₓ.run_bind

@[simp]
theorem run_map (f : α → β) [LawfulMonad m] : (f <$> x).run = Option.map f <$> x.run := by
  rw [← bind_pure_comp _ x.run]
  change x.run >>= (fun
                     | some a => OptionT.run (pure (f a))
                     | none   => pure none) = _
  apply bind_congr
  intro a; cases a <;> simp [Option.map, Option.bind]
#align option_t.run_map OptionTₓ.run_map

@[simp]
theorem run_monadLift {n} [MonadLiftT n m] (x : n α) :
    (monadLift x : OptionT m α).run = (monadLift x : m α) >>= fun a => pure (some a) :=
  rfl
#align option_t.run_monad_lift OptionTₓ.run_monadLift

@[simp]
theorem run_monadMap {n} [MonadFunctorT n m] (f : ∀ {α}, n α → n α) :
    (monadMap (@f) x : OptionT m α).run = monadMap (@f) x.run :=
  rfl
#align option_t.run_monad_map OptionTₓ.run_monadMap

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

instance : LawfulMonad (EIO ε) := inferInstanceAs <| LawfulMonad (EStateM _ _)
instance : LawfulMonad BaseIO := inferInstanceAs <| LawfulMonad (EIO _)
instance : LawfulMonad IO := inferInstance

instance : LawfulMonad (EST ε σ) := inferInstanceAs <| LawfulMonad (EStateM _ _)
instance : LawfulMonad (ST ε) := inferInstance
