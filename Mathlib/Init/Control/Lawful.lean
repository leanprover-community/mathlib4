/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

! This file was ported from Lean 3 source module init.control.lawful
! leanprover-community/lean commit 9af482290ef68e8aaa5ead01aa7b09b7be7019fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

import Mathlib.Mathport.Rename

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

variable {α β : Type u}

variable (x : StateT σ m α) (st : σ)

/-
Porting note:
In Lean 4, `StateT` doesn't require a constructor, but it appears confusing to declare the
following theorem as a simp theorem.
```lean
@[simp]
theorem run_fun (f : σ → m (α × σ)) : StateT.run (fun s => f s) st = f st :=
  rfl
```
So, we declare a constructor-like definition `StateT.mk` and a simp theorem for it.
-/

protected def mk (f : σ → m (α × σ)) : StateT σ m α := f
#align state_t.mk StateT.mk

@[simp]
theorem run_mk (f : σ → m (α × σ)) : StateT.run (StateT.mk f) st = f st :=
  rfl

#align state_t.ext StateTₓ.ext

variable [Monad m]

#align state_t.run_pure StateTₓ.run_pure

#align state_t.run_bind StateTₓ.run_bind

#align state_t.run_map StateTₓ.run_map

#align state_t.run_monad_lift StateTₓ.run_monadLift

#align state_t.run_monad_map StateTₓ.run_monadMap

@[simp]
theorem run_adapt {σ' σ''} (st : σ) (split : σ → σ' × σ'') (join : σ' → σ'' → σ)
    (x : StateT σ' m α) :
    (StateT.adapt split join x : StateT σ m α).run st = do
      let (st, ctx) := split st
      let (a, st') ← x.run st
      pure (a, join st' ctx) :=
  by delta StateT.adapt <;> rfl
#align state_t.run_adapt StateTₓ.run_adapt

#align state_t.run_get StateTₓ.run_get

#align state_t.run_put StateTₓ.run_set

end

end StateT

namespace ExceptT

variable {α β ε : Type u} {m : Type u → Type v} (x : ExceptT ε m α)

theorem ext {x x' : ExceptT ε m α} (h : x.run = x'.run) : x = x' := by
  cases x <;> cases x' <;> simp_all
#align except_t.ext ExceptTₓ.ext

variable [Monad m]

@[simp]
theorem run_pure (a) : (pure a : ExceptT ε m α).run = pure (@Except.ok ε α a) :=
  rfl
#align except_t.run_pure ExceptTₓ.run_pure

@[simp]
theorem run_bind (f : α → ExceptT ε m β) : (x >>= f).run = x.run >>= ExceptT.bindCont f :=
  rfl
#align except_t.run_bind ExceptTₓ.run_bind

@[simp]
theorem run_map (f : α → β) [LawfulMonad m] : (f <$> x).run = Except.map f <$> x.run :=
  by
  rw [← bind_pure_comp_eq_map _ x.run]
  change x.run >>= ExceptT.bindCont (pure ∘ f) = _
  apply bind_ext_congr
  intro a <;> cases a <;> simp [ExceptT.bindCont, Except.map]
#align except_t.run_map ExceptTₓ.run_map

@[simp]
theorem run_monadLift {n} [HasMonadLiftT n m] (x : n α) :
    (monadLift x : ExceptT ε m α).run = Except.ok <$> (monadLift x : m α) :=
  rfl
#align except_t.run_monad_lift ExceptTₓ.run_monadLift

@[simp]
theorem run_monadMap {m' n n'} [Monad m'] [MonadFunctorT n n' m m'] (f : ∀ {α}, n α → n' α) :
    (monadMap (@f) x : ExceptT ε m' α).run = monadMap (@f) x.run :=
  rfl
#align except_t.run_monad_map ExceptTₓ.run_monadMap

end ExceptT

instance (m : Type u → Type v) [Monad m] [LawfulMonad m] (ε : Type u) : LawfulMonad (ExceptT ε m)
    where
  id_map := by
    intros; apply ExceptT.ext; simp only [ExceptT.run_map]
    rw [map_ext_congr, id_map]
    intro a; cases a <;> rfl
  bind_pure_comp_eq_map := by
    intros; apply ExceptT.ext; simp only [ExceptT.run_map, ExceptT.run_bind]
    rw [bind_ext_congr, bind_pure_comp_eq_map]
    intro a; cases a <;> rfl
  bind_assoc := by
    intros; apply ExceptT.ext; simp only [ExceptT.run_bind, bind_assoc]
    rw [bind_ext_congr]
    intro a; cases a <;> simp [ExceptT.bindCont]
  pure_bind := by intros <;> apply ExceptT.ext <;> simp [ExceptT.bindCont]

namespace ReaderT

section

variable {ρ : Type u}

variable {m : Type u → Type v}

variable {α β : Type u}

variable (x : ReaderT ρ m α) (r : ρ)

theorem ext {x x' : ReaderT ρ m α} (h : ∀ r, x.run r = x'.run r) : x = x' := by
  cases x <;> cases x' <;> simp [show x = x' from funext h]
#align reader_t.ext ReaderTₓ.ext

variable [Monad m]

@[simp]
theorem run_pure (a) : (pure a : ReaderT ρ m α).run r = pure a :=
  rfl
#align reader_t.run_pure ReaderTₓ.run_pure

@[simp]
theorem run_bind (f : α → ReaderT ρ m β) : (x >>= f).run r = x.run r >>= fun a => (f a).run r :=
  rfl
#align reader_t.run_bind ReaderTₓ.run_bind

@[simp]
theorem run_map (f : α → β) [LawfulMonad m] : (f <$> x).run r = f <$> x.run r := by
  rw [← bind_pure_comp_eq_map _ (x.run r)] <;> rfl
#align reader_t.run_map ReaderTₓ.run_map

@[simp]
theorem run_monadLift {n} [HasMonadLiftT n m] (x : n α) :
    (monadLift x : ReaderT ρ m α).run r = (monadLift x : m α) :=
  rfl
#align reader_t.run_monad_lift ReaderTₓ.run_monadLift

@[simp]
theorem run_monadMap {m' n n'} [Monad m'] [MonadFunctorT n n' m m'] (f : ∀ {α}, n α → n' α) :
    (monadMap (@f) x : ReaderT ρ m' α).run r = monadMap (@f) (x.run r) :=
  rfl
#align reader_t.run_monad_map ReaderTₓ.run_monadMap

@[simp]
theorem run_read : (ReaderT.read : ReaderT ρ m ρ).run r = pure r :=
  rfl
#align reader_t.run_read ReaderTₓ.run_read

end

end ReaderT

instance (ρ : Type u) (m : Type u → Type v) [Monad m] [LawfulMonad m] : LawfulMonad (ReaderT ρ m)
    where
  id_map := by intros <;> apply ReaderT.ext <;> intro <;> simp
  pure_bind := by intros <;> apply ReaderT.ext <;> intro <;> simp
  bind_assoc := by intros <;> apply ReaderT.ext <;> intro <;> simp [bind_assoc]

namespace OptionT

variable {α β : Type u} {m : Type u → Type v} (x : OptionT m α)

theorem ext {x x' : OptionT m α} (h : x.run = x'.run) : x = x' := by
  cases x <;> cases x' <;> simp_all
#align option_t.ext OptionTₓ.ext

variable [Monad m]

@[simp]
theorem run_pure (a) : (pure a : OptionT m α).run = pure (some a) :=
  rfl
#align option_t.run_pure OptionTₓ.run_pure

@[simp]
theorem run_bind (f : α → OptionT m β) : (x >>= f).run = x.run >>= OptionT.bindCont f :=
  rfl
#align option_t.run_bind OptionTₓ.run_bind

@[simp]
theorem run_map (f : α → β) [LawfulMonad m] : (f <$> x).run = Option.map f <$> x.run :=
  by
  rw [← bind_pure_comp_eq_map _ x.run]
  change x.run >>= OptionT.bindCont (pure ∘ f) = _
  apply bind_ext_congr
  intro a <;> cases a <;> simp [OptionT.bindCont, Option.map, Option.bind]
#align option_t.run_map OptionTₓ.run_map

@[simp]
theorem run_monadLift {n} [HasMonadLiftT n m] (x : n α) :
    (monadLift x : OptionT m α).run = some <$> (monadLift x : m α) :=
  rfl
#align option_t.run_monad_lift OptionTₓ.run_monadLift

@[simp]
theorem run_monadMap {m' n n'} [Monad m'] [MonadFunctorT n n' m m'] (f : ∀ {α}, n α → n' α) :
    (monadMap (@f) x : OptionT m' α).run = monadMap (@f) x.run :=
  rfl
#align option_t.run_monad_map OptionTₓ.run_monadMap

end OptionT

instance (m : Type u → Type v) [Monad m] [LawfulMonad m] : LawfulMonad (OptionT m)
    where
  id_map := by
    intros; apply OptionT.ext; simp only [OptionT.run_map]
    rw [map_ext_congr, id_map]
    intro a; cases a <;> rfl
  bind_assoc := by
    intros; apply OptionT.ext; simp only [OptionT.run_bind, bind_assoc]
    rw [bind_ext_congr]
    intro a; cases a <;> simp [OptionT.bindCont]
  pure_bind := by intros <;> apply OptionT.ext <;> simp [OptionT.bindCont]
