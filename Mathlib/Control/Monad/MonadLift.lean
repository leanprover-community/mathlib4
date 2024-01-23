/-
Copyright (c) 2023 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.Control.Monad.Cont
import Mathlib.Control.Monad.Writer
import Mathlib.Tactic.MonadReassoc
import Mathlib.Tactic.SimpRw
-- TODO: Implement WriterT instances

universe u v₁ v₂ v₃

namespace MonadLift

@[always_inline]
def as_MonadLiftT {m : Type u → Type v₁} {n : Type u → Type v₂}
  [MonadLift m n] : MonadLiftT m n where monadLift := MonadLift.monadLift

end MonadLift

class LawfulMonadLift (m : Type u → Type v₁) (n : Type u → Type v₂)
    [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [MonadLift m n] where
  monadLift_pure : ∀ {α} (x : α), MonadLift.monadLift (pure x : m α) = (pure x : n α)
  monadLift_bind : ∀ {α β} (x : m α) (f : α → m β),
    (MonadLift.monadLift (x >>= f) : n β)
    = MonadLift.monadLift x >>= MonadLift.monadLift ∘ f

attribute [reassocM] LawfulMonadLift.monadLift_pure LawfulMonadLift.monadLift_bind

class LawfulMonadLiftT (m : Type u → Type v₁) (n : Type u → Type v₂)
    [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [MonadLiftT m n] where
  monadLift_pure : ∀ {α} (x : α), monadLift (pure x : m α) = (pure x : n α)
  monadLift_bind : ∀ {α β} (x : m α) (f : α → m β),
    (monadLift (x >>= f) : n β) = monadLift x >>= monadLift ∘ f

export LawfulMonadLiftT (monadLift_pure monadLift_bind)

attribute [reassocM] monadLift_pure monadLift_bind

instance (m : Type u → Type v₁) [Monad m] [LawfulMonad m] : LawfulMonadLiftT m m where
  monadLift_pure _   := rfl
  monadLift_bind _ _ := rfl

instance (m : Type u → Type v₁) (n : Type u → Type v₂) (o : Type u → Type v₃)
  [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [LawfulMonad o]
  [MonadLift n o] [MonadLiftT m n] [LawfulMonadLift n o] [LawfulMonadLiftT m n]
    : LawfulMonadLiftT m o where
  monadLift_pure x   :=
    Eq.trans (congrArg MonadLift.monadLift $ monadLift_pure x)
             (LawfulMonadLift.monadLift_pure x)
  monadLift_bind x f :=
    Eq.trans (congrArg MonadLift.monadLift $ monadLift_bind x f)
    $ Eq.trans (LawfulMonadLift.monadLift_bind (monadLift x) (monadLift ∘ f))
    $ congrArg _ $ Eq.symm $ Function.comp.assoc _ _ _

@[reassocM (attr := simp)] abbrev liftM_pure := @monadLift_pure
@[reassocM (attr := simp)] abbrev liftM_bind := @monadLift_bind

namespace LawfulMonadLiftT

variable {m : Type u → Type v₁} {n : Type u → Type v₂}
  [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
  [MonadLiftT m n] [LawfulMonadLiftT m n] {α β : Type u}

@[simp] theorem liftM_comp_pure : liftM ∘ (pure : α → m α) = (pure : α → n α)
  := funext liftM_pure

@[reassocM (attr := simp)]
theorem liftM_map (f : α → β) (x : m α)
    : (liftM (f <$> x) : n β) = f <$> liftM x :=
  by simp only [map_eq_pure_bind, liftM_bind]
     congr; ext; simp only [Function.comp_apply, liftM_pure]

@[reassocM (attr := simp)]
theorem liftM_seq (f : m (α → β)) (x : m α)
    : (liftM (f <*> x) : n β) = liftM f <*> liftM x :=
  by simp_rw [seq_eq_bind, liftM_bind, ← liftM_map]; rfl

@[reassocM (attr := simp)]
theorem liftM_seqLeft (x : m α) (y : m β)
    : (liftM (x <* y) : n α) = liftM x <* liftM y :=
  by rw [seqLeft_eq, seqLeft_eq, liftM_seq, liftM_map]

@[reassocM (attr := simp)]
theorem liftM_seqRight (x : m α) (y : m β)
    : (liftM (x *> y) : n β) = liftM x *> liftM y :=
  by rw [seqRight_eq, seqRight_eq, liftM_seq, liftM_map]

end LawfulMonadLiftT

namespace LawfulMonadLift

open MonadLift renaming monadLift → lift

variable {m : Type u → Type v₁} {n : Type u → Type v₂}
  [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
  [MonadLift m n] [LawfulMonadLift m n] {α β : Type u}

@[always_inline]
def as_LawfulMonadLiftT : @LawfulMonadLiftT m n _ _ _ _ MonadLift.as_MonadLiftT where
  monadLift_pure := LawfulMonadLift.monadLift_pure
  monadLift_bind := LawfulMonadLift.monadLift_bind

theorem monadLift_comp_pure : lift ∘ (pure : α → m α) = (pure : α → n α) :=
  @LawfulMonadLiftT.liftM_comp_pure m n _ _ _ _ _ as_LawfulMonadLiftT α

@[reassocM]
theorem monadLift_map
    : ∀ (f : α → β) (x : m α), lift (n:=n) (f <$> x) = f <$> lift x :=
  @LawfulMonadLiftT.liftM_map m n _ _ _ _ _ as_LawfulMonadLiftT α β

@[reassocM]
theorem monadLift_seq
    : ∀ (f : m (α → β)) (x : m α), lift (n:=n) (f <*> x) = lift f <*> lift x :=
  @LawfulMonadLiftT.liftM_seq m n _ _ _ _ _ as_LawfulMonadLiftT α β

@[reassocM]
theorem monadLift_seqLeft
    : ∀ (x : m α) (y : m β), lift (n:=n) (x <* y) = lift x <* lift y :=
  @LawfulMonadLiftT.liftM_seqLeft m n _ _ _ _ _ as_LawfulMonadLiftT α β

@[reassocM]
theorem monadLift_seqRight
    : ∀ (x : m α) (y : m β), lift (n:=n) (x *> y) = lift x *> lift y :=
  @LawfulMonadLiftT.liftM_seqRight m n _ _ _ _ _ as_LawfulMonadLiftT α β

end LawfulMonadLift

variable {r ε ρ σ : Type u} {m : Type u → Type v₁} [Monad m] [LawfulMonad m] {ω α β : Type u}

namespace ContT

instance : LawfulMonadLift m (ContT r m) where
  monadLift_pure x :=
    by funext; simp only [MonadLift.monadLift, monadLift, pure_bind, pure]
  monadLift_bind   := ContT.monadLift_bind

end ContT

namespace ExceptCpsT

instance : LawfulMonadLift m (ExceptCpsT ε m) where
  monadLift_pure x :=
    by funext; simp_rw [MonadLift.monadLift, lift, pure, pure_bind]
  monadLift_bind x f :=
    by funext; simp only [MonadLift.monadLift, lift, bind_assoc, bind]; rfl

end ExceptCpsT

/-
these should all be coming from `LawfulMonadControl`
-/

namespace ExceptT

instance : LawfulMonadLift m (ExceptT ε m) where
  monadLift_pure x := by simp only [MonadLift.monadLift, ExceptT.lift, map_pure, pure, ExceptT.pure]
  monadLift_bind x f := ext $ by
    simp only [MonadLift.monadLift, run_lift, map_eq_pure_bind, bind_assoc,
               run_bind, Function.comp_apply, pure_bind]

instance : LawfulMonadLift (Except ε) (ExceptT ε m) where
  monadLift_pure x := by simp only [MonadLift.monadLift, pure, Except.pure, ExceptT.pure]
  monadLift_bind x f := ext $ by cases x <;>
    simp only [MonadLift.monadLift, mk, bind, Except.bind, ExceptT.bind,
               ExceptT.bindCont, Function.comp_apply, pure_bind]

end ExceptT

namespace OptionT

instance : LawfulMonadLift m (OptionT m) where
  monadLift_pure x := Eq.trans (map_eq_bind_pure_comp _ _ _).symm (map_pure _ _)
  monadLift_bind x f := ext $ by
    simp only [MonadLift.monadLift, OptionT.lift, OptionT.mk, bind_assoc, bind,
               OptionT.bind, Function.comp_apply, pure_bind]

end OptionT

namespace ReaderT

instance : LawfulMonadLift m (ReaderT ρ m) where
  monadLift_pure x := rfl
  monadLift_bind x f := rfl

end ReaderT

namespace StateCpsT

instance : LawfulMonadLift m (StateCpsT σ m) where
  monadLift_pure x :=
    by funext; simp_rw [MonadLift.monadLift, StateCpsT.lift, pure, pure_bind]
  monadLift_bind x f :=
    by funext; simp only [MonadLift.monadLift, StateCpsT.lift, bind_assoc, bind]; rfl

end StateCpsT

namespace StateT

instance : LawfulMonadLift m (StateT σ m) where
  monadLift_pure x :=
    by funext; simp_rw [MonadLift.monadLift, StateT.lift, pure, StateT.pure, pure_bind]
  monadLift_bind x f :=
    by funext; simp only [MonadLift.monadLift, StateT.lift, bind_assoc, bind,
                          Function.comp_apply, StateT.bind, pure_bind]

end StateT

section ShouldBeMoved

universe v

@[reassocM (attr:=simp)]
lemma cond_bind {m : Type u → Type v} [Monad m] {α β}
  (b : Bool) (t e : m α) (f : α → m β)
    : (cond b t e) >>= f = cond b (t >>= f) (e >>= f) :=
  by cases b <;> exact rfl

@[reassocM (attr:=simp)]
lemma ite_bind {m : Type u → Type v} [Monad m] {α β}
  (P : Prop) [d : Decidable P] (t e : m α) (f : α → m β)
    : (ite P t e) >>= f = ite P (t >>= f) (e >>= f) :=
  by cases d <;> exact rfl

@[reassocM (attr:=simp)]
lemma dite_bind {m : Type u → Type v} [Monad m] {α β}
  (P : Prop) [d : Decidable P] (t : P → m α) (e : ¬ P → m α) (f : α → m β)
    : (dite P t e) >>= f = dite P (t . >>= f) (e . >>= f) :=
  by cases d <;> exact rfl

end ShouldBeMoved
