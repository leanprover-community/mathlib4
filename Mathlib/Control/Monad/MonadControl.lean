-- /-
-- Copyright (c) 2023 Brendan Murphy. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Brendan Murphy
-- -/

import Mathlib.Control.Monad.MonadLift

universe u v₁ v₂ v₃

namespace MonadControl

instance as_MonadLift {m : Type u → Type v₁} {n : Type u → Type v₂}
    [MonadControl n m] : MonadLift n m where
  monadLift := liftWith ∘ Function.const _

@[always_inline]
def as_MonadControlT {m : Type u → Type v₁} {n : Type u → Type v₂}
  [Pure m] [MonadControl m n] : MonadControlT m n where
    stM := MonadControl.stM m n
    liftWith := MonadControl.liftWith
    restoreM {α} := @MonadControl.restoreM m n _ α ∘ pure

end MonadControl

namespace MonadControlT

instance as_MonadLiftT {m : Type u → Type v₁} {n : Type u → Type v₂}
    [MonadControlT n m] : MonadLiftT n m where
  monadLift := liftWith ∘ Function.const _

end MonadControlT

class LawfulMonadControl (m : Type u → Type v₁) (n : Type u → Type v₂)
    [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [i : MonadControl m n]
  -- unclear to me whether we want this to extend or if we want to ask for the laws explicitly?
  extends LawfulMonadLift m n where
  -- liftWith_const_pure : ∀ {α} a, MonadControl.liftWith (fun _ => (pure a : m α)) = (pure a : n α)
  -- liftWith_const_bind : ∀ {α β} (x : m α) (f : α → m β),
  --   MonadControl.liftWith (fun _ => x >>= f)
  --   = (MonadControl.liftWith (fun _ => x) : n α)
  --     >>= fun a => MonadControl.liftWith (fun _ => f a)
  liftWith_run_bind_restore_pure_noop : ∀ {α} (x : n α),
    MonadControl.liftWith (fun runWith => runWith x)
      >>= (MonadControl.restoreM ∘ (pure : _ → m _))
    = x

class LawfulMonadControlT (m : Type u → Type v₁) (n : Type u → Type v₂)
    [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n] [i : MonadControlT m n]
    extends LawfulMonadLiftT m n where
  -- liftWith_const_pure : ∀ {α} a, liftWith (fun _ => (pure a :m α)) = (pure a : n α)
  -- liftWith_const_bind : ∀ {α β} (x : m α) (f : α → m β),
  --   liftWith (fun _ => x >>= f)
  --   = (liftWith (fun _ => x) : n α)
  --     >>= fun a => liftWith (fun _ => f a)
  liftWith_apply_bind_restoreM_noop  : ∀ {α} (x : n α),
    liftWith (fun f => (f x : m _)) >>= restoreM = x

export LawfulMonadControlT (liftWith_apply_bind_restoreM_noop)

instance (m : Type u → Type v₁) [Monad m] [LawfulMonad m] : LawfulMonadControlT m m where
  liftWith_apply_bind_restoreM_noop := bind_pure

instance (m : Type u → Type v₁) (n : Type u → Type v₂) (o : Type u → Type v₃)
  [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [LawfulMonad o]
  [MonadControl n o] [MonadControlT m n] [LawfulMonadControl n o] [LawfulMonadControlT m n]
    : LawfulMonadControlT m o where
  liftWith_apply_bind_restoreM_noop := by
    intro α x
    simp [liftWith, restoreM]
    have this := @liftWith_apply_bind_restoreM_noop m n _ _ _ _ _ _ (stM m o α)
    conv =>
      lhs
      left
      right
      intro f
      rw [← this (liftWith fun g ↦ g (f x))]

      -- tactic =>
      --   refine this _ ▸ ?_


      -- rw [← this]

    admit

  -- monadLift_pure x   :=
  --   Eq.trans (congrArg MonadLift.monadLift $ monadLift_pure x)
  --            (LawfulMonadLift.monadLift_pure x)
  -- monadLift_bind x f :=
  --   Eq.trans (congrArg MonadLift.monadLift $ monadLift_bind x f)
  --   $ Eq.trans (LawfulMonadLift.monadLift_bind (monadLift x) (monadLift ∘ f))
  --   $ congrArg _ $ Eq.symm $ Function.comp.assoc _ _ _

-- @[simp] abbrev liftM_pure := @monadLift_pure
-- @[simp] abbrev liftM_bind := @monadLift_bind

-- namespace LawfulMonadLiftT

-- variable {m : Type u → Type v₁} {n : Type u → Type v₂}
--   [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
--   [MonadLiftT m n] [LawfulMonadLiftT m n] {α β : Type u}

-- @[simp] theorem liftM_comp_pure : liftM ∘ (pure : α → m α) = (pure : α → n α)
--   := funext liftM_pure

-- @[simp] theorem liftM_map (f : α → β) (x : m α)
--     : (liftM (f <$> x) : n β) = f <$> liftM x :=
--   by simp only [map_eq_pure_bind, liftM_bind]
--      congr; ext; simp only [Function.comp_apply, liftM_pure]

-- @[simp] theorem liftM_seq (f : m (α → β)) (x : m α)
--     : (liftM (f <*> x) : n β) = liftM f <*> liftM x :=
--   by simp_rw [seq_eq_bind, liftM_bind, ← liftM_map]; rfl

-- @[simp] theorem liftM_seqLeft (x : m α) (y : m β)
--     : (liftM (x <* y) : n α) = liftM x <* liftM y :=
--   by rw [seqLeft_eq, seqLeft_eq, liftM_seq, liftM_map]

-- @[simp] theorem liftM_seqRight (x : m α) (y : m β)
--     : (liftM (x *> y) : n β) = liftM x *> liftM y :=
--   by rw [seqRight_eq, seqRight_eq, liftM_seq, liftM_map]

-- end LawfulMonadLiftT

-- namespace LawfulMonadLift

-- open MonadLift renaming monadLift → lift

-- attribute [simp] LawfulMonadLift.monadLift_pure
-- attribute [simp] LawfulMonadLift.monadLift_bind

-- variable {m : Type u → Type v₁} {n : Type u → Type v₂}
--   [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
--   [MonadLift m n] [LawfulMonadLift m n] {α β : Type u}

-- @[always_inline]
-- def as_LawfulMonadLiftT : @LawfulMonadLiftT m n _ _ _ _ MonadLift.as_MonadLiftT where
--   monadLift_pure := LawfulMonadLift.monadLift_pure
--   monadLift_bind := LawfulMonadLift.monadLift_bind

-- @[simp]
-- theorem monadLift_comp_pure : lift ∘ (pure : α → m α) = (pure : α → n α) :=
--   @LawfulMonadLiftT.liftM_comp_pure m n _ _ _ _ _ as_LawfulMonadLiftT α

-- @[simp]
-- theorem monadLift_map
--     : ∀ (f : α → β) (x : m α), lift (n:=n) (f <$> x) = f <$> lift x :=
--   @LawfulMonadLiftT.liftM_map m n _ _ _ _ _ as_LawfulMonadLiftT α β

-- @[simp]
-- theorem monadLift_seq
--     : ∀ (f : m (α → β)) (x : m α), lift (n:=n) (f <*> x) = lift f <*> lift x :=
--   @LawfulMonadLiftT.liftM_seq m n _ _ _ _ _ as_LawfulMonadLiftT α β

-- @[simp]
-- theorem monadLift_seqLeft
--     : ∀ (x : m α) (y : m β), lift (n:=n) (x <* y) = lift x <* lift y :=
--   @LawfulMonadLiftT.liftM_seqLeft m n _ _ _ _ _ as_LawfulMonadLiftT α β

-- @[simp]
-- theorem monadLift_seqRight
--     : ∀ (x : m α) (y : m β), lift (n:=n) (x *> y) = lift x *> lift y :=
--   @LawfulMonadLiftT.liftM_seqRight m n _ _ _ _ _ as_LawfulMonadLiftT α β

-- end LawfulMonadLift
