/-
Copyright (c) 2023 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/

import Mathlib.Control.Monad.MonadLift
import Mathlib.Tactic.MonadReassoc

universe u v w

namespace MonadStateOf

@[always_inline, inline]
abbrev modifyThenGetThe (σ : Type u) {m : Type u → Type v} [MonadStateOf σ m]
  (f : σ → σ) : m σ := modifyGet fun s => (f s, f s)

end MonadStateOf

namespace MonadState

@[always_inline, inline]
def modifyThenGet {σ : Type u} {m : Type u → Type v} [MonadState σ m]
  (f : σ → σ) : m σ := modifyGet fun s => (f s, f s)

end MonadState

export MonadState (modifyThenGet)

class LawfulMonadStateOf (σ : Type u) (m : Type u → Type v)
    [MonadStateOf σ m] [Monad m] [LawfulMonad m] where
  set_set : ∀ (s₁ s₂ : σ), (do set s₁; set s₂ : m PUnit) = set s₂
  set_get : ∀ (s : σ), (do set s; get : m σ) = (do set s; pure s)
  get_set : (do let s ← (get : m σ); set s) = pure PUnit.unit
  get_get_pair : (do let s₁ ← (get : m σ); let s₂ ← get; pure (s₁, s₂))
               = (do let s ← get; pure (s, s))
  modifyGet_def : ∀ {α} (f : σ → α × σ),
    (modifyGet f : m α) = (do let p := f (← get); set p.snd; pure p.fst)

-- ?
open LawfulMonadStateOf (set_set set_get get_set get_get_pair modifyGet_def)
attribute [reassocM (attr := simp)] set_set set_get get_set get_get_pair modifyGet_def

section

variable {σ : Type u} {m : Type u → Type v} [MonadStateOf σ m] [Monad m]
  [LawfulMonad m] [LawfulMonadStateOf σ m] {α : Type u}

namespace LawfulMonadStateOf

@[reassocM (attr := simp)]
theorem get_get (k : σ → σ → m α)
    : (do k (← get) (← get)) = (get >>= fun s => k s s) :=
  get_get_pair_assoc k.uncurry

@[reassocM (attr := simp)]
theorem modify_def (f : σ → σ) : (modify f : m PUnit) = (do set (f (← get))) :=
  by simp only [modify, modifyGet_def, bind_pure_unit]

@[reassocM (attr := simp)]
theorem getModify_def (f : σ → σ)
    : (getModify f : m σ) = (do let s ← get; modify f; pure s) :=
  by simp only [modify_def, getModify, modifyGet_def, get_get, bind_assoc]

@[reassocM (attr := simp)]
theorem modifyThenGet_def (f : σ → σ)
    : (modifyThenGet f : m σ) = (do modify f; get) :=
  by simp only [modifyThenGet, modifyGet_def, modify_def, set_get, bind_assoc]

@[reassocM (attr := simp)]
theorem get_set_pure_eq_get : (do let s ← get; set s; pure s) = (get : m σ) := by
  conv => enter [1, 2, s]; rw [← set_get]
  rw [← bind_assoc, get_set, pure_bind]

end LawfulMonadStateOf

section

open MonadState renaming set → set'

class LawfulMonadState (σ : Type u) (m : Type u → Type v)
    [MonadState σ m] [Monad m] [LawfulMonad m] where
  set_set : ∀ s₁ s₂, (do set' s₁; set' s₂ : m PUnit) = set' s₂
  set_get : ∀ s, (do set' s; get : m σ) = (do set' s; pure s)
  get_set : (do let s ← (get : m σ); set' s) = pure PUnit.unit
  get_get_pair : (do let s₁ ← (get : m σ); let s₂ ← get; pure (s₁, s₂))
               = (do let s ← get; pure (s, s))
  modifyGet_def : ∀ {α} (f : σ → α × σ),
    (modifyGet f : m α) = (do let p := f (← get); set' p.snd; pure p.fst)

end

instance (σ : Type u) (m : Type u → Type v) [MonadStateOf σ m] [Monad m]
    [LawfulMonad m] [LawfulMonadStateOf σ m] : LawfulMonadState σ m where
  set_set       := LawfulMonadStateOf.set_set
  set_get       := LawfulMonadStateOf.set_get
  get_set       := LawfulMonadStateOf.get_set
  get_get_pair  := LawfulMonadStateOf.get_get_pair
  modifyGet_def := LawfulMonadStateOf.modifyGet_def

@[always_inline]
instance {σ : Type u} {m : Type u → Type v} {n : Type u → Type w}
-- not sure about the order here
    [MonadStateOf σ m] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [MonadLift m n] [LawfulMonadLift m n] [LawfulMonadStateOf σ m]
    : LawfulMonadStateOf σ n where
  set_set s₁ s₂ := Eq.trans (Eq.symm $ liftM_bind _ _)
                   $ congrArg liftM (set_set s₁ s₂)
  set_get s₀    := Eq.trans (Eq.symm $ liftM_bind (set s₀ : m PUnit) _)
                   $ Eq.trans (congrArg liftM (set_get s₀))
                   $ Eq.trans (liftM_bind _ _)
                   $ bind_congr $ fun _ => liftM_pure s₀
  get_set       := Eq.trans (Eq.symm $ liftM_bind (get : m σ) set)
                   $ Eq.trans (congrArg liftM get_set) $ liftM_pure _
  get_get_pair  := by
    refine Eq.trans ?_ (Eq.trans (liftM_bind (get : m σ) _)
                                 $ bind_congr $ fun s => liftM_pure (s, s))
    refine Eq.trans ?_ (congrArg liftM get_get_pair)
    refine Eq.trans ?_ (Eq.symm $ liftM_bind _ _)
    apply bind_congr; intro s₁
    simp only [Function.comp_apply, liftM_bind]
    apply bind_congr; intro s₂
    simp only [Function.comp_apply, liftM_pure]
  modifyGet_def f := by
    refine Eq.trans (congrArg liftM (modifyGet_def f)) ?_
    simp only [liftM_bind]
    apply bind_congr; intro
    simp only [Function.comp_apply, liftM_bind]
    apply bind_congr; intro
    exact monadLift_pure _

variable {σ : Type u} {m : Type u → Type v} [Monad m] [LawfulMonad m]

namespace StateT

open StateT renaming get → get', set → set', modifyGet → modifyGet'

-- private?
macro "solve_StateT" : tactic => `(tactic| {
  refine StateT.ext (fun _ => ?_)
  simp only [run_set, run_get, run_modifyGet, run_bind, run_pure, pure_bind] })

theorem set_set (s₁ s₂ : σ) : (do set' s₁; set' s₂ : StateT σ m PUnit) = set' s₂ :=
  show (do set s₁; set s₂ : StateT σ m PUnit) = set s₂
  by solve_StateT

theorem set_get (s : σ) : (do set' s; get' : StateT σ m σ) = (do set' s; pure s) :=
  show (do set s; get : StateT σ m σ) = (do set s; pure s)
  by solve_StateT

theorem get_set : (get' : StateT σ m σ) >>= set' = pure PUnit.unit :=
  show (get : StateT σ m σ) >>= set = pure PUnit.unit
  by solve_StateT

theorem get_get_pair : (do let s₁ ← get'; let s₂ ← get'; pure (s₁, s₂))
                     = ((get' : StateT σ m σ) >>= fun s => pure (s, s)) :=
  show (do let s₁ ← get; let s₂ ← get; pure (s₁, s₂))
       = ((get : StateT σ m σ) >>= fun s => pure (s, s))
  by solve_StateT

theorem modifyGet_def {α} (f : σ → α × σ)
    : modifyGet' f = get' >>= (fun s₀ =>
      (do let (a, s₁) := f s₀; set' s₁; StateT.pure a : StateT σ m α)) :=
  show modifyGet f = get >>= (fun s₀ =>
      (do let (a, s₁) := f s₀; set s₁; pure a : StateT σ m α))
  by solve_StateT

instance : LawfulMonadStateOf σ (StateT σ m) where
  set_set       := set_set
  set_get       := set_get
  get_set       := get_set
  get_get_pair  := get_get_pair
  modifyGet_def := modifyGet_def

end StateT

namespace StateCpsT

instance : LawfulMonadStateOf σ (StateCpsT σ m) := by
  refine' { .. } <;> intros <;> rfl

end StateCpsT
