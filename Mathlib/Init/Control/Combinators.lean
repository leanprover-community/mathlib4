/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Mathport.Rename

/-! ## Monad combinators, as in Haskell's Control.Monad. -/

universe u v w

#align list.mmap List.mapM

#align list.mmap' List.mapM'

def joinM {m : Type u → Type u} [Monad m] {α : Type u} (a : m (m α)) : m α :=
  bind a id

#align mjoin joinM

#align list.mfilter List.filterM

#align list.mfoldl List.foldlM

#align list.mfoldr List.foldrM

#align list.mfirst List.firstM

def when {m : Type → Type} [Monad m] (c : Prop) [Decidable c] (t : m Unit) : m Unit :=
  ite c t (pure ())

def condM {m : Type → Type} [Monad m] {α : Type} (mbool : m Bool) (tm fm : m α) : m α := do
  let b ← mbool
  cond b tm fm

#align mcond condM

def whenM {m : Type → Type} [Monad m] (c : m Bool) (t : m Unit) : m Unit :=
  condM c t (return ())

#align mwhen whenM


export List (mapM mapM' filterM foldlM)

namespace Monad

def mapM :=
  @List.mapM
#align monad.mapm Monad.mapM

def mapM' :=
  @List.mapM'
#align monad.mapm' Monad.mapM'

def join :=
  @joinM

def filter :=
  @filterM

def foldl :=
  @List.foldlM

def cond :=
  @condM

def sequence {m : Type u → Type v} [Monad m] {α : Type u} : List (m α) → m (List α)
  | [] => return []
  | h :: t => do
    let h' ← h
    let t' ← sequence t
    return (h' :: t')

def sequence' {m : Type → Type u} [Monad m] {α : Type} : List (m α) → m Unit
  | [] => return ()
  | h :: t => h *> sequence' t

def whenb {m : Type → Type} [Monad m] (b : Bool) (t : m Unit) : m Unit :=
  _root_.cond b t (return ())

def unlessb {m : Type → Type} [Monad m] (b : Bool) (t : m Unit) : m Unit :=
  _root_.cond b (return ()) t

end Monad
