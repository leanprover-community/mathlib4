/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Mathport.Rename

/-!  Monad combinators, as in Haskell's Control.Monad. -/

universe u v w

def List.mmap {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β) :
    List α → m (List β)
  | [] => return []
  | h :: t => do
    let h' ← f h
    let t' ← List.mmap f t
    return (h' :: t')

def List.mmap' {m : Type → Type v} [Monad m] {α : Type u} {β : Type} (f : α → m β) :
    List α → m Unit
  | [] => return ()
  | h :: t => f h *> List.mmap' f t

def mjoin {m : Type u → Type u} [Monad m] {α : Type u} (a : m (m α)) : m α :=
  bind a id

def List.mfilter {m : Type → Type v} [Monad m] {α : Type} (f : α → m Bool) : List α → m (List α)
  | [] => return []
  | h :: t => do
    let b ← f h
    let t' ← List.mfilter f t
    cond b (return (h :: t')) (return t')

def List.mfoldl {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} :
    (s → α → m s) → s → List α → m s
  | _, s, [] => return s
  | f, s, h :: r => do
    let s' ← f s h
    List.mfoldl f s' r

def List.mfoldr {m : Type u → Type v} [Monad m] {s : Type u} {α : Type w} :
    (α → s → m s) → s → List α → m s
  | _, s, [] => return s
  | f, s, h :: r => do
    let s' ← List.mfoldr f s r
    f h s'

/- warning: list.mfirst -> List.mfirst is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u} -> Type.{v}} [_inst_1 : Monad.{u v} m] [_inst_2 : Alternative.{u v} m]
    {α : Type.{w}} {β : Type.{u}}, (α -> (m β)) -> (List.{w} α) -> (m β)
but is expected to have type
  forall {m : Type.{u} -> Type.{v}} [_inst_2 : Alternative.{u v} m]
    {α : Type.{w}} {β : Type.{u}}, (α -> (m β)) -> (List.{w} α) -> (m β)
Case conversion may be inaccurate. Consider using '#align list.mfirst List.mfirstₓ'. -/
def List.mfirst {m : Type u → Type v} [Monad m] [Alternative m] {α : Type w} {β : Type u}
    (f : α → m β) : List α → m β
  | [] => failure
  | a :: as => f a <|> List.mfirst f as
#align list.mfirst List.mfirst -- TODO: check if is this correct

def when {m : Type → Type} [Monad m] (c : Prop) [Decidable c] (t : m Unit) : m Unit :=
  ite c t (pure ())

def mcond {m : Type → Type} [Monad m] {α : Type} (mbool : m Bool) (tm fm : m α) : m α := do
  let b ← mbool
  cond b tm fm

def mwhen {m : Type → Type} [Monad m] (c : m Bool) (t : m Unit) : m Unit :=
  mcond c t (return ())

export List (mmap mmap' mfilter mfoldl)

namespace Monad

def mapm :=
  @mmap

def mapm' :=
  @mmap'

def join :=
  @mjoin

def filter :=
  @mfilter

def foldl :=
  @mfoldl

def cond :=
  @mcond

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
