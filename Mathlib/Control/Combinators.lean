/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/

import Mathlib.Init
/-!
# Monad combinators, as in Haskell's Control.Monad.
-/

universe u v w

/-- Collapses two layers of monadic structure into one,
passing the effects of the inner monad through the outer. -/
def joinM {m : Type u → Type u} [Monad m] {α : Type u} (a : m (m α)) : m α :=
  bind a id

/-- Executes `t` conditional on `c` holding true, doing nothing otherwise. -/
@[deprecated "Use `if c then t` without `else` in `do` notation instead." (since := "2025-04-07")]
def when {m : Type → Type} [Monad m] (c : Prop) [Decidable c] (t : m Unit) : m Unit :=
  ite c t (pure ())

/-- Executes `tm` or `fm` depending on whether the result of `mbool` is `true` or `false`
respectively. -/
def condM {m : Type → Type} [Monad m] {α : Type} (mbool : m Bool) (tm fm : m α) : m α := do
  let b ← mbool
  cond b tm fm

set_option linter.deprecated false in
/-- Executes `t` if `c` results in `true`, doing nothing otherwise. -/
@[deprecated "Use `if ← c then t` without `else` in `do` notation instead." (since := "2025-04-07")]
def whenM {m : Type → Type} [Monad m] (c : m Bool) (t : m Unit) : m Unit :=
  condM c t (return ())

namespace Monad

@[deprecated List.mapM (since := "2025-04-07"), inherit_doc List.mapM]
def mapM :=
  @List.mapM

@[deprecated List.mapM' (since := "2025-04-07"), inherit_doc List.mapM']
def mapM' :=
  @List.mapM'

@[deprecated joinM (since := "2025-04-07"), inherit_doc joinM]
def join :=
  @joinM

@[deprecated List.filterM (since := "2025-04-07"), inherit_doc List.filterM]
def filter :=
  @List.filterM

@[deprecated List.filterM (since := "2025-04-07"), inherit_doc List.foldlM]
def foldl :=
  @List.filterM

@[deprecated condM (since := "2025-04-07"), inherit_doc condM]
def cond :=
  @condM

/-- Executes a list of monadic actions in sequence, collecting the results. -/
@[deprecated "Use `_root_.sequence` instead." (since := "2025-04-07")]
def sequence {m : Type u → Type v} [Monad m] {α : Type u} : List (m α) → m (List α)
  | [] => return []
  | h :: t => do
    let h' ← h
    let t' ← sequence t
    return (h' :: t')

/-- Executes a list of monadic actions in sequence, discarding the results. -/
@[deprecated "Use `_root_.sequence` instead." (since := "2025-04-07")]
def sequence' {m : Type → Type u} [Monad m] {α : Type} : List (m α) → m Unit
  | [] => return ()
  | h :: t => h *> sequence' t

/-- Executes `t` if `b` is `true`, doing nothing otherwise.

See also `when` and `whenM`. -/
@[deprecated "Use `if ... then` without `else` in `do` notation instead." (since := "2025-04-07")]
def whenb {m : Type → Type} [Monad m] (b : Bool) (t : m Unit) : m Unit :=
  _root_.cond b t (return ())

/-- Executes `t` if `b` is `false`, doing nothing otherwise. -/
@[deprecated "Use `unless` in `do` notation instead." (since := "2025-04-07")]
def unlessb {m : Type → Type} [Monad m] (b : Bool) (t : m Unit) : m Unit :=
  _root_.cond b (return ()) t

end Monad
