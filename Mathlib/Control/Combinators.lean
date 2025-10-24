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

/-- Executes `tm` or `fm` depending on whether the result of `mbool` is `true` or `false`
respectively. -/
def condM {m : Type → Type} [Monad m] {α : Type} (mbool : m Bool) (tm fm : m α) : m α := do
  let b ← mbool
  cond b tm fm

namespace Monad

end Monad
