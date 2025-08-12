/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import Mathlib.Init

/-! # Tracing utilities -/

open Lean

namespace Mathlib.Meta

/--
A wrapper around `Lean.withTraceNode` where every node wraps a function `k : α → m β`.
The resulting trace node includes output of the form `{a} ⇒ {(← k a)}` upon success,
and `{a} ⇒ {err}` on error.

Typically this should be used in extensible tactics like `norm_num` and `positivity`.
-/
def withTraceNodeApplication
  {α β : Type} {m : Type → Type} [Monad m] [MonadTrace m] [MonadRef m] [AddMessageContext m]
  [ToMessageData α] [ToMessageData β]
  [MonadOptions m] [always : MonadAlwaysExcept Exception m] [MonadLiftT BaseIO m] (cls : Name)
  (k_name : Name) (k : α → m β) (a : α) (collapsed : Bool := true) (tag : String := "") :
    m β :=
  withTraceNode cls
    (return m!"{exceptEmoji ·} {.ofConstName k_name}")
    (collapsed := collapsed) (tag := tag)
    do
      unless ← Lean.isTracingEnabledFor cls do
        return ← k a
      let _ := always.except
      try
        let b ← k a
        Lean.addTrace cls <| .group m!"{a}{Format.line}⇒ {.nest 2 (toMessageData b)}"
        return b
      catch err =>
        Lean.addTrace cls <| .group m!"{a}{Format.line}⇒ {.nest 2 err.toMessageData}"
        throw err

end Mathlib.Meta
