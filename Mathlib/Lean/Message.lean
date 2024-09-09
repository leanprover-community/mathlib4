/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Init
import Lean.Message

/-!
# Additional operations on MessageData and related types
-/

open Lean Std MessageData

instance {α β : Type} [ToMessageData α] [ToMessageData β] : ToMessageData (α × β) :=
  ⟨fun x => paren <| toMessageData x.1 ++ ofFormat "," ++ Format.line ++ toMessageData x.2⟩
