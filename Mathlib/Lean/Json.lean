/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import Mathlib.Init

/-!
# Json serialization typeclass for `PUnit` & `Fin n` & `Subtype p`
-/

universe u


namespace Lean

deriving instance FromJson, ToJson for PUnit

instance {n : Nat} : FromJson (Fin n) where
  fromJson? j := do
    let i : Nat ← fromJson? j
    if h : i < n then
      return ⟨i, h⟩
    else
      throw s!"must be less than {n}"

instance {n : Nat} : ToJson (Fin n) where
  toJson i := toJson i.val

instance {α : Type u} [FromJson α] (p : α → Prop) [DecidablePred p] : FromJson (Subtype p) where
  fromJson? j := do
    let i : α ← fromJson? j
    if h : p i then
      return ⟨i, h⟩
    else
      throw "condition does not hold"

instance {α : Type u} [ToJson α] (p : α → Prop) : ToJson (Subtype p) where
  toJson x := toJson x.val

end Lean
