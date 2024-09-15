/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.List.GroupBy
import Mathlib.Order.TypeTags

/-!
# Run-length encoding
-/

variable {α : Type*} [DecidableEq α]

def RunLength (l : List α) : List (ℕ+ × α) :=
  (l.groupBy (· == ·)).attach.map (fun ⟨m, hm⟩ ↦ by
    
  )
