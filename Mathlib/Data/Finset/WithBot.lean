/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Order.WithBot.Basic
import Mathlib.Logic.Embedding.WithBot
import Mathlib.Logic.Equiv.WithBot

/-!
# Finite sets in `WithBot α`

In this file we define

* `Finset.insertBot`: given `s : Finset α`, lift it to a finset on `WithBot α` using `WithBot.some`
  and then insert `⊥`;
* `Finset.eraseBot`: given `s : Finset (WithBot α)`, returns `t : Finset α` such that
  `x ∈ t ↔ some x ∈ s`.

Then we prove some basic lemmas about these definitions.

## Tags

finset, option
-/


variable {α β : Type*}

open Function

namespace Finset

/-- Given a finset on `α`, lift it to being a finset on `WithBot α`
using `WithBot.some` and then insert `⊥`. -/
def insertBot : Finset α ↪o Finset (WithBot α) :=
  (OrderEmbedding.ofMapLEIff fun s => cons ⊥ (s.map Embedding.withBot) <| by simp) fun s t => by
    rw [le_iff_subset, cons_subset_cons, map_subset_map, le_iff_subset]

-- TODO: reproduce the API from `Finset.insertNone`.

attribute [local instance] WithBot.instDecidableEqBot in
/-- Given `s : Finset (WithBot α)`, `eraseBot s : Finset α` is the set of non-`⊥` `x : α`. -/
def eraseBot : Finset (WithBot α) →o Finset α :=
  (Finset.mapEmbedding (Equiv.withBotNeBot α).toEmbedding).toOrderHom.comp
    ⟨Finset.subtype _, subtype_mono⟩

@[simp]
theorem mem_eraseBot {s : Finset (WithBot α)} {x : α} : x ∈ eraseBot s ↔ (x : WithBot α) ∈ s := by
  simp [eraseBot]

-- TODO: reproduce the API from `Finset.eraseNone`.

/-- Given a finset on `α`, lift it to being a finset on `WithTop α`
using `WithTop.some` and then insert `⊤`. -/
def insertTop : Finset α ↪o Finset (WithTop α) :=
  (OrderEmbedding.ofMapLEIff fun s => cons ⊤ (s.map Embedding.withTop) <| by simp) fun s t => by
    rw [le_iff_subset, cons_subset_cons, map_subset_map, le_iff_subset]

-- TODO: reproduce the API from `Finset.insertNone`.

attribute [local instance] WithTop.instDecidableEqTop in
/-- Given `s : Finset (WithTop α)`, `eraseTop s : Finset α` is the set of non-`⊤` `x : α`. -/
def eraseTop : Finset (WithTop α) →o Finset α :=
  (Finset.mapEmbedding (Equiv.withTopNeTop α).toEmbedding).toOrderHom.comp
    ⟨Finset.subtype _, subtype_mono⟩

@[simp]
theorem mem_eraseTop {s : Finset (WithTop α)} {x : α} : x ∈ eraseTop s ↔ (x : WithTop α) ∈ s := by
  simp [eraseTop]

-- TODO: reproduce the API from `Finset.eraseNone`.

end Finset
