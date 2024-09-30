/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.Data.Set.Image

/-!
# Graph of a function as a set

Define the graph of a function as a set of pairs.

## See also

`Function.graph` for the graph as a binary relation.
-/

open Function

namespace Set
variable {α β γ : Type*} {f g : α → β} {x : α × β}

/-- The graph of a function, as a subset of the product space. -/
def graph (f : α → β) : Set (α × β) := {(x, f x) | x : α}

@[simp] lemma mem_graph : x ∈ graph f ↔ f x.1 = x.2 := by aesop (add simp graph)

lemma fst_injOn_graph : (graph f).InjOn Prod.fst := by aesop (add simp InjOn)

lemma graph_injective : Injective (graph : (α → β) → Set (α × β)) := by
  aesop (add simp [Injective, Set.ext_iff])

@[simp] lemma graph_inj : graph f = graph g ↔ f = g := graph_injective.eq_iff

@[simp] lemma image_fst_graph (f : α → β) : Prod.fst '' graph f = Set.univ := by ext; simp
@[simp] lemma image_snd_graph (f : α → β) : Prod.snd '' graph f = f '' Set.univ := by ext; simp

lemma graph_comp (f : α → β) (g : β → γ) : graph (g ∘ f) = (fun x ↦ (x.1, g x.2)) '' graph f := by
  aesop

lemma graph_nonempty [Nonempty α] : (graph f).Nonempty := ⟨_, Classical.arbitrary _, rfl⟩

end Set
