/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Order.Bounds.Basic

/-!
# Scott continuity

A function `f : α → β` between preorders is Scott continuous (referring to Dana Scott) if it
distributes over `IsLUB`. Scott continuity corresponds to continuity in Scott topological spaces
(defined in `Mathlib/Topology/Order/ScottTopology.lean`). It is distinct from the (more commonly
used) continuity from topology (see `Mathlib/Topology/Basic.lean`).

## Implementation notes

Given a set `D` of directed sets, we define say `f` is `ScottContinuousOn D` if it distributes over
`IsLUB` for all elements of `D`. This allows us to consider Scott Continuity on all directed sets
in this file, and ωScott Continuity on chains later in
`Mathlib/Order/OmegaCompletePartialOrder.lean`.

## References

* [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]
* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]

-/

open Set

variable {α β : Type*}

section ScottContinuous
variable [Preorder α] [Preorder β] {D D₁ D₂ : Set (Set α)}
  {f : α → β}

/-- A function between preorders is said to be Scott continuous on a set `D` of directed sets if it
preserves `IsLUB` on elements of `D`.

The dual notion

```lean
∀ ⦃d : Set α⦄, d ∈ D →  d.Nonempty → DirectedOn (· ≥ ·) d → ∀ ⦃a⦄, IsGLB d a → IsGLB (f '' d) (f a)
```

does not appear to play a significant role in the literature, so is omitted here.
-/
def ScottContinuousOn (D : Set (Set α)) (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → IsLUB (f '' d) (f a)

lemma ScottContinuousOn.mono (hD : D₁ ⊆ D₂) (hf : ScottContinuousOn D₂ f) :
    ScottContinuousOn D₁ f := fun _ hdD₁ hd₁ hd₂ _ hda => hf (hD hdD₁) hd₁ hd₂ hda

protected theorem ScottContinuousOn.monotone (D : Set (Set α)) (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D)
    (h : ScottContinuousOn D f) : Monotone f := by
  refine fun a b hab =>
    (h (hD a b hab) (insert_nonempty _ _) (directedOn_pair le_refl hab) ?_).1
      (mem_image_of_mem _ <| mem_insert _ _)
  rw [IsLUB, upperBounds_insert, upperBounds_singleton,
    inter_eq_self_of_subset_right (Ici_subset_Ici.2 hab)]
  exact isLeast_Ici

@[simp] lemma ScottContinuousOn.id : ScottContinuousOn D (id : α → α) := by simp [ScottContinuousOn]

variable {g : α → β}

lemma ScottContinuousOn.prodMk (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D)
    (hf : ScottContinuousOn D f) (hg : ScottContinuousOn D g) :
    ScottContinuousOn D fun x => (f x, g x) := fun d hd₁ hd₂ hd₃ a hda => by
  rw [IsLUB, IsLeast, upperBounds]
  constructor
  · simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_setOf_eq,
      Prod.mk_le_mk]
    intro b hb
    exact ⟨hf.monotone D hD (hda.1 hb), hg.monotone D hD (hda.1 hb)⟩
  · intro ⟨p₁, p₂⟩ hp
    simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_setOf_eq,
      Prod.mk_le_mk] at hp
    constructor
    · rw [isLUB_le_iff (hf hd₁ hd₂ hd₃ hda), upperBounds]
      simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_setOf_eq]
      intro _ hb
      exact (hp _ hb).1
    · rw [isLUB_le_iff (hg hd₁ hd₂ hd₃ hda), upperBounds]
      simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_setOf_eq]
      intro _ hb
      exact (hp _ hb).2

/-- A function between preorders is said to be Scott continuous if it preserves `IsLUB` on directed
sets. It can be shown that a function is Scott continuous if and only if it is continuous w.r.t. the
Scott topology.
-/
def ScottContinuous (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → IsLUB (f '' d) (f a)

@[simp] lemma scottContinuousOn_univ : ScottContinuousOn univ f ↔ ScottContinuous f := by
  simp [ScottContinuousOn, ScottContinuous]

lemma ScottContinuous.scottContinuousOn {D : Set (Set α)} :
    ScottContinuous f → ScottContinuousOn D f := fun h _ _ d₂ d₃ _ hda => h d₂ d₃ hda

protected theorem ScottContinuous.monotone (h : ScottContinuous f) : Monotone f :=
  h.scottContinuousOn.monotone univ (fun _ _ _ ↦ mem_univ _)

@[simp] lemma ScottContinuous.id : ScottContinuous (id : α → α) := by simp [ScottContinuous]

end ScottContinuous

section SemilatticeSup

variable [SemilatticeSup β]

/-- The join operation is Scott continuous -/
lemma ScottContinuous.sup₂ :
    ScottContinuous fun b : β × β => (b.1 ⊔ b.2 : β) := fun d _ _ ⟨p₁, p₂⟩ hdp => by
  simp only [IsLUB, IsLeast, upperBounds, Prod.forall, mem_setOf_eq, Prod.mk_le_mk] at hdp
  simp only [IsLUB, IsLeast, upperBounds, mem_image, Prod.exists, forall_exists_index, and_imp]
  have e1 : (p₁, p₂) ∈ lowerBounds {x | ∀ (b₁ b₂ : β), (b₁, b₂) ∈ d → (b₁, b₂) ≤ x} := hdp.2
  simp only [lowerBounds, mem_setOf_eq, Prod.forall, Prod.mk_le_mk] at e1
  refine ⟨fun a b₁ b₂ hbd hba => ?_,fun b hb => ?_⟩
  · rw [← hba]
    exact sup_le_sup (hdp.1 _ _ hbd).1 (hdp.1 _ _ hbd).2
  · rw [sup_le_iff]
    exact e1 _ _ fun b₁ b₂ hb' => sup_le_iff.mp (hb b₁ b₂ hb' rfl)

lemma ScottContinuousOn.sup₂ {D : Set (Set (β × β))} :
    ScottContinuousOn D fun (a, b) => (a ⊔ b : β) :=
  ScottContinuous.sup₂.scottContinuousOn

end SemilatticeSup
