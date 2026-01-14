/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Order.ScottContinuity
import Mathlib.Order.Bounds.Lattice

/-!
# Scott continuity on product spaces

## Main result

- `ScottContinuous_prod_of_ScottContinuous`: A function is Scott continuous on a product space if it
  is Scott continuous in each variable.
- `ScottContinuousOn.inf₂`: For complete linear orders, the meet operation is Scott continuous.

-/

open Set

variable {α β γ : Type*}

/-- If  is Scott continuous on a product space if it is Scott continuous and monotone in each
variable -/
lemma ScottContinuousOn.fromProd [Preorder α] [Preorder β] [Preorder γ]
    {f : α × β → γ} {D : Set (Set (α × β))}
    (h₁ : ∀ a, ScottContinuousOn ((fun d => Prod.snd '' d) '' D) (fun b => f (a, b)))
    (h₂ : ∀ b, ScottContinuousOn ((fun d => Prod.fst '' d) '' D) (fun a => f (a, b)))
    (h₁' : ∀ a, Monotone (fun b => f (a, b))) (h₂' : ∀ b, Monotone (fun a => f (a, b))) :
    ScottContinuousOn D f := fun d hX hd₁ hd₂ ⟨p1, p2⟩ hdp => by
  rw [isLUB_congr ((monotone_prod_iff.mpr ⟨h₁', h₂'⟩).upperBounds_image_of_directedOn_prod hd₂),
    ← iUnion_of_singleton_coe (Prod.fst '' d), iUnion_prod_const, image_iUnion,
    ← isLUB_iUnion_iff_of_isLUB (fun a => by
      rw [singleton_prod, image_image f (fun b ↦ (a, b))]
      exact h₁ _ (mem_image_of_mem (fun d ↦ Prod.snd '' d) hX) (Nonempty.image Prod.snd hd₁)
        (DirectedOn.snd hd₂) ((isLUB_prod (_,_)).mp hdp).2) _, Set.range]
  convert (h₂ _
    (mem_image_of_mem (fun d ↦ Prod.fst '' d) hX) (Nonempty.image Prod.fst hd₁) (DirectedOn.fst hd₂)
    ((isLUB_prod (p1,p2)).mp hdp).1)
  ext : 1
  simp_all only [Subtype.exists, mem_image, Prod.exists,
    exists_and_right, exists_eq_right, exists_prop, mem_setOf_eq]

lemma ScottContinuous.fromProd {γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
    {f : α × β → γ} (h₁ : ∀ a, ScottContinuous (fun b => f (a, b)))
    (h₂ : ∀ b, ScottContinuous (fun a => f (a, b))) : ScottContinuous f := by
  simp_rw [← scottContinuousOn_univ] at ⊢
  exact .fromProd (fun a ↦ (h₁ a).scottContinuousOn) (fun b ↦ (h₂ b).scottContinuousOn)
    (fun a ↦ (h₁ a).monotone) (fun b ↦ (h₂ b).monotone)

lemma ScottContinuous.prod {α' β' : Type*} [Preorder α] [Preorder β] [Preorder α'] [Preorder β']
    {f : α → α'} {g : β → β'} (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous (Prod.map f g) := by
  refine .fromProd (fun a d hd₁ hd₂ c hdc ↦ ?_) (fun b d hd₁ hd₂ c hdc ↦ ?_)
  · have e1 : (fun b ↦ (f a, g b)) '' d = {f a} ×ˢ (g '' d) := by aesop
    simp_rw [Prod.map_apply, e1]
    exact .prod (singleton_nonempty _) (hd₁.image _) isLUB_singleton (hg hd₁ hd₂ hdc)
  · have e2 : ((fun a ↦ (f a, g b)) '' d) = (f '' d) ×ˢ {g b} := by aesop
    simp_rw [Prod.map_apply, e2]
    exact .prod (hd₁.image _) (singleton_nonempty _) (hf hd₁ hd₂ hdc) isLUB_singleton
