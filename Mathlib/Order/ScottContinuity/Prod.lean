/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Order.Bounds.Lattice
public import Mathlib.Order.ScottContinuity

/-!
# Scott continuity on product spaces

## Main result

- `ScottContinuous_prod_of_ScottContinuous`: A function is Scott continuous on a product space if it
  is Scott continuous in each variable.
- `ScottContinuousOn.inf₂`: For complete linear orders, the meet operation is Scott continuous.

-/

public section

open Set

variable {α β γ : Type*}

/-- A function is Scott continuous on a product space if it is Scott continuous and monotone in each
variable. -/
@[to_dual
/-- A function is Scott continuous on a product space if it is Scott continuous and monotone in each
variable. -/]
lemma SupScottContinuousOn.fromProd [Preorder α] [Preorder β] [Preorder γ]
    {f : α × β → γ} {D : Set (Set (α × β))}
    (h₁ : ∀ a, SupScottContinuousOn ((fun d => Prod.snd '' d) '' D) (fun b => f (a, b)))
    (h₂ : ∀ b, SupScottContinuousOn ((fun d => Prod.fst '' d) '' D) (fun a => f (a, b)))
    (h₁' : ∀ a, Monotone (fun b => f (a, b))) (h₂' : ∀ b, Monotone (fun a => f (a, b))) :
    SupScottContinuousOn D f := fun d hX hd₁ hd₂ ⟨p1, p2⟩ hdp => by
  rw [isLUB_congr ((monotone_prod_iff.mpr ⟨h₁', h₂'⟩).upperBounds_image_of_directedOn_prod hd₂),
    ← iUnion_of_singleton_coe (Prod.fst '' d), iUnion_prod_const, image_iUnion,
    ← isLUB_iUnion_iff_of_isLUB (fun a => by
      rw [singleton_prod, image_image f (fun b ↦ (a, b))]
      exact h₁ _ (mem_image_of_mem (fun d ↦ Prod.snd '' d) hX) (Nonempty.image Prod.snd hd₁)
        (DirectedOn.snd hd₂) (isLUB_prod.mp hdp).2) _, Set.range]
  simpa [Set.image] using
     h₂ _ (mem_image_of_mem (Prod.fst '' ·) hX) (hd₁.image Prod.fst) hd₂.fst (isLUB_prod.mp hdp).1

@[deprecated (since := "2026-11-08")]
alias ScottContinuousOn.fromProd := SupScottContinuousOn.fromProd

@[to_dual]
lemma SupScottContinuous.fromProd {γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
    {f : α × β → γ} (h₁ : ∀ a, SupScottContinuous (fun b => f (a, b)))
    (h₂ : ∀ b, SupScottContinuous (fun a => f (a, b))) : SupScottContinuous f := by
  simp_rw [← supScottContinuousOn_univ] at ⊢
  exact .fromProd (fun a ↦ (h₁ a).supScottContinuousOn) (fun b ↦ (h₂ b).supScottContinuousOn)
    (fun a ↦ (h₁ a).monotone) (fun b ↦ (h₂ b).monotone)

@[deprecated (since := "2026-11-08")]
alias ScottContinuous.fromProd := SupScottContinuous.fromProd

@[to_dual]
lemma SupScottContinuous.prod {α' β' : Type*} [Preorder α] [Preorder β] [Preorder α'] [Preorder β']
    {f : α → α'} {g : β → β'} (hf : SupScottContinuous f) (hg : SupScottContinuous g) :
    SupScottContinuous (Prod.map f g) := by
  refine .fromProd (fun a d hd₁ hd₂ c hdc ↦ ?_) (fun b d hd₁ hd₂ c hdc ↦ ?_)
  · have e1 : (fun b ↦ (f a, g b)) '' d = {f a} ×ˢ (g '' d) := by aesop
    simp_rw [Prod.map_apply, e1]
    exact .prod (singleton_nonempty _) (hd₁.image _) isLUB_singleton (hg hd₁ hd₂ hdc)
  · have e2 : ((fun a ↦ (f a, g b)) '' d) = (f '' d) ×ˢ {g b} := by aesop
    simp_rw [Prod.map_apply, e2]
    exact .prod (hd₁.image _) (singleton_nonempty _) (hf hd₁ hd₂ hdc) isLUB_singleton

@[deprecated (since := "2026-11-08")] alias ScottContinuous.prod := SupScottContinuous.prod
