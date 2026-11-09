/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Directed
public import Mathlib.Tactic.FunProp.Attr

import Mathlib.Order.Bounds.Image
import Mathlib.Tactic.ToFun

/-!
# Scott continuity

A function `f : α → β` between preorders is Scott continuous for suprema (referring to Dana Scott)
if it distributes over `IsLUB`. Scott continuity for infima is defined analogously. Scott continuity
corresponds to continuity in Scott topological spaces (defined in
`Mathlib/Topology/Order/ScottTopology.lean`).

## Implementation notes

Given a set `D` of directed sets, we define say `f` is `SupScottContinuousOn D` if it distributes
over `IsLUB` for all elements of `D`. This allows us to consider Scott continuity on all directed
sets in this file, and ω-Scott continuity on chains later in
`Mathlib/Order/OmegaCompletePartialOrder.lean`.

## References

* [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]
* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
-/

@[expose] public section

open Set

variable {α β γ : Type*}

section ScottContinuous
variable [Preorder α] [Preorder β] [Preorder γ] {D D₁ D₂ : Set (Set α)}
  {f : α → β}

-- Allow `to_fun` to eta-expand `g ∘ f`. Ideally, `Function.comp_def` would be a global pull lemma
-- instead, which is not supported yet: see https://github.com/leanprover-community/mathlib4/issues/40183.
attribute [local push ←] Function.comp_def
attribute [local push] Function.const_def

/-- A function between preorders is said to be Scott continuous for suprema on a set `D` of directed
sets if it preserves `IsLUB` on elements of `D`. -/
@[to_dual (attr := fun_prop)
/-- A function between preorders is said to be Scott continuous for infima on a set `D` of
codirected sets if it preserves `IsGLB` on elements of `D`. -/]
def SupScottContinuousOn (D : Set (Set α)) (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d ∈ D → d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → IsLUB (f '' d) (f a)

@[deprecated (since := "2026-11-08")] alias ScottContinuousOn := SupScottContinuousOn

@[to_dual]
lemma SupScottContinuousOn.mono (hD : D₁ ⊆ D₂) (hf : SupScottContinuousOn D₂ f) :
    SupScottContinuousOn D₁ f := fun _ hdD₁ hd₁ hd₂ _ hda => hf (hD hdD₁) hd₁ hd₂ hda

@[deprecated (since := "2026-11-08")] alias ScottContinuousOn.mono := SupScottContinuousOn.mono

@[to_dual (reorder := hD (a b))]
protected theorem SupScottContinuousOn.monotone (D : Set (Set α))
    (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D) (h : SupScottContinuousOn D f) : Monotone f := by
  refine fun a b hab =>
    (h (hD a b hab) (insert_nonempty _ _) (directedOn_pair hab) ?_).1
      (mem_image_of_mem _ <| mem_insert _ _)
  rw [IsLUB, upperBounds_insert, upperBounds_singleton,
    inter_eq_self_of_subset_right (Ici_subset_Ici.2 hab)]
  exact isLeast_Ici

@[deprecated (since := "2026-11-08")] alias ScottContinuousOn.monotone :=
  SupScottContinuousOn.monotone

@[to_dual (attr := fun_prop, to_fun (attr := simp))]
lemma SupScottContinuousOn.id : SupScottContinuousOn D (id : α → α) := by
  simp [SupScottContinuousOn]

@[deprecated (since := "2026-11-08")] alias ScottContinuousOn.id := SupScottContinuousOn.id

@[to_dual (attr := fun_prop, to_fun (attr := simp))]
lemma SupScottContinuousOn.const (x : β) : SupScottContinuousOn D (Function.const α x) := by
  rintro s _ ⟨a⟩ _ _ _
  simp [IsLUB, IsLeast, upperBounds, lowerBounds]; grind

@[deprecated (since := "2026-11-08")] alias ScottContinuousOn.const := SupScottContinuousOn.const

@[to_dual (reorder := hD (a b)) (attr := fun_prop, to_fun)]
theorem SupScottContinuousOn.comp {g : β → γ} {D'}
    (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D) (hD' : Set.MapsTo (f '' ·) D D')
    (hg : SupScottContinuousOn D' g) (hf : SupScottContinuousOn D f) :
    SupScottContinuousOn D (g ∘ f) := by
  intro d hd₁ hd₂ hd₃ a ha
  have hd : DirectedOn (fun x1 x2 ↦ x1 ≤ x2) (f '' d) := by
    have := hf.monotone
    simp only [Monotone, DirectedOn, mem_image, exists_exists_and_eq_and, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂] at ⊢ this hd₃
    grind
  rw [Set.image_comp]
  exact hg (hD' hd₁) ⟨f hd₂.choose, by grind⟩ hd (hf hd₁ hd₂ hd₃ ha)

@[deprecated (since := "2026-11-08")] alias ScottContinuousOn.comp := SupScottContinuousOn.comp

@[to_dual (reorder := hD (a b)) (attr := fun_prop, to_fun)]
theorem SupScottContinuousOn.image_comp {g : β → γ}
    (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D)
    (hg : SupScottContinuousOn ((f '' ·) '' D) g)
    (hf : SupScottContinuousOn D f) :
    SupScottContinuousOn D (g ∘ f) :=
  SupScottContinuousOn.comp hD (Set.mapsTo_image (f '' ·) D) hg hf

@[deprecated (since := "2026-11-08")] alias ScottContinuousOn.image_comp :=
  SupScottContinuousOn.image_comp

@[to_dual (attr := fun_prop)]
lemma SupScottContinuousOn.prodMk {g : α → γ} (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D)
    (hf : SupScottContinuousOn D f) (hg : SupScottContinuousOn D g) :
    SupScottContinuousOn D fun x => (f x, g x) := fun d hd₁ hd₂ hd₃ a hda => by
  rw [IsLUB, IsLeast, upperBounds]
  constructor
  · simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_ofPred_eq,
      Prod.mk_le_mk]
    intro b hb
    exact ⟨hf.monotone D hD (hda.1 hb), hg.monotone D hD (hda.1 hb)⟩
  · intro ⟨p₁, p₂⟩ hp
    simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_ofPred_eq,
      Prod.mk_le_mk] at hp
    constructor
    · rw [isLUB_le_iff (hf hd₁ hd₂ hd₃ hda), upperBounds]
      simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_ofPred_eq]
      intro _ hb
      exact (hp _ hb).1
    · rw [isLUB_le_iff (hg hd₁ hd₂ hd₃ hda), upperBounds]
      simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_ofPred_eq]
      intro _ hb
      exact (hp _ hb).2

@[deprecated (since := "2026-11-08")] alias ScottContinuousOn.prodMk :=
  SupScottContinuousOn.prodMk

@[to_dual (attr := simp, fun_prop)]
lemma SupScottContinuousOn.fst {D} : SupScottContinuousOn D (Prod.fst : α × β → α) := by
  intro d hd₁ hd₂ hd₃ a ha
  simp only [isLUB_prod] at ha
  exact ha.1

@[deprecated (since := "2026-11-08")] alias ScottContinuousOn.fst := SupScottContinuousOn.fst

@[to_dual (attr := simp, fun_prop)]
lemma SupScottContinuousOn.snd {D} : SupScottContinuousOn D (Prod.snd : α × β → β) := by
  intro d hd₁ hd₂ hd₃ a ha
  simp only [isLUB_prod] at ha
  exact ha.2

@[deprecated (since := "2026-11-08")] alias ScottContinuousOn.snd := SupScottContinuousOn.snd

/-- A function between preorders is said to be Scott continuous for suprema if it preserves `IsLUB`
on directed sets. It can be shown that a function is Scott continuous if and only if it is
continuous w.r.t. the Scott topology. -/
@[to_dual (attr := fun_prop)
/-- A function between preorders is said to be Scott continuous for infima if it preserves `IsGLB`
on codirected sets. -/
]
def SupScottContinuous (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → IsLUB (f '' d) (f a)

@[deprecated (since := "2026-11-08")] alias ScottContinuous := SupScottContinuous

@[to_dual (attr := simp)]
lemma supScottContinuousOn_univ : SupScottContinuousOn univ f ↔ SupScottContinuous f := by
  simp [SupScottContinuousOn, SupScottContinuous]

@[deprecated (since := "2026-11-08")] alias scottContinuousOn_univ := supScottContinuousOn_univ

@[to_dual]
lemma SupScottContinuous.supScottContinuousOn {D : Set (Set α)} :
    SupScottContinuous f → SupScottContinuousOn D f := fun h _ _ d₂ d₃ _ hda => h d₂ d₃ hda

@[deprecated (since := "2026-11-08")] alias ScottContinuous.scottContinuousOn :=
  SupScottContinuous.supScottContinuousOn

@[to_dual]
protected theorem SupScottContinuous.monotone (h : SupScottContinuous f) : Monotone f :=
  h.supScottContinuousOn.monotone univ (fun _ _ _ ↦ mem_univ _)

@[deprecated (since := "2026-11-08")] alias ScottContinuous.monotone :=
  SupScottContinuous.monotone

@[to_dual (attr := fun_prop, to_fun (attr := simp))]
lemma SupScottContinuous.id : SupScottContinuous (id : α → α) := by simp [SupScottContinuous]

@[deprecated (since := "2026-11-08")] alias ScottContinuous.is :=
  SupScottContinuous.id

@[to_dual (attr := fun_prop, to_fun (attr := simp))]
lemma SupScottContinuous.const (x : β) : SupScottContinuous (Function.const α x) := by
  simp_rw [← supScottContinuousOn_univ, SupScottContinuousOn.const]

@[deprecated (since := "2026-11-08")] alias ScottContinuous.const := SupScottContinuous.const

@[to_dual (attr := fun_prop, to_fun)]
lemma SupScottContinuous.comp {g : β → γ} (hf : SupScottContinuous f) (hg : SupScottContinuous g) :
    SupScottContinuous (g ∘ f) := by
  rw [← supScottContinuousOn_univ] at ⊢ hf hg
  exact SupScottContinuousOn.comp (by simp) (by simp [MapsTo]) hg hf

@[deprecated (since := "2026-11-08")] alias ScottContinuous.comp := SupScottContinuous.comp

@[to_dual (attr := fun_prop)]
lemma SupScottContinuous.prodMk {g : α → γ}
    (hf : SupScottContinuous f) (hg : SupScottContinuous g) :
    SupScottContinuous fun x => (f x, g x) := by
  rw [← supScottContinuousOn_univ] at ⊢ hf hg
  exact SupScottContinuousOn.prodMk (by grind) hf hg

@[deprecated (since := "2026-11-08")] alias ScottContinuous.prodMk := SupScottContinuous.prodMk

@[to_dual (attr := simp, fun_prop)]
lemma SupScottContinuous.fst : SupScottContinuous (Prod.fst : α × β → α) := by
  simp_rw [← supScottContinuousOn_univ, SupScottContinuousOn.fst]

@[deprecated (since := "2026-11-08")] alias ScottContinuous.fst := SupScottContinuous.fst

@[to_dual (attr := simp, fun_prop)]
lemma SupScottContinuous.snd : SupScottContinuous (Prod.snd : α × β → β) := by
  simp_rw [← supScottContinuousOn_univ, SupScottContinuousOn.snd]

@[deprecated (since := "2026-11-08")] alias ScottContinuous.snd := SupScottContinuous.snd

end ScottContinuous

section SemilatticeSup

variable [SemilatticeSup β]

/-- The join operation is Scott continuous for suprema. -/
@[to_dual (attr := fun_prop)
/-- The meet operation is Scott continuous for infima. -/]
protected lemma SupScottContinuous.sup :
    SupScottContinuous fun b : β × β => b.1 ⊔ b.2 := fun d _ _ ⟨p₁, p₂⟩ hdp => by
  simp only [IsLUB, IsLeast, upperBounds, Prod.forall, mem_ofPred_eq, Prod.mk_le_mk] at hdp
  simp only [IsLUB, IsLeast, upperBounds, mem_image, Prod.exists, forall_exists_index, and_imp]
  have e1 : (p₁, p₂) ∈ lowerBounds {x | ∀ (b₁ b₂ : β), (b₁, b₂) ∈ d → (b₁, b₂) ≤ x} := hdp.2
  simp only [lowerBounds, mem_ofPred_eq, Prod.forall, Prod.mk_le_mk] at e1
  refine ⟨fun a b₁ b₂ hbd hba => ?_,fun b hb => ?_⟩
  · rw [← hba]
    exact sup_le_sup (hdp.1 _ _ hbd).1 (hdp.1 _ _ hbd).2
  · rw [sup_le_iff]
    exact e1 _ _ fun b₁ b₂ hb' => sup_le_iff.mp (hb b₁ b₂ hb' rfl)

@[deprecated (since := "2026-11-08")] alias ScottContinuous.sup₂ := SupScottContinuous.sup

@[fun_prop]
lemma SupScottContinuousOn.sup {D : Set (Set (β × β))} :
    SupScottContinuousOn D fun (a, b) => (a ⊔ b : β) :=
  SupScottContinuous.sup.supScottContinuousOn

@[deprecated (since := "2026-11-08")] alias ScottContinuousOn.sup₂ := SupScottContinuousOn.sup

end SemilatticeSup
