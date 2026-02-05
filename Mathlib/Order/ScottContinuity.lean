/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic.FunProp.Attr
public import Mathlib.Tactic.ToFun
import Mathlib.Order.Bounds.Image

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

@[expose] public section

open Set

variable {α β γ : Type*}

section ScottContinuous
variable [Preorder α] [Preorder β] [Preorder γ] {D D₁ D₂ : Set (Set α)}
  {f : α → β}

attribute [local push ←] Function.comp_def
attribute [local push] Function.const_def

/-- A function between preorders is said to be Scott continuous on a set `D` of directed sets if it
preserves `IsLUB` on elements of `D`.

The dual notion

```lean
∀ ⦃d : Set α⦄, d ∈ D →  d.Nonempty → DirectedOn (· ≥ ·) d → ∀ ⦃a⦄, IsGLB d a → IsGLB (f '' d) (f a)
```

does not appear to play a significant role in the literature, so is omitted here.
-/
@[fun_prop]
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

@[fun_prop, to_fun (attr := simp)]
lemma ScottContinuousOn.id : ScottContinuousOn D (id : α → α) := by simp [ScottContinuousOn]

@[fun_prop, to_fun (attr := simp)]
lemma ScottContinuousOn.const (x : β) : ScottContinuousOn D (Function.const α x) := by
  rintro s _ ⟨a⟩ _ _ _
  simp [IsLUB, IsLeast, upperBounds, lowerBounds]; grind

@[fun_prop, to_fun]
theorem ScottContinuousOn.comp {g : β → γ} {D'}
    (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D) (hD' : Set.MapsTo (f '' ·) D D')
    (hg : ScottContinuousOn D' g) (hf : ScottContinuousOn D f) :
    ScottContinuousOn D (g ∘ f) := by
  intro d hd₁ hd₂ hd₃ a ha
  have hd : DirectedOn (fun x1 x2 ↦ x1 ≤ x2) (f '' d) := by
    have := hf.monotone
    simp only [Monotone, DirectedOn, mem_image, exists_exists_and_eq_and, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂] at ⊢ this hd₃
    grind
  rw [Set.image_comp]
  exact hg (hD' hd₁) ⟨f hd₂.choose, by grind⟩ hd (hf hd₁ hd₂ hd₃ ha)

@[fun_prop, to_fun]
theorem ScottContinuousOn.image_comp {g : β → γ}
    (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D)
    (hg : ScottContinuousOn ((f '' ·) '' D) g)
    (hf : ScottContinuousOn D f) :
    ScottContinuousOn D (g ∘ f) :=
  ScottContinuousOn.comp hD (Set.mapsTo_image  (f '' ·) D) hg hf

@[fun_prop]
lemma ScottContinuousOn.prodMk {g : α → γ} (hD : ∀ a b : α, a ≤ b → {a, b} ∈ D)
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

@[simp, fun_prop]
lemma ScottContinuousOn.fst {D} : ScottContinuousOn D (Prod.fst : α × β → α) := by
  intro d hd₁ hd₂ hd₃ a ha
  simp only [isLUB_prod] at ha
  exact ha.1

@[simp, fun_prop]
lemma ScottContinuousOn.snd {D} : ScottContinuousOn D (Prod.snd : α × β → β) := by
  intro d hd₁ hd₂ hd₃ a ha
  simp only [isLUB_prod] at ha
  exact ha.2

/-- A function between preorders is said to be Scott continuous if it preserves `IsLUB` on directed
sets. It can be shown that a function is Scott continuous if and only if it is continuous w.r.t. the
Scott topology.
-/
@[fun_prop]
def ScottContinuous (f : α → β) : Prop :=
  ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → ∀ ⦃a⦄, IsLUB d a → IsLUB (f '' d) (f a)

@[simp] lemma scottContinuousOn_univ : ScottContinuousOn univ f ↔ ScottContinuous f := by
  simp [ScottContinuousOn, ScottContinuous]

lemma ScottContinuous.scottContinuousOn {D : Set (Set α)} :
    ScottContinuous f → ScottContinuousOn D f := fun h _ _ d₂ d₃ _ hda => h d₂ d₃ hda

protected theorem ScottContinuous.monotone (h : ScottContinuous f) : Monotone f :=
  h.scottContinuousOn.monotone univ (fun _ _ _ ↦ mem_univ _)

@[fun_prop, to_fun (attr := simp)]
lemma ScottContinuous.id : ScottContinuous (id : α → α) := by simp [ScottContinuous]

@[fun_prop, to_fun (attr := simp)]
lemma ScottContinuous.const (x : β) : ScottContinuous (Function.const α x) := by
  simp_rw [← scottContinuousOn_univ, ScottContinuousOn.const]

@[fun_prop, to_fun]
lemma ScottContinuous.comp {g : β → γ}
    (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous (g ∘ f) := by
  rw [← scottContinuousOn_univ] at ⊢ hf hg
  exact ScottContinuousOn.comp (by simp) (by simp [MapsTo]) hg hf

@[fun_prop]
lemma ScottContinuous.prodMk {g : α → γ}
    (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous fun x => (f x, g x) := by
  rw [← scottContinuousOn_univ] at ⊢ hf hg
  exact ScottContinuousOn.prodMk (by grind) hf hg

@[simp, fun_prop]
lemma ScottContinuous.fst : ScottContinuous (Prod.fst : α × β → α) := by
  simp_rw [← scottContinuousOn_univ, ScottContinuousOn.fst]

@[simp, fun_prop]
lemma ScottContinuous.snd : ScottContinuous (Prod.snd : α × β → β) := by
  simp_rw [← scottContinuousOn_univ, ScottContinuousOn.snd]

end ScottContinuous

section SemilatticeSup

variable [SemilatticeSup β]

/-- The join operation is Scott continuous -/
@[fun_prop]
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

@[fun_prop]
lemma ScottContinuousOn.sup₂ {D : Set (Set (β × β))} :
    ScottContinuousOn D fun (a, b) => (a ⊔ b : β) :=
  ScottContinuous.sup₂.scottContinuousOn

end SemilatticeSup
