/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Bounds.Lattice

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
    ScottContinuousOn D₁ f := fun _  hdD₁ hd₁ hd₂ _ hda => hf (hD hdD₁) hd₁ hd₂ hda

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
sets. It can be shown that a function is Scott continuous if and only if it is continuous wrt the
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

section CompleteLattice

variable [CompleteLattice α] [CompleteLattice β]

lemma scottContinuous_iff_map_sSup {f : α → β} : ScottContinuous f ↔
    ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → f (sSup d) = sSup (f '' d) :=
  ⟨fun h _ d₁ d₂ => by rw [IsLUB.sSup_eq (h d₁ d₂ (isLUB_iff_sSup_eq.mpr rfl))],
    fun h _ d₁ d₂ _ hda => by rw [isLUB_iff_sSup_eq, ← (h d₁ d₂), IsLUB.sSup_eq hda]⟩

alias ⟨ScottContinuous.map_sSup, ScottContinuous.of_map_sSup⟩ :=
  scottContinuous_iff_map_sSup

end CompleteLattice

section Pi

variable {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [Preorder β]

/-
open Set in
lemma Pi.upperBounds {f : (Π i, α i) → β} (hf : Monotone f)
    {d : Set (Π i, α i)} (hd : DirectedOn (· ≤ ·) d) :
    upperBounds (f '' d) = upperBounds (f '' (pi univ (fun i => (fun a => a i) '' d))) := by
  apply le_antisymm
  · intro u hu c hc
    simp at hc
    obtain ⟨a, ⟨ha, hfac⟩⟩ := hc
    obtain ⟨z,hz⟩ := hd
    sorry
  · exact upperBounds_mono_set (image_mono (by intro a ha₁ i hi; use a))
-/


end Pi

section Products

variable {γ : Type*}

variable [Preorder α] [Preorder β] [Preorder γ]

/-- TODO: Come up with better name -/
lemma step1 {f : α × β → γ} {d : Set (α × β)} (hd₁ : (Prod.snd '' d).Nonempty)
    (hd₂ : DirectedOn (· ≤ ·) (Prod.snd '' d)) {p₁ : α} {p₂ : β} (h : IsLUB d (p₁,p₂))
    (h₁ : ∀ a, ScottContinuous (fun b => f (a,b))) {a : α} :
    IsLUB (f '' {a} ×ˢ (Prod.snd '' d)) (f (a,p₂)) := by
  simp only [singleton_prod]
  have e1 : IsLUB (Prod.snd '' d) p₂ := ((isLUB_prod (p₁,p₂)).mp h).2
  have e3 {S : Set β} : f '' ((fun b ↦ (a, b)) '' S) = (fun b ↦ f (a, b)) '' S := by
    exact image_image f (fun b ↦ (a, b)) S
  rw [e3]
  exact h₁ a hd₁ hd₂ e1

lemma ScottContinuous_prod_of_ScottContinuous {f : α × β → γ}
    (h₁ : ∀ a, ScottContinuous (fun b => f (a,b))) (h₂ : ∀ b, ScottContinuous (fun a => f (a,b))) :
    ScottContinuous f := by
  intro d hd₁ hd₂ p hdp
  rw [isLUB_congr ((monotone_prod_iff.mpr ⟨(fun a => (h₁ a).monotone),
    (fun a => (h₂ a).monotone)⟩).upperBounds_image_of_directedOn_prod hd₂)]
  rw [← iUnion_of_singleton_coe (Prod.fst '' d), iUnion_prod_const, image_iUnion]
  rw [← isLUB_iUnion_iff_of_isLUB (fun a => step1 (Nonempty.image Prod.snd hd₁) hd₂.snd hdp h₁) _]
  have e2 : IsLUB ((fun a ↦ f (a, p.2)) '' (Prod.fst '' d)) (f (p.1,p.2)) :=
    h₂ p.2 (Nonempty.image Prod.fst hd₁) hd₂.fst ((isLUB_prod (p.1,p.2)).mp hdp).1
  rw [Set.range]
  rw [Set.image] at e2
  aesop

end Products

section SemilatticeSup

variable [Preorder α]

lemma ScottContinuousOn.sup₂ [SemilatticeSup β] {D : Set (Set (β × β))} :
    ScottContinuousOn D fun (a, b) => (a ⊔ b : β) := by
  simp only
  intro d _ _ _ ⟨p₁, p₂⟩ hdp
  rw [IsLUB, IsLeast, upperBounds] at hdp
  simp only [Prod.forall, mem_setOf_eq, Prod.mk_le_mk] at hdp
  rw [IsLUB, IsLeast, upperBounds]
  constructor
  · simp only [mem_image, Prod.exists, forall_exists_index, and_imp, mem_setOf_eq]
    intro a b₁ b₂ hbd hba
    rw [← hba]
    exact sup_le_sup (hdp.1 _ _ hbd).1 (hdp.1 _ _ hbd).2
  · simp only [mem_image, Prod.exists, forall_exists_index, and_imp]
    intro b hb
    simp only [sup_le_iff]
    have e1 : (p₁, p₂) ∈ lowerBounds {x | ∀ (b₁ b₂ : β), (b₁, b₂) ∈ d → (b₁, b₂) ≤ x} := hdp.2
    rw [lowerBounds] at e1
    simp only [mem_setOf_eq, Prod.forall, Prod.mk_le_mk] at e1
    apply e1
    intro b₁ b₂ hb'
    exact sup_le_iff.mp (hb b₁ b₂ hb' rfl)

lemma inf_sSup_eq_sSup_map  [CompleteLinearOrder β] (a : β) (d : Set β) :
    a ⊓ sSup d = sSup ((fun b ↦ a ⊓ b) '' d) := by
  apply eq_of_forall_ge_iff fun e ↦ ?_
  simp only [inf_le_iff, sSup_le_iff, ← forall_or_left, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

/-
lemma upperBounds_eq [CompleteLinearOrder β] (a : β) (s : Set β) :
   (fun b ↦ a ⊓ b) '' (upperBounds s) = upperBounds ((fun b ↦ a ⊓ b) '' s) := sorry
  --apply eq_of_forall_ge_iff fun e ↦ ?_
  --simp only [le_eq_subset, image_subset_iff]

-/

/-
  rw [upperBounds, upperBounds]
  simp [← forall_or_right, ← forall_or_left]
  apply le_antisymm
  · intro u hu
    simp only [mem_setOf_eq]
    simp at hu
    obtain ⟨x,⟨hx1,hx2⟩⟩ := hu
    intro b hb
    rw [← hx2]

    aesop?
-/


/-
lemma inf_IsLUB_iff_IsLUB_map [CompleteLinearOrder β] (a u : β) (d : Set β) :
    IsLUB d u ↔ IsLUB ((fun b ↦ a ⊓ b) '' d) (a ⊓ u) := by
  rw [IsLUB, IsLUB, IsLeast, IsLeast]
  have e1 : u ∈ upperBounds d ↔ a ⊓ u ∈ upperBounds ((fun b ↦ a ⊓ b) '' d) := by
    rw [← upperBounds_eq]
    simp only [mem_image]

    exact?
  rw [upperBounds_eq]
-/



lemma sSup_inf_eq_sSup_map [CompleteLinearOrder β] (b : β) (d : Set β) :
    sSup d ⊓ b = sSup ((fun a ↦ a ⊓ b) '' d) := by
  apply eq_of_forall_ge_iff fun e ↦ ?_
  simp [inf_le_iff, sSup_le_iff, ← forall_or_right, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]

lemma left_cont_inf [CompleteLinearOrder β] (a : β) : ScottContinuous fun b ↦ a ⊓ b := by
  refine ScottContinuous.of_map_sSup (fun d _ _ ↦ by rw [inf_sSup_eq_sSup_map])

lemma right_cont_inf [CompleteLinearOrder β] (b : β) : ScottContinuous fun a ↦ a ⊓ b := by
  refine ScottContinuous.of_map_sSup (fun d _ _ ↦ by rw [sSup_inf_eq_sSup_map])

lemma ScottContinuousOn.inf₂ [CompleteLinearOrder β] :
    ScottContinuous fun (a, b) => (a ⊓ b : β) :=
  ScottContinuous_prod_of_ScottContinuous left_cont_inf right_cont_inf


end SemilatticeSup
