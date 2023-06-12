/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang

! This file was ported from Lean 3 source module topology.category.Top.limits.konig
! leanprover-community/mathlib commit dbdf71cee7bb20367cb7e37279c08b0c218cf967
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Category.Top.Limits.Basic

/-!
# Topological Kőnig's lemma

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A topological version of Kőnig's lemma is that the inverse limit of nonempty compact Hausdorff
spaces is nonempty.  (Note: this can be generalized further to inverse limits of nonempty compact
T0 spaces, where all the maps are closed maps; see [Stone1979] --- however there is an erratum
for Theorem 4 that the element in the inverse limit can have cofinally many components that are
not closed points.)

We give this in a more general form, which is that cofiltered limits
of nonempty compact Hausdorff spaces are nonempty
(`nonempty_limit_cone_of_compact_t2_cofiltered_system`).

This also applies to inverse limits, where `{J : Type u} [preorder J] [is_directed J (≤)]` and
`F : Jᵒᵖ ⥤ Top`.

The theorem is specialized to nonempty finite types (which are compact Hausdorff with the
discrete topology) in lemmas `nonempty_sections_of_finite_cofiltered_system` and
`nonempty_sections_of_finite_inverse_system` in the file `category_theory.cofiltered_system`.

(See <https://stacks.math.columbia.edu/tag/086J> for the Set version.)
-/


open CategoryTheory

open CategoryTheory.Limits

universe u v w

noncomputable section

namespace TopCat

section TopologicalKonig

variable {J : Type u} [SmallCategory J]

variable (F : J ⥤ TopCat.{u})

private abbrev finite_diagram_arrow {J : Type u} [SmallCategory J] (G : Finset J) :=
  Σ' (X Y : J) (mX : X ∈ G) (mY : Y ∈ G), X ⟶ Y

private abbrev finite_diagram (J : Type u) [SmallCategory J] :=
  Σ G : Finset J, Finset (FiniteDiagramArrow G)

/-- Partial sections of a cofiltered limit are sections when restricted to
a finite subset of objects and morphisms of `J`.
-/
def partialSections {J : Type u} [SmallCategory J] (F : J ⥤ TopCat.{u}) {G : Finset J}
    (H : Finset (FiniteDiagramArrow G)) : Set (∀ j, F.obj j) :=
  {u | ∀ {f : FiniteDiagramArrow G} (hf : f ∈ H), F.map f.2.2.2.2 (u f.1) = u f.2.1}
#align Top.partial_sections TopCat.partialSections

theorem partialSections.nonempty [IsCofilteredOrEmpty J] [h : ∀ j : J, Nonempty (F.obj j)]
    {G : Finset J} (H : Finset (FiniteDiagramArrow G)) : (partialSections F H).Nonempty := by
  classical
  cases isEmpty_or_nonempty J
  · exact ⟨isEmptyElim, fun j => IsEmpty.elim' inferInstance j.1⟩
  haveI : is_cofiltered J := ⟨⟩
  use fun j : J =>
    if hj : j ∈ G then F.map (is_cofiltered.inf_to G H hj) (h (is_cofiltered.inf G H)).some
    else (h _).some
  rintro ⟨X, Y, hX, hY, f⟩ hf
  dsimp only
  rwa [dif_pos hX, dif_pos hY, ← comp_app, ← F.map_comp, @is_cofiltered.inf_to_commutes _ _ _ G H]
#align Top.partial_sections.nonempty TopCat.partialSections.nonempty

theorem partialSections.directed :
    Directed Superset fun G : FiniteDiagram J => partialSections F G.2 := by
  classical
  intro A B
  let ιA : finite_diagram_arrow A.1 → finite_diagram_arrow (A.1 ⊔ B.1) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_left _ f.2.2.1, Finset.mem_union_left _ f.2.2.2.1, f.2.2.2.2⟩
  let ιB : finite_diagram_arrow B.1 → finite_diagram_arrow (A.1 ⊔ B.1) := fun f =>
    ⟨f.1, f.2.1, Finset.mem_union_right _ f.2.2.1, Finset.mem_union_right _ f.2.2.2.1, f.2.2.2.2⟩
  refine' ⟨⟨A.1 ⊔ B.1, A.2.image ιA ⊔ B.2.image ιB⟩, _, _⟩
  · rintro u hu f hf
    have : ιA f ∈ A.2.image ιA ⊔ B.2.image ιB :=
      by
      apply Finset.mem_union_left
      rw [Finset.mem_image]
      refine' ⟨f, hf, rfl⟩
    exact hu this
  · rintro u hu f hf
    have : ιB f ∈ A.2.image ιA ⊔ B.2.image ιB :=
      by
      apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine' ⟨f, hf, rfl⟩
    exact hu this
#align Top.partial_sections.directed TopCat.partialSections.directed

theorem partialSections.closed [∀ j : J, T2Space (F.obj j)] {G : Finset J}
    (H : Finset (FiniteDiagramArrow G)) : IsClosed (partialSections F H) :=
  by
  have :
    partial_sections F H =
      ⋂ (f : finite_diagram_arrow G) (hf : f ∈ H), {u | F.map f.2.2.2.2 (u f.1) = u f.2.1} :=
    by
    ext1
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [this]
  apply isClosed_biInter
  intro f hf
  apply isClosed_eq
  continuity
#align Top.partial_sections.closed TopCat.partialSections.closed

/-- Cofiltered limits of nonempty compact Hausdorff spaces are nonempty topological spaces.
-/
theorem nonempty_limitCone_of_compact_t2_cofiltered_system [IsCofilteredOrEmpty J]
    [∀ j : J, Nonempty (F.obj j)] [∀ j : J, CompactSpace (F.obj j)] [∀ j : J, T2Space (F.obj j)] :
    Nonempty (TopCat.limitCone.{u} F).pt := by
  classical
  obtain ⟨u, hu⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed (fun G => partial_sections F _)
      (partial_sections.directed F) (fun G => partial_sections.nonempty F _)
      (fun G => IsClosed.isCompact (partial_sections.closed F _)) fun G =>
      partial_sections.closed F _
  use u
  intro X Y f
  let G : finite_diagram J :=
    ⟨{X, Y},
      {⟨X, Y, by simp only [true_or_iff, eq_self_iff_true, Finset.mem_insert], by
          simp only [eq_self_iff_true, or_true_iff, Finset.mem_insert, Finset.mem_singleton], f⟩}⟩
  exact hu _ ⟨G, rfl⟩ (Finset.mem_singleton_self _)
#align Top.nonempty_limit_cone_of_compact_t2_cofiltered_system TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system

end TopologicalKonig

end TopCat

