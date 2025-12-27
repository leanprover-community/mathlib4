/-
Copyright (c) 2025 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Riccardo Brasca, Stefano Francaviglia, Hang Lu Su,
Francesco Milizia, Valerio Proietti, Lawrence Wu
-/
module

public import Mathlib.GroupTheory.Presentation
public import Mathlib.GroupTheory.Finiteness

/-!
# Finitely presented groups

Main definitions:
* `Group.Presentation.IsFinite` records that the generators and relators are finite.
* `Group.FinitelyPresented` says that a group has some finite presentation.

Main results:
* `Group.finitelyPresented_iff_exists_presentedGroup` connects with `GroupTheory.PresentedGroup`.
* `Group.fg_of_finitelyPresented` shows that finitely presented groups are finitely generated.
* `Group.finitelyPresented_congr` shows invariance under group isomorphisms.
-/

@[expose] public section

namespace Group

universe u v

namespace Presentation

variable {G : Type u} [Group G] {ι : Type*}

/-- A presentation is finite if the generators and relators are finite. -/
def IsFinite (P : Group.Presentation G ι) : Prop :=
  Finite ι ∧ P.rels.Finite

end Presentation

/-- A group is finitely presented if it admits a finite presentation. -/
def FinitelyPresented (G : Type u) [Group G] : Prop :=
  ∃ (ι : Type*) (P : Group.Presentation G ι), P.IsFinite

section

variable {G : Type u} [Group G]

/-- A finite presentation of `G` yields finite relators and
an isomorphism with a PresentedGroup. -/
theorem finitelyPresented_exists_presentedGroup :
    Group.FinitelyPresented.{u, v} G →
      ∃ (α : Type v) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G) := by
  rintro ⟨ι, P, hP⟩
  refine ⟨ι, P.rels, hP.1, hP.2, ?_⟩
  refine ⟨?_⟩
  simpa [Presentation.presentedGroup] using P.equivPresentedGroup

/-- Finitely presented groups are finitely generated. -/
theorem fg_of_finitelyPresented :
    Group.FinitelyPresented G → Group.FG G := by
  rintro ⟨ι, P, hP⟩
  classical
  refine (Group.fg_iff).2 ?_
  -- hP.1 is now the finiteness of ι directly
  haveI : Finite ι := hP.1
  refine ⟨Set.range P.val, ?_, ?_⟩
  · simpa using P.closure_range_val
  · simpa using (Set.finite_range P.val)

/-- `FinitelyPresented` is invariant under group isomorphism. -/
theorem finitelyPresented_congr {H : Type _} [Group H] (e : G ≃* H) :
    Group.FinitelyPresented.{u, v} G ↔ Group.FinitelyPresented.{_, v} H := by
  constructor
  · rintro ⟨ι, P, hP⟩
    refine ⟨ι, Group.Presentation.mapMulEquiv P e, ?_⟩
    simpa [Group.Presentation.IsFinite, Group.Presentation.mapMulEquiv] using hP
  · rintro ⟨ι, P, hP⟩
    refine ⟨ι, Group.Presentation.mapMulEquiv P e.symm, ?_⟩
    simpa [Group.Presentation.IsFinite, Group.Presentation.mapMulEquiv] using hP

end

namespace PresentedGroup

variable {α : Type v} (rels : Set (FreeGroup α))

/-- Finite generators and relators make `PresentedGroup rels` finitely presented. -/
theorem finitelyPresented_of_finite
    [Finite α] (hrels : rels.Finite) :
    Group.FinitelyPresented.{v, v} (PresentedGroup rels) := by
  refine ⟨α, toPresentation rels, ?_⟩
  exact And.intro (inferInstance : Finite α) hrels

end PresentedGroup

section

variable {G : Type u} [Group G]

/-- An isomorphism from a finitely presented presented group makes `G` finitely presented. -/
theorem finitelyPresented_of_exists_presentedGroup :
    (∃ (α : Type v) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G)) →
      Group.FinitelyPresented.{u, v} G := by
  rintro ⟨α, rels, hα, hrels, ⟨e⟩⟩
  classical
  haveI : Finite α := hα
  have hPG : Group.FinitelyPresented (PresentedGroup rels) :=
    PresentedGroup.finitelyPresented_of_finite (rels := rels) hrels
  exact (Group.finitelyPresented_congr (G := PresentedGroup rels) (H := G) e).1 hPG

/-- Characterizes finitely presented groups via isomorphism with a PresentedGroup
with finite generators and relators. -/
theorem finitelyPresented_iff_exists_presentedGroup :
    Group.FinitelyPresented.{u, v} G ↔
      ∃ (α : Type v) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G) := by
  constructor
  · exact finitelyPresented_exists_presentedGroup
  · exact finitelyPresented_of_exists_presentedGroup

end

end Group
