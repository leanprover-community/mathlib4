/-
Copyright (c) 2025 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Riccardo Brasca, Stefano Francaviglia, Hang Lu Su,
Francesco Milizia, Valerio Proietti, Lawrence Wu
-/

import Mathlib.GroupTheory.Presentation
import Mathlib.GroupTheory.Finiteness

/-!
# Finitely presented groups

Main definitions:
* `Group.Presentation.IsFinite` records that the generators and relators are finite.
* `Group.FinitelyPresented` says that a group has some finite presentation.

Main results:
* `Group.finitelyPresented_iff_exists_presentedGroup` connects with `GroupTheory.PresentedGroup`.
* `Group.fg_of_finitelyPresented` shows that finitely presented groups are finitely generated.
* `Group.finitelyPresented_congr` shows invariance under group isomorphisms.
* `PresentedGroup.toPresentation` gives the canonical finite presentation of a presented group.
-/

namespace Group

universe u

namespace Presentation

variable {G : Type u} [Group G]

/-- A presentation is finite if the generators and relators are finite. -/
def IsFinite (P : Group.Presentation (G := G)) : Prop :=
  Finite P.ι ∧ P.rels.Finite

end Presentation

/-- A group is finitely presented if it admits a finite presentation. -/
def FinitelyPresented (G : Type u) [Group G] : Prop :=
  ∃ P : Group.Presentation (G := G), P.IsFinite

section

variable {G : Type u} [Group G]

theorem finitelyPresented_exists_presentedGroup :
    Group.FinitelyPresented (G := G) →
      ∃ (α : Type u) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G) := by
  rintro ⟨P, hP⟩
  refine ⟨P.ι, P.rels, hP.1, hP.2, ?_⟩
  refine ⟨?_⟩
  simpa [Presentation.presentedGroup] using P.equivPresentedGroup

/-- Finitely presented groups are finitely generated. -/
theorem fg_of_finitelyPresented :
    Group.FinitelyPresented (G := G) → Group.FG G := by
  rintro ⟨P, hP⟩
  classical
  refine (Group.fg_iff).2 ?_
  haveI : Finite P.ι := hP.1
  refine ⟨Set.range P.val, ?_, ?_⟩
  · simpa using P.closure_range_val
  · simpa using (Set.finite_range P.val)

/-- `FinitelyPresented` is invariant under group isomorphism. -/
theorem finitelyPresented_congr {H : Type u} [Group H] (e : G ≃* H) :
    Group.FinitelyPresented (G := G) ↔ Group.FinitelyPresented (G := H) := by
  constructor
  · rintro ⟨P, hP⟩
    refine ⟨Group.Presentation.mapMulEquiv (G := H) (P := P) e, ?_⟩
    simpa [Group.Presentation.IsFinite, Group.Presentation.mapMulEquiv] using hP
  · rintro ⟨P, hP⟩
    refine ⟨Group.Presentation.mapMulEquiv (G := G) (P := P) e.symm, ?_⟩
    simpa [Group.Presentation.IsFinite, Group.Presentation.mapMulEquiv] using hP

end

end Group

namespace PresentedGroup

universe v
variable {α : Type v} (rels : Set (FreeGroup α))

@[simp]
theorem lift_of_eq_mk :
    FreeGroup.lift (PresentedGroup.of (rels := rels)) = PresentedGroup.mk rels := by
  ext a
  simp [PresentedGroup.of]

/-- The canonical `Group.Presentation` of `PresentedGroup rels`. -/
def toPresentation : Group.Presentation (G := PresentedGroup rels) :=
{ ι := α
  val := (PresentedGroup.of (rels := rels))
  closure_range_val := by
    simp only [closure_range_of]
  rels := rels
  ker_eq_normalClosure := by
    ext x
    simp [MonoidHom.mem_ker, PresentedGroup.mk_eq_one_iff, lift_of_eq_mk (rels := rels)] }

theorem finitelyPresented_of_finite
    [Finite α] (hrels : rels.Finite) :
    Group.FinitelyPresented (G := PresentedGroup rels) := by
  refine ⟨toPresentation (rels := rels), ?_⟩
  exact And.intro (inferInstance : Finite α) hrels

end PresentedGroup

namespace Group

universe u

section

variable {G : Type u} [Group G]

theorem finitelyPresented_of_exists_presentedGroup :
    (∃ (α : Type u) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G)) →
      Group.FinitelyPresented (G := G) := by
  rintro ⟨α, rels, hα, hrels, ⟨e⟩⟩
  classical
  haveI : Finite α := hα
  have hPG : Group.FinitelyPresented (G := PresentedGroup rels) :=
    PresentedGroup.finitelyPresented_of_finite (rels := rels) hrels
  exact (Group.finitelyPresented_congr (G := PresentedGroup rels) (H := G) e).1 hPG

theorem finitelyPresented_iff_exists_presentedGroup :
    Group.FinitelyPresented (G := G) ↔
      ∃ (α : Type u) (rels : Set (FreeGroup α)),
        Finite α ∧ rels.Finite ∧ Nonempty (PresentedGroup rels ≃* G) := by
  constructor
  · exact finitelyPresented_exists_presentedGroup (G := G)
  · exact finitelyPresented_of_exists_presentedGroup (G := G)

end

end Group
