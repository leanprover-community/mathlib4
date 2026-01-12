/-
Copyright (c) 2025 Valerio Proietti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Riccardo Brasca, Stefano Francaviglia,
Francesco Milizia, Valerio Proietti, Hang Lu Su, Lawrence Wu
-/
module

public import Mathlib.GroupTheory.Presentation
public import Mathlib.GroupTheory.Finiteness

/-!
This file will be replaced by the FinitelyPresentedGroup.lean file in HLS's branch
which will be added as a new PR. So `Group.IsFinitelyPresented` will be defined there
and the 3 theorems below will have to be adapted.

# Finitely presented groups

Main definitions:
* `Group.Presentation.IsFinite` asserts that a presentation has a finite type of generators
  and a finite set of relators.
* `Group.FinitelyPresented` is the property that a group is a quotient of `FreeGroup (Fin n)`
  by the normal closure of a finite set (via a surjective map).
* `Group.finitelyPresented_congr` shows that being finitely presented is invariant
  under group isomorphism.
* `Group.fg_of_finitelyPresented` shows that every finitely presented group is
  finitely generated.
-/

@[expose] public section

namespace Group

universe u

def IsNormalClosureOfFiniteSet {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = H

namespace Presentation

variable {G : Type*} [Group G] {ι : Type*}

/-- A presentation is finite if the generators and relators are finite. -/
def IsFinite (P : Group.Presentation G ι) : Prop :=
  Finite ι ∧ P.rels.Finite

end Presentation

section

variable {G : Type*} [Group G]

--this one
/--
From `Group.IsFinitelyPresented`, we can package the data into an actual `Group.Presentation`
which is `Presentation.IsFinite`.
-/
theorem exists_isFinite_presentation_of_finitelyPresented :
    Group.FinitelyPresented (G := G) →
      ∃ (ι : Type) (P : Group.Presentation G ι), P.IsFinite := by
  rintro ⟨n, π, hsurj, hnc⟩
  rcases hnc with ⟨rels, hker⟩
  -- Define the generator map `Fin n → G` induced from `π`.
  let val : Fin n → G := fun i => π (FreeGroup.of i)
  have hlift : FreeGroup.lift val = π := by ext i; simp [val]
  have hsurj' : Function.Surjective (FreeGroup.lift val) := by
    simpa [hlift] using hsurj
  have hcl : Subgroup.closure (Set.range val) = ⊤ := by
    simpa [FreeGroup.range_lift_eq_closure] using
      (MonoidHom.range_eq_top).2 hsurj'
  have hker' :
      (FreeGroup.lift val).ker = Subgroup.normalClosure (rels : Set (FreeGroup (Fin n))) := by
    -- `hker.2 : normalClosure rels = ker π`
    simpa [hlift] using hker.2.symm
  let P : Group.Presentation G (Fin n) :=
    { val := val
      closure_range_val := hcl
      rels := (rels : Set (FreeGroup (Fin n)))
      ker_eq_normalClosure := by simpa using hker' }
  refine ⟨Fin n, P, ?_⟩
  simpa [Presentation.IsFinite, P] using
    And.intro (inferInstance : Finite (Fin n)) hker.1

section

variable {G : Type*} [Group G]

--this one
/--
If `G` admits some finite presentation (on a finite generator type),
then `G` is finitely presented.
-/
theorem finitelyPresented_of_exists_isFinite_presentation :
    (∃ (ι : Type*) (P : Group.Presentation G ι), P.IsFinite) →
      Group.IsFinitelyPresented (G := G) := by
  rintro ⟨ι, P, hP⟩
  refine finitelyPresented_of_exists_presentedGroup (G := G) ?_
  refine ⟨ι, P.rels, hP.1, hP.2, ?_⟩
  refine ⟨?_⟩
  simpa [Presentation.presentedGroup] using P.equivPresentedGroup

--this one
/--
Characterization: `G` is finitely presented iff it admits a presentation
which is `Presentation.IsFinite`.
-/
theorem finitelyPresented_iff_exists_isFinite_presentation :
    Group.IsFinitelyPresented (G := G) ↔
      ∃ (ι : Type) (P : Group.Presentation G ι), P.IsFinite := by
  constructor
  · intro h
    simpa using (exists_isFinite_presentation_of_finitelyPresented (G := G) h)
  · intro h
    exact finitelyPresented_of_exists_isFinite_presentation (G := G) h

end

end Group
