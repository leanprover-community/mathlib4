/-
Copyright (c) 2025 Valerio Proietti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Riccardo Brasca, Stefano Francaviglia,
Francesco Milizia, Valerio Proietti, Hang Lu Su, Lawrence Wu
-/
module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Presentation of a group
This file introduces the notion of 'Presentation' of a group, aligned with
`Mathlib.GroupTheory.PresentedGroup`.

Main definitions:
* `Group.GeneratingSet` packages a type of generators with a map to the group whose range
  generates it.
* `Group.Presentation` extends a generating set with relators and the usual kernel condition.
* `Group.Presentation.toGroup` is the canonical map `PresentedGroup P.rels →* G`.
* `Group.Presentation.mapMulEquiv` transports a presentation along a group isomorphism.
* `Group.Presentation.equivPresentedGroup` identifies `PresentedGroup P.rels` with `G`.
-/

@[expose] public section

namespace Group

/-- A generating system for a group `G` indexed by `ι`. -/
-- direct presentation, don't do it in two steps
structure GeneratingSet (G : Type*) [Group G] (ι : Type*) where
  /-- The assignment of each abstract generator to an element of `G`. -/
  val : ι → G
  /-- The images of the generators generate `G`. -/
  closure_range_val : Subgroup.closure (Set.range val) = ⊤

/-- A presentation of a group `G` with generators indexed by `ι`. -/
structure Presentation (G : Type*) [Group G] (ι : Type*)
    extends GeneratingSet G ι where
  /-- The relations (relators). -/
  rels : Set (FreeGroup ι)
  /-- Kernel of the induced map is the normal closure of the relators. -/
  ker_eq_normalClosure : (FreeGroup.lift val).ker = Subgroup.normalClosure rels

namespace GeneratingSet

variable {G : Type*} [Group G] {ι : Type*}

/-- If the range of `X.val` generates `G`, then `FreeGroup.lift X.val` is surjective. -/
theorem lift_surjective (X : GeneratingSet G ι) :
    Function.Surjective (FreeGroup.lift X.val) := by
  have hrange : (FreeGroup.lift X.val).range = ⊤ := by
    simp [FreeGroup.range_lift_eq_closure, X.closure_range_val]
  exact MonoidHom.range_eq_top.mp hrange

end GeneratingSet

namespace Presentation

variable {G : Type*} [Group G] {ι : Type*}

/-- The `PresentedGroup` attached to a `Group.Presentation`. -/
abbrev presentedGroup (P : Presentation G ι) : Type _ :=
  PresentedGroup P.rels

@[simp]
lemma presentedGroup_def (P : Presentation G ι) :
    P.presentedGroup = PresentedGroup P.rels := rfl

/-- Each relator maps to `1` under the induced map `FreeGroup ι →* G`. -/
theorem lift_eq_one_of_mem_rels (P : Presentation G ι) {r : FreeGroup ι}
    (hr : r ∈ P.rels) :
    FreeGroup.lift P.val r = 1 := by
  have : r ∈ (FreeGroup.lift P.val).ker := by
    simpa [P.ker_eq_normalClosure] using
      (Subgroup.subset_normalClosure hr :
        r ∈ Subgroup.normalClosure P.rels)
  simpa [MonoidHom.mem_ker] using this

/--
Given a `Group.Presentation G ι`, we obtain the canonical map
`PresentedGroup P.rels →* G` (sending generators to `P.val`).
-/
def toGroup (P : Presentation G ι) :
    P.presentedGroup →* G :=
  PresentedGroup.toGroup (rels := P.rels)
    (f := P.val) (by
      intro r hr
      simpa using (P.lift_eq_one_of_mem_rels (r := r) hr))

@[simp]
theorem toGroup_of (P : Presentation G ι) (x : ι) :
    P.toGroup (PresentedGroup.of (rels := P.rels) x) = P.val x := by
  simp [Presentation.toGroup]

/--
Transport a presentation across a group isomorphism.
If `P` is a presentation of `G` and `e : G ≃* H`, we get a presentation of `H`
with the same generators/relators and generator map composed with `e`.
-/
def mapMulEquiv {G : Type*} [Group G] {H : Type*} [Group H]
    {ι : Type*} (P : Presentation G ι) (e : G ≃* H) :
    Presentation H ι :=
{ val := fun i => e (P.val i)
  closure_range_val := by
    -- express the new range as the image of the old range
    have hrange :
        Set.range (fun i : ι => e (P.val i)) = e '' Set.range P.val := by
      simpa [Function.comp] using
        (Set.range_comp (f := P.val) (g := fun x : G => e x))
    -- map closure along `e`
    have hcl :
        Subgroup.closure (Set.range fun i : ι => e (P.val i))
          = Subgroup.map e.toMonoidHom (Subgroup.closure (Set.range P.val)) := by
      simpa [hrange] using
        (MonoidHom.map_closure (e.toMonoidHom) (Set.range P.val)).symm
    simp [hcl, P.closure_range_val]
  rels := P.rels
  ker_eq_normalClosure := by
    -- identify the lift as a composition
    have hlift :
        FreeGroup.lift (fun i : ι => e (P.val i))
          = e.toMonoidHom.comp (FreeGroup.lift P.val) := by
      ext i
      simp
    -- kernel unchanged because `e` is injective
    have hker :
        (FreeGroup.lift (fun i : ι => e (P.val i))).ker
          = (FreeGroup.lift P.val).ker := by
      apply le_antisymm
      · intro x hx
        -- `x ∈ ker (e ∘ φ)` implies `φ x = 1` by injectivity
        have : e (FreeGroup.lift P.val x) = 1 := by
          -- `hx : (e ∘ φ) x = 1`
          simpa [hlift, MonoidHom.mem_ker] using hx
        have : FreeGroup.lift P.val x = 1 := e.injective (by simpa using this)
        simpa [MonoidHom.mem_ker] using this
      · intro x hx
        -- `x ∈ ker φ` implies `x ∈ ker (e ∘ φ)`
        have : FreeGroup.lift P.val x = 1 := by
          simpa [MonoidHom.mem_ker] using hx
        simp [hlift, MonoidHom.mem_ker, this]
    simpa [hker] using P.ker_eq_normalClosure }

/--
From a `Group.Presentation G ι`, build a group isomorphism
`PresentedGroup P.rels ≃* G`.
-/
noncomputable def equivPresentedGroup {G : Type*} [Group G] {ι : Type*}
    (P : Presentation G ι) : P.presentedGroup ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq P.ker_eq_normalClosure.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (FreeGroup.lift P.val)
      P.toGeneratingSet.lift_surjective)

/-!
Any two presentations of the same group present isomorphic groups.
-/
-- better name for this?
noncomputable def equivPresentedGroups {G : Type*} [Group G]
    {ι κ : Type*} (P : Presentation G ι) (Q : Presentation G κ) :
    P.presentedGroup ≃* Q.presentedGroup :=
  P.equivPresentedGroup.trans Q.equivPresentedGroup.symm

end Presentation

namespace PresentedGroup

variable {α : Type*} (rels : Set (FreeGroup α))

@[simp]
theorem lift_of_eq_mk :
    FreeGroup.lift (PresentedGroup.of (rels := rels)) = PresentedGroup.mk rels := by
  ext a
  simp [PresentedGroup.of]

/-- The canonical `Group.Presentation` of `PresentedGroup rels`. -/
def toPresentation : Group.Presentation (PresentedGroup rels) α where
  val := PresentedGroup.of (rels := rels)
  closure_range_val := by
    simp [PresentedGroup.closure_range_of]
  rels := rels
  ker_eq_normalClosure := by
    ext x
    simp [MonoidHom.mem_ker, PresentedGroup.mk_eq_one_iff, lift_of_eq_mk (rels := rels)]

end PresentedGroup

/-!
## Tietze transformations

This section records the four standard Tietze moves for group presentations.
-/

namespace Tietze

variable {G : Type*} [Group G] {ι : Type*}

/-!
### Equal normal closures give isomorphic presented groups
-/

noncomputable def equiv_of_normalClosure_eq
    (rels₁ rels₂ : Set (FreeGroup ι))
    (h : Subgroup.normalClosure rels₁ = Subgroup.normalClosure rels₂) :
    PresentedGroup rels₁ ≃* PresentedGroup rels₂ := by
  simpa [PresentedGroup] using
    (QuotientGroup.quotientMulEquivOfEq (G := FreeGroup ι)
      (M := Subgroup.normalClosure rels₁) (N := Subgroup.normalClosure rels₂) h)

/-- Adding a relator already in the normal closure does not change the normal closure. -/
lemma normalClosure_union_singleton_eq_of_mem
    (rels : Set (FreeGroup ι)) (r : FreeGroup ι)
    (hr : r ∈ Subgroup.normalClosure rels) :
    Subgroup.normalClosure (rels ∪ {r}) = Subgroup.normalClosure rels := by
  apply le_antisymm
  · refine Subgroup.normalClosure_le_normal
      (s := rels ∪ {r}) (N := Subgroup.normalClosure rels) ?_
    intro x hx
    rcases hx with hx | hx
    · exact Subgroup.subset_normalClosure hx
    · rcases Set.mem_singleton_iff.mp hx with rfl
      simpa using hr
  · exact Subgroup.normalClosure_mono (Set.subset_union_left)

/-!
### (1) Add a derived relation
-/

/--
Given `P : Group.Presentation G ι`, if `r` lies in the normal closure of `P.rels`,
we can add `r` as a relator and still get a presentation of `G`.
-/
def addRelator (P : Group.Presentation G ι) (r : FreeGroup ι)
    (hr : r ∈ Subgroup.normalClosure P.rels) :
    Group.Presentation G ι where
  val := P.val
  closure_range_val := P.closure_range_val
  rels := Set.insert r P.rels
  ker_eq_normalClosure := by
    -- use that the normal closure does not change after inserting a derived relator
    have hN :
        Subgroup.normalClosure (Set.insert r P.rels) =
          Subgroup.normalClosure P.rels := by
      simpa [Set.insert, Set.union_comm] using
        (normalClosure_union_singleton_eq_of_mem (ι := ι) (rels := P.rels) (r := r) hr)
    -- rewrite `P.ker_eq_normalClosure` along `hN`
    simpa [hN] using P.ker_eq_normalClosure

/--
Tietze (1), at the level of presented groups: adding a derived relator gives an isomorphic
presented group.
-/
noncomputable def add_relator_equiv
    (P : Group.Presentation G ι) (r : FreeGroup ι)
    (hr : r ∈ Subgroup.normalClosure P.rels) :
    P.presentedGroup ≃* (addRelator (G := G) (ι := ι) P r hr).presentedGroup := by
  simpa using
    (Presentation.equivPresentedGroups (G := G) (P := P)
      (Q := addRelator (G := G) (ι := ι) P r hr))

/-!
### (2) Remove a derived relation
-/

/--
Given `P : Group.Presentation G ι`, if a relator `r` is derivable from the other relators
(i.e. `r ∈ normalClosure (P.rels \ {r})`),
then we may remove it and still get a presentation of `G`.
-/
def removeRelator (P : Group.Presentation G ι) (r : FreeGroup ι)
    (hr : r ∈ Subgroup.normalClosure (P.rels \ {r})) :
    Group.Presentation G ι where
  val := P.val
  closure_range_val := P.closure_range_val
  rels := P.rels \ {r}
  ker_eq_normalClosure := by
    -- Show that every relator of `P` lies in the normal closure of `P.rels \\ {r}`.
    have hsubset :
        P.rels ⊆ Subgroup.normalClosure (P.rels \ {r}) := by
      intro x hx
      by_cases hxr : x = r
      · -- the removed relator is in the normal closure by assumption
        simpa [hxr] using hr
      · -- the others are already in the subset
        have hx' : x ∈ P.rels \ {r} := ⟨hx, by simp [Set.mem_singleton_iff, hxr]⟩
        exact Subgroup.subset_normalClosure hx'
    -- so the normal closure of `P.rels` is contained in that of `P.rels \\ {r}`
    have hle :
        Subgroup.normalClosure P.rels ≤
          Subgroup.normalClosure (P.rels \ {r}) :=
      Subgroup.normalClosure_le_normal
        (s := P.rels) (N := Subgroup.normalClosure (P.rels \ {r})) hsubset
    have hge :
        Subgroup.normalClosure (P.rels \ {r}) ≤
          Subgroup.normalClosure P.rels :=
      Subgroup.normalClosure_mono (by intro x hx; exact hx.1)
    have hN :
        Subgroup.normalClosure (P.rels \ {r}) =
          Subgroup.normalClosure P.rels :=
      le_antisymm hge hle
    simpa [hN] using P.ker_eq_normalClosure

/--
Tietze (2), at the level of presented groups: removing a derivable relator gives an isomorphic
presented group.
-/
noncomputable def remove_relator_equiv
    (P : Group.Presentation G ι) (r : FreeGroup ι)
    (hr : r ∈ Subgroup.normalClosure (P.rels \ {r})) :
    P.presentedGroup ≃* (removeRelator (G := G) (ι := ι) P r hr).presentedGroup := by
  simpa using
    (Presentation.equivPresentedGroups (G := G) (P := P)
      (Q := removeRelator (G := G) (ι := ι) P r hr))

end Tietze

end Group
