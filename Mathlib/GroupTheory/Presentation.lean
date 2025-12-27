/-
Copyright (c) 2025 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Riccardo Brasca, Stefano Francaviglia, Hang Lu Su,
Francesco Milizia, Valerio Proietti, Lawrence Wu
-/
module

public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Presentation of a group
This file introduces generating systems and presentations for a group, aligned with
`Mathlib.GroupTheory.PresentedGroup`.

Main definitions:
* `Group.GeneratingSystem` packages a type of generators with a map to the group whose range
  generates it.
* `Group.Presentation` extends a generating system with relators and the usual kernel condition.
* `Group.Presentation.toGroup` is the canonical map `PresentedGroup P.rels →* G`.
* `Group.Presentation.mapMulEquiv` transports a presentation along a group isomorphism.
* `Group.Presentation.equivPresentedGroup` identifies `PresentedGroup P.rels` with `G`.
-/

@[expose] public section

universe u v

namespace Group

/-- A generating system for a group `G` indexed by `ι`. -/
structure GeneratingSystem (G : Type u) [Group G] (ι : Type*) where
  /-- The assignment of each abstract generator to an element of `G`. -/
  val : ι → G
  /-- The images of the generators generate `G`. -/
  closure_range_val : Subgroup.closure (Set.range val) = ⊤

/-- A presentation of a group `G` with generators indexed by `ι`. -/
structure Presentation (G : Type u) [Group G] (ι : Type*)
    extends GeneratingSystem G ι where
  /-- The relations (relators). -/
  rels : Set (FreeGroup ι)
  /-- Kernel of the induced map is the normal closure of the relators. -/
  ker_eq_normalClosure : (FreeGroup.lift val).ker = Subgroup.normalClosure rels

namespace GeneratingSystem

variable {G : Type u} [Group G] {ι : Type v}

/-- If the range of `X.val` generates `G`, then `FreeGroup.lift X.val` is surjective. -/
theorem lift_surjective (X : GeneratingSystem G ι) :
    Function.Surjective (FreeGroup.lift X.val) := by
  have hrange : (FreeGroup.lift X.val).range = ⊤ := by
    simp [FreeGroup.range_lift_eq_closure, X.closure_range_val]
  exact MonoidHom.range_eq_top.mp hrange

end GeneratingSystem

namespace Presentation

variable {G : Type u} [Group G] {ι : Type*}

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
def mapMulEquiv {G : Type u} [Group G] {H : Type _} [Group H]
    (P : Presentation G ι) (e : G ≃* H) :
    Presentation H ι := by
  refine
    { val := fun i => e (P.val i)
      closure_range_val := ?_
      rels := P.rels
      ker_eq_normalClosure := ?_ }
  · have hrange :
        Set.range (fun i : ι => e (P.val i)) = e '' Set.range P.val := by
      simpa [Function.comp] using
        (Set.range_comp (f := P.val) (g := fun x : G => e x))
    calc
      Subgroup.closure (Set.range fun i : ι => e (P.val i))
          = Subgroup.map e.toMonoidHom (Subgroup.closure (Set.range P.val)) := by
            simpa [hrange] using
              (MonoidHom.map_closure (e.toMonoidHom) (Set.range P.val)).symm
      _ = ⊤ := by simp [P.closure_range_val]
  · have hlift :
        FreeGroup.lift (fun i : ι => e (P.val i))
          = e.toMonoidHom.comp (FreeGroup.lift P.val) := by
      ext i; simp
    calc
      (FreeGroup.lift (fun i : ι => e (P.val i))).ker
          = (FreeGroup.lift P.val).ker := by
            ext x; constructor <;> intro hx
            · have hx' : e (FreeGroup.lift P.val x) = 1 := by
                simpa [hlift, MonoidHom.mem_ker] using hx
              have hx'' : FreeGroup.lift P.val x = 1 :=
                e.injective (by simpa using hx')
              simpa [MonoidHom.mem_ker] using hx''
            · simpa [hlift, MonoidHom.mem_ker] using hx
      _ = Subgroup.normalClosure P.rels := P.ker_eq_normalClosure

/--
From a `Group.Presentation G ι`, build a group isomorphism
`PresentedGroup P.rels ≃* G`.
-/
noncomputable def equivPresentedGroup (P : Presentation G ι) :
    P.presentedGroup ≃* G := by
  let φ : FreeGroup ι →* G := FreeGroup.lift P.val
  have hsurj : Function.Surjective φ := P.toGeneratingSystem.lift_surjective
  have e₁ :
      (FreeGroup ι ⧸ Subgroup.normalClosure P.rels) ≃*
      (FreeGroup ι ⧸ φ.ker) :=
    QuotientGroup.quotientMulEquivOfEq (G := FreeGroup ι)
      (M := Subgroup.normalClosure P.rels) (N := φ.ker) (by
        simpa [φ] using P.ker_eq_normalClosure.symm)
  have e₂ : (FreeGroup ι ⧸ φ.ker) ≃* G :=
    QuotientGroup.quotientKerEquivOfSurjective φ hsurj
  simpa [Presentation.presentedGroup, PresentedGroup] using e₁.trans e₂

end Presentation

namespace PresentedGroup

variable {α : Type v} (rels : Set (FreeGroup α))

@[simp]
theorem lift_of_eq_mk :
    FreeGroup.lift (PresentedGroup.of (rels := rels)) = PresentedGroup.mk rels := by
  ext a
  simp [PresentedGroup.of]

/-- The canonical `Group.Presentation` of `PresentedGroup rels`. -/
def toPresentation : Group.Presentation (PresentedGroup rels) α :=
{ val := (PresentedGroup.of (rels := rels))
  closure_range_val := by
    simp only [PresentedGroup.closure_range_of]
  rels := rels
  ker_eq_normalClosure := by
    ext x
    simp [MonoidHom.mem_ker, PresentedGroup.mk_eq_one_iff, lift_of_eq_mk (rels := rels)] }

end PresentedGroup

end Group
