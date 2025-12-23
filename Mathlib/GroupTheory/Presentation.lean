/-
Copyright (c) 2025 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Riccardo Brasca, Stefano Francaviglia, Hang Lu Su,
Francesco Milizia, Valerio Proietti, Lawrence Wu
-/

import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Presentation of a group
This file introduces “chosen” generating systems and presentations for a group, aligned with
`Mathlib.GroupTheory.PresentedGroup`.

Main definitions:
* `Group.GeneratingSystem` packages a type of generators with a map to the group whose range
  generates it.
* `Group.Presentation` extends a generating system with relators and the usual kernel condition.
* `Group.Presentation.toGroup` is the canonical map `PresentedGroup P.rels →* G`.
* `Group.Presentation.mapMulEquiv` transports a presentation along a group isomorphism.
* `Group.Presentation.equivPresentedGroup` identifies `PresentedGroup P.rels` with `G`.
-/

namespace Group

universe u

/-- A (chosen) generating system for a group `G`. -/
structure GeneratingSystem (G : Type u) [Group G] where
  /-- The type of abstract generators. -/
  ι : Type u
  /-- The assignment of each abstract generator to an element of `G`. -/
  val : ι → G
  /-- The images of the generators generate `G`. -/
  closure_range_val : Subgroup.closure (Set.range val) = ⊤

/-- A presentation of a group `G`. -/
structure Presentation (G : Type u) [Group G] extends GeneratingSystem G where
  /-- The relations (relators). -/
  rels : Set (FreeGroup ι)
  /-- Kernel of the induced map is the normal closure of the relators. -/
  ker_eq_normalClosure : (FreeGroup.lift val).ker = Subgroup.normalClosure rels

namespace GeneratingSystem

variable {G : Type u} [Group G]

/-- If the range of `X.val` generates `G`, then `FreeGroup.lift X.val` is surjective. -/
theorem lift_surjective (X : Group.GeneratingSystem (G := G)) :
    Function.Surjective (FreeGroup.lift X.val) := by
  have hrange : (FreeGroup.lift X.val).range = ⊤ := by
    simp [FreeGroup.range_lift_eq_closure, X.closure_range_val]
  exact MonoidHom.range_eq_top.mp hrange

end GeneratingSystem

namespace Presentation

variable {G : Type u} [Group G]

/-- The `PresentedGroup` attached to a `Group.Presentation`. -/
abbrev presentedGroup (P : Group.Presentation (G := G)) : Type u :=
  PresentedGroup (α := P.ι) P.rels

@[simp]
lemma presentedGroup_def (P : Group.Presentation (G := G)) :
    P.presentedGroup = PresentedGroup (α := P.ι) P.rels := rfl

/-- Each relator maps to `1` under the induced map `FreeGroup P.ι →* G`. -/
theorem lift_eq_one_of_mem_rels (P : Group.Presentation (G := G)) {r : FreeGroup P.ι}
    (hr : r ∈ P.rels) :
    FreeGroup.lift P.val r = 1 := by
  have : r ∈ (FreeGroup.lift P.val).ker := by
    simpa [P.ker_eq_normalClosure] using
      (Subgroup.subset_normalClosure hr :
        r ∈ Subgroup.normalClosure P.rels)
  simpa [MonoidHom.mem_ker] using this

/--
Given a `Group.Presentation G`, we obtain the canonical map
`PresentedGroup P.rels →* G` (sending generators to `P.val`).
-/
def toGroup (P : Group.Presentation (G := G)) :
    P.presentedGroup →* G :=
  PresentedGroup.toGroup (rels := P.rels)
    (f := P.val) (by
      intro r hr
      simpa using (P.lift_eq_one_of_mem_rels (r := r) hr))

@[simp]
theorem toGroup_of (P : Group.Presentation (G := G)) (x : P.ι) :
    P.toGroup (PresentedGroup.of (rels := P.rels) x) = P.val x := by
  simp [Presentation.toGroup]

/--
Transport a presentation across a group isomorphism.
If `P` is a presentation of `H` and `e : H ≃* G`, we get a presentation of `G`
with the same generators/relators and generator map composed with `e`.
-/
def mapMulEquiv {H : Type u} [Group H]
    (P : Group.Presentation (G := H)) (e : H ≃* G) :
    Group.Presentation (G := G) := by
  refine
    { ι := P.ι
      val := fun i => e (P.val i)
      closure_range_val := ?_
      rels := P.rels
      ker_eq_normalClosure := ?_ }
  · have hrange :
        Set.range (fun i : P.ι => e (P.val i)) = e '' Set.range P.val := by
      simpa [Function.comp] using
        (Set.range_comp (f := P.val) (g := fun x : H => e x))
    calc
      Subgroup.closure (Set.range fun i : P.ι => e (P.val i))
          = Subgroup.closure (e '' Set.range P.val) := by simp [hrange]
      _ = Subgroup.map e.toMonoidHom (Subgroup.closure (Set.range P.val)) := by
            simpa using
              (MonoidHom.map_closure (e.toMonoidHom) (Set.range P.val)).symm
      _ = Subgroup.map e.toMonoidHom ⊤ := by simp [P.closure_range_val]
      _ = ⊤ := by simp
  · have hlift :
        FreeGroup.lift (fun i : P.ι => e (P.val i))
          = e.toMonoidHom.comp (FreeGroup.lift P.val) := by
      ext i
      simp
    have hker_comp {K : Type u} [Group K] (φ : K →* H) :
      (e.toMonoidHom.comp φ).ker = φ.ker := by
        ext x; constructor <;> intro hx
        · have hx' : e (φ x) = 1 := by simpa [MonoidHom.mem_ker] using hx
          have hx'' : φ x = 1 := e.injective (by simpa using hx')
          simpa [MonoidHom.mem_ker] using hx''
        · simpa [MonoidHom.mem_ker] using hx
    calc
      (FreeGroup.lift (fun i : P.ι => e (P.val i))).ker
          = (e.toMonoidHom.comp (FreeGroup.lift P.val)).ker := by
              simp [hlift]
      _ = (FreeGroup.lift P.val).ker := by
        simpa using hker_comp (φ := FreeGroup.lift P.val)
      _ = Subgroup.normalClosure P.rels := P.ker_eq_normalClosure

/--
From a `Group.Presentation G`, build a group isomorphism
`PresentedGroup P.rels ≃* G`.
-/
noncomputable def equivPresentedGroup (P : Group.Presentation (G := G)) :
    P.presentedGroup ≃* G := by
  let φ : FreeGroup P.ι →* G := FreeGroup.lift P.val
  have hsurj : Function.Surjective φ := P.toGeneratingSystem.lift_surjective
  have e₁ :
      (FreeGroup P.ι ⧸ Subgroup.normalClosure P.rels) ≃*
        (FreeGroup P.ι ⧸ φ.ker) :=
    QuotientGroup.quotientMulEquivOfEq (G := FreeGroup P.ι)
      (M := Subgroup.normalClosure P.rels) (N := φ.ker) (by
        simpa [φ] using P.ker_eq_normalClosure.symm)
  have e₂ : (FreeGroup P.ι ⧸ φ.ker) ≃* G :=
    QuotientGroup.quotientKerEquivOfSurjective φ hsurj
  simpa [Presentation.presentedGroup, PresentedGroup] using e₁.trans e₂

end Presentation

end Group
