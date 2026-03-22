/-
Copyright (c) 2025 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Fabrizio Barroero, Stefano Francaviglia,
  Francesco Milizia, Valerio Proietti, Hang Lu Su, Lawrence Wu
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Finitely Presented Groups

This file defines finitely presented groups.

## Main definitions
* `IsNormalClosureFG`: defines when a subgroup is the normal closure of a finite set.
* `IsFinitelyPresented`: defines when a group is finitely presented.

## Main results
* `IsNormalClosureFG.map`: `IsNormalClosureFG` is invariant under surjective homomorphism.
* `IsFinitelyPresented.of_mulEquiv`: finitely presented groups are closed under isomorphism.

## Tags
finitely presented group, finitely generated normal closure
-/

@[expose] public section

variable {G H α β : Type*} [Group G] [Group H]

/-- This is a statement about the following commutative diagram:
suppose that `G` and `H` are isomorphic via `iso`, and `S` is a set in `G`,
then the canonical inclusion map from `FreeGroup(iso '' S)` to `H` is given by
first taking the inverse isomorphism between the `FreeGroup (S)` and `FreeGroup (iso '' S)`, then
composing with the canonical inclusion map from `FreeGroup(S)` to `G` and then taking `iso`. -/
lemma FreeGroup.lift_mulEquiv_image (iso : G ≃* H) (S : Set G) :
    FreeGroup.lift ((↑) : ↥(↑iso '' S) → H) =
      iso.toMonoidHom.comp ((FreeGroup.lift ((↑) : S → G)).comp
        (FreeGroup.freeGroupCongr (iso.toEquiv.image S).symm)) := by
  ext ⟨_, s, hs, rfl⟩; simp [Equiv.image]

/-- Defining when a subgroup is given by the normal closure of finitely many elements. -/
def IsNormalClosureFG (N : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = N

namespace IsNormalClosureFG

/-- `IsNormalClosureFG` is invariant under surjective homomorphism. -/
theorem map (f : G →* H) (hf : Function.Surjective f) (N : Subgroup G) (hN : IsNormalClosureFG N) :
    IsNormalClosureFG (N.map f) := by
  obtain ⟨S, hSfinite, hSclosure⟩ := hN
  refine ⟨f '' S, hSfinite.image _, ?_⟩
  rw [ ← hSclosure, Subgroup.map_normalClosure _ _ hf]

/-- Composing with a reindexing free group isomorphism preserves finite generation in
normal closure of the kernel. -/
lemma ker_comp_freeGroupCongr (e : α ≃ β) (f : FreeGroup α →* G) (hfker : IsNormalClosureFG f.ker) :
    IsNormalClosureFG
      (f.comp (FreeGroup.freeGroupCongr e.symm : FreeGroup β →* FreeGroup α)).ker := by
  simp only [MonoidHom.ker_comp_mulEquiv]
  exact map ((FreeGroup.freeGroupCongr e.symm).symm : FreeGroup α →* FreeGroup β)
    (FreeGroup.freeGroupCongr e.symm).symm.surjective f.ker hfker

end IsNormalClosureFG

/-- A group is finitely presented if it has a finite generating set such that the kernel
of the induced map from the free group on that set is the normal closure of finitely many
relations. -/
@[mk_iff]
class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out: ∃ S : Set G, S.Finite ∧ Subgroup.closure S = ⊤ ∧
  IsNormalClosureFG (FreeGroup.lift ((↑) : S → G)).ker

namespace IsFinitelyPresented

/-- Finitely presented groups are closed under isomorphism. -/
theorem of_mulEquiv (iso : G ≃* H) (h : IsFinitelyPresented G) : IsFinitelyPresented H := by
  obtain ⟨S, hSfinite, hSclosure, hker⟩ := h
  use iso '' S, hSfinite.image iso,
    MonoidHom.closure_image_eq_top (iso : G →* H) iso.surjective hSclosure
  rw [FreeGroup.lift_mulEquiv_image, MonoidHom.ker_eq_of_comp_mulEquiv]
  exact IsNormalClosureFG.ker_comp_freeGroupCongr (iso.toEquiv.image S) _ hker

end IsFinitelyPresented
