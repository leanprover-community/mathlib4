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
* `Subgroup.IsNormalClosureFG`: defines when a subgroup is the normal closure of a finite set.
* `IsFinitelyPresented`: defines when a group is finitely presented.

## Main results
* `Subgroup.IsNormalClosureFG_map`: being the normal closure of a finite set is invariant
  under surjective homomorphism.
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
      (↑iso : G →* H).comp ((FreeGroup.lift ((↑) : S → G)).comp
        (FreeGroup.freeGroupCongr (iso.toEquiv.image S).symm)) := by
  ext ⟨_, s, hs, rfl⟩; simp [Equiv.image]

/-- Defines when a subgroup is the normal closure of a finite set. -/
def Subgroup.IsNormalClosureFG (N : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = N

namespace Subgroup.IsNormalClosureFG

/-- Being the normal closure of a finite set is invariant under surjective homomorphism. -/
protected theorem map (f : G →* H) (hf : Function.Surjective f) (N : Subgroup G)
    (hN : N.IsNormalClosureFG) : (N.map f).IsNormalClosureFG := by
  obtain ⟨S, hSfinite, hSclosure⟩ := hN
  refine ⟨f '' S, hSfinite.image _, ?_⟩
  rw [ ← hSclosure, Subgroup.map_normalClosure _ _ hf]

/-- Composing with a reindexing free group isomorphism preserves finite generation in
normal closure of the kernel. -/
lemma ker_comp_freeGroupCongr (e : α ≃ β) (f : FreeGroup α →* G)
    (hfker : f.ker.IsNormalClosureFG) :
    (f.comp (FreeGroup.freeGroupCongr e.symm : FreeGroup β →* FreeGroup α)).ker.IsNormalClosureFG
    := by
  simp only [MonoidHom.ker_comp_mulEquiv]
  exact hfker.map ((FreeGroup.freeGroupCongr e.symm).symm : FreeGroup α →* FreeGroup β)
    (FreeGroup.freeGroupCongr e.symm).symm.surjective f.ker

end Subgroup.IsNormalClosureFG

/-- A group is finitely presented if it has a finite generating set such that the kernel
of the induced map from the free group on that set is the normal closure of finitely many
relations. -/
@[mk_iff]
class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out : ∃ S : Set G, S.Finite ∧ Subgroup.closure S = ⊤ ∧
  (FreeGroup.lift ((↑) : S → G)).ker.IsNormalClosureFG

namespace IsFinitelyPresented

/-- Finitely presented groups are closed under isomorphism. -/
theorem of_mulEquiv (iso : G ≃* H) (h : IsFinitelyPresented G) : IsFinitelyPresented H := by
  obtain ⟨S, hSfinite, hSclosure, hker⟩ := h
  use iso '' S, hSfinite.image iso,
    MonoidHom.closure_eq_top_image_of_surjective (iso : G →* H) iso.surjective hSclosure
  rw [FreeGroup.lift_mulEquiv_image, MonoidHom.ker_eq_of_comp_mulEquiv]
  exact hker.ker_comp_freeGroupCongr (iso.toEquiv.image S) _

end IsFinitelyPresented
