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
* `Subgroup.IsNormalClosureFG N`: says that the subgroup `N` is the normal closure of a
  finitely generated subgroup.
* `IsFinitelyPresented`: defines when a group is finitely presented.

## Main results
* `Subgroup.IsNormalClosureFG_map`: Being the normal closure of a finite set is preserved under
  surjective homomorphism.
* `IsFinitelyPresented.equiv`: finitely presented groups are closed under isomorphism.

## Tags
finitely presented group, finitely generated normal closure
-/

@[expose] public section

variable {G H α β : Type*} [Group G] [Group H]

/--
`IsNormalClosureFG N` says that the subgroup `N` is the normal closure of a finitely-generated
subgroup.
-/
def Subgroup.IsNormalClosureFG (N : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = N

namespace Subgroup.IsNormalClosureFG

/-- Being the normal closure of a finite set is invariant under surjective homomorphism. -/
protected theorem map {N : Subgroup G} (hN : IsNormalClosureFG N)
    {f : G →* H} (hf : Function.Surjective f) : (N.map f).IsNormalClosureFG := by
  obtain ⟨S, hSfinite, hSclosure⟩ := hN
  refine ⟨f '' S, hSfinite.image _, ?_⟩
  rw [← hSclosure, Subgroup.map_normalClosure _ _ hf]

end Subgroup.IsNormalClosureFG

/-- A group is finitely presented if it has a finite generating set such that the kernel
of the induced map from the free group on that set is the normal closure of finitely many
relations. -/
@[mk_iff]
class Group.IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out : ∃ (n : ℕ) (φ : FreeGroup (Fin n) →* G), Function.Surjective φ ∧ φ.ker.IsNormalClosureFG

namespace Group.IsFinitelyPresented

/-- Finitely presented groups are closed under isomorphism. -/
theorem equiv (iso : G ≃* H) (h : IsFinitelyPresented G) : IsFinitelyPresented H := by
  obtain ⟨n, φ, hφsurj, hNC⟩ := h
  refine ⟨n, (iso : G →* H).comp φ, iso.surjective.comp hφsurj, ?_⟩
  rwa [MonoidHom.ker_mulEquiv_comp φ iso]

/-- The trivial group is the normal closure of a finite set of relations. -/
theorem Subgroup.isNormalClosureFG_bot : Subgroup.IsNormalClosureFG (⊥ : Subgroup G) :=
  ⟨∅, Finite.of_subsingleton, Subgroup.normalClosure_empty⟩

/-- A free group (with a finite number of generators) is finitely presented. -/
instance [Finite α] : Group.IsFinitelyPresented (FreeGroup α) := by
  have ⟨n, _, f, hf_surj, hf_inj⟩ := Finite.exists_equiv_fin α
  refine ⟨n, FreeGroup.map f, ?_, ?_⟩
  · exact FreeGroup.map_surjective hf_surj.surjective
  · rw [(FreeGroup.map f).ker_eq_bot_iff.mpr (FreeGroup.map_injective hf_inj.injective)]
    exact Subgroup.isNormalClosureFG_bot

end Group.IsFinitelyPresented
