/-
Copyright (c) 2025 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Fabrizio Barroero, Stefano Francaviglia,
  Francesco Milizia, Valerio Proietti, Hang Lu Su, Lawrence Wu
-/
module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Data.Finite.Card
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Finitely Presented Groups

This file defines finitely-presented groups.

## Main definitions
* `IsNormalClosureFG`: defines when a subgroup is the normal closure of a finite set.
* `IsFinitelyPresented`: defines when a group admits a finite generating set whose
  relation subgroup is the normal closure of a finite set.

## Main results

## Tags
finitely presented group, finitely generated normal closure
-/

@[expose] public section

variable {G H α β : Type*} [Group G] [Group H]

-- TODO: move to Logic/Equiv/Set.lean
/-- The subtype coercion from `e '' S` factors as `e ∘ val ∘ (e.image S)⁻¹`. -/
theorem Equiv.val_image_symm_comp {α β : Type*} (e : α ≃ β) (S : Set α) :
    (Subtype.val : ↥(e '' S) → β) = e ∘ Subtype.val ∘ (e.image S).symm :=
  funext fun x => by simp [Equiv.image]

-- TODO: move to FreeGroup/Basic.lean
/-- Post-composing with a group homomorphism commutes with `FreeGroup.lift`. -/
theorem FreeGroup.lift_comp_monoidHom (f : α → G) (g : G →* H) :
    FreeGroup.lift (g ∘ f) = g.comp (FreeGroup.lift f) := by
  ext x; simp

-- TODO: move to FreeGroup/Basic.lean
/-- Pre-composing with an equivalence corresponds to
post-composing `FreeGroup.lift` with `FreeGroup.freeGroupCongr`. -/
theorem FreeGroup.lift_comp_equiv (f : α → G) (e : β ≃ α) :
    FreeGroup.lift (f ∘ e) =
      (FreeGroup.lift f).comp
        (FreeGroup.freeGroupCongr e : FreeGroup β →* FreeGroup α) := by
  ext x; simp [FreeGroup.freeGroupCongr, FreeGroup.map_eq_lift]

-- TODO: move to FreeGroup/Basic.lean
/-- Lifting the subtype coercion from a `MulEquiv`-image set factors as
`iso ∘ (lift val) ∘ freeGroupCongr`. -/
theorem FreeGroup.lift_subtype_val_mulEquiv_image (iso : G ≃* H) (S : Set G) :
    FreeGroup.lift (Subtype.val : ↥(↑iso '' S) → H) =
      iso.toMonoidHom.comp ((FreeGroup.lift (Subtype.val : ↥S → G)).comp
        (FreeGroup.freeGroupCongr (iso.toEquiv.image S).symm)) := by
  ext ⟨_, s, hs, rfl⟩; simp [Equiv.image]

-- TODO move this to Subgroup/Map.lean
/-- A surjective homomorphism sends a generating set to a generating set. -/
lemma closure_image_eq_top (f : G →* H) (hf : Function.Surjective f) {S : Set G}
    (hS : Subgroup.closure S = ⊤) : Subgroup.closure (f '' S) = ⊤ := by
  rw [← MonoidHom.map_closure, hS, Subgroup.map_top_of_surjective _ hf]

/-- Definition of subgroup that is given by the normal closure of finitely many elements. -/
def IsNormalClosureFG (N : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = N

namespace IsNormalClosureFG

/-- `IsNormalClosureFG` is invariant under surjective homomorphism. -/
theorem map (f : G →* H) (hf : Function.Surjective f) (N : Subgroup G) (hN : IsNormalClosureFG N) :
    IsNormalClosureFG (N.map f) := by
  obtain ⟨S, hSfinite, hSclosure⟩ := hN
  use f '' S
  refine ⟨hSfinite.image _, ?_⟩
  rw [ ← hSclosure, Subgroup.map_normalClosure _ _ hf]

/-- Composing with a reindexing free group isomorphism preserves finite generation in
normal closure of the kernel. -/
lemma ker_comp_freeGroupCongr
    (e : α ≃ β) (f : FreeGroup α →* G) (hfker : IsNormalClosureFG f.ker) :
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
  use iso '' S, hSfinite.image iso, closure_image_eq_top (iso : G →* H) iso.surjective hSclosure
  rw [FreeGroup.lift_subtype_val_mulEquiv_image, MonoidHom.ker_eq_of_comp_mulEquiv]
  exact IsNormalClosureFG.ker_comp_freeGroupCongr (iso.toEquiv.image S) _ hker

end IsFinitelyPresented
