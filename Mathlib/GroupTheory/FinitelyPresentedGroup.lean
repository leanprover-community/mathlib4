/-
Copyright (c) Hang Lu Su 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Fabrizio Barroero, Stefano Francaviglia,
  Francesco Milizia, Valerio Proietti, Hang Lu Su, Lawrence Wu
-/

import Mathlib

/-!
# Finitely Presented Groups

This file defines finitely presented groups and proves their basic properties.

## Main definitions

## Main results

## Tags

finitely presented group, normal closure finitely generated,
-/

open Subgroup

def IsNormalClosureOfFiniteSet {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = H

class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out : ∃ (n : ℕ) (f : (FreeGroup (Fin n)) →* G),
    Function.Surjective f ∧ IsNormalClosureOfFiniteSet (MonoidHom.ker f)

lemma isFinitelyPresented_iff_finite_set {G : Type*} [Group G] :
  IsFinitelyPresented G ↔ ∃ (S : Set G) (f : FreeGroup S →* G), S.Finite ∧
  Function.Surjective f ∧ IsNormalClosureOfFiniteSet (MonoidHom.ker f) := by
    constructor
    · -- mp
      intro ⟨n, f', hfsurj, hkernel⟩
      let S : Set G := Set.range (fun i : Fin n => f' (FreeGroup.of i))
      have hSfinite : S.Finite := Set.finite_range (fun i : Fin n => f' (FreeGroup.of i))
      use S
      sorry
    · -- mpr
      sorry

lemma isFinitelyPresented_iff_fintype {G : Type*} [Group G] :
  IsFinitelyPresented G ↔ ∃ (α : Type*) [Fintype α] (f : FreeGroup α →* G),
  Function.Surjective f ∧ IsNormalClosureOfFiniteSet (MonoidHom.ker f) := by
  sorry

variable (G : Type) [Group G] (g : G)

/- instance [h : IsFinitelyPresented G] : Group.FG G := by
  rw [isFinitelyPresented_iff'] at h
  rw [Group.fg_iff_exists_freeGroup_hom_surjective]
  obtain ⟨S, f, hfsurj, hkernel⟩ := h
  use S
  constructor
  · use f
    exact hfsurj
  · exact Finset.finite_toSet S -/

/-   lemma fpGroup_is_fgGroup (G: Type*) [Group G] (h: IsFinitelyPresented G) : Group.FG G := by
  rw [Group.fg_iff_exists_freeGroup_hom_surjective]
  apply isFinitelyPresented_iff at G
  --constructor
  sorry -/

/- lemma isFinitelyPresented_stupid (α : Type) [Finite α] (s : Finset (FreeGroup α)) :
    IsFinitelyPresented ((FreeGroup α) ⧸ normalClosure s) := by
    rw [isFinitelyPresented_iff]
    constructor
    sorry -/

namespace IsFinitelyPresented

variable {G H : Type*} [Group G] [Group H]

-- Finitely presented groups are closed under isomorphism
lemma of_equiv (e : G ≃* H) (h : IsFinitelyPresented G) :
    IsFinitelyPresented H := by
  sorry

-- Trivial group is finitely presented
instance instTrivial : IsFinitelyPresented (Unit) := by
  sorry

-- Finite groups are finitely presented
instance instFinite [Finite G] : IsFinitelyPresented G := by
  sorry

end IsFinitelyPresented

/- -- Free groups are finitely presented
instance FreeGroup.instFinitelyPresented (α : Type*) [Fintype α] :
    IsFinitelyPresented (FreeGroup α) := by
  sorry

-- Cyclic groups are finitely presented
instance Int.instFinitelyPresented : IsFinitelyPresented ℤ := by
  sorry

instance ZMod.instFinitelyPresented (n : ℕ) : IsFinitelyPresented (ZMod n) := by
  sorry -/
