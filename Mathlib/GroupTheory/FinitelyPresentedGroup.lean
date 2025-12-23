/-
Copyright (c) Hang Lu Su 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Fabrizio Barroero, Stefano Francaviglia,
  Francesco Milizia, Valerio Proietti, Hang Lu Su, Lawrence Wu
-/

import Mathlib

open Subgroup

def normalClosureIsFG {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ S : Finset G, Subgroup.normalClosure S = H

class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out : ∃ (n : ℕ) (f : (FreeGroup (Fin n)) →* G),
    Function.Surjective f ∧ normalClosureIsFG (MonoidHom.ker f)

lemma isFinitelyPresented_iff {G : Type*} [Group G] :
  IsFinitelyPresented G ↔ ∃ (S : Set G) (f : FreeGroup S →* G), S.Finite ∧
  Function.Surjective f ∧ normalClosureIsFG (MonoidHom.ker f) := by
    constructor
    · -- mp
      intro ⟨n, f, hfsurj, hkernel⟩
      let S : Set G := Set.range (fun i : Fin n => f (FreeGroup.of i))
      have hSfinite : S.Finite := Set.finite_range (fun i : Fin n => f (FreeGroup.of i))
      sorry
    · -- mpr
    sorry

lemma isFinitelyPresented_iff' {G : Type*} [Group G] :
  IsFinitelyPresented G ↔ ∃ (S : Finset G) (f : FreeGroup S →* G),
  Function.Surjective f ∧ normalClosureIsFG (MonoidHom.ker f) := by
    sorry

variable (G : Type) [Group G] (g : G)

instance [h : IsFinitelyPresented G] : Group.FG G := by
  rw [isFinitelyPresented_iff'] at h
  rw [Group.fg_iff_exists_freeGroup_hom_surjective]
  obtain ⟨S, f, hfsurj, hkernel⟩ := h
  use S
  constructor
  · use f
    exact hfsurj
  · exact Finset.finite_toSet S

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
