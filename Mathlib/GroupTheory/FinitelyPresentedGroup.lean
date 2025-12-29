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

-- We define the normal closure of a finite set that.
def IsNormalClosureOfFiniteSet {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = H

-- We state that this property is invariant under surjective homomorphism.
lemma IsNormalClosureOfFiniteSet.map {G H : Type*} [Group G] [Group H]
  (f : G →* H) (hf : Function.Surjective f) (K : Subgroup G) (hK : IsNormalClosureOfFiniteSet K)
  : IsNormalClosureOfFiniteSet (K.map f) := by
  obtain ⟨ S, hSfinite, hSclosure ⟩ := hK
  use f '' S
  constructor
  · exact hSfinite.image _
  · rw [ ← hSclosure]
    have h := Subgroup.map_normalClosure S f hf
    exact h.symm

class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out : ∃ (n : ℕ) (f : (FreeGroup (Fin n)) →* G),
    Function.Surjective f ∧ IsNormalClosureOfFiniteSet (MonoidHom.ker f)

/- lemma isFinitelyPresented_iff_finite_set {G : Type*} [Group G] :
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
      sorry -/

lemma isFinitelyPresented_iff_fintype {G : Type*} [Group G] :
  IsFinitelyPresented G ↔ ∃ (α : Type) (_ : Fintype α) (f : FreeGroup α →* G),
  Function.Surjective f ∧ IsNormalClosureOfFiniteSet (MonoidHom.ker f) := by
    constructor
    · -- mp
      intro ⟨n, f, hfsurj, hkernel⟩
      use Fin n, inferInstance, f
    · -- mpr
      intro ⟨α, instα, f, hfsurj, hkernel⟩
      let n := Fintype.card α
      let e := Fintype.equivFin α
      let iso : FreeGroup (Fin n) ≃* FreeGroup α := FreeGroup.freeGroupCongr e.symm
      let f' := f.comp iso.toMonoidHom
      use n, f'
      constructor
      · exact hfsurj.comp iso.surjective
      · --exact  IsNormalClosureOfFiniteSet.map iso.symm.toMonoidHom iso.symm.surjective (MonoidHom.ker f) hkernel
        obtain ⟨ S, hSfinite, hS ⟩ := hkernel;
        refine' ⟨ iso.symm '' S, hSfinite.image _, _ ⟩;
        convert congr_arg ( Subgroup.map iso.symm.toMonoidHom ) hS using 1;
        · refine' le_antisymm _ _;
          · simp +decide [ Subgroup.normalClosure ];
            simp +decide [ Group.conjugatesOfSet, Set.subset_def ];
            simp +decide [ conjugatesOf ];
            -- Since iso is an equivalence, we can take x_3 = y * x_1 * y⁻¹.
            intro x y hy z hz
            use iso z * y * (iso z)⁻¹;
            exact ⟨ Subgroup.subset_closure ( Set.mem_iUnion₂.2 ⟨ y, hy, ⟨ iso z, rfl ⟩ ⟩ ), by simpa [ mul_assoc ] using hz ⟩;
          · rw [ Subgroup.map_le_iff_le_comap ];
            refine' Subgroup.normalClosure_le_normal _;
            intro x hx;
            exact Subgroup.subset_normalClosure ( Set.mem_image_of_mem _ hx );
        · ext; simp [f'];
          exact ⟨ fun hx => ⟨ _, hx, by simp +decide ⟩, by rintro ⟨ x, hx, rfl ⟩ ; simpa using hx ⟩


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

/- instance [h : IsFinitelyPresented G] : PresentedGroup G := by
  sorry
-/

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

/- namespace IsFinitelyPresented

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

end IsFinitelyPresented -/

/- -- Free groups are finitely presented
instance FreeGroup.instFinitelyPresented (α : Type*) [Fintype α] :
    IsFinitelyPresented (FreeGroup α) := by
  sorry

-- Cyclic groups are finitely presented
instance Int.instFinitelyPresented : IsFinitelyPresented ℤ := by
  sorry

instance ZMod.instFinitelyPresented (n : ℕ) : IsFinitelyPresented (ZMod n) := by
  sorry -/
