/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 55ee58f9-6859-488b-8684-9eb9e4802ee6

The following was proved by Aristotle:

- lemma isFinitelyPresented_iff_fintype {G : Type*} [Group G] :
  IsFinitelyPresented G ↔ ∃ (α : Type) (_ : Fintype α) (f : FreeGroup α →* G),
  Function.Surjective f ∧ IsNormalClosureOfFiniteSet (MonoidHom.ker f)
-/

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

lemma IsNormalClosureOfFiniteSet.map {G H : Type*} [Group G] [Group H]
  (f : G →* H) (hf : Function.Surjective f) (K : Subgroup G) (hK : IsNormalClosureOfFiniteSet K)
  : IsNormalClosureOfFiniteSet (K.map f) := by
  obtain ⟨ S, hSf, hS ⟩ := hK
  refine' ⟨ f '' S, hSf.image _, _ ⟩
  rw [ ← hS, Subgroup.map_normalClosure ]
  exact hf

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