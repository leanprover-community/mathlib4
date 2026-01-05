/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 4d935855-74ea-44f6-b058-509850d40896

The following was proved by Aristotle:

- theorem Group.fg_iff_exists_freeGroup_hom_surjective_fintype {G : Type*} [Group G] :
    Group.FG G ↔ ∃ (α : Type) (_ : Fintype α) (φ : FreeGroup α →* G), Function.Surjective φ
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

/-- The kernel of a composition with an isomorphism equals the preimage (map by symm) of the
kernel. -/
@[simp]
lemma MonoidHom.ker_comp_mulEquiv {G H K : Type*} [Group G] [Group H] [Group K]
    (f : H →* K) (e : G ≃* H) : (f.comp e.toMonoidHom).ker = (Subgroup.map (↑e.symm) f.ker) := by
  rw [← MonoidHom.comap_ker, Subgroup.comap_equiv_eq_map_symm']
  rfl

open Subgroup

-- We define a subgroup that is given by the normal closure of finitely many elements.
def IsNormalClosureFG {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = H

-- We state that this property is invariant under surjective homomorphism.
lemma IsNormalClosureFG.map {G H : Type*} [Group G] [Group H]
  (f : G →* H) (hf : Function.Surjective f) (K : Subgroup G) (hK : IsNormalClosureFG K)
  : IsNormalClosureFG (K.map f) := by
  obtain ⟨ S, hSfinite, hSclosure ⟩ := hK
  use f '' S
  constructor
  · exact hSfinite.image _
  · rw [ ← hSclosure, Subgroup.map_normalClosure _ _ hf]

class IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out : ∃ (n : ℕ) (f : (FreeGroup (Fin n)) →* G),
    Function.Surjective f ∧ IsNormalClosureFG (MonoidHom.ker f)

lemma isFinitelyPresented_iff_fintype {G : Type*} [Group G] :
    IsFinitelyPresented G ↔ ∃ (α : Type) (_ : Fintype α) (f : FreeGroup α →* G),
    Function.Surjective f ∧ IsNormalClosureFG (f.ker) := by
  constructor
  · intro ⟨n, f, hfsurj, hkernel⟩
    exact ⟨Fin n, inferInstance, f, hfsurj, hkernel⟩
  · intro ⟨α, _, f, hfsurj, hfkernel⟩
    let iso := FreeGroup.freeGroupCongr (Fintype.equivFin α).symm
    refine ⟨Fintype.card α, f.comp iso.toMonoidHom, hfsurj.comp iso.surjective, ?_⟩
    simp only [MonoidHom.ker_comp_mulEquiv] -- this could further be factored as a lemma I feel.
    exact IsNormalClosureFG.map iso.symm.toMonoidHom iso.symm.surjective f.ker hfkernel

/- lemma isFinitelyPresented_iff_set_finite {G : Type*} [Group G] :
    IsFinitelyPresented G ↔ ∃ (S : Set G), ∃ (_ : S.Finite) (f : FreeGroup S →* G),
    Function.Surjective f ∧ IsNormalClosureFG (f.ker) := by
    constructor
    · intro ⟨n, f, hfsurj, hfkernel⟩
      let S : Set G := Set.range (fun i : Fin n => f (FreeGroup.of i))
      have hSfinite : S.Finite := Set.finite_range _
      refine ⟨S, hSfinite, ?_⟩
      let g : S → G := fun ⟨x, hx⟩ => x  -- Inclusion map
      let φ : FreeGroup S →* G := FreeGroup.lift g
      sorry
    · sorry -/

variable (G : Type) [Group G] (g : G)

theorem Group.fg_iff_exists_freeGroup_hom_surjective' :
    Group.FG G ↔ ∃ (S : Set G) (_ : S.Finite) (φ : FreeGroup S →* G), Function.Surjective φ := by
  refine ⟨fun ⟨S, hS⟩ ↦ ⟨S, S.finite_toSet, FreeGroup.lift Subtype.val, ?_⟩, ?_⟩
  · rwa [← MonoidHom.range_eq_top, ← FreeGroup.closure_eq_range]
  · rintro ⟨S, hfin : Finite S, φ, hφ⟩
    refine fg_iff.mpr ⟨φ '' Set.range FreeGroup.of, ?_, Set.toFinite _⟩
    simp [← MonoidHom.map_closure, hφ, FreeGroup.closure_range_of, ← MonoidHom.range_eq_map]

theorem Group.fg_iff_exists_freeGroup_hom_surjective_fintype {G : Type*} [Group G] :
    Group.FG G ↔ ∃ (α : Type) (_ : Fintype α) (φ : FreeGroup α →* G), Function.Surjective φ := by
      constructor <;> intro h;
      · obtain ⟨S, hS⟩ : ∃ S : Set G, S.Finite ∧ Subgroup.closure S = ⊤ := by
          obtain ⟨ S, hS ⟩ := h;
          exact ⟨ S, S.finite_toSet, hS ⟩;
        -- Let α be the finite set S.
        obtain ⟨α, hα⟩ : ∃ α : Type, ∃ (x : Fintype α), Nonempty (α ≃ S) := by
          have := hS.1.exists_finset_coe;
          obtain ⟨ s', rfl ⟩ := this; exact ⟨ Fin s'.card, inferInstance, ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩ ⟩ ;
        obtain ⟨ x, ⟨ e ⟩ ⟩ := hα;
        refine' ⟨ α, x, FreeGroup.lift ( fun a => ( e a : G ) ), _ ⟩;
        intro g
        have h_closure : g ∈ Subgroup.closure S := by
          aesop;
        refine' Subgroup.closure_induction ( fun g hg => _ ) _ _ _ h_closure;
        · exact ⟨ FreeGroup.of ( e.symm ⟨ g, hg ⟩ ), by simp +decide ⟩;
        · exact ⟨ 1, map_one _ ⟩;
        · rintro x y hx hy ⟨ a, rfl ⟩ ⟨ b, rfl ⟩ ; exact ⟨ a * b, by simp +decide ⟩;
        · rintro x hx ⟨ a, rfl ⟩ ; exact ⟨ a⁻¹, by simp +decide ⟩ ;
      · obtain ⟨ α, hα, φ, hφ ⟩ := h
        -- Since α is finite, the image of α under φ is also finite. Therefore, the image of α generates G, proving that G is finitely generated.
        have h_image_finite : Set.Finite (Set.range (fun a : α => φ (FreeGroup.of a))) := by
          exact Set.toFinite _;
        refine' ⟨ h_image_finite.toFinset, _ ⟩;
        refine' eq_top_iff.mpr fun g hg => _;
        obtain ⟨ x, rfl ⟩ := hφ g;
        induction x using FreeGroup.induction_on <;> aesop

instance [h : IsFinitelyPresented G] : Group.FG G := by
  rw [Group.fg_iff_exists_freeGroup_hom_surjective_fintype]
  rw [isFinitelyPresented_iff_fintype] at h
  obtain ⟨S, hSfinite, f, hfsurj, hkernel⟩ := h
  use S, hSfinite, f, hfsurj