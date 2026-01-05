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

/- lemma isFinitelyPresented_iff_finite_set {G : Type*} [Group G] :
  IsFinitelyPresented G ↔ ∃ (S : Set G) (f : FreeGroup S →* G), S.Finite ∧
  Function.Surjective f ∧ IsNormalClosureFinitelyGenerated (MonoidHom.ker f) := by
    constructor
    · -- mp
      intro ⟨n, f', hfsurj, hkernel⟩
      let S : Set G := Set.range (fun i : Fin n => f' (FreeGroup.of i))
      have hSfinite : S.Finite := Set.finite_range (fun i : Fin n => f' (FreeGroup.of i))
      use S
      sorry
    · -- mpr
      sorry -/

/- lemma isFinitelyPresented_iff_fintype_old {G : Type*} [Group G] :
  IsFinitelyPresented G ↔ ∃ (α : Type) (_ : Fintype α) (f : FreeGroup α →* G),
  Function.Surjective f ∧ IsNormalClosureFG (f.ker) := by
    constructor
    · intro ⟨n, f, hfsurj, hkernel⟩
      use Fin n, inferInstance, f
    · intro ⟨α, instα, f, hfsurj, hfkernel⟩
      let n := Fintype.card α
      let e := Fintype.equivFin α
      let iso : FreeGroup (Fin n) ≃* FreeGroup α := FreeGroup.freeGroupCongr e.symm
      let f' := f.comp iso.toMonoidHom
      use n, f'
      have hf'surj := hfsurj.comp iso.surjective
      constructor
      · exact hf'surj
      · unfold f'
        simp only [MonoidHom.ker_comp_mulEquiv]
        exact IsNormalClosureFG.map iso.symm.toMonoidHom iso.symm.surjective f.ker hfkernel -/

lemma isFinitelyPresented_iff_fintype {G : Type*} [Group G] :
    IsFinitelyPresented G ↔ ∃ (α : Type) (_ : Fintype α) (f : FreeGroup α →* G),
    Function.Surjective f ∧ IsNormalClosureFG (f.ker) := by
  constructor
  · intro ⟨n, f, hfsurj, hkernel⟩
    exact ⟨Fin n, inferInstance, f, hfsurj, hkernel⟩
  · intro ⟨α, instα, f, hfsurj, hfkernel⟩
    let iso := FreeGroup.freeGroupCongr (Fintype.equivFin α).symm
    refine ⟨Fintype.card α, f.comp iso.toMonoidHom, hfsurj.comp iso.surjective, ?_⟩
    simp only [MonoidHom.ker_comp_mulEquiv] -- this could further be factored as a lemma I feel.
    exact IsNormalClosureFG.map iso.symm.toMonoidHom iso.symm.surjective f.ker hfkernel

variable (G : Type) [Group G] (g : G)

/- instance [h : IsFinitelyPresented G] : Group.FG G := by
  rw [isFinitelyPresented_iff_fintype] at h
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
