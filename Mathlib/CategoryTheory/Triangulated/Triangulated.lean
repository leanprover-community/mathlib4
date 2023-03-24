/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module category_theory.triangulated.triangulated
! leanprover-community/mathlib commit 19786714ebe478f40b503acb4705fb058ba47303
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Triangulated.Pretriangulated

/-!
# Triangulated Categories

This file contains the definition of triangulated categories, which are
pretriangulated categories which satisfy the octahedron axiom.

-/


noncomputable section

namespace CategoryTheory

open Limits Category Preadditive Pretriangulated

open ZeroObject

variable {C : Type _} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

variable {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C} {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃}
  (comm : u₁₂ ≫ u₂₃ = u₁₃) {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧}
  (h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ (dist_triang C)) {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧}
  (h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ (dist_triang C)) {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧}
  (h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ (dist_triang C))

namespace Triangulated

include comm h₁₂ h₂₃ h₁₃

/-- An octahedron is a type of datum whose existence is asserted by
the octahedron axiom (TR 4), see https://stacks.math.columbia.edu/tag/05QK -/
structure Octahedron where
  m₁ : Z₁₂ ⟶ Z₁₃
  m₃ : Z₁₃ ⟶ Z₂₃
  comm₁ : v₁₂ ≫ m₁ = u₂₃ ≫ v₁₃
  comm₂ : m₁ ≫ w₁₃ = w₁₂
  comm₃ : v₁₃ ≫ m₃ = v₂₃
  comm₄ : w₁₃ ≫ u₁₂⟦1⟧' = m₃ ≫ w₂₃
  Mem : Triangle.mk m₁ m₃ (w₂₃ ≫ v₁₂⟦1⟧') ∈ (dist_triang C)
#align category_theory.triangulated.octahedron CategoryTheory.Triangulated.Octahedron

omit comm h₁₂ h₂₃ h₁₃

instance (X : C) :
    Nonempty
      (Octahedron (comp_id (𝟙 X)) (contractible_distinguished X) (contractible_distinguished X)
        (contractible_distinguished X)) :=
  by
  refine' ⟨⟨0, 0, _, _, _, _, by convert contractible_distinguished (0 : C)⟩⟩
  all_goals apply Subsingleton.elim

namespace Octahedron

attribute [reassoc.1] comm₁ comm₂ comm₃ comm₄

variable {comm h₁₂ h₂₃ h₁₃} (h : Octahedron comm h₁₂ h₂₃ h₁₃)

/-- The triangle `Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃ ⟶ Z₁₂⟦1⟧` given by an octahedron. -/
@[simps]
def triangle : Triangle C :=
  Triangle.mk h.m₁ h.m₃ (w₂₃ ≫ v₁₂⟦1⟧')
#align category_theory.triangulated.octahedron.triangle CategoryTheory.Triangulated.Octahedron.triangle

/-- The first morphism of triangles given by an octahedron. -/
@[simps]
def triangleMorphism₁ : Triangle.mk u₁₂ v₁₂ w₁₂ ⟶ Triangle.mk u₁₃ v₁₃ w₁₃
    where
  hom₁ := 𝟙 X₁
  hom₂ := u₂₃
  hom₃ := h.m₁
  comm₁' := by
    dsimp
    rw [id_comp, comm]
  comm₂' := h.comm₁
  comm₃' := by
    dsimp
    simpa only [Functor.map_id, comp_id] using h.comm₂.symm
#align category_theory.triangulated.octahedron.triangle_morphism₁ CategoryTheory.Triangulated.Octahedron.triangleMorphism₁

/-- The second morphism of triangles given an octahedron. -/
@[simps]
def triangleMorphism₂ : Triangle.mk u₁₃ v₁₃ w₁₃ ⟶ Triangle.mk u₂₃ v₂₃ w₂₃
    where
  hom₁ := u₁₂
  hom₂ := 𝟙 X₃
  hom₃ := h.m₃
  comm₁' := by
    dsimp
    rw [comp_id, comm]
  comm₂' := by
    dsimp
    rw [id_comp, h.comm₃]
  comm₃' := h.comm₄
#align category_theory.triangulated.octahedron.triangle_morphism₂ CategoryTheory.Triangulated.Octahedron.triangleMorphism₂

/- TODO (@joelriou): show that in order to verify the existence of an octahedron, one may
replace the composable maps `u₁₂` and `u₂₃` by any isomorphic composable maps
and the given "cones" of `u₁₂`, `u₂₃`, `u₁₃` by any choice of cones. -/
end Octahedron

end Triangulated

open Triangulated

variable (C)

/-- A triangulated category is a pretriangulated category which satisfies
the octahedron axiom (TR 4), see https://stacks.math.columbia.edu/tag/05QK -/
class IsTriangulated where
  octahedron_axiom :
    ∀ ⦃X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C⦄ ⦃u₁₂ : X₁ ⟶ X₂⦄ ⦃u₂₃ : X₂ ⟶ X₃⦄ ⦃u₁₃ : X₁ ⟶ X₃⦄
      (comm : u₁₂ ≫ u₂₃ = u₁₃) ⦃v₁₂ : X₂ ⟶ Z₁₂⦄ ⦃w₁₂ : Z₁₂ ⟶ X₁⟦1⟧⦄
      (h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ (dist_triang C)) ⦃v₂₃ : X₃ ⟶ Z₂₃⦄ ⦃w₂₃ : Z₂₃ ⟶ X₂⟦1⟧⦄
      (h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ (dist_triang C)) ⦃v₁₃ : X₃ ⟶ Z₁₃⦄ ⦃w₁₃ : Z₁₃ ⟶ X₁⟦1⟧⦄
      (h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ (dist_triang C)), Nonempty (Octahedron comm h₁₂ h₂₃ h₁₃)
#align category_theory.is_triangulated CategoryTheory.IsTriangulated

namespace Triangulated

variable {C}

/-- A choice of octahedron given by the octahedron axiom. -/
def someOctahedron [IsTriangulated C] : Octahedron comm h₁₂ h₂₃ h₁₃ :=
  (IsTriangulated.octahedron_axiom comm h₁₂ h₂₃ h₁₃).some
#align category_theory.triangulated.some_octahedron CategoryTheory.Triangulated.someOctahedron

end Triangulated

end CategoryTheory

