/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module category_theory.triangulated.triangulated
! leanprover-community/mathlib commit 19786714ebe478f40b503acb4705fb058ba47303
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Triangulated Categories

This file contains the definition of triangulated categories, which are
pretriangulated categories which satisfy the octahedron axiom.

-/


noncomputable section

namespace CategoryTheory

open Limits Category Preadditive Pretriangulated

open ZeroObject

variable (C : Type _) [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

namespace Triangulated

-- porting note: this structure was added because otherwise Lean4 would complain that
-- the definition of `Octahedron` contains free variables
/-- in a pretriangulated category `C`, `i : OctahedronInput C` consists of two composable
morphisms `u₁₂`, `u₂₃`, their composition `u₁₃`, and three distinguished triangles which
provide "cones" for `u₁₂`, `u₂₃`, `u₁₃`. The octahedron axiom `Octahedron i` for this
input `i` shall say that the these three cones fit into a suitable distinguished triangle. -/
structure OctahedronInput where
  {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
  {u₁₂ : X₁ ⟶ X₂}
  {u₂₃ : X₂ ⟶ X₃}
  {u₁₃ : X₁ ⟶ X₃}
  (comm : u₁₂ ≫ u₂₃ = u₁₃)
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧}
  (h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C)
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧}
  (h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C)
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧}
  (h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang C)

variable {C}

/-- An octahedron is a type of datum whose existence is asserted by
the octahedron axiom (TR 4), see https://stacks.math.columbia.edu/tag/05QK -/
structure Octahedron (i : OctahedronInput C) where
  m₁ : i.Z₁₂ ⟶ i.Z₁₃
  m₃ : i.Z₁₃ ⟶ i.Z₂₃
  comm₁ : i.v₁₂ ≫ m₁ = i.u₂₃ ≫ i.v₁₃
  comm₂ : m₁ ≫ i.w₁₃ = i.w₁₂
  comm₃ : i.v₁₃ ≫ m₃ = i.v₂₃
  comm₄ : i.w₁₃ ≫ i.u₁₂⟦1⟧' = m₃ ≫ i.w₂₃
  mem : Triangle.mk m₁ m₃ (i.w₂₃ ≫ i.v₁₂⟦1⟧') ∈ distTriang C
#align category_theory.triangulated.octahedron CategoryTheory.Triangulated.Octahedron

instance (X : C) :
    Nonempty (Octahedron (OctahedronInput.mk (comp_id (𝟙 X)) (contractible_distinguished X)
      (contractible_distinguished X)
      (contractible_distinguished X))) := by
  refine' ⟨⟨0, 0, _, _, _, _, isomorphic_distinguished _ (contractible_distinguished (0 : C)) _
    (Triangle.isoMk _ _ (by rfl) (by rfl) (by rfl) (by simp) (by simp) (by simp))⟩⟩
  all_goals apply Subsingleton.elim

namespace Octahedron

attribute [reassoc] comm₁ comm₂ comm₃ comm₄

variable {i : OctahedronInput C} (h : Octahedron i)

/-- The triangle `Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃ ⟶ Z₁₂⟦1⟧` given by an octahedron. -/
@[simps!]
def triangle : Triangle C :=
  Triangle.mk h.m₁ h.m₃ (i.w₂₃ ≫ i.v₁₂⟦1⟧')
#align category_theory.triangulated.octahedron.triangle CategoryTheory.Triangulated.Octahedron.triangle

/-- The first morphism of triangles given by an octahedron. -/
@[simps]
def triangleMorphism₁ : Triangle.mk i.u₁₂ i.v₁₂ i.w₁₂ ⟶ Triangle.mk i.u₁₃ i.v₁₃ i.w₁₃
    where
  hom₁ := 𝟙 i.X₁
  hom₂ := i.u₂₃
  hom₃ := h.m₁
  comm₁ := by
    dsimp
    rw [id_comp, i.comm]
  comm₂ := h.comm₁
  comm₃ := by
    dsimp
    simpa only [Functor.map_id, comp_id] using h.comm₂.symm
#align category_theory.triangulated.octahedron.triangle_morphism₁ CategoryTheory.Triangulated.Octahedron.triangleMorphism₁

/-- The second morphism of triangles given an octahedron. -/
@[simps]
def triangleMorphism₂ : Triangle.mk i.u₁₃ i.v₁₃ i.w₁₃ ⟶ Triangle.mk i.u₂₃ i.v₂₃ i.w₂₃
    where
  hom₁ := i.u₁₂
  hom₂ := 𝟙 i.X₃
  hom₃ := h.m₃
  comm₁ := by
    dsimp
    rw [comp_id, i.comm]
  comm₂ := by
    dsimp
    rw [id_comp, h.comm₃]
  comm₃ := h.comm₄
#align category_theory.triangulated.octahedron.triangle_morphism₂ CategoryTheory.Triangulated.Octahedron.triangleMorphism₂

/- TODO (@joelriou): show that in order to verify the existence of an octahedron, one may
replace the composable maps `u₁₂` and `u₂₃` by any isomorphic composable maps
and the given "cones" of `u₁₂`, `u₂₃`, `u₁₃` by any choice of cones. -/
end Octahedron

end Triangulated

open Triangulated

/-- A triangulated category is a pretriangulated category which satisfies
the octahedron axiom (TR 4), see https://stacks.math.columbia.edu/tag/05QK -/
class IsTriangulated where
  /-- the octahedron axiom (TR 4) -/
  octahedron_axiom :
    ∀ (i : OctahedronInput C), Nonempty (Octahedron i)
#align category_theory.is_triangulated CategoryTheory.IsTriangulated

namespace Triangulated

variable {C}

/-- A choice of octahedron given by the octahedron axiom. -/
def someOctahedron' [IsTriangulated C] (i : OctahedronInput C) : Octahedron i :=
  (IsTriangulated.octahedron_axiom i).some

/-- A choice of octahedron given by the octahedron axiom. -/
def someOctahedron [IsTriangulated C]
  {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C} {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃}
  (comm : u₁₂ ≫ u₂₃ = u₁₃)
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C)
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} (h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C)
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang C) :
    Octahedron (OctahedronInput.mk comm h₁₂ h₂₃ h₁₃) :=
  someOctahedron' _
#align category_theory.triangulated.some_octahedron CategoryTheory.Triangulated.someOctahedron

end Triangulated

end CategoryTheory
