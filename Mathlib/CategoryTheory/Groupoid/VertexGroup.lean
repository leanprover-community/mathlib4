/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.PathCategory
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Hom.Group
import Mathlib.Algebra.Hom.Equiv.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.ConnectedComponent

#align_import category_theory.groupoid.vertex_group from "leanprover-community/mathlib"@"47b51515e69f59bca5cf34ef456e6000fe205a69"

/-!
# Vertex group

This file defines the vertex group (*aka* isotropy group) of a groupoid at a vertex.

## Implementation notes

* The instance is defined "manually", instead of relying on `CategoryTheory.Aut.group` or
  using `CategoryTheory.inv`.
* The multiplication order therefore matches the categorical one: `x * y = x ≫ y`.
* The inverse is directly defined in terms of the groupoidal inverse: `x ⁻¹ = Groupoid.inv x`.

## Tags

isotropy, vertex group, groupoid
-/


namespace CategoryTheory

namespace Groupoid

universe u v

variable {C : Type u} [Groupoid C]

/-- The vertex group at `c`. -/
@[simps mul one inv]
instance vertexGroup (c : C) : Group (c ⟶ c) where
  mul := fun x y : c ⟶ c => x ≫ y
  mul_assoc := Category.assoc
  one := 𝟙 c
  one_mul := Category.id_comp
  mul_one := Category.comp_id
  inv := Groupoid.inv
  mul_left_inv := inv_comp
#align category_theory.groupoid.vertex_group CategoryTheory.Groupoid.vertexGroup

/-- The inverse in the group is equal to the inverse given by `CategoryTheory.inv`. -/
theorem vertexGroup.inv_eq_inv (c : C) (γ : c ⟶ c) : γ⁻¹ = CategoryTheory.inv γ :=
  Groupoid.inv_eq_inv γ
#align category_theory.groupoid.vertex_group.inv_eq_inv CategoryTheory.Groupoid.vertexGroup.inv_eq_inv

/-- An arrow in the groupoid defines, by conjugation, an isomorphism of groups between
its endpoints.
-/
@[simps]
def vertexGroupIsomOfMap {c d : C} (f : c ⟶ d) : (c ⟶ c) ≃* (d ⟶ d)
    where
  toFun γ := inv f ≫ γ ≫ f
  invFun δ := f ≫ δ ≫ inv f
  left_inv γ := by
    simp_rw [Category.assoc, comp_inv, Category.comp_id, ← Category.assoc, comp_inv,
      Category.id_comp]
  right_inv δ := by
    simp_rw [Category.assoc, inv_comp, ← Category.assoc, inv_comp, Category.id_comp,
      Category.comp_id]
  map_mul' γ₁ γ₂ := by
    simp only [vertexGroup_mul, inv_eq_inv, Category.assoc, IsIso.hom_inv_id_assoc]
    -- 🎉 no goals
#align category_theory.groupoid.vertex_group_isom_of_map CategoryTheory.Groupoid.vertexGroupIsomOfMap

/-- A path in the groupoid defines an isomorphism between its endpoints.
-/
def vertexGroupIsomOfPath {c d : C} (p : Quiver.Path c d) : (c ⟶ c) ≃* (d ⟶ d) :=
  vertexGroupIsomOfMap (composePath p)
#align category_theory.groupoid.vertex_group_isom_of_path CategoryTheory.Groupoid.vertexGroupIsomOfPath

/-- A functor defines a morphism of vertex group. -/
@[simps]
def CategoryTheory.Functor.mapVertexGroup {D : Type v} [Groupoid D] (φ : C ⥤ D) (c : C) :
    (c ⟶ c) →* (φ.obj c ⟶ φ.obj c) where
  toFun := φ.map
  map_one' := φ.map_id c
  map_mul' := φ.map_comp
#align category_theory.functor.map_vertex_group CategoryTheory.Groupoid.CategoryTheory.Functor.mapVertexGroup

end Groupoid

end CategoryTheory
