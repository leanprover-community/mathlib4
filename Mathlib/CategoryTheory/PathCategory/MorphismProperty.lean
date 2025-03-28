/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Properties of morphisms in a path category.

We provide a formulation of induction principles for morphisms in a path category in terms of
`MorphismProperty`. This file is separate from `CategoryTheory.PathCategory.Basic` in order to
reduce transitive imports. -/


universe v₁ u₁

namespace CategoryTheory.Paths

section
variable (V : Type u₁) [Quiver.{v₁ + 1} V]

/-- A reformulation of `CategoryTheory.Paths.induction` in terms of `MorphismProperty`. -/
lemma morphismProperty_eq_top
    (P : MorphismProperty (Paths V))
    (id : ∀ {v : V}, P (𝟙 ((of V).obj v)))
    (comp : ∀ {u v w : V}
      (p : (of V).obj u ⟶ (of V).obj v) (q : v ⟶ w), P p → P (p ≫ (of V).map q)) :
    P = ⊤ := by
  ext; constructor
  · simp
  · exact fun _ ↦ induction (fun f ↦ P f) id comp _

/-- A reformulation of `CategoryTheory.Paths.induction'` in terms of `MorphismProperty`. -/
lemma morphismProperty_eq_top'
    (P : MorphismProperty (Paths V))
    (id : ∀ {v : V}, P (𝟙 ((of V).obj v)))
    (comp : ∀ {u v w : V}
      (p : u ⟶ v) (q : (of V).obj v ⟶ (of V).obj w), P q → P ((of V).map p ≫ q)) :
    P = ⊤ := by
  ext; constructor
  · simp
  · exact fun _ ↦ induction' (fun f ↦ P f) id comp _

end
section

variable {V : Type u₁} [Quiver.{v₁ + 1} V]

/-- A natural transformation between `F G : Paths V ⥤ C` is defined by its components and
its unary naturality squares. -/
def liftNatTrans {C} [Category C] {F G : Paths V ⥤ C} (α_app : (v : V) → (F.obj v ⟶ G.obj v))
    (α_nat : {X Y : V} → (f : X ⟶ Y) →
      F.map (Quiver.Hom.toPath f) ≫ α_app Y = α_app X ≫ G.map (Quiver.Hom.toPath f)) : F ⟶ G where
        app := α_app
        naturality := by
          apply MorphismProperty.of_eq_top
          apply morphismProperty_eq_top
          · simp only [Functor.map_id, Category.id_comp, Category.comp_id, implies_true]
          · simp only [of_obj, of_map, Functor.map_comp, Category.assoc]
            intro _ _ _ _ q hyp
            rw [α_nat q, ← Category.assoc, hyp, Category.assoc]

/-- A natural isomorphism between `F G : Paths V ⥤ C` is defined by its components and
its unary naturality squares. -/
def liftNatIso {C} [Category C] {F G : Paths V ⥤ C} (α_app : (v : V) → (F.obj v ≅ G.obj v))
    (α_nat : {X Y : V} → (f : X ⟶ Y) →
      F.map (Quiver.Hom.toPath f) ≫ (α_app Y).hom = (α_app X).hom ≫ G.map (Quiver.Hom.toPath f)) :
    F ≅ G :=
  NatIso.ofComponents α_app (fun f ↦ (liftNatTrans (fun v ↦ (α_app v).hom) α_nat).naturality f)

end

end CategoryTheory.Paths
