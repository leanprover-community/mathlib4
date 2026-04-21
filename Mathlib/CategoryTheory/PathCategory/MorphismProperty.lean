/-
Copyright (c) 2024 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Properties of morphisms in a path category.

We provide a formulation of induction principles for morphisms in a path category in terms of
`MorphismProperty`. This file is separate from `Mathlib/CategoryTheory/PathCategory/Basic.lean` in
order to reduce transitive imports. -/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


universe v₁ u₁

namespace CategoryTheory.Paths

section
variable (V : Type u₁) [Quiver.{v₁} V]

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

lemma morphismProperty_eq_top_of_isMultiplicative (P : MorphismProperty (Paths V))
    [P.IsMultiplicative]
    (hP : ∀ {u v : V} (p : u ⟶ v), P ((of V).map p)) : P = ⊤ :=
  morphismProperty_eq_top _ _ (P.id_mem _) (fun _ q hp ↦ P.comp_mem _ _ hp (hP q))
end
section

variable {C : Type*} [Category* C] {V : Type u₁} [Quiver.{v₁} V]

/-- A natural transformation between `F G : Paths V ⥤ C` is defined by its components and
its unary naturality squares. -/
@[simps]
def liftNatTrans {F G : Paths V ⥤ C} (α_app : (v : V) → (F.obj v ⟶ G.obj v))
    (α_nat : {X Y : V} → (f : X ⟶ Y) →
      F.map (Quiver.Hom.toPath f) ≫ α_app Y = α_app X ≫ G.map (Quiver.Hom.toPath f)) : F ⟶ G where
  app := α_app
  naturality := by
    apply MorphismProperty.of_eq_top
      (P := MorphismProperty.naturalityProperty (F₁ := F) α_app)
    exact morphismProperty_eq_top_of_isMultiplicative _ _ α_nat

/-- A natural isomorphism between `F G : Paths V ⥤ C` is defined by its components and
its unary naturality squares. -/
@[simps!]
def liftNatIso {C} [Category* C] {F G : Paths V ⥤ C} (α_app : (v : V) → (F.obj v ≅ G.obj v))
    (α_nat : {X Y : V} → (f : X ⟶ Y) →
      F.map (Quiver.Hom.toPath f) ≫ (α_app Y).hom = (α_app X).hom ≫ G.map (Quiver.Hom.toPath f)) :
    F ≅ G :=
  NatIso.ofComponents α_app (fun f ↦ (liftNatTrans (fun v ↦ (α_app v).hom) α_nat).naturality f)

end

end CategoryTheory.Paths
