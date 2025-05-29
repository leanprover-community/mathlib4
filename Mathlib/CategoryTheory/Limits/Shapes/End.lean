/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-!
# Ends and coends

In this file, given a functor `F : Jᵒᵖ ⥤ J ⥤ C`, we define its end `end_ F`,
which is a suitable multiequalizer of the objects `(F.obj (op j)).obj j` for all `j : J`.
For this shape of limits, cones are named wedges: the corresponding type is `Wedge F`.

## References
* https://ncatlab.org/nlab/show/end

## TODO

* define coends

-/

universe v v' u u'

namespace CategoryTheory

open Opposite

namespace Limits

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
  (F : Jᵒᵖ ⥤ J ⥤ C)

variable (J) in
/-- The shape of multiequalizer diagrams involved in the definition of ends. -/
@[simps]
def multicospanShapeEnd : MulticospanShape where
  L := J
  R := Arrow J
  fst f := f.left
  snd f := f.right

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the multicospan index which shall be used
to define the end of `F`. -/
@[simps]
def multicospanIndexEnd : MulticospanIndex (multicospanShapeEnd J) C where
  left j := (F.obj (op j)).obj j
  right f := (F.obj (op f.left)).obj f.right
  fst f := (F.obj (op f.left)).map f.hom
  snd f := (F.map f.hom.op).app f.right

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, a wedge for `F` is a type of cones (specifically
the type of multiforks for `multicospanIndexEnd F`):
the point of universal of these wedges shall be the end of `F`. -/
abbrev Wedge := Multifork (multicospanIndexEnd F)

namespace Wedge

variable {F}

section Constructor

variable (pt : C) (π : ∀ (j : J), pt ⟶ (F.obj (op j)).obj j)
  (hπ : ∀ ⦃i j : J⦄ (f : i ⟶ j), π i ≫ (F.obj (op i)).map f = π j ≫ (F.map f.op).app j)

/-- Constructor for wedges. -/
@[simps! pt]
abbrev mk : Wedge F :=
  Multifork.ofι _ pt π (fun f ↦ hπ f.hom)

@[simp]
lemma mk_ι (j : J) : (mk pt π hπ).ι j = π j := rfl

end Constructor

@[reassoc]
lemma condition (c : Wedge F) {i j : J} (f : i ⟶ j) :
    c.ι i ≫ (F.obj (op i)).map f = c.ι j ≫ (F.map f.op).app j :=
  Multifork.condition c (Arrow.mk f)

namespace IsLimit

variable {c : Wedge F} (hc : IsLimit c)

lemma hom_ext (hc : IsLimit c) {X : C} {f g : X ⟶ c.pt} (h : ∀ j, f ≫ c.ι j = g ≫ c.ι j) :
    f = g :=
  Multifork.IsLimit.hom_ext hc h

/-- Construct a morphism to the end from its universal property. -/
def lift (hc : IsLimit c) {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j) :
    X ⟶ c.pt :=
  Multifork.IsLimit.lift hc f (fun _ ↦ hf _)

@[reassoc (attr := simp)]
lemma lift_ι (hc : IsLimit c) {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
    (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j) (j : J) :
    lift hc f hf ≫ c.ι j = f j := by
  apply IsLimit.fac


end IsLimit

end Wedge

section End

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this property asserts the existence of the end of `F`. -/
abbrev HasEnd := HasMultiequalizer (multicospanIndexEnd F)

variable [HasEnd F]

/-- The end of a functor `F : Jᵒᵖ ⥤ J ⥤ C`. -/
noncomputable def end_ : C := multiequalizer (multicospanIndexEnd F)

/-- Given `F : Jᵒᵖ ⥤ J ⥤ C`, this is the projection `end_ F ⟶ (F.obj (op j)).obj j`
for any `j : J`. -/
noncomputable def end_.π (j : J) : end_ F ⟶ (F.obj (op j)).obj j := Multiequalizer.ι _ _

@[reassoc]
lemma end_.condition {i j : J} (f : i ⟶ j) :
    π F i ≫ (F.obj (op i)).map f = π F j ≫ (F.map f.op).app j := by
  apply Wedge.condition

variable {F}

@[ext]
lemma hom_ext {X : C} {f g : X ⟶ end_ F} (h : ∀ j, f ≫ end_.π F j = g ≫ end_.π F j) :
    f = g :=
  Multiequalizer.hom_ext _ _ _ (fun _ ↦ h _)

section

variable {X : C} (f : ∀ j, X ⟶ (F.obj (op j)).obj j)
  (hf : ∀ ⦃i j : J⦄ (g : i ⟶ j), f i ≫ (F.obj (op i)).map g = f j ≫ (F.map g.op).app j)

/-- Constructor for morphisms to the end of a functor. -/
noncomputable def end_.lift : X ⟶ end_ F :=
  Wedge.IsLimit.lift (limit.isLimit _) f hf

@[reassoc (attr := simp)]
lemma end_.lift_π (j : J) : lift f hf ≫ π F j = f j := by
  apply IsLimit.fac

end

end End

end Limits

end CategoryTheory
