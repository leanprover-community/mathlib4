/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-!
# Conservative families of points

Let `J` be a Grothendieck topology on a category `C`.
Let `P : ObjectProperty J.Point` be a family of points. We say that
`P` is a conservative family of points if the corresponding
fiber functors `Sheaf J (Type w) ⥤ Type w` jointly reflect
isomorphisms. Under suitable assumptions on the coefficient
category `A`, this implies that the fiber functors
`Sheaf J A ⥤ A` corresponding to the points in `P`
jointly reflect isomorphisms, epimorphisms and monomorphisms,
and they are also jointly faithful.

## TODO
* Formalize SGA 4 IV 6.5 (a) which characterizes conservative families
of points.

-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (P : ObjectProperty (GrothendieckTopology.Point.{w} J))

namespace ObjectProperty

/-- Let `P : ObjectProperty J.Point` a family of points of a
site `(C, J)`). We say that it is a conservative family of points
if the corresponding fiber functors `Sheaf J (Type w) ⥤ Type w`
jointly reflect isomorphisms. -/
@[stacks 00YK "(1)"]
structure IsConservativeFamilyOfPoints : Prop where
  jointlyReflectIsomorphisms_type :
    JointlyReflectIsomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := Type w))

namespace IsConservativeFamilyOfPoints

variable {P} (hP : P.IsConservativeFamilyOfPoints)
  (A : Type u') [Category.{v'} A] [LocallySmall.{w} C]
  [HasColimitsOfSize.{w, w} A]
  {FC : A → A → Type*} {CC : A → Type w}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w} A FC]
  [(forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
  [hJ : J.HasSheafCompose (forget A)]

include hP hJ

@[stacks 00YK "(1)"]
lemma jointlyReflectIsomorphisms :
    JointlyReflectIsomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) where
  isIso {K L} f _ := by
    rw [← isIso_iff_of_reflects_iso _ (sheafCompose J (forget A)),
      hP.jointlyReflectIsomorphisms_type.isIso_iff]
    exact fun Φ ↦ ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (Φ.obj.sheafFiberCompIso (forget A))).app (Arrow.mk f))).2
          (inferInstanceAs (IsIso ((forget A).map (Φ.obj.sheafFiber.map f))))

@[stacks 00YL "(1)"]
lemma jointlyReflectMonomorphisms [AB5OfSize.{w, w} A] [HasFiniteLimits A] :
    JointlyReflectMonomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  (hP.jointlyReflectIsomorphisms A).jointlyReflectMonomorphisms

@[stacks 00YL "(2)"]
lemma jointlyReflectEpimorphisms
    [J.WEqualsLocallyBijective A] [HasSheafify J A] :
    JointlyReflectEpimorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  (hP.jointlyReflectIsomorphisms A).jointlyReflectEpimorphisms

@[stacks 00YL "(3)"]
lemma jointlyFaithful [AB5OfSize.{w, w} A] [HasFiniteLimits A] :
    JointlyFaithful
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  (hP.jointlyReflectIsomorphisms A).jointlyFaithful

end IsConservativeFamilyOfPoints

end ObjectProperty

namespace GrothendieckTopology

/-- A site has enough points (relatively to a universe `w`)
if it has a `w`-small conservative family of points. -/
class HasEnoughPoints (J : GrothendieckTopology C) : Prop where
  exists_objectProperty (J) :
    ∃ (P : ObjectProperty (Point.{w} J)),
      ObjectProperty.Small.{w} P ∧ P.IsConservativeFamilyOfPoints

end GrothendieckTopology

end CategoryTheory
