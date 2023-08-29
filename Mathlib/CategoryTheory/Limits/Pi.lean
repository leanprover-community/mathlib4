/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Limits.HasLimits

#align_import category_theory.limits.pi from "leanprover-community/mathlib"@"744d59af0b28d0c42f631038627df9b85ae1d1ce"

/-!
# Limits in the category of indexed families of objects.

Given a functor `F : J ⥤ Π i, C i` into a category of indexed families,
1. we can assemble a collection of cones over `F ⋙ Pi.eval C i` into a cone over `F`
2. if all those cones are limit cones, the assembled cone is a limit cone, and
3. if we have limits for each of `F ⋙ Pi.eval C i`, we can produce a
   `HasLimit F` instance
-/


open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.pi

universe v₁ v₂ u₁ u₂

variable {I : Type v₁} {C : I → Type u₁} [∀ i, Category.{v₁} (C i)]

variable {J : Type v₁} [SmallCategory J]

variable {F : J ⥤ ∀ i, C i}

/-- A cone over `F : J ⥤ Π i, C i` has as its components cones over each of the `F ⋙ Pi.eval C i`.
-/
def coneCompEval (c : Cone F) (i : I) : Cone (F ⋙ Pi.eval C i) where
  pt := c.pt i
  π :=
    { app := fun j => c.π.app j i
      naturality := fun _ _ f => congr_fun (c.π.naturality f) i }
#align category_theory.pi.cone_comp_eval CategoryTheory.pi.coneCompEval

/--
A cocone over `F : J ⥤ Π i, C i` has as its components cocones over each of the `F ⋙ Pi.eval C i`.
-/
def coconeCompEval (c : Cocone F) (i : I) : Cocone (F ⋙ Pi.eval C i) where
  pt := c.pt i
  ι :=
    { app := fun j => c.ι.app j i
      naturality := fun _ _ f => congr_fun (c.ι.naturality f) i }
#align category_theory.pi.cocone_comp_eval CategoryTheory.pi.coconeCompEval

/--
Given a family of cones over the `F ⋙ Pi.eval C i`, we can assemble these together as a `Cone F`.
-/
def coneOfConeCompEval (c : ∀ i, Cone (F ⋙ Pi.eval C i)) : Cone F where
  pt i := (c i).pt
  π :=
    { app := fun j i => (c i).π.app j
      naturality := fun j j' f => by
        funext i
        -- ⊢ (((Functor.const J).obj fun i => (c i).pt).map f ≫ (fun j i => NatTrans.app  …
        exact (c i).π.naturality f }
        -- 🎉 no goals
#align category_theory.pi.cone_of_cone_comp_eval CategoryTheory.pi.coneOfConeCompEval

/-- Given a family of cocones over the `F ⋙ Pi.eval C i`,
we can assemble these together as a `Cocone F`.
-/
def coconeOfCoconeCompEval (c : ∀ i, Cocone (F ⋙ Pi.eval C i)) : Cocone F where
  pt i := (c i).pt
  ι :=
    { app := fun j i => (c i).ι.app j
      naturality := fun j j' f => by
        funext i
        -- ⊢ (F.map f ≫ (fun j i => NatTrans.app (c i).ι j) j') i = ((fun j i => NatTrans …
        exact (c i).ι.naturality f }
        -- 🎉 no goals
#align category_theory.pi.cocone_of_cocone_comp_eval CategoryTheory.pi.coconeOfCoconeCompEval

/-- Given a family of limit cones over the `F ⋙ Pi.eval C i`,
assembling them together as a `Cone F` produces a limit cone.
-/
def coneOfConeEvalIsLimit {c : ∀ i, Cone (F ⋙ Pi.eval C i)} (P : ∀ i, IsLimit (c i)) :
    IsLimit (coneOfConeCompEval c) where
  lift s i := (P i).lift (coneCompEval s i)
  fac s j := by
    funext i
    -- ⊢ ((fun s i => IsLimit.lift (P i) (coneCompEval s i)) s ≫ NatTrans.app (coneOf …
    exact (P i).fac (coneCompEval s i) j
    -- 🎉 no goals
  uniq s m w := by
    funext i
    -- ⊢ m i = (fun s i => IsLimit.lift (P i) (coneCompEval s i)) s i
    exact (P i).uniq (coneCompEval s i) (m i) fun j => congr_fun (w j) i
    -- 🎉 no goals
#align category_theory.pi.cone_of_cone_eval_is_limit CategoryTheory.pi.coneOfConeEvalIsLimit

/-- Given a family of colimit cocones over the `F ⋙ Pi.eval C i`,
assembling them together as a `Cocone F` produces a colimit cocone.
-/
def coconeOfCoconeEvalIsColimit {c : ∀ i, Cocone (F ⋙ Pi.eval C i)} (P : ∀ i, IsColimit (c i)) :
    IsColimit (coconeOfCoconeCompEval c) where
  desc s i := (P i).desc (coconeCompEval s i)
  fac s j := by
    funext i
    -- ⊢ (NatTrans.app (coconeOfCoconeCompEval c).ι j ≫ (fun s i => IsColimit.desc (P …
    exact (P i).fac (coconeCompEval s i) j
    -- 🎉 no goals
  uniq s m w := by
    funext i
    -- ⊢ m i = (fun s i => IsColimit.desc (P i) (coconeCompEval s i)) s i
    exact (P i).uniq (coconeCompEval s i) (m i) fun j => congr_fun (w j) i
    -- 🎉 no goals
#align category_theory.pi.cocone_of_cocone_eval_is_colimit CategoryTheory.pi.coconeOfCoconeEvalIsColimit

section

variable [∀ i, HasLimit (F ⋙ Pi.eval C i)]

/-- If we have a functor `F : J ⥤ Π i, C i` into a category of indexed families,
and we have limits for each of the `F ⋙ Pi.eval C i`,
then `F` has a limit.
-/
theorem hasLimit_of_hasLimit_comp_eval : HasLimit F :=
  HasLimit.mk
    { cone := coneOfConeCompEval fun _ => limit.cone _
      isLimit := coneOfConeEvalIsLimit fun _ => limit.isLimit _ }
#align category_theory.pi.has_limit_of_has_limit_comp_eval CategoryTheory.pi.hasLimit_of_hasLimit_comp_eval

end

section

variable [∀ i, HasColimit (F ⋙ Pi.eval C i)]

/-- If we have a functor `F : J ⥤ Π i, C i` into a category of indexed families,
and colimits exist for each of the `F ⋙ Pi.eval C i`,
there is a colimit for `F`.
-/
theorem hasColimit_of_hasColimit_comp_eval : HasColimit F :=
  HasColimit.mk
    { cocone := coconeOfCoconeCompEval fun _ => colimit.cocone _
      isColimit := coconeOfCoconeEvalIsColimit fun _ => colimit.isColimit _ }
#align category_theory.pi.has_colimit_of_has_colimit_comp_eval CategoryTheory.pi.hasColimit_of_hasColimit_comp_eval

end

/-!
As an example, we can use this to construct particular shapes of limits
in a category of indexed families.

With the addition of
`import CategoryTheory.Limits.Shapes.Types`
we can use:
```
local attribute [instance] hasLimit_of_hasLimit_comp_eval
example : hasBinaryProducts (I → Type v₁) := ⟨by infer_instance⟩
```
-/


end CategoryTheory.pi
