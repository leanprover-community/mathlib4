/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang, Emily Riehl
-/
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Monad.Products

#align_import category_theory.adjunction.over from "leanprover-community/mathlib"@"cea27692b3fdeb328a2ddba6aabf181754543184"

/-!
# Adjunctions related to the over category

Construct the left adjoint `star X` to `Over.forget X : Over X ⥤ C`.

## TODO
Show `star X` itself has a left adjoint provided `C` is locally cartesian closed.
-/


noncomputable section

universe v u

namespace CategoryTheory

open Category Limits Comonad

variable {C : Type u} [Category.{v} C] (X : C)


namespace Over

open Limits

-- Porting note: removed semireducible from the simps config
/-- Given a morphism `f : X ⟶ Y`, the functor `baseChange f` takes morphisms over `Y` to morphisms
over `X` via pullbacks. -/
@[simps! (config := { simpRhs := true}) obj_left obj_hom map_left]
def baseChange [HasPullbacks C] {X Y : C} (f : X ⟶ Y) : Over Y ⥤ Over X where
  obj g := Over.mk (pullback.snd : pullback g.hom f ⟶ _)
  map i := Over.homMk (pullback.map _ _ _ _ i.left (𝟙 _) (𝟙 _) (by simp) (by simp))
  map_id Z := by
    apply Over.OverMorphism.ext; apply pullback.hom_ext
    · dsimp; simp
    · dsimp; simp
  map_comp f g := by
    apply Over.OverMorphism.ext; apply pullback.hom_ext
    · dsimp; simp
    · dsimp; simp
#align category_theory.limits.base_change CategoryTheory.Over.baseChange

-- deprecated on 2024-05-15
@[deprecated] noncomputable alias Limits.baseChange := Over.baseChange

/-- The adjunction `Over.map ⊣ baseChange` -/
@[simps! unit_app counit_app]
def mapAdjunction [HasPullbacks C] {X Y : C} (f : X ⟶ Y) : Over.map f ⊣ baseChange f :=
  .mkOfHomEquiv <| {
    homEquiv := fun X Y => {
      toFun := fun u => Over.homMk (pullback.lift u.left X.hom <| by simp)
      invFun := fun v => Over.homMk (v.left ≫ pullback.fst) <|
        by simp [← Over.w v, pullback.condition]
      left_inv := by aesop_cat
      right_inv := by
        intro v
        ext
        dsimp
        ext
        · simp
        · simpa using Over.w v |>.symm } }

/--
The functor from `C` to `Over X` which sends `Y : C` to `π₁ : X ⨯ Y ⟶ X`, sometimes denoted `X*`.
-/
@[simps! obj_left obj_hom map_left]
def star [HasBinaryProducts C] : C ⥤ Over X :=
  cofree _ ⋙ coalgebraToOver X
#align category_theory.star CategoryTheory.Over.star

/-- The functor `Over.forget X : Over X ⥤ C` has a right adjoint given by `star X`.

Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
def forgetAdjStar [HasBinaryProducts C] : forget X ⊣ star X :=
  (coalgebraEquivOver X).symm.toAdjunction.comp (adj _)
#align category_theory.forget_adj_star CategoryTheory.Over.forgetAdjStar

/-- Note that the binary products assumption is necessary: the existence of a right adjoint to
`Over.forget X` is equivalent to the existence of each binary product `X ⨯ -`.
-/
instance [HasBinaryProducts C] : (forget X).IsLeftAdjoint  :=
  ⟨_, ⟨forgetAdjStar X⟩⟩

end Over

@[deprecated (since := "2024-05-18")] noncomputable alias star := Over.star

@[deprecated (since := "2024-05-18")] noncomputable alias forgetAdjStar := Over.forgetAdjStar


end CategoryTheory
