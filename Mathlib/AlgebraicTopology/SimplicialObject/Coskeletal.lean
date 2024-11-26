/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Coskeletal simplicial objects

The identity natural transformation exhibits a simplicial object `X` as a right extension of its
restriction along `(Truncated.inclusion n).op` recorded by `rightExtensionInclusion X n`.

The simplicial object `X` is *n-coskeletal* if `rightExtensionInclusion X n` is a right Kan
extension.

When the ambient category admits right Kan extensions along `(Truncated.inclusion n).op`,
then when `X` is `n`-coskeletal, the unit of `coskAdj n` defines an isomorphism:
`isoCoskOfIsCoskeletal : X ≅ (Truncated.cosk n).obj ((truncation n).obj X)`.

TODO: Prove that `X` is `n`-coskeletal whenever a certain canonical cone is a limit cone.
-/

open Opposite

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor SimplexCategory

universe v u v' u'

namespace CategoryTheory

namespace SimplicialObject
variable {C : Type u} [Category.{v} C]
variable (X : SimplicialObject C) (n : ℕ)

namespace Truncated

/-- The identity natural transformation exhibits a simplicial set as a right extension of its
restriction along `(Truncated.inclusion n).op`.-/
@[simps!]
def rightExtensionInclusion :
    RightExtension (Truncated.inclusion n).op
      ((Truncated.inclusion n).op ⋙ X) := RightExtension.mk _ (𝟙 _)

end Truncated

open Truncated

/-- A simplicial object `X` is `n`-coskeletal when it is the right Kan extension of its restriction
along `(Truncated.inclusion n).op` via the identity natural transformation. -/
class IsCoskeletal : Prop where
  nonempty_isRightKanExtension :
    Nonempty (IsRightKanExtension X (𝟙 ((Truncated.inclusion n).op ⋙ X)))

variable [X.IsCoskeletal n]

/-- If `X` is `n`-cosketal, then `𝟙 ((Truncated.inclusion n).op ⋙ X)` defines a right Kan
extension of `(Truncated.inclusion.op ⋙ X)` along `(Truncated.inclusion n).op`. -/
theorem IsCoskeletal.isRightKanExtension :
    IsRightKanExtension X (𝟙 ((Truncated.inclusion n).op ⋙ X)) :=
  IsCoskeletal.nonempty_isRightKanExtension.some

/-- If `X` is `n`-coskeletal, then `rightExtensionInclusion X n` is a terminal object in the
category `RightExtension (Truncated.inclusion n).op (Truncated.inclusion.op ⋙ X)`. -/
noncomputable def IsCoskeletal.isUniversalOfIsRightKanExtension :
    (rightExtensionInclusion X n).IsUniversal := by
  have := isRightKanExtension X n
  apply Functor.isUniversalOfIsRightKanExtension

variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]

/-- There is a map of costructured arrows from `rightExtensionInclusion X n` to the right extension
of the `n`-truncation of `X` defined by the counit of `coskAdj n`. -/
noncomputable def Truncated.rightExtensionCosk.hom : Truncated.rightExtensionInclusion X n ⟶
    RightExtension.mk _
      ((coskAdj n).counit.app ((Truncated.inclusion n).op ⋙ X)) :=
  CostructuredArrow.homMk ((coskAdj n).unit.app X) ((coskAdj n).left_triangle_components X)

instance Truncated.isRightKanExtensionCosk : IsRightKanExtension
    ((Truncated.cosk n).obj ((inclusion n).op ⋙ X))
    ((coskAdj n).counit.app ((inclusion n).op ⋙ X)) := by
  unfold Truncated.cosk coskAdj
  rw [ranAdjunction_counit]
  exact Functor.instIsRightKanExtensionObjRanAppRanCounit _ _

/-- The map `coskRightExtension.hom X` is a natural transformation between two right Kan extensions
of the diagram `Truncated.inclusion.op ⋙ X` and thus is an isomorphism. -/
instance IsCoskeletal.coskRightExtension.isIso_hom : IsIso (rightExtensionCosk.hom X n) :=
  isIso_of_isTerminal (IsCoskeletal.isUniversalOfIsRightKanExtension X n)
    (((Truncated.cosk n).obj
      ((Truncated.inclusion n).op ⋙ X)).isUniversalOfIsRightKanExtension
        ((coskAdj n).counit.app ((Truncated.inclusion n).op ⋙ X)))
      (rightExtensionCosk.hom X n)

/-- The map `coskRightExtension.hom X` is a natural transformation between two right Kan extensions
of the diagram `Truncated.inclusion.op ⋙ X` and thus is an isomorphism. -/
noncomputable def IsCoskeletal.coskRightExtension.homIso :
    Truncated.rightExtensionInclusion X n ≅ RightExtension.mk _
      ((coskAdj n).counit.app ((Truncated.inclusion n).op ⋙ X)) :=
  asIso (rightExtensionCosk.hom X n)

/-- The isomorphism `X ≅ (cosk n).obj X` that exists when `X` is coskeletal and the
`n`-coskeleton functor exists.-/
noncomputable def isoCoskOfIsCoskeletal : X ≅ (cosk n).obj X :=
  (CostructuredArrow.proj ((whiskeringLeft _ _ _).obj (Truncated.inclusion n).op)
    ((Truncated.inclusion n).op ⋙ X)).mapIso (IsCoskeletal.coskRightExtension.homIso X n)


end SimplicialObject

end CategoryTheory
