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
`isoCoskOfIsCoskeletal : X ≅ (cosk n).obj X`.

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
restriction along `(Truncated.inclusion n).op`. -/
@[simps!]
def rightExtensionInclusion :
    RightExtension (Truncated.inclusion n).op
      ((Truncated.inclusion n).op ⋙ X) := RightExtension.mk _ (𝟙 _)

end Truncated

open Truncated

/-- A simplicial object `X` is `n`-coskeletal when it is the right Kan extension of its restriction
along `(Truncated.inclusion n).op` via the identity natural transformation. -/
@[mk_iff]
class IsCoskeletal : Prop where
  isRightKanExtension : IsRightKanExtension X (𝟙 ((Truncated.inclusion n).op ⋙ X))

attribute [instance] IsCoskeletal.isRightKanExtension

section

variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]

/-- If `X` is `n`-coskeletal, then `Truncated.rightExtensionInclusion X n` is a terminal object in
the category `RightExtension (Truncated.inclusion n).op (Truncated.inclusion.op ⋙ X)`. -/
noncomputable def IsCoskeletal.isUniversalOfIsRightKanExtension [X.IsCoskeletal n] :
    (rightExtensionInclusion X n).IsUniversal := by
  apply Functor.isUniversalOfIsRightKanExtension

theorem isCoskeletal_iff_isIso : X.IsCoskeletal n ↔ IsIso ((coskAdj n).unit.app X) := by
  rw [isCoskeletal_iff]
  exact isRightKanExtension_iff_isIso ((coskAdj n).unit.app X)
    ((coskAdj n).counit.app _) (𝟙 _) ((coskAdj n).left_triangle_components X)

instance [X.IsCoskeletal n] : IsIso ((coskAdj n).unit.app X) := by
  rw [← isCoskeletal_iff_isIso]
  infer_instance

/-- The canonical isomorphism `X ≅ (cosk n).obj X` defined when `X` is coskeletal and the
`n`-coskeleton functor exists. -/
@[simps! hom]
noncomputable def isoCoskOfIsCoskeletal [X.IsCoskeletal n] : X ≅ (cosk n).obj X :=
  asIso ((coskAdj n).unit.app X)

end

end SimplicialObject

end CategoryTheory
