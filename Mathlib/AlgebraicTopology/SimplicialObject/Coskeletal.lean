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
@[mk_iff]
class IsCoskeletal : Prop where
  isRightKanExtension : IsRightKanExtension X (𝟙 ((Truncated.inclusion n).op ⋙ X))

attribute [instance] IsCoskeletal.isRightKanExtension

section

variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]

/-- There is a map of costructured arrows from `Truncated.rightExtensionInclusion X n` to the right
extension of the `n`-truncation of `X` defined by the counit of `coskAdj n`. -/
noncomputable def Truncated.rightExtensionCosk.hom : Truncated.rightExtensionInclusion X n ⟶
    RightExtension.mk _
      ((coskAdj n).counit.app ((Truncated.inclusion n).op ⋙ X)) :=
  CostructuredArrow.homMk ((coskAdj n).unit.app X) ((coskAdj n).left_triangle_components X)

/-- The counit of an adjunction is always a right Kan extension. -/
instance Truncated.isRightKanExtensionCosk : IsRightKanExtension
    ((Truncated.cosk n).obj ((inclusion n).op ⋙ X))
    ((coskAdj n).counit.app ((inclusion n).op ⋙ X)) := by
  unfold Truncated.cosk coskAdj
  rw [ranAdjunction_counit]
  infer_instance

/-- The counit of an adjunction is always a right Kan extension. -/
instance Truncated.isRightKanExtensionCosk' : IsRightKanExtension
    ((Truncated.cosk n).obj ((truncation n).obj X))
    ((coskAdj n).counit.app ((truncation n).obj X)) := by
  show IsRightKanExtension
    ((Truncated.cosk n).obj ((inclusion n).op ⋙ X))
    ((coskAdj n).counit.app ((inclusion n).op ⋙ X))
  infer_instance

/-- The counit of an adjunction is always a right Kan extension. -/
instance Truncated.isRightKanExtensionCosk'' : IsRightKanExtension
    ((Truncated.cosk n).obj ((inclusion n).op ⋙ X))
    ((coskAdj n).counit.app ((truncation n).obj X)) := by
  show IsRightKanExtension
    ((Truncated.cosk n).obj ((inclusion n).op ⋙ X))
    ((coskAdj n).counit.app ((inclusion n).op ⋙ X))
  infer_instance

/-- The counit of an adjunction is always a right Kan extension. -/
instance Truncated.isRightKanExtensionCosk''' : IsRightKanExtension
    ((truncation n ⋙ Truncated.cosk n).obj X)
    ((coskAdj n).counit.app ((inclusion n).op ⋙ X)) := by
  show IsRightKanExtension
    ((Truncated.cosk n).obj ((inclusion n).op ⋙ X))
    ((coskAdj n).counit.app ((inclusion n).op ⋙ X))
  infer_instance

section

variable [X.IsCoskeletal n]

/-- If `X` is `n`-cosketal, then `𝟙 ((Truncated.inclusion n).op ⋙ X)` defines a right Kan
extension of `(Truncated.inclusion.op ⋙ X)` along `(Truncated.inclusion n).op`. -/
instance IsCoskeletal.isRightKanExtension :
    IsRightKanExtension X (𝟙 ((Truncated.inclusion n).op ⋙ X)) :=
  IsCoskeletal.nonempty_isRightKanExtension.some

/-- If `X` is `n`-coskeletal, then `Truncated.rightExtensionInclusion X n` is a terminal object in
the category `RightExtension (Truncated.inclusion n).op (Truncated.inclusion.op ⋙ X)`. -/
noncomputable def IsCoskeletal.isUniversalOfIsRightKanExtension :
    (rightExtensionInclusion X n).IsUniversal := by
  have := isRightKanExtension X n
  apply Functor.isUniversalOfIsRightKanExtension

/-- The map `Truncated.rightExtensionCosk.hom X` is a natural transformation between two right Kan
extensions of the diagram `(Truncated.inclusion n).op ⋙ X` and thus is an isomorphism. -/
instance IsCoskeletal.isIso_rightExtensionCosk_hom_of_isCoskeletal :
    IsIso (rightExtensionCosk.hom X n) :=
  isIso_of_isTerminal (IsCoskeletal.isUniversalOfIsRightKanExtension X n)
    (((Truncated.cosk n).obj
      ((Truncated.inclusion n).op ⋙ X)).isUniversalOfIsRightKanExtension
        ((coskAdj n).counit.app ((Truncated.inclusion n).op ⋙ X)))
      (rightExtensionCosk.hom X n)

/-- The map `Truncated.coskRightExtension.hom X` is a natural transformation between two right Kan
extensions of the diagram `(Truncated.inclusion n).op ⋙ X` and thus is an isomorphism. -/
noncomputable def IsCoskeletal.rightExtensionCosk.homIso :
    Truncated.rightExtensionInclusion X n ≅ RightExtension.mk _
      ((coskAdj n).counit.app ((Truncated.inclusion n).op ⋙ X)) :=
  asIso (rightExtensionCosk.hom X n)

/-- The canonical isomorphism `X ≅ (cosk n).obj X` defined when `X` is coskeletal and the
`n`-coskeleton functor exists.-/
noncomputable def isoCoskOfIsCoskeletal : X ≅ (cosk n).obj X :=
  Functor.rightKanExtensionUnique _ (𝟙 _) _ ((coskAdj n).counit.app _)

@[simp]
lemma isoCoskOfIsCoskeletal_hom : (X.isoCoskOfIsCoskeletal n).hom = (coskAdj n).unit.app X := by
  refine hom_ext_of_isRightKanExtension _
    ((coskAdj n).counit.app ((Truncated.inclusion n).op ⋙ X))
    (X.isoCoskOfIsCoskeletal n).hom ((coskAdj n).unit.app X) ?_
  have : whiskerLeft (inclusion n).op
    ((coskAdj n).unit.app X) ≫ (coskAdj n).counit.app ((inclusion n).op ⋙ X) = 𝟙 _ :=
      (coskAdj n).left_triangle_components X
  rw [this]
  simp [isoCoskOfIsCoskeletal]
  apply liftOfIsRightKanExtension_fac

end

theorem isRightKanExtensionCosk_iff_isIso :
    IsRightKanExtension X (𝟙 ((Truncated.inclusion n).op ⋙ X)) ↔
    IsIso ((coskAdj n).unit.app X) := by
  refine isRightKanExtension_iff_isIso
    ((coskAdj n).unit.app X) ((coskAdj n).counit.app ((inclusion n).op ⋙ X)) (𝟙 _) ?_
  simp only [id_obj, comp_obj]
  exact (coskAdj n).left_triangle_components X

theorem isCoskeletal_iff_isIso : X.IsCoskeletal n ↔ IsIso ((coskAdj n).unit.app X) where
  mp := by
    intro hyp
    rw [← isoCoskOfIsCoskeletal_hom]
    exact Iso.isIso_hom (X.isoCoskOfIsCoskeletal n)
  mpr := fun hyp => {
    nonempty_isRightKanExtension := Nonempty.intro ((isRightKanExtensionCosk_iff_isIso X n).mpr hyp)
  }

end

end SimplicialObject

end CategoryTheory
