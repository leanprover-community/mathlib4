/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.Algebra.Category.AlgebraCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The monoidal category structure on R-algebras
-/

open CategoryTheory
open scoped MonoidalCategory

universe v u w v₁ w₁

variable {R : Type u} [CommRing R]

/-- The `R`-algebra equivalence between `ULift A` and `A`. -/
@[simps apply symm_apply]
def ULift.algebraEquiv {R : Type u} [CommSemiring R] {A : Type v} [Semiring A] [Algebra R A] :
    ULift A ≃ₐ[R] A :=
  { ULift.ringEquiv with
    toFun := ULift.down
    invFun := ULift.up
    commutes' := fun _ => rfl}

namespace AlgebraCat

noncomputable section

namespace instMonoidalCategory

open scoped TensorProduct

/-- Auxiliary definition used to fight a timeout when building
`AlgebraCat.instMonoidalCategory`. -/
@[simps!]
noncomputable abbrev tensorObj (X Y : AlgebraCat R) : AlgebraCat R :=
  of R (X ⊗[R] Y)

/-- Auxiliary definition used to fight a timeout when building
`AlgebraCat.instMonoidalCategory`. -/
noncomputable abbrev tensorHom {W X Y Z : AlgebraCat R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
  Algebra.TensorProduct.map f g

open MonoidalCategory

end instMonoidalCategory

open instMonoidalCategory

instance : MonoidalCategoryStruct (AlgebraCatMax.{v, u} R) where
  tensorObj := instMonoidalCategory.tensorObj
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight {X₁ X₂} (f : X₁ ⟶ X₂) Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := of R (ULift R)
  associator X Y Z := (Algebra.TensorProduct.assoc R X Y Z).toAlgebraIso
  leftUnitor X := ((Algebra.TensorProduct.congr ULift.algebraEquiv AlgEquiv.refl).trans <|
    Algebra.TensorProduct.lid R X).toAlgebraIso
  rightUnitor X := ((Algebra.TensorProduct.congr AlgEquiv.refl ULift.algebraEquiv).trans <|
    Algebra.TensorProduct.rid R R X).toAlgebraIso

variable (X Y Z : AlgebraCat R)

theorem forget₂_map_associator_hom (X Y Z : AlgebraCatMax.{v, u} R) :
    (forget₂ (AlgebraCatMax.{v, u} R) (ModuleCatMax.{v, u} R)).map (α_ X Y Z).hom =
      (α_
        (forget₂ (AlgebraCatMax.{v, u} R)  (ModuleCatMax.{v, u} R) |>.obj X)
        (forget₂ (AlgebraCatMax.{v, u} R)  (ModuleCatMax.{v, u} R) |>.obj Y)
        (forget₂ (AlgebraCatMax.{v, u} R)  (ModuleCatMax.{v, u} R) |>.obj Z)).hom := by
  simp only [forget₂_module_obj, forget₂_module_map]
  rfl

theorem forget₂_map_associator_inv (X Y Z : AlgebraCatMax.{v, u} R) :
    (forget₂ (AlgebraCatMax.{v, u} R) (ModuleCatMax.{v, u} R)).map (α_ X Y Z).inv =
      (α_
        (forget₂ (AlgebraCatMax.{v, u} R) (ModuleCatMax.{v, u} R) |>.obj X)
        (forget₂ (AlgebraCatMax.{v, u} R) (ModuleCatMax.{v, u} R) |>.obj Y)
        (forget₂ (AlgebraCatMax.{v, u} R) (ModuleCatMax.{v, u} R) |>.obj Z)).inv := by
  simp only [forget₂_module_obj, forget₂_module_map]
  rfl

/-- -/
def εIso : 𝟙_ (ModuleCat R)
    ≅ (forget₂ _ (ModuleCat R)).obj (𝟙_ (AlgebraCat R)) :=
  LinearEquiv.toModuleIso
    { toFun := fun ⟨x⟩ => ⟨x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun ⟨x⟩ => ⟨x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

noncomputable instance instMonoidalCategory : MonoidalCategory (AlgebraCat R) :=
  Monoidal.induced
    (forget₂ (AlgebraCat R) (ModuleCat R))
    { μIso := fun X Y => Iso.refl _
      εIso := LinearEquiv.toModuleIso
        { toFun := fun ⟨x⟩ => ⟨x⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          invFun := fun ⟨x⟩ => ⟨x⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      associator_eq := fun X Y Z => by
        apply TensorProduct.ext_threefold
        intro x y z
        rfl
      leftUnitor_eq := fun X => by
        apply TensorProduct.ext
        apply ULift.ext_linearMap
        apply LinearMap.ext_ring
        rfl
      rightUnitor_eq := fun X => by
        apply TensorProduct.ext
        apply LinearMap.ext
        intro x
        apply ULift.ext_linearMap
        apply LinearMap.ext_ring
        rfl }

variable (R) in
/-- `forget₂ (AlgebraCat R) (ModuleCat R)` as a monoidal functor. -/
def toModuleCatMonoidalFunctor : MonoidalFunctor (AlgebraCat R) (ModuleCat R) := by
  unfold instMonoidalCategory
  exact Monoidal.fromInduced (forget₂ (AlgebraCat R) (ModuleCat R)) _

instance : (toModuleCatMonoidalFunctor R).Faithful :=
  forget₂_faithful _ _

end

end AlgebraCat
