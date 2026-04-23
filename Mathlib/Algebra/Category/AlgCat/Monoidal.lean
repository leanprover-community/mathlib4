/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike

/-!
# The monoidal category structure on R-algebras
-/

@[expose] public section

open CategoryTheory
open scoped MonoidalCategory

universe v u

variable {R : Type u} [CommRing R]

namespace AlgCat

noncomputable section

namespace instMonoidalCategory

open scoped TensorProduct

/-- Auxiliary definition used to fight a timeout when building
`AlgCat.instMonoidalCategory`. -/
@[simps!]
noncomputable abbrev tensorObj (X Y : AlgCat.{u} R) : AlgCat.{u} R :=
  of R (X ⊗[R] Y)

/-- Auxiliary definition used to fight a timeout when building
`AlgCat.instMonoidalCategory`. -/
noncomputable abbrev tensorHom {W X Y Z : AlgCat.{u} R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
  ofHom <| Algebra.TensorProduct.map f.hom g.hom

end instMonoidalCategory

open instMonoidalCategory

instance : MonoidalCategoryStruct (AlgCat.{u} R) where
  tensorObj := instMonoidalCategory.tensorObj
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight {X₁ X₂} (f : X₁ ⟶ X₂) Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := of R R
  associator X Y Z := (Algebra.TensorProduct.assoc R R R X Y Z).toAlgebraIso
  leftUnitor X := (Algebra.TensorProduct.lid R X).toAlgebraIso
  rightUnitor X := (Algebra.TensorProduct.rid R R X).toAlgebraIso

theorem hom_tensorHom {K L M N : AlgCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) :
    (f ⊗ₘ g).hom = Algebra.TensorProduct.map f.hom g.hom :=
  rfl

theorem hom_whiskerLeft (L : AlgCat.{u} R) {M N : AlgCat.{u} R} (f : M ⟶ N) :
    (L ◁ f).hom = Algebra.TensorProduct.map (.id _ _) f.hom :=
  rfl

theorem hom_whiskerRight {L M : AlgCat.{u} R} (f : L ⟶ M) (N : AlgCat.{u} R) :
    (f ▷ N).hom = Algebra.TensorProduct.map f.hom (.id _ _) :=
  rfl

theorem hom_hom_leftUnitor {M : AlgCat.{u} R} :
    (λ_ M).hom.hom = (Algebra.TensorProduct.lid _ _).toAlgHom :=
  rfl

theorem hom_inv_leftUnitor {M : AlgCat.{u} R} :
    (λ_ M).inv.hom = (Algebra.TensorProduct.lid _ _).symm.toAlgHom :=
  rfl

theorem hom_hom_rightUnitor {M : AlgCat.{u} R} :
    (ρ_ M).hom.hom = (Algebra.TensorProduct.rid _ _ _).toAlgHom :=
  rfl

theorem hom_inv_rightUnitor {M : AlgCat.{u} R} :
    (ρ_ M).inv.hom = (Algebra.TensorProduct.rid _ _ _).symm.toAlgHom :=
  rfl

theorem hom_hom_associator {M N K : AlgCat.{u} R} :
    (α_ M N K).hom.hom = (Algebra.TensorProduct.assoc R R R M N K).toAlgHom :=
  rfl

theorem hom_inv_associator {M N K : AlgCat.{u} R} :
    (α_ M N K).inv.hom = (Algebra.TensorProduct.assoc R R R M N K).symm.toAlgHom :=
  rfl

noncomputable instance instMonoidalCategory : MonoidalCategory (AlgCat.{u} R) :=
  Monoidal.induced
    (forget₂ (AlgCat R) (ModuleCat R))
    { μIso := fun _ _ => Iso.refl _
      εIso := Iso.refl _
      associator_eq := fun _ _ _ =>
        ModuleCat.hom_ext <| TensorProduct.ext_threefold (fun _ _ _ => rfl)
      leftUnitor_eq := fun _ => ModuleCat.hom_ext <| TensorProduct.ext' (fun _ _ => rfl)
      rightUnitor_eq := fun _ => ModuleCat.hom_ext <| TensorProduct.ext' (fun _ _ => rfl) }

/-- `forget₂ (AlgCat R) (ModuleCat R)` as a monoidal functor. -/
example : (forget₂ (AlgCat R) (ModuleCat R)).Monoidal := inferInstance

end

end AlgCat
