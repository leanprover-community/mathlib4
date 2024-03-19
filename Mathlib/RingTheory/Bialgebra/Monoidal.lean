import Mathlib.Algebra.Category.AlgebraCat.Symmetric
import Mathlib.RingTheory.TensorProduct
import Mathlib.RingTheory.Bialgebra.Cat
import Mathlib.RingTheory.Coalgebra.Monoidal

universe v u

section
open scoped TensorProduct
namespace Bialgebra

variable {R A B C D : Type u} [CommRing R] [Ring A] [Ring B] [Ring C] [Ring D]
    [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]

set_option profiler true

lemma TensorProduct.counit_eq_toLinearMap :
    Coalgebra.counit (R := R) (A := A ⊗[R] B)
      = ((Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map
      (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R B))).toLinearMap := by
  simp only [Coalgebra.tensorProductCoalgebraStruct_counit, AlgHom.comp_toLinearMap,
    Algebra.TensorProduct.map_toLinearMap, Algebra.TensorProduct.lmul'_toLinearMap]
  rfl

lemma TensorProduct.comul_eq_toLinearMap :
  Coalgebra.comul (R := R) (A := A ⊗[R] B)
    = ((Algebra.TensorProduct.tensorTensorTensorComm R A A B B).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R A)
      (Bialgebra.comulAlgHom R B))).toLinearMap := by
  simp only [Coalgebra.tensorProductCoalgebraStruct_comul, AlgEquiv.toAlgHom_eq_coe,
    AlgHom.comp_toLinearMap, AlgEquiv.toAlgHom_toLinearMap,
    Algebra.TensorProduct.tensorTensorTensorComm_toLinearMap,
    Algebra.TensorProduct.map_toLinearMap]
  rfl

noncomputable instance {A B : Type u} [Ring A] [Ring B]
    [Bialgebra R A] [Bialgebra R B] : Bialgebra R (A ⊗[R] B) := by
  refine' Bialgebra.mk' R (A ⊗[R] B) _ (fun {x y} => _) _ (fun {x y} => _)
  <;> simp only [AlgHom.toLinearMap_apply, TensorProduct.counit_eq_toLinearMap,
    TensorProduct.comul_eq_toLinearMap]
  <;> simp only [map_one, map_mul]

@[simps! toCoalgHom] noncomputable def TensorProduct.map (f : A →b[R] B) (g : C →b[R] D) :
    A ⊗[R] C →b[R] B ⊗[R] D :=
  { Coalgebra.TensorProduct.map f.toCoalgHom g.toCoalgHom,
      Algebra.TensorProduct.map f.toAlgHom g.toAlgHom with }

variable (A)

noncomputable abbrev lTensor (f : B →b[R] C) : A ⊗[R] B →b[R] A ⊗[R] C :=
  TensorProduct.map (BialgHom.id R A) f

noncomputable abbrev rTensor (f : B →b[R] C) : B ⊗[R] A →b[R] C ⊗[R] A :=
  TensorProduct.map f (BialgHom.id R A)

variable (R B C)

lemma ffs3 (x) :
  Coalgebra.TensorProduct.assoc R A B C x = Algebra.TensorProduct.assoc R A B C x := rfl
--set_option trace.profiler true
noncomputable def TensorProduct.assoc :
    (A ⊗[R] B) ⊗[R] C ≃b[R] A ⊗[R] (B ⊗[R] C) :=
  { Coalgebra.TensorProduct.assoc R A B C with
    --map_mul' := fun x y => by

    --by simp only [ffs3, map_mul]-- map_mul (Algebra.TensorProduct.assoc R A B C)
    --commutes' := sorry --by simp only [ffs3, AlgHomClass.commutes]
     }-- (Algebra.TensorProduct.assoc R A B C) }

@[simps! toCoalgEquiv] noncomputable def TensorProduct.lid : R ⊗[R] A ≃b[R] A :=
  { Coalgebra.TensorProduct.lid R A, Algebra.TensorProduct.lid R A with }

@[simps! toCoalgEquiv] noncomputable def TensorProduct.rid : A ⊗[R] R ≃b[R] A := by
  refine
  { Coalgebra.TensorProduct.rid R A with
    map_mul' := fun x y => ?_
    commutes' := fun r => ?_ }
  <;> simp only [Coalgebra.TensorProduct.rid_toCoalgHom, AddHom.toFun_eq_coe,
    LinearMap.coe_toAddHom, LinearEquiv.coe_coe, ← TensorProduct.AlgebraTensorModule.rid_eq_rid,
    ← Algebra.TensorProduct.rid_toLinearEquiv, AlgEquiv.toLinearEquiv_apply, AlgEquiv.map_mul,
    AlgEquiv.commutes]

namespace MonoidalCategory
open TensorProduct CategoryTheory MonoidalCategory Bialgebra

@[simps] noncomputable instance : MonoidalCategoryStruct.{u} (BialgCat R) where
  tensorObj := fun X Y => BialgCat.of R (X ⊗[R] Y)
  whiskerLeft := fun X _ _ f => BialgCat.ofHom (lTensor X f)
  whiskerRight := fun f X => BialgCat.ofHom (rTensor X f)
  tensorHom := fun f g => BialgCat.ofHom (TensorProduct.map f g)
  tensorUnit := BialgCat.of R R
  associator := fun X Y Z => (TensorProduct.assoc R X Y Z).toBialgIso
  leftUnitor := fun X => (TensorProduct.lid R X).toBialgIso
  rightUnitor := fun X => (TensorProduct.rid R X).toBialgIso

set_option profiler true

@[simps] noncomputable def inducingFunctorData :
    Monoidal.InducingFunctorData (forget₂ (BialgCat R) (AlgebraCat R)) where
  μIso := fun X Y => Iso.refl _
  whiskerLeft_eq := fun X Y Z f => by ext; rfl
  whiskerRight_eq := fun X f => by ext; rfl
  tensorHom_eq := fun f g => by ext; rfl
  εIso := Iso.refl _
  associator_eq := fun X Y Z => Algebra.TensorProduct.ext
      (Algebra.TensorProduct.ext (by ext; rfl) (by ext; rfl)) (by ext; rfl)
  leftUnitor_eq := fun X => Algebra.TensorProduct.ext rfl (by ext; rfl)
  rightUnitor_eq := fun X => Algebra.TensorProduct.ext (by ext; rfl) rfl

noncomputable instance : MonoidalCategory (BialgCat R) :=
  Monoidal.induced (forget₂ _ (AlgebraCat R)) (inducingFunctorData R)

end Bialgebra.MonoidalCategory
