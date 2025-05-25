/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Andrew Yang
-/
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor products of bialgebras

We define the data in the monoidal structure on the category of bialgebras - e.g. the bialgebra
instance on a tensor product of bialgebras, and the tensor product of two `BialgHom`s as a
`BialgHom`. This is done by combining the corresponding API for coalgebras and algebras.

-/

open scoped TensorProduct

namespace Bialgebra.TensorProduct

open Coalgebra.TensorProduct

variable (R A B C D : Type*) [CommSemiring R] [Semiring A] [Semiring B]
  [Bialgebra R A] [Bialgebra R B]

lemma counit_eq_algHom_toLinearMap :
    Coalgebra.counit (R := R) (A := A ⊗[R] B) =
      ((Algebra.TensorProduct.rid _ _ _).toAlgHom.comp (Algebra.TensorProduct.map
      (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R B))).toLinearMap :=
  rfl

lemma comul_eq_algHom_toLinearMap :
    Coalgebra.comul (R := R) (A := A ⊗[R] B) =
      ((Algebra.TensorProduct.tensorTensorTensorComm R R A A B B).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R A)
      (Bialgebra.comulAlgHom R B))).toLinearMap :=
  rfl

noncomputable instance _root_.TensorProduct.instBialgebra : Bialgebra R (A ⊗[R] B) := by
  have hcounit := congr(DFunLike.coe $(counit_eq_algHom_toLinearMap R A B))
  have hcomul := congr(DFunLike.coe $(comul_eq_algHom_toLinearMap R A B))
  refine Bialgebra.mk' R (A ⊗[R] B) ?_ (fun {x y} => ?_) ?_ (fun {x y} => ?_) <;>
  simp_all only [AlgHom.toLinearMap_apply] <;>
  simp only [map_one, map_mul]

variable {R A B C D}

variable [Semiring C] [Semiring D] [Bialgebra R C] [Bialgebra R D]

/-- The tensor product of two bialgebra morphisms as a bialgebra morphism. -/
noncomputable def map (f : A →ₐc[R] C) (g : B →ₐc[R] D) :
    A ⊗[R] B →ₐc[R] C ⊗[R] D :=
  { Coalgebra.TensorProduct.map (f : A →ₗc[R] C) (g : B →ₗc[R] D),
    Algebra.TensorProduct.map (f : A →ₐ[R] C) (g : B →ₐ[R] D) with }

@[simp]
theorem map_tmul (f : A →ₐc[R] C) (g : B →ₐc[R] D) (x : A) (y : B) :
    map f g (x ⊗ₜ y) = f x ⊗ₜ g y :=
  rfl

@[simp]
theorem map_toCoalgHom (f : A →ₐc[R] C) (g : B →ₐc[R] D) :
    map f g = Coalgebra.TensorProduct.map (f : A →ₗc[R] C) (g : B →ₗc[R] D) := rfl

@[simp]
theorem map_toAlgHom (f : A →ₐc[R] C) (g : B →ₐc[R] D) :
    (map f g : A ⊗[R] B →ₐ[R] C ⊗[R] D) =
      Algebra.TensorProduct.map (f : A →ₐ[R] C) (g : B →ₐ[R] D) :=
  rfl

variable (R A C D) in
/-- The associator for tensor products of R-bialgebras, as a bialgebra equivalence. -/
protected noncomputable def assoc :
    (A ⊗[R] C) ⊗[R] D ≃ₐc[R] A ⊗[R] (C ⊗[R] D) :=
  { Coalgebra.TensorProduct.assoc R A C D, Algebra.TensorProduct.assoc R A C D with }

@[simp]
theorem assoc_tmul (x : A) (y : C) (z : D) :
    Bialgebra.TensorProduct.assoc R A C D ((x ⊗ₜ y) ⊗ₜ z) = x ⊗ₜ (y ⊗ₜ z) :=
  rfl

@[simp]
theorem assoc_symm_tmul (x : A) (y : C) (z : D) :
    (Bialgebra.TensorProduct.assoc R A C D).symm (x ⊗ₜ (y ⊗ₜ z)) = (x ⊗ₜ y) ⊗ₜ z :=
  rfl

@[simp]
theorem assoc_toCoalgEquiv :
    (Bialgebra.TensorProduct.assoc R A C D : _ ≃ₗc[R] _) =
    Coalgebra.TensorProduct.assoc R A C D := rfl

@[simp]
theorem assoc_toAlgEquiv :
    (Bialgebra.TensorProduct.assoc R A C D : _ ≃ₐ[R] _) =
    Algebra.TensorProduct.assoc R A C D := by ext; rfl

variable (R B) in
/-- The base ring is a left identity for the tensor product of bialgebras, up to
bialgebra equivalence. -/
protected noncomputable def lid : R ⊗[R] B ≃ₐc[R] B :=
  { Coalgebra.TensorProduct.lid R B, Algebra.TensorProduct.lid R B with }

@[simp]
theorem lid_toCoalgEquiv :
    (Bialgebra.TensorProduct.lid R B : R ⊗[R] B ≃ₗc[R] B) = Coalgebra.TensorProduct.lid R B := rfl

@[simp]
theorem lid_toAlgEquiv :
    (Bialgebra.TensorProduct.lid R B : R ⊗[R] B ≃ₐ[R] B) = Algebra.TensorProduct.lid R B := rfl

@[simp]
theorem lid_tmul (r : R) (a : B) : Bialgebra.TensorProduct.lid R B (r ⊗ₜ a) = r • a := rfl

@[simp]
theorem lid_symm_apply (a : B) : (Bialgebra.TensorProduct.lid R B).symm a = 1 ⊗ₜ a := rfl

theorem coalgebra_rid_eq_algebra_rid_apply (x : A ⊗[R] R) :
    Coalgebra.TensorProduct.rid R A x = Algebra.TensorProduct.rid R R A x := rfl

variable (R A) in
/-- The base ring is a right identity for the tensor product of bialgebras, up to
bialgebra equivalence. -/
protected noncomputable def rid : A ⊗[R] R ≃ₐc[R] A where
  toCoalgEquiv := Coalgebra.TensorProduct.rid R A
  map_mul' x y := by
    simp only [CoalgEquiv.toCoalgHom_eq_coe, CoalgHom.toLinearMap_eq_coe, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, CoalgHom.coe_toLinearMap, CoalgHom.coe_coe,
      coalgebra_rid_eq_algebra_rid_apply, map_mul]

@[simp]
theorem rid_toCoalgEquiv :
    (TensorProduct.rid R A : A ⊗[R] R ≃ₗc[R] A) = Coalgebra.TensorProduct.rid R A := rfl

@[simp]
theorem rid_toAlgEquiv :
    (Bialgebra.TensorProduct.rid R A : A ⊗[R] R ≃ₐ[R] A) = Algebra.TensorProduct.rid R R A := by
  ext x
  exact coalgebra_rid_eq_algebra_rid_apply x

@[simp]
theorem rid_tmul (r : R) (a : A) : Bialgebra.TensorProduct.rid R A (a ⊗ₜ r) = r • a := rfl

@[simp]
theorem rid_symm_apply (a : A) : (Bialgebra.TensorProduct.rid R A).symm a = a ⊗ₜ 1 := rfl

end Bialgebra.TensorProduct
namespace BialgHom

variable {R A B C : Type*} [CommRing R] [Ring A] [Ring B] [Ring C]
    [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]

variable (A)

/-- `lTensor A f : A ⊗ B →ₐc A ⊗ C` is the natural bialgebra morphism induced by `f : B →ₐc C`. -/
noncomputable abbrev lTensor (f : B →ₐc[R] C) : A ⊗[R] B →ₐc[R] A ⊗[R] C :=
  Bialgebra.TensorProduct.map (BialgHom.id R A) f

/-- `rTensor A f : B ⊗ A →ₐc C ⊗ A` is the natural bialgebra morphism induced by `f : B →ₐc C`. -/
noncomputable abbrev rTensor (f : B →ₐc[R] C) : B ⊗[R] A →ₐc[R] C ⊗[R] A :=
  Bialgebra.TensorProduct.map f (BialgHom.id R A)

end BialgHom
