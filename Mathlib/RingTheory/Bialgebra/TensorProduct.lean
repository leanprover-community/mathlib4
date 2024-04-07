/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor products of bialgebras

To-do: write this.

-/

universe v u

section
open scoped TensorProduct

namespace Bialgebra.TensorProduct
variable {R A B : Type u} [CommRing R] [Ring A] [Ring B]
    [Bialgebra R A] [Bialgebra R B]

lemma coe_counit_eq :
    ⇑(Coalgebra.counit (R := R) (A := A ⊗[R] B))
      = (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map
      (Bialgebra.counitAlgHom R A) (Bialgebra.counitAlgHom R B)) := by
  rfl

lemma coe_comul_eq :
    ⇑(Coalgebra.comul (R := R) (A := A ⊗[R] B))
      = (Algebra.TensorProduct.tensorTensorTensorComm R A A B B).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom R A)
      (Bialgebra.comulAlgHom R B)) := by
  rfl

end Bialgebra.TensorProduct

noncomputable instance TensorProduct.instBialgebra
    {R A B : Type u} [CommRing R] [Ring A] [Ring B]
    [Bialgebra R A] [Bialgebra R B] : Bialgebra R (A ⊗[R] B) := by
  refine' Bialgebra.mk' R (A ⊗[R] B) _ (fun {x y} => _) _ (fun {x y} => _)
  <;> simp only [Bialgebra.TensorProduct.coe_counit_eq, Bialgebra.TensorProduct.coe_comul_eq]
  <;> simp only [_root_.map_one, _root_.map_mul]

namespace Bialgebra.TensorProduct

variable {R A B C D : Type u} [CommRing R] [Ring A] [Ring B] [Ring C] [Ring D]
    [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]

/-- The tensor product of two bialgebra morphisms as a bialgebra morphism. -/
noncomputable def map (f : A →ₐc[R] B) (g : C →ₐc[R] D) :
    A ⊗[R] C →ₐc[R] B ⊗[R] D :=
  { Coalgebra.TensorProduct.map (f : A →ₗc[R] B) (g : C →ₗc[R] D),
    Algebra.TensorProduct.map (f : A →ₐ[R] B) (g : C →ₐ[R] D) with }

@[simp]
theorem map_tmul (f : A →ₐc[R] B) (g : C →ₐc[R] D) (x : A) (y : C) :
    map f g (x ⊗ₜ y) = f x ⊗ₜ g y :=
  rfl

@[simp]
theorem map_toCoalgHom (f : A →ₐc[R] B) (g : C →ₐc[R] D) :
    map f g = Coalgebra.TensorProduct.map (f : A →ₗc[R] B) (g : C →ₗc[R] D) := rfl

variable (R A B C)

/-- The associator for tensor products of R-bialgebras, as a bialgebra equivalence. -/
protected noncomputable def assoc :
    (A ⊗[R] B) ⊗[R] C ≃ₐc[R] A ⊗[R] (B ⊗[R] C) :=
  { Coalgebra.TensorProduct.assoc R A B C, Algebra.TensorProduct.assoc R A B C with }

variable {R A B C}

@[simp]
theorem assoc_tmul (x : A) (y : B) (z : C) :
    Bialgebra.TensorProduct.assoc R A B C ((x ⊗ₜ y) ⊗ₜ z) = x ⊗ₜ (y ⊗ₜ z) :=
  rfl

@[simp]
theorem assoc_symm_tmul (x : A) (y : B) (z : C) :
    (Coalgebra.TensorProduct.assoc R A B C).symm (x ⊗ₜ (y ⊗ₜ z)) = (x ⊗ₜ y) ⊗ₜ z :=
  rfl

@[simp]
theorem assoc_toCoalgEquiv :
    (Bialgebra.TensorProduct.assoc R A B C : _ ≃ₗc[R] _)
      = Coalgebra.TensorProduct.assoc R A B C := rfl

variable (R A)

/-- The base ring is a left identity for the tensor product of bialgebras, up to
bialgebra equivalence. -/
protected noncomputable def lid : R ⊗[R] A ≃ₐc[R] A :=
  { Coalgebra.TensorProduct.lid R A, Algebra.TensorProduct.lid R A with }

variable {R A}

@[simp]
theorem lid_toCoalgEquiv :
    (Bialgebra.TensorProduct.lid R A : R ⊗[R] A ≃ₗc[R] A) = Coalgebra.TensorProduct.lid R A := rfl

@[simp]
theorem lid_tmul (r : R) (a : A) : Bialgebra.TensorProduct.lid R A (r ⊗ₜ a) = r • a := rfl

@[simp]
theorem lid_symm_apply (a : A) : (Bialgebra.TensorProduct.lid R A).symm a = 1 ⊗ₜ a := rfl

-- could deal with this better
theorem coalgebraRid_eq_algebraRid_apply (x) :
    Coalgebra.TensorProduct.rid R A x = Algebra.TensorProduct.rid R R A x := by
  show _root_.TensorProduct.rid R A x = _
  rw [← TensorProduct.AlgebraTensorModule.rid_eq_rid]
  rfl

variable (R A)

/-- The base ring is a right identity for the tensor product of bialgebras, up to
bialgebra equivalence. -/
protected noncomputable def rid : A ⊗[R] R ≃ₐc[R] A :=
  { Coalgebra.TensorProduct.rid R A with
    map_mul' := fun x y => by
      simp only [CoalgEquiv.toCoalgHom_eq_coe, CoalgHom.toLinearMap_eq_coe, AddHom.toFun_eq_coe,
        LinearMap.coe_toAddHom, CoalgHom.coe_toLinearMap, CoalgHom.coe_coe,
        coalgebraRid_eq_algebraRid_apply, AlgEquiv.map_mul] }

variable {R A}

@[simp]
theorem rid_toCoalgEquiv :
    (Bialgebra.TensorProduct.rid R A : A ⊗[R] R ≃ₗc[R] A) = Coalgebra.TensorProduct.rid R A := rfl

@[simp]
theorem rid_tmul (r : R) (a : A) : Bialgebra.TensorProduct.rid R A (a ⊗ₜ r) = r • a := rfl

@[simp]
theorem rid_symm_apply (a : A) : (Bialgebra.TensorProduct.rid R A).symm a = a ⊗ₜ 1 := rfl

end Bialgebra.TensorProduct
namespace BialgHom

variable {R A B C D : Type u} [CommRing R] [Ring A] [Ring B] [Ring C] [Ring D]
    [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]

variable (A)

/-- `lTensor A f : A ⊗ B →ₐc A ⊗ C` is the natural bialgebra morphism induced by `f : B →ₐc C`. -/
noncomputable abbrev lTensor (f : B →ₐc[R] C) : A ⊗[R] B →ₐc[R] A ⊗[R] C :=
  Bialgebra.TensorProduct.map (BialgHom.id R A) f

/-- `rTensor A f : B ⊗ A →ₐc C ⊗ A` is the natural bialgebra morphism induced by `f : B →ₐc C`. -/
noncomputable abbrev rTensor (f : B →ₐc[R] C) : B ⊗[R] A →ₐc[R] C ⊗[R] A :=
  Bialgebra.TensorProduct.map f (BialgHom.id R A)

end BialgHom
