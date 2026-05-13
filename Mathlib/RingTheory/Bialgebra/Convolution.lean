/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Convolution product on bialgebra homs

This file constructs the ring structure on algebra homs `C → A` where `C` is a bialgebra and `A` an
algebra, and also the ring structure on bialgebra homs `C → A` where `C` and `A` are bialgebras.
Both multiplications are given by
```
         .
        / \
f * g = f g
        \ /
         .
```
-/

public section

suppress_compilation

open Algebra Coalgebra Bialgebra TensorProduct WithConv

variable {R A B C : Type*} [CommSemiring R]

namespace AlgHom
variable [CommSemiring A] [CommSemiring B] [Semiring C] [Bialgebra R C] [Algebra R A]

instance : One (C →ₐ[R] A) where one := (Algebra.ofId R A).comp <| counitAlgHom R C
instance : Mul (C →ₐ[R] A) where
  mul f g := .comp (lmul' R) <| .comp (Algebra.TensorProduct.map f g) <| comulAlgHom R C

instance : Pow (C →ₐ[R] A) ℕ := ⟨fun f n ↦ npowRec n f⟩

lemma convOne_def : (1 : C →ₐ[R] A) = (Algebra.ofId R A).comp (counitAlgHom ..) := rfl
lemma convMul_def (f g : C →ₐ[R] A) :
    f * g = (.comp (lmul' R) <| .comp (Algebra.TensorProduct.map f g) <| comulAlgHom R C) := rfl

private lemma convPow_succ (f : C →ₐ[R] A) (n : ℕ) : f ^ (n + 1) = (f ^ n) * f := rfl

lemma convOne_apply (c : C) : (1 : C →ₐ[R] A) c = algebraMap R A (counit c) := rfl

lemma convMul_apply (f g : C →ₐ[R] A) (c : C) :
    (f * g) c = Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _) (comul c) := by
  simp only [convMul_def, coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply]
  rw [← comp_apply]
  congr 1
  ext <;> simp

lemma toLinearMap_convOne : toConv (1 : C →ₐ[R] A).toLinearMap = 1 := rfl
lemma toLinearMap_convMul (f g : C →ₐ[R] A) :
    toConv (f * g).toLinearMap = toConv f.toLinearMap * toConv g.toLinearMap := rfl

lemma toLinearMap_convPow (f : C →ₐ[R] A) :
    ∀ n : ℕ, toConv (f ^ n).toLinearMap = toConv f.toLinearMap ^ n
  | 0 => rfl
  | n + 1 => by simp only [convPow_succ, toLinearMap_convMul, toLinearMap_convPow, pow_succ]

lemma convMul_distrib_comp [Bialgebra R B] (f g : C →ₐ A) (h : B →ₐc[R] C) :
    AlgHom.comp (f * g) (h : B →ₐ[R] C) = (.comp f h) * (.comp g h) := calc
  _ = (.comp (lmul' R) <| .comp (Algebra.TensorProduct.map f g) <|
      .comp (Algebra.TensorProduct.map (h : B →ₐ[R] C) (h : B →ₐ[R] C)) (comulAlgHom R B)) := by
    simp [convMul_def, comp_assoc]
  _ = (.comp (lmul' R) <|
      .comp (Algebra.TensorProduct.map (.comp f h) (.comp g h)) (comulAlgHom R B)) := by
    rw [Algebra.TensorProduct.map_comp]
    simp [comp_assoc]
  _ = _ := by simp [convMul_def]

lemma comp_convMul_distrib [Algebra R B] (f g : C →ₐ[R] A) (h : A →ₐ[R] B) :
    h.comp (f * g) = h.comp f * h.comp g := by
  apply toLinearMap_injective
  apply WithConv.toConv_injective
  simp only [AlgHom.comp_toLinearMap]
  rw [show (f * g).toLinearMap = (toConv f.toLinearMap * toConv g.toLinearMap).ofConv from
        congr_arg WithConv.ofConv (toLinearMap_convMul f g),
      LinearMap.algHom_comp_convMul_distrib]
  simp only [WithConv.toConv_ofConv]
  rw [toLinearMap_convMul (h.comp f) (h.comp g)]
  simp [AlgHom.comp_toLinearMap]

instance : Monoid (C →ₐ[R] A) :=
  (toConv_injective.comp toLinearMap_injective).monoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

variable [IsCocomm R C]

instance : CommMonoid (C →ₐ[R] A) :=
  (toConv_injective.comp toLinearMap_injective).commMonoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

end AlgHom

namespace BialgHom
variable [CommSemiring A] [CommSemiring C] [Bialgebra R A] [Bialgebra R C]

instance : One (C →ₐc[R] A) where one := (unitBialgHom R A).comp <| counitBialgHom R C

lemma convOne_def : (1 : C →ₐc[R] A) = (unitBialgHom R A).comp (counitBialgHom ..) := rfl

@[simp] lemma convOne_apply (c : C) : (1 : C →ₐc[R] A) c = algebraMap R A (counit c) := rfl

lemma toLinearMap_convOne : toConv (1 : C →ₐc[R] A).toLinearMap = 1 := rfl

variable [IsCocomm R C]

instance : Mul (C →ₐc[R] A) where
  mul f g := .comp (mulBialgHom R A) <| .comp (Bialgebra.TensorProduct.map f g) <| comulBialgHom R C

instance : Pow (C →ₐc[R] A) ℕ := ⟨fun f n ↦ npowRec n f⟩

lemma convMul_def (f g : C →ₐc[R] A) :
    f * g =
      (.comp (mulBialgHom R A) <| .comp (Bialgebra.TensorProduct.map f g) <| comulBialgHom R C) :=
  rfl

private lemma convPow_succ (f : C →ₐc[R] A) (n : ℕ) : f ^ (n + 1) = (f ^ n) * f := rfl

lemma toLinearMap_convMul (f g : C →ₐc[R] A) :
    toConv (f * g).toLinearMap = toConv f.toLinearMap * toConv g.toLinearMap := rfl

lemma toLinearMap_convPow (f : C →ₐc[R] A) :
    ∀ n, toConv (f ^ n).toLinearMap = toConv f.toLinearMap ^ n
  | 0 => rfl
  | n + 1 => by simp only [convPow_succ, pow_succ, toLinearMap_convMul, toLinearMap_convPow]

instance : CommMonoid (C →ₐc[R] A) :=
  (toConv_injective.comp coe_linearMap_injective).commMonoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

end BialgHom
