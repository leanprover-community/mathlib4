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
         |
         μ
|   |   / \
f * g = f g
|   |   \ /
         δ
         |
```
diagrammatically, where `μ` stands for multiplication and `δ` for comultiplication.
-/

public section

suppress_compilation

open Algebra Coalgebra Bialgebra TensorProduct WithConv

variable {R A B C : Type*} [CommSemiring R]

namespace AlgHom
variable [CommSemiring A] [CommSemiring B] [Semiring C] [Bialgebra R C] [Algebra R A]

instance : One (WithConv <| C →ₐ[R] A) where
  one := toConv <| (Algebra.ofId R A).comp <| counitAlgHom R C

instance : Mul (WithConv <| C →ₐ[R] A) where
  mul f g := toConv <| .comp (lmul' R) <| .comp (map f.ofConv g.ofConv) <| comulAlgHom R C

instance : Pow (WithConv <| C →ₐ[R] A) ℕ := ⟨fun f n ↦ npowRec n f⟩

lemma convOne_def : 1 = toConv ((Algebra.ofId R A).comp (counitAlgHom R C)) := rfl

lemma convMul_def (f g : WithConv <| C →ₐ[R] A) :
    f * g = toConv (.comp (lmul' R) <| .comp (map f.ofConv g.ofConv) <| comulAlgHom R C) := rfl

private lemma convPow_succ (f : WithConv <| C →ₐ[R] A) (n : ℕ) : f ^ (n + 1) = (f ^ n) * f := rfl

@[simp]
lemma convOne_apply (c : C) : (1 : WithConv <| C →ₐ[R] A) c = algebraMap R A (counit c) := rfl

lemma convMul_apply (f g : WithConv <| C →ₐ[R] A) (c : C) :
    (f * g) c = lift f.ofConv g.ofConv (fun _ _ ↦ .all ..) (comul c) := by
  simp only [convMul_def, coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply]
  rw [← comp_apply]
  congr 1
  ext <;> simp

@[simp]
lemma toLinearMap_convOne : toConv (1 : WithConv <| C →ₐ[R] A).ofConv.toLinearMap = 1 := rfl

@[simp]
lemma toLinearMap_convMul (f g : WithConv <| C →ₐ[R] A) :
    toConv (f * g).ofConv.toLinearMap = toConv f.ofConv.toLinearMap * toConv g.ofConv.toLinearMap :=
  rfl

@[simp]
lemma toLinearMap_convPow (f : WithConv <| C →ₐ[R] A) :
    ∀ n : ℕ, toConv (f ^ n).ofConv.toLinearMap = toConv f.ofConv.toLinearMap ^ n
  | 0 => rfl
  | n + 1 => by simp only [convPow_succ, toLinearMap_convMul, toLinearMap_convPow, pow_succ]

lemma convMul_comp_bialgHom_distrib [Bialgebra R B] (f g : WithConv <| C →ₐ[R] A) (h : B →ₐc[R] C) :
    AlgHom.comp (f * g).ofConv (h : B →ₐ[R] C) =
      ofConv (toConv (f.ofConv.comp h) * toConv (g.ofConv.comp h)) := by
  simp [convMul_def, comp_assoc, Algebra.TensorProduct.map_comp]

lemma comp_convMul_distrib [Algebra R B] (h : A →ₐ[R] B) (f g : WithConv <| C →ₐ[R] A) :
    h.comp (f * g).ofConv = ofConv (toConv (h.comp f.ofConv) * toConv (h.comp g.ofConv)) := by
  apply toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.comp_toLinearMap, ← ofConv_toConv (f * g).ofConv.toLinearMap, toLinearMap_convMul]
  simp [LinearMap.algHom_comp_convMul_distrib, toLinearMap_convMul]

instance : Monoid (WithConv <| C →ₐ[R] A) := fast_instance%
  (toConv_injective.comp <| toLinearMap_injective.comp ofConv_injective).monoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

variable [IsCocomm R C]

instance : CommMonoid (WithConv <| C →ₐ[R] A) := fast_instance%
  (toConv_injective.comp <| toLinearMap_injective.comp ofConv_injective).commMonoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

end AlgHom

namespace BialgHom
variable [Semiring C] [Bialgebra R C]

section Semiring
variable [Semiring A] [Bialgebra R A]

/-- Pre- and post-composing the convolution by `f` agree on linear maps it intertwines. -/
lemma convCompLeft_eq_convCompRight (f : A →ₐc[R] C) {g : C →ₗ[R] C} {g' : A →ₗ[R] A}
    (hg : g ∘ₗ f.toLinearMap = f.toLinearMap ∘ₗ g') :
    f.toCoalgHom.convCompLeft (toConv g) = f.toAlgHom.convCompRight (toConv g') :=
  WithConv.ext hg

/-- Pre- and post-composing the convolution by `f` agree on the identity. -/
lemma convCompLeft_toConv_id (f : A →ₐc[R] C) :
    f.toCoalgHom.convCompLeft (toConv .id) = f.toAlgHom.convCompRight (toConv .id) :=
  f.convCompLeft_eq_convCompRight (g' := .id) (by simp)

end Semiring

variable [CommSemiring A] [Bialgebra R A]

instance : One (WithConv <| C →ₐc[R] A) where
  one := toConv <| (unitBialgHom R A).comp <| counitBialgHom R C

lemma convOne_def : 1 = toConv ((unitBialgHom R A).comp (counitBialgHom R C)) := rfl

@[simp]
lemma convOne_apply (c : C) : (1 : WithConv <| C →ₐc[R] A) c = algebraMap R A (counit c) := rfl

@[simp]
lemma toLinearMap_convOne :
    toConv (SemilinearMapClass.semilinearMap (1 : WithConv <| C →ₐc[R] A).ofConv) = 1 := rfl

@[simp] lemma toAlgHom_convOne : toConv (1 : WithConv <| C →ₐc[R] A).ofConv.toAlgHom = 1 := rfl

variable [IsCocomm R C]

instance : Mul (WithConv <| C →ₐc[R] A) where
  mul f g := toConv <| .comp (mulBialgHom R A) <| .comp (map f.ofConv g.ofConv) <| comulBialgHom R C

instance : Pow (WithConv <| C →ₐc[R] A) ℕ := ⟨fun f n ↦ npowRec n f⟩

lemma convMul_def (f g : WithConv <| C →ₐc[R] A) :
    f * g =
      toConv (.comp (mulBialgHom R A) <| .comp (map f.ofConv g.ofConv) <| comulBialgHom R C) :=
  rfl

private lemma convPow_succ (f : WithConv <| C →ₐc[R] A) (n : ℕ) : f ^ (n + 1) = (f ^ n) * f := rfl

-- TODO: Make simp once `SemilinearMapClass.semilinearMap` is not simp nf anymore.
-- @[simp]
lemma toLinearMap_convMul (f g : WithConv <| C →ₐc[R] A) :
    toConv (f * g).ofConv.toLinearMap = toConv f.ofConv.toLinearMap * toConv g.ofConv.toLinearMap :=
  rfl

@[simp]
lemma toAlgHom_convMul (f g : WithConv <| C →ₐc[R] A) :
    toConv (f * g).ofConv.toAlgHom = toConv f.ofConv.toAlgHom * toConv g.ofConv.toAlgHom :=
  rfl

-- TODO: Make simp once `SemilinearMapClass.semilinearMap` is not simp nf anymore.
-- @[simp]
lemma toLinearMap_convPow (f : WithConv <| C →ₐc[R] A) :
    ∀ n, toConv (f ^ n).ofConv.toLinearMap = toConv f.ofConv.toLinearMap ^ n
  | 0 => rfl
  | n + 1 => by simp only [convPow_succ, pow_succ, toLinearMap_convMul, toLinearMap_convPow]

@[simp]
lemma toAlgHom_convPow (f : WithConv <| C →ₐc[R] A) :
    ∀ n, toConv (f ^ n).ofConv.toAlgHom = toConv f.ofConv.toAlgHom ^ n
  | 0 => rfl
  | n + 1 => by simp only [convPow_succ, pow_succ, toAlgHom_convMul, toAlgHom_convPow]

instance : CommMonoid (WithConv <| C →ₐc[R] A) := fast_instance%
  (toConv_injective.comp <| coe_linearMap_injective.comp ofConv_injective).commMonoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

end BialgHom
