/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Quadratic algebras are stable under base change

Let `R → S` be a base change. We show that `QuadraticAlgebra S (algebraMap R S a)
(algebraMap R S b)` is the base change of `QuadraticAlgebra R a b` along it, that is, that the
square
```
          R             →               S
          ↓                             ↓
QuadraticAlgebra R a b  →  QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)
```
is a pushout.

## Main results

* `QuadraticAlgebra.isPushout`: the base change square is a pushout.

* `QuadraticAlgebra.baseChangeEquiv`: the resulting isomorphism
  `S ⊗[R] QuadraticAlgebra R a b ≃ₐ[S] QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)`

## Implementation notes

`QuadraticAlgebra.algebra` is activated as a local instance throughout this file.
-/

@[expose] public section

namespace QuadraticAlgebra

open TensorProduct

variable {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] (a b : R)

attribute [local instance] QuadraticAlgebra.algebra

@[simp]
theorem algebraMap_eq_mapRingHom :
    algebraMap (QuadraticAlgebra R a b)
        (QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) =
      mapRingHom (algebraMap R S) a b :=
  rfl

instance :
    IsScalarTower R (QuadraticAlgebra R a b)
      (QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ QuadraticAlgebra.ext rfl (map_zero _).symm

/-- A quadratic algebra is stable under base change. -/
instance isPushout :
    Algebra.IsPushout R S (QuadraticAlgebra R a b)
      (QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) := by
  refine ⟨IsBaseChange.of_lift_unique _ fun Q _ _ _ _ g ↦ ?_⟩
  refine ⟨(basis _ _).constr S ![g 1, g ω], ?_, fun k hk ↦ ?_⟩
  · ext x
    rw [← re_smul_add_im_smul x]
    simp
  · ext x
    rw [← re_smul_add_im_smul x]
    simp [← LinearMap.congr_fun hk]

/-- The base change of `QuadraticAlgebra R a b` along `R → S`, as an algebra isomorphism. -/
noncomputable def baseChangeEquiv :
    S ⊗[R] QuadraticAlgebra R a b ≃ₐ[S]
      QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b) :=
  Algebra.IsPushout.equiv R S _ _

@[simp]
theorem baseChangeEquiv_tmul (s : S) (x : QuadraticAlgebra R a b) :
    baseChangeEquiv S a b (s ⊗ₜ x) = s • mapRingHom (algebraMap R S) a b x := by
  rw [baseChangeEquiv, Algebra.IsPushout.equiv_tmul, Algebra.smul_def]
  simp

end QuadraticAlgebra
