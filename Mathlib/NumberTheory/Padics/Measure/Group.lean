/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.Padics.Measure.Basic

/-!
# Distributions on a topological monoid

We show that if `G` is a monoid, then `D(G, R)` inherits a convolution product from `G`.
-/

public section

variable {G : Type*} [TopologicalSpace G] {R : Type*} [NormedCommRing R]

attribute [local ext] DFunLike.ext -- why is this not set by default?

namespace AbstractMeasure

section Mul

variable [Mul G] [ContinuousMul G]

/-!
### Convolution of a measure and a function

When `G` has a continuous multiplication law, we can define convolution of a measure with a
function.
-/

/--
For `μ` a measure and `f` a function, return the convolution of `f` with `μ` acting on the right,
i.e. the function `fun x ↦ ∫ y, f (x * y) dμ` (bundled as a continuous map).
-/
@[expose] noncomputable def convolveFunRight : D(G, R) →ₗ[R] C(G, R) →ₗ[R] C(G, R) :=
  ((ContinuousMap.comapCLM R ⟨_, continuous_mul⟩).toLinearMap.lcomp _ _).comp contractSnd

lemma convolveFunRight_apply (μ : D(G, R)) (f : C(G, R)) (x : G) :
    μ.convolveFunRight f x = μ ⟨fun y ↦ f (x * y), by continuity⟩ := by
  simp [convolveFunRight, ContinuousMap.comapCLM_apply]

@[simp]
lemma convolveFunRight_dirac_apply (x : G) (f : C(G, R)) (y : G) :
    convolveFunRight (dirac R x) f y = f (y * x) := by
  simp [convolveFunRight_apply]

section LocallyCompact

variable [LocallyCompactSpace G]

/-!
### Convolution of two measures
-/

noncomputable instance : NonUnitalNonAssocRing D(G, R) where
  mul μ ν := map ⟨fun p : G × G ↦ p.1 * p.2, continuous_mul⟩ (μ.prodMk' ν)
  zero_mul ν := show map _ _ = 0 by simp
  mul_zero μ := show map _ _ = 0 by simp
  right_distrib μ ν ν' := show map _ _ = map _ _ + map _ _ by simp
  left_distrib μ ν ν' := show map _ _ = map _ _ + map _ _ by simp

lemma mul_apply (μ ν : D(G, R)) (f : C(G, R)) : (μ * ν) f = μ (convolveFunRight ν f) := by
  change (map _ _) f = _
  simp only [map_apply, prodMk'_apply]
  congr 1 with x
  simp [convolveFunRight_apply]

-- The next two instances are the best approximation to "D(G, R) is an R-algebra" that we can
-- formulate without requiring associativity.

instance : SMulCommClass R D(G, R) D(G, R) where smul_comm _ _ _ := by ext; simp [mul_apply]

instance : IsScalarTower R D(G, R) D(G, R) where smul_assoc _ _ _ := by ext; simp [mul_apply]

/-- Convolution of Dirac measures corresponds to addition in the group. -/
lemma dirac_mul_dirac (x y : G) : dirac R x * dirac R y = dirac R (x * y) :=  by
  ext f
  simp only [mul_apply, dirac_apply, convolveFunRight_apply, ContinuousMap.coe_mk]

end LocallyCompact

end Mul

section Semigroup

variable [Semigroup G] [ContinuousMul G] [LocallyCompactSpace G]

lemma convolveFunRight_mul (μ ν : D(G, R)) (f : C(G, R)) :
    convolveFunRight (μ * ν) f = convolveFunRight μ (convolveFunRight ν f) := by
  ext
  simp only [convolveFunRight_apply, mul_apply]
  congr 1 with h
  simp [mul_assoc, convolveFunRight_apply]

noncomputable instance : NonUnitalRing D(G, R) where
  mul_assoc _ _ _ := by ext; simp [mul_apply, convolveFunRight_mul]

end Semigroup

section One

variable [One G]

/--
When `G` has an identity element, we define `1` to be the Dirac measure at 1 (since we are writing
convolution as multiplication).
-/
instance : AddMonoidWithOne D(G, R) where one := dirac R 1

@[simp] lemma one_apply (f : C(G, R)) : (1 : D(G, R)) f = f 1 := by
  simp [show (1 : D(G, R)) = dirac R 1 by rfl]

end One

section MulOneClass

variable [MulOneClass G] [ContinuousMul G]

lemma convolveFunRight_apply_one (μ : D(G, R)) (f : C(G, R)) :
    convolveFunRight μ f 1 = μ f := by
  simp only [convolveFunRight_apply, one_mul]
  rfl

@[simp] lemma convolveFunRight_one (f : C(G, R)) : convolveFunRight 1 f = f := by
  ext
  simp [convolveFunRight_apply]

variable [LocallyCompactSpace G]

noncomputable instance : NonAssocRing D(G, R) where
  one_mul _ := by ext; simp [mul_apply, convolveFunRight_apply_one]
  mul_one _ := by ext; simp [mul_apply]

end MulOneClass

/-!
## Ring structure

When `G` is a monoid (associative with 1), then we obtain a `R`-algebra structure on measures.
-/

section Monoid

variable [Monoid G] [ContinuousMul G] [LocallyCompactSpace G]

noncomputable instance : Ring D(G, R) where

/-- Measures form a `R`-algebra. -/
noncomputable instance : Algebra R D(G, R) := Algebra.ofModule smul_mul_assoc mul_smul_comm

noncomputable instance : Module D(G, R) C(G, R) where
  smul μ := μ.convolveFunRight
  one_smul := convolveFunRight_one
  smul_zero μ := map_zero _
  zero_smul f := show convolveFunRight 0 f = 0 by simp
  smul_add μ := map_add _
  add_smul μ ν f := by
    change convolveFunRight _ _ = convolveFunRight _ _ + convolveFunRight _ _
    simp only [map_add, LinearMap.add_apply]
  mul_smul μ ν f := by
    change convolveFunRight _ _ = convolveFunRight _ (convolveFunRight _ _)
    ext g
    simp only [convolveFunRight_apply, mul_apply]
    congr 1 with h
    simp only [convolveFunRight_apply, ContinuousMap.coe_mk, mul_assoc]

end Monoid

section Commutative

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

noncomputable instance [CommMagma G] [ContinuousMul G] : NonUnitalNonAssocCommRing D(G, R) where
  mul_comm μ ν := by
    ext
    simp [mul_apply, convolveFunRight, ContinuousMap.comp, Function.comp_def,
      ← prodMk'_apply, prodMk'_flip μ ν, prodMk_eq_prodMk', mul_comm]

noncomputable instance [CommSemigroup G] [ContinuousMul G] : NonUnitalCommRing D(G, R) where

noncomputable instance [CommMonoid G] [ContinuousMul G] : CommRing D(G, R) where

end Commutative

end AbstractMeasure

end
