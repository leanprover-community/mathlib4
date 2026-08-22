/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.NumberTheory.Padics.Measure.Basic

/-!
# Distributions on a topological monoid

We show that if `G` is a monoid, then `D(G, R)` inherits a convolution product from `G`.
-/

public noncomputable section

variable {G R : Type*} [TopologicalSpace G]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

attribute [local ext] DFunLike.ext -- why is this not set by default?

namespace AbstractMeasure

section Monoid

variable [Monoid G] [ContinuousMul G]

/-!
### Convolution of a measure and a function

When `G` has a continuous multiplication law, we can define convolution of a measure with a
function.
-/

/--
For `μ` a measure and `f` a function, return the convolution of `f` with `μ` acting on the right,
i.e. the function `fun x ↦ ∫ y, f (x * y) dμ` (bundled as a continuous map).
-/
def convolveFunRight : D(G, R) →ₗ[R] C(G, R) →ₗ[R] C(G, R) :=
  ((ContinuousMap.compCLM R R ⟨_, continuous_mul⟩).toLinearMap.lcomp _ _).comp contractSnd

lemma convolveFunRight_apply (μ : D(G, R)) (f : C(G, R)) (x : G) :
    μ.convolveFunRight f x = μ ⟨fun y ↦ f (x * y), by continuity⟩ := by
  simp [convolveFunRight, ContinuousMap.compCLM_apply]

@[simp]
lemma convolveFunRight_dirac_apply (x : G) (f : C(G, R)) (y : G) :
    convolveFunRight (dirac R x) f y = f (y * x) := by
  simp [convolveFunRight_apply]

lemma convolveFunRight_apply_one (μ : D(G, R)) (f : C(G, R)) :
    convolveFunRight μ f 1 = μ f := by
  simp only [convolveFunRight_apply, one_mul]
  rfl

/--
We define `1 : D(G, R)` to be the Dirac measure at `1 : G` (since we are writing convolution as
multiplication).
-/
instance : One D(G, R) where one := dirac R 1

omit [ContinuousMul G] in
@[simp] lemma one_apply (f : C(G, R)) : (1 : D(G, R)) f = f 1 := by
  simp [show (1 : D(G, R)) = dirac R 1 by rfl]

@[simp] lemma convolveFunRight_one (f : C(G, R)) : convolveFunRight 1 f = f := by
  ext
  simp [convolveFunRight_apply]

section LocallyCompact

variable [LocallyCompactSpace G]

/-!
### Convolution of two measures
-/

instance : NonUnitalNonAssocRing D(G, R) where
  mul μ ν := map ⟨fun p : G × G ↦ p.1 * p.2, continuous_mul⟩ (μ.prodMk' ν)
  zero_mul ν := show map _ _ = 0 by simp
  mul_zero μ := show map _ _ = 0 by simp
  right_distrib μ ν ν' := show map _ _ = map _ _ + map _ _ by simp
  left_distrib μ ν ν' := show map _ _ = map _ _ + map _ _ by simp

lemma mul_apply (μ ν : D(G, R)) (f : C(G, R)) : (μ * ν) f = μ (convolveFunRight ν f) := by
  change (map _ _) f = _
  simp only [map_apply, prodMk'_apply]
  rfl

/-- Convolution of Dirac measures corresponds to addition in the group. -/
lemma dirac_mul_dirac (x y : G) : dirac R x * dirac R y = dirac R (x * y) :=  by
  ext f
  simp only [mul_apply, dirac_apply, convolveFunRight_apply, ContinuousMap.coe_mk]

lemma convolveFunRight_mul (μ ν : D(G, R)) (f : C(G, R)) :
    convolveFunRight (μ * ν) f = convolveFunRight μ (convolveFunRight ν f) := by
  ext
  simp only [convolveFunRight_apply, mul_apply]
  congr 1 with h
  simp [mul_assoc, convolveFunRight_apply]

instance : Ring D(G, R) where
  mul_assoc _ _ _ := by ext; simp [mul_apply, convolveFunRight_mul]
  one_mul _ := by ext; simp [mul_apply, convolveFunRight_apply_one]
  mul_one _ := by ext; simp [mul_apply]

/-- The canonical map `G → D(G, R)`, packaged as a multiplicative homomorphism. -/
@[expose] def diracHom : G →* D(G, R) where
  toFun := dirac R
  map_one' := by ext; simp
  map_mul' g h := by ext f; simp [dirac_mul_dirac]

/-- Measures form a `R`-algebra. -/
noncomputable instance : Algebra R D(G, R) := Algebra.ofModule
  (by intro r μ ν; ext; simp [mul_apply]) (by intro r μ ν; ext; simp [mul_apply])

/-- The canonical hom from the monoid algebra `R[G]` to `D(G, R)`. -/
def monoidAlgebraHom : MonoidAlgebra R G →ₐ[R] D(G, R) :=
  MonoidAlgebra.lift R _ G diracHom

@[simp] lemma monoidAlgebraHom_single (g : G) :
    monoidAlgebraHom (.single g 1) = dirac R g := by
  simp [monoidAlgebraHom, diracHom]

instance : Module D(G, R) C(G, R) where
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

end LocallyCompact

end Monoid

section CommMonoid

variable [CommMonoid G] [ContinuousMul G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [T0Space R]

noncomputable instance : CommRing D(G, R) where
  mul_comm μ ν := by
    ext
    simp [mul_apply, convolveFunRight, ContinuousMap.comp, Function.comp_def,
      ← prodMk'_apply, prodMk'_flip μ ν, prodMk_eq_prodMk', mul_comm]

end CommMonoid

end AbstractMeasure

end
