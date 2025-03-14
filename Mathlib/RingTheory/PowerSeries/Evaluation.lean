/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.PiTopology

/-! # Evaluation of power series

Power series in one indeterminate are the particular case of multivariate power series,
for the `Unit` type of indeterminates.
This file provides a simpler syntax.

Let `R` `S` be types, with `CommRing R`, `CommRing
One assumes that `TopologicalRing R` and `UniformAddGroup R`,
and that `S` is a complete and separated topological `R`-algebra,
with `LinearTopology R`, which means there is a basis of ighborhoods of 0
consisting of ideals.

Given `φ : R →+* S`, `a : S`, and `f : MvPowerSeries σ R`,
`MvPowerSeries.eval₂ f φ a` is the evaluation of the power series `f` at `a`.
It `f` is (the coercion of) a polynomial, it coincides with the evaluation of that polynomial.
Otherwise, it is defined by density from polynomials;
its values are irrelevant unless `φ` is continuous and `a` satisfies the condition
bundled in `PowerSeries.HasEval a` :
  - `a` is topologically nilpotent (`a ^ n` tends to 0 when `n` tends to infinity)

Under `Continuous φ` and `PowerSeries.HasEval a`,
the following lemmas furnish the properties of evaluation:

* `PowerSeries.eval₂Hom`: the evaluation of multivariate power series, as a ring morphism,
* `PowerSeries.aeval`: the evaluation map as an algebra map
* `PowerSeries.uniformContinuous_eval₂`: uniform continuity of the evaluation
* `PowerSeries.continuous_eval₂`: continuity of the evaluation
* `PowerSeries.eval₂_eq_tsum`:  the evaluation is given by the sum of its monomials, evaluated.

We refer to the documentation of `MvPowerSeries.eval₂` for more details.

-/
namespace PowerSeries

open WithPiTopology


variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S]

section

variable [TopologicalSpace R] [TopologicalSpace S]

theorem hasEval_iff {a : S} :
    MvPowerSeries.HasEval (Function.const Unit a) ↔ IsTopologicallyNilpotent a :=
  ⟨fun ha ↦ ha.hpow default, fun ha ↦ ⟨fun _ ↦ ha, by simp⟩⟩

theorem hasEval {a : S} (ha : IsTopologicallyNilpotent a) :
    MvPowerSeries.HasEval (Function.const Unit a) := hasEval_iff.mpr ha

theorem isTopologicallyNilpotent_X :
    IsTopologicallyNilpotent (PowerSeries.X : PowerSeries R) :=
  tendsto_pow_zero_of_constantCoeff_zero (MvPowerSeries.constantCoeff_X _)

end

variable (φ : R →+* S) (a : S)

variable [UniformSpace R] [UniformSpace S]

/-- Evaluation of a power series `f` at a point `a`.

It coincides with the evaluation of `f` as a polynomial if `f` is the coercion of a polynomial.
Otherwise, it is only relevant if `φ` is continuous and `a` is topologically nilpotent. -/
noncomputable def eval₂ : PowerSeries R → S :=
  MvPowerSeries.eval₂ φ (fun _ ↦ a)

noncomputable example : Polynomial R →ₐ[R] MvPolynomial Unit R :=
  Polynomial.aeval (MvPolynomial.X default)

noncomputable example : MvPolynomial Unit R →ₐ[R] Polynomial R :=
  MvPolynomial.aeval (Function.const _ Polynomial.X)

noncomputable example : Polynomial R ≃ₐ[R] MvPolynomial Unit R := {
  Polynomial.aeval (MvPolynomial.X default)  with
  invFun := (MvPolynomial.aeval (Function.const _ Polynomial.X)).toFun
  left_inv f := by
    rw [← AlgHom.comp_apply]
    conv_rhs => rw [← AlgHom.id_apply (R := Polynomial R) f]
    revert f
    rw [← AlgHom.ext_iff]
    apply congr_arg
    rw [Polynomial.eval_unique]
    sorry
  right_inv f := by
    dsimp
    rw [MvPolynomial.aeval_unique]
    sorry
  }

noncomputable example : MvPolynomial Unit R →ₐ[R] Polynomial R :=
  MvPolynomial.aeval (Function.const _ Polynomial.X)



theorem eval₂_coe (f : Polynomial R) : PowerSeries.eval₂ φ a f = f.eval₂ φ a := by
  have : ∃ p : MvPolynomial Unit R, (p : MvPowerSeries Unit R) = f := by sorry
  obtain ⟨p, hp⟩ := this
  rw [PowerSeries.eval₂, ← hp, MvPowerSeries.eval₂_coe]

  have := MvPowerSeries.eval₂_coe φ (Function.const Unit a)
  sorry

variable {a}

variable [UniformSpace R] [UniformAddGroup R] [IsTopologicalSemiring R]
    [UniformSpace S] [UniformAddGroup S] [T2Space S] [CompleteSpace S]
    [IsTopologicalRing S] [IsLinearTopology S S]

/-- The evaluation homomorphism at `a` on `PowerSeries`, as a `RingHom`. -/
noncomputable def eval₂Hom (hφ : Continuous φ) (ha : IsTopologicallyNilpotent a) :
    PowerSeries R →+* S :=
  MvPowerSeries.eval₂Hom hφ (hasEval ha)

variable [Algebra R S] [ContinuousSMul R S]

/-- For `HasEval a`, the evaluation homomorphism at `a` on `PowerSeries`, as an `AlgHom`. -/
noncomputable def aeval (ha : IsTopologicallyNilpotent a) :
    PowerSeries R →ₐ[R] S :=
  MvPowerSeries.aeval (hasEval ha)

end PowerSeries
