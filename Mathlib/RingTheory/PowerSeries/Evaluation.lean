/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.RingTheory.MvPowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Evaluation of power series

Power series in one indeterminate are the particular case of multivariate power series,
for the `Unit` type of indeterminates.
This file provides a simpler syntax.

Let `R`, `S` be types, with `CommRing R`, `CommRing S`.
One assumes that `IsTopologicalRing R` and `IsUniformAddGroup R`,
and that `S` is a complete and separated topological `R`-algebra,
with `IsLinearTopology S S`, which means there is a basis of neighborhoods of 0
consisting of ideals.

Given `φ : R →+* S`, `a : S`, and `f : MvPowerSeries σ R`,
`PowerSeries.eval₂ f φ a` is the evaluation of the power series `f` at `a`.
It `f` is (the coercion of) a polynomial, it coincides with the evaluation of that polynomial.
Otherwise, it is defined by density from polynomials;
its values are irrelevant unless `φ` is continuous and `a` is topologically
nilpotent (`a ^ n` tends to 0 when `n` tends to infinity).

Under `Continuous φ` and `IsTopologicallyNilpotent a`,
the following lemmas furnish the properties of evaluation:

* `PowerSeries.eval₂Hom`: the evaluation of multivariate power series, as a ring morphism,
* `PowerSeries.aeval`: the evaluation map as an algebra morphism
* `PowerSeries.uniformContinuous_eval₂`: uniform continuity of the evaluation
* `PowerSeries.continuous_eval₂`: continuity of the evaluation
* `PowerSeries.eval₂_eq_tsum`: the evaluation is given by the sum of its monomials, evaluated.

We refer to the documentation of `MvPowerSeries.eval₂` for more details.

-/
namespace PowerSeries

open WithPiTopology

variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S]

section

variable [TopologicalSpace R] [TopologicalSpace S]

theorem hasEval_iff {a : S} :
    MvPowerSeries.HasEval (fun (_ : Unit) ↦ a) ↔ IsTopologicallyNilpotent a :=
  ⟨fun ha ↦ ha.hpow default, fun ha ↦ ⟨fun _ ↦ ha, by simp⟩⟩

theorem hasEval {a : S} (ha : IsTopologicallyNilpotent a) :
    MvPowerSeries.HasEval (fun (_ : Unit) ↦ a) := hasEval_iff.mpr ha

theorem isTopologicallyNilpotent_X :
    IsTopologicallyNilpotent (PowerSeries.X : PowerSeries R) :=
  tendsto_pow_zero_of_constantCoeff_zero PowerSeries.constantCoeff_X

end

variable (φ : R →+* S) (a : S)

variable [UniformSpace R] [UniformSpace S]

/-- Evaluation of a power series `f` at a point `a`.

It coincides with the evaluation of `f` as a polynomial if `f` is the coercion of a polynomial.
Otherwise, it is only relevant if `φ` is continuous and `a` is topologically nilpotent. -/
noncomputable def eval₂ : PowerSeries R → S :=
  MvPowerSeries.eval₂ φ (fun _ ↦ a)

@[simp]
theorem eval₂_coe (f : Polynomial R) : eval₂ φ a f = f.eval₂ φ a := by
  let g : MvPolynomial Unit R := (MvPolynomial.pUnitAlgEquiv R).symm f
  have : f = MvPolynomial.pUnitAlgEquiv R g := by
    simp only [g, ← AlgEquiv.symm_apply_eq]
  simp only [this, PowerSeries.eval₂, MvPolynomial.eval₂_const_pUnitAlgEquiv]
  rw [← MvPolynomial.toMvPowerSeries_pUnitAlgEquiv, MvPowerSeries.eval₂_coe]

@[simp]
theorem eval₂_C (r : R) :
    eval₂ φ a (C R r) = φ r := by
  rw [← Polynomial.coe_C, eval₂_coe, Polynomial.eval₂_C]

@[simp]
theorem eval₂_X :
    eval₂ φ a X = a := by
  rw [← Polynomial.coe_X, eval₂_coe, Polynomial.eval₂_X]

variable {φ a}

variable [IsUniformAddGroup R] [IsTopologicalSemiring R]
    [IsUniformAddGroup S] [T2Space S] [CompleteSpace S]
    [IsTopologicalRing S] [IsLinearTopology S S]

/-- The evaluation homomorphism at `a` on `PowerSeries`, as a `RingHom`. -/
noncomputable def eval₂Hom (hφ : Continuous φ) (ha : IsTopologicallyNilpotent a) :
    PowerSeries R →+* S :=
  MvPowerSeries.eval₂Hom hφ (hasEval ha)

theorem coe_eval₂Hom (hφ : Continuous φ) (ha : IsTopologicallyNilpotent a) :
    ⇑(eval₂Hom hφ ha) = eval₂ φ a :=
  MvPowerSeries.coe_eval₂Hom hφ (hasEval ha)

-- Note: this is still true without the `T2Space` hypothesis, by arguing that the case
-- disjunction in the definition of `eval₂` only replaces some values by topologically
-- inseparable ones.
theorem uniformContinuous_eval₂ (hφ : Continuous φ) (ha : IsTopologicallyNilpotent a) :
    UniformContinuous (eval₂ φ a) :=
  MvPowerSeries.uniformContinuous_eval₂ hφ (hasEval ha)

theorem continuous_eval₂ (hφ : Continuous φ) (ha : IsTopologicallyNilpotent a) :
    Continuous (eval₂ φ a : PowerSeries R → S) :=
  (uniformContinuous_eval₂ hφ ha).continuous

theorem hasSum_eval₂ (hφ : Continuous φ) (ha : IsTopologicallyNilpotent a) (f : PowerSeries R) :
    HasSum (fun (d : ℕ) ↦ φ (coeff R d f) * a ^ d) (f.eval₂ φ a) := by
  have := MvPowerSeries.hasSum_eval₂ hφ (hasEval ha) f
  simp only [PowerSeries.eval₂]
  rw [← (Finsupp.single_injective ()).hasSum_iff] at this
  · convert this; simp; congr
  · intro d hd
    exact False.elim (hd ⟨d (), by ext; simp⟩)

theorem eval₂_eq_tsum (hφ : Continuous φ) (ha : IsTopologicallyNilpotent a) (f : PowerSeries R) :
    PowerSeries.eval₂ φ a f =
      ∑' d : ℕ, φ (coeff R d f) * a ^ d :=
  (hasSum_eval₂ hφ ha f).tsum_eq.symm

theorem eval₂_unique (hφ : Continuous φ) (ha : IsTopologicallyNilpotent a)
    {ε : PowerSeries R → S} (hε : Continuous ε)
    (h : ∀ p : Polynomial R, ε p = Polynomial.eval₂ φ a p) :
    ε = eval₂ φ a := by
  apply MvPowerSeries.eval₂_unique hφ (hasEval ha) hε
  intro p
  rw [MvPolynomial.toMvPowerSeries_pUnitAlgEquiv, h, ← MvPolynomial.eval₂_pUnitAlgEquiv]

theorem comp_eval₂ (hφ : Continuous φ) (ha : IsTopologicallyNilpotent a)
    {T : Type*} [UniformSpace T] [CompleteSpace T] [T2Space T]
    [CommRing T] [IsTopologicalRing T] [IsLinearTopology T T] [IsUniformAddGroup T]
    {ε : S →+* T} (hε : Continuous ε) :
    ε ∘ eval₂ φ a = eval₂ (ε.comp φ) (ε a) := by
  apply eval₂_unique _ (ha.map hε)
  · exact Continuous.comp hε (continuous_eval₂ hφ ha)
  · intro p
    simp only [Function.comp_apply, eval₂_coe]
    exact Polynomial.hom_eval₂ p φ ε a
  · simp only [RingHom.coe_comp, Continuous.comp hε hφ]

variable [Algebra R S] [ContinuousSMul R S]

/-- For `IsTopologicallyNilpotent a`,
the evaluation homomorphism at `a` on `PowerSeries`, as an `AlgHom`. -/
noncomputable def aeval (ha : IsTopologicallyNilpotent a) :
    PowerSeries R →ₐ[R] S :=
  MvPowerSeries.aeval (hasEval ha)

theorem coe_aeval (ha : IsTopologicallyNilpotent a) :
    ↑(aeval ha) = eval₂ (algebraMap R S) a :=
  MvPowerSeries.coe_aeval (hasEval ha)

theorem continuous_aeval (ha : IsTopologicallyNilpotent a) :
    Continuous (aeval ha : PowerSeries R → S) :=
  MvPowerSeries.continuous_aeval (hasEval ha)

@[simp]
theorem aeval_coe (ha : IsTopologicallyNilpotent a) (p : Polynomial R) :
    aeval ha (p : PowerSeries R) = Polynomial.aeval a p := by
  rw [coe_aeval, Polynomial.aeval_def, eval₂_coe]

theorem aeval_unique {ε : PowerSeries R →ₐ[R] S} (hε : Continuous ε) :
    aeval (isTopologicallyNilpotent_X.map hε) = ε :=
  MvPowerSeries.aeval_unique hε

theorem hasSum_aeval (ha : IsTopologicallyNilpotent a) (f : PowerSeries R) :
    HasSum (fun d ↦ coeff R d f • a ^ d) (f.aeval ha) := by
  simp_rw [coe_aeval, ← algebraMap_smul (R := R) S, smul_eq_mul]
  exact hasSum_eval₂ (continuous_algebraMap R S) ha f

theorem aeval_eq_sum (ha : IsTopologicallyNilpotent a) (f : PowerSeries R) :
    aeval ha f = tsum fun d ↦ coeff R d f • a ^ d :=
  (hasSum_aeval ha f).tsum_eq.symm

theorem comp_aeval (ha : IsTopologicallyNilpotent a)
    {T : Type*} [CommRing T] [UniformSpace T] [IsUniformAddGroup T]
    [IsTopologicalRing T] [IsLinearTopology T T]
    [T2Space T] [Algebra R T] [ContinuousSMul R T] [CompleteSpace T]
    {ε : S →ₐ[R] T} (hε : Continuous ε) :
    ε.comp (aeval ha) = aeval (ha.map hε) :=
  MvPowerSeries.comp_aeval (hasEval ha) hε

end PowerSeries
