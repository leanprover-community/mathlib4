/-
Copyright (c) 2025 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# The field `ℂ_[p]` of `p`-adic complex numbers.

In this file we define the field `ℂ_[p]` of `p`-adic complex numbers as the `p`-adic completion of
an algebraic closure of `ℚ_[p]`. We endow `ℂ_[p]` with both a normed field and a valued field
structure, induced by the unique extension of the `p`-adic norm to `ℂ_[p]`.

## Main Definitions
* `PadicAlgCl p` : the algebraic closure of `ℚ_[p]`.
* `PadicComplex p` : the type of `p`-adic complex numbers, denoted by `ℂ_[p]`.
* `PadicComplexInt p` : the ring of integers of `ℂ_[p]`.

## Main Results

* `PadicComplex.norm_extends` : the norm on `ℂ_[p]` extends the norm on `PadicAlgCl p`, and hence
  the norm on `ℚ_[p]`.
* `PadicComplex.isNonarchimedean` : The norm on `ℂ_[p]` is nonarchimedean.

## Notation

We introduce the notation `ℂ_[p]` for the `p`-adic complex numbers, and `𝓞_ℂ_[p]` for its ring of
integers.

## Tags

p-adic, p adic, padic, norm, valuation, Cauchy, completion, p-adic completion
-/

noncomputable section

open Valuation

open scoped NNReal

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- `PadicAlgCl p` is a fixed algebraic closure of `ℚ_[p]`. -/
abbrev PadicAlgCl := AlgebraicClosure ℚ_[p]

namespace PadicAlgCl

/-- `PadicAlgCl p` is an algebraic extension of `ℚ_[p]`. -/
theorem isAlgebraic : Algebra.IsAlgebraic ℚ_[p] (PadicAlgCl p) := AlgebraicClosure.isAlgebraic _

instance : Coe ℚ_[p] (PadicAlgCl p) := ⟨algebraMap ℚ_[p] (PadicAlgCl p)⟩

theorem coe_eq : (Coe.coe : ℚ_[p] → PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) := rfl

/-- `PadicAlgCl p` is a normed field, where the norm is the `p`-adic norm, that is, the
spectral norm induced by the `p`-adic norm on `ℚ_[p]`. -/
instance normedField : NormedField (PadicAlgCl p) := spectralNorm.normedField ℚ_[p] (PadicAlgCl p)

/-- The norm on `PadicAlgCl p` is nonarchimedean. -/
theorem isNonarchimedean : IsNonarchimedean (norm : PadicAlgCl p → ℝ) :=
  isNonarchimedean_spectralNorm (K := ℚ_[p]) (L := PadicAlgCl p)

/-- The norm on `PadicAlgCl p` is the spectral norm induced by the `p`-adic norm on `ℚ_[p]`. -/
@[simp]
theorem spectralNorm_eq (x : PadicAlgCl p) : spectralNorm ℚ_[p] (PadicAlgCl p) x = ‖x‖ := rfl

/-- The norm on `PadicAlgCl p` extends the `p`-adic norm on `ℚ_[p]`. -/
@[simp] theorem norm_extends (x : ℚ_[p]) : ‖(x : PadicAlgCl p)‖ = ‖x‖ :=
  spectralAlgNorm_extends (K := ℚ_[p]) (L := PadicAlgCl p) _

instance : IsUltrametricDist (PadicAlgCl p) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (PadicAlgCl.isNonarchimedean p)

/-- `PadicAlgCl p` is a valued field, with the valuation corresponding to the `p`-adic norm. -/
instance valued : Valued (PadicAlgCl p) ℝ≥0 := NormedField.toValued

/-- The valuation of `x : PadicAlgCl p` agrees with its `ℝ≥0`-valued norm. -/
theorem valuation_def (x : PadicAlgCl p) : Valued.v x = ‖x‖₊ := rfl

/-- The coercion of the valuation of `x : PadicAlgCl p` to `ℝ` agrees with its norm. -/
@[simp] theorem valuation_coe (x : PadicAlgCl p) : ((Valued.v x : ℝ≥0) : ℝ) = ‖x‖ := rfl

/-- The valuation of `p : PadicAlgCl p` is `1/p`. -/
theorem valuation_p (p : ℕ) [Fact p.Prime] : Valued.v (p : PadicAlgCl p) = 1 / (p : ℝ≥0) := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p))]
  ext
  rw [valuation_coe, norm_extends, padicNormE.norm_p, one_div, NNReal.coe_inv,
    NNReal.coe_natCast]

/-- The valuation on `PadicAlgCl p` has rank one. -/
instance : RankOne (PadicAlgCl.valued p).v where
  hom         := MonoidWithZeroHom.id ℝ≥0
  strictMono' := strictMono_id
  exists_val_nontrivial := by
    use p
    have hp : Nat.Prime p := hp.1
    simp only [valuation_p, one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, inv_eq_one,
      Nat.cast_eq_one]
    exact ⟨hp.ne_zero, hp.ne_one⟩

instance : UniformContinuousConstSMul ℚ_[p] (PadicAlgCl p) :=
  uniformContinuousConstSMul_of_continuousConstSMul ℚ_[p] (PadicAlgCl p)

end PadicAlgCl

/-- `ℂ_[p]` is the field of `p`-adic complex numbers, that is, the completion of `PadicAlgCl p` with
respect to the `p`-adic norm. -/
abbrev PadicComplex := UniformSpace.Completion (PadicAlgCl p)

/-- `ℂ_[p]` is the field of `p`-adic complex numbers. -/
notation "ℂ_[" p "]" => PadicComplex p

namespace PadicComplex
/-- `ℂ_[p]` is a valued field, where the valuation is the one extending that on `PadicAlgCl p`. -/
instance valued : Valued ℂ_[p] ℝ≥0 := inferInstance

/-- The valuation on `ℂ_[p]` extends the valuation on `PadicAlgCl p`. -/
theorem valuation_extends (x : PadicAlgCl p) : Valued.v (x : ℂ_[p]) = Valued.v x :=
  Valued.extension_extends _

theorem coe_eq (x : PadicAlgCl p) : (x : ℂ_[p]) = algebraMap (PadicAlgCl p) ℂ_[p] x := rfl

@[simp] theorem coe_zero : ((0 : PadicAlgCl p) : ℂ_[p]) = 0 := rfl

/-- `ℂ_[p]` is an algebra over `ℚ_[p]`. -/
instance : Algebra ℚ_[p] ℂ_[p] where
  smul := (UniformSpace.Completion.instSMul ℚ_[p] (PadicAlgCl p)).smul
  algebraMap := (UniformSpace.Completion.coeRingHom).comp (algebraMap ℚ_[p] (PadicAlgCl p))
  commutes' r x := by rw [mul_comm]
  smul_def' r x := by
    apply UniformSpace.Completion.ext' (continuous_const_smul r) (continuous_mul_left _)
    intro a
    rw [RingHom.coe_comp, Function.comp_apply, Algebra.smul_def]
    rfl

instance : IsScalarTower ℚ_[p] (PadicAlgCl p) ℂ_[p] := IsScalarTower.of_algebraMap_eq (congrFun rfl)

@[simp, norm_cast]
lemma coe_natCast (n : ℕ) : ((n : PadicAlgCl p) : ℂ_[p]) = (n : ℂ_[p]) := by
  rw [← map_natCast (algebraMap (PadicAlgCl p) ℂ_[p]) n, coe_eq]

/-- The valuation of `p : ℂ_[p]` is `1/p`. -/
theorem valuation_p : Valued.v (p : ℂ_[p]) = 1 / (p : ℝ≥0) := by
  rw [← map_natCast (algebraMap (PadicAlgCl p) ℂ_[p]), ← coe_eq, valuation_extends,
    PadicAlgCl.valuation_p]

/-- The valuation on `ℂ_[p]` has rank one. -/
instance : RankOne (PadicComplex.valued p).v where
  hom         := MonoidWithZeroHom.id ℝ≥0
  strictMono' := strictMono_id
  exists_val_nontrivial := by
    use p
    have hp : Nat.Prime p := hp.1
    simp only [valuation_p, one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, inv_eq_one,
      Nat.cast_eq_one]
    exact ⟨hp.ne_zero, hp.ne_one⟩

lemma rankOne_hom_eq :
    RankOne.hom (PadicComplex.valued p).v = RankOne.hom (PadicAlgCl.valued p).v := rfl

/-- `ℂ_[p]` is a normed field, where the norm corresponds to the extension of the `p`-adic
  valuation. -/
instance : NormedField ℂ_[p] := Valued.toNormedField _ _

theorem norm_def : (Norm.norm : ℂ_[p] → ℝ) = Valued.norm := rfl

/-- The norm on `ℂ_[p]` extends the norm on `PadicAlgCl p`. -/
theorem norm_extends (x : PadicAlgCl p) : ‖(x : ℂ_[p])‖ = ‖x‖ := by
  rw [norm_def, Valued.norm, ← coe_nnnorm, valuation_extends p x, coe_nnnorm]
  rfl

/-- The `ℝ≥0`-valued norm on `ℂ_[p]` extends that on `PadicAlgCl p`. -/
theorem nnnorm_extends (x : PadicAlgCl p) : ‖(x : ℂ_[p])‖₊ = ‖x‖₊ := by ext; exact norm_extends p x

/-- The norm on `ℂ_[p]` is nonarchimedean. -/
theorem isNonarchimedean : IsNonarchimedean (Norm.norm : ℂ_[p] → ℝ) := fun x y ↦ by
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_le (continuous_norm.comp continuous_add) (by fun_prop)) (fun a b ↦ ?_)
  rw [← UniformSpace.Completion.coe_add, norm_extends, norm_extends, norm_extends]
  exact PadicAlgCl.isNonarchimedean p a b

end PadicComplex

/-- We define `𝓞_ℂ_[p]` as the valuation subring of of `ℂ_[p]`, consisting of those elements with
  valuation `≤ 1`. -/
def PadicComplexInt : ValuationSubring ℂ_[p] := (PadicComplex.valued p).v.valuationSubring

/-- We define `𝓞_ℂ_[p]` as the subring of elements of `ℂ_[p]` with valuation `≤ 1`. -/
notation "𝓞_ℂ_[" p "]" => PadicComplexInt p

/-- `𝓞_ℂ_[p]` is the ring of integers of `ℂ_[p]`. -/
theorem PadicComplexInt.integers : Valuation.Integers (PadicComplex.valued p).v 𝓞_ℂ_[p] :=
  Valuation.integer.integers _
