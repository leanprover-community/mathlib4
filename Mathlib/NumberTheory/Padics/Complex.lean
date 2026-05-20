/-
Copyright (c) 2025 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Field.Dense
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuedField

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
* `PadicComplex.isAlgClosed` : `ℂ_[p]` is algebraically closed.

## Notation

We introduce the notation `ℂ_[p]` for the `p`-adic complex numbers, and `𝓞_ℂ_[p]` for its ring of
integers.

## Tags

p-adic, p adic, padic, norm, valuation, Cauchy, completion, p-adic completion
-/

@[expose] public section

noncomputable section

open Valuation

open scoped NNReal

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- `PadicAlgCl p` is a fixed algebraic closure of `ℚ_[p]`. -/
abbrev PadicAlgCl := AlgebraicClosure ℚ_[p]

namespace PadicAlgCl

/-- `PadicAlgCl p` is an algebraic extension of `ℚ_[p]`. -/
instance isAlgebraic : Algebra.IsAlgebraic ℚ_[p] (PadicAlgCl p) := AlgebraicClosure.isAlgebraic _

instance : Coe ℚ_[p] (PadicAlgCl p) := ⟨algebraMap ℚ_[p] (PadicAlgCl p)⟩

theorem coe_eq : (Coe.coe : ℚ_[p] → PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) := rfl

/-- `PadicAlgCl p` is a normed field, where the norm is the `p`-adic norm, that is, the
spectral norm induced by the `p`-adic norm on `ℚ_[p]`. -/
instance normedField : NormedField (PadicAlgCl p) := spectralNorm.normedField ℚ_[p] (PadicAlgCl p)

/-- The norm on `PadicAlgCl p` is nonarchimedean. -/
theorem isNonarchimedean : IsNonarchimedean (norm : PadicAlgCl p → ℝ) :=
  isNonarchimedean_spectralNorm (K := ℚ_[p]) (L := PadicAlgCl p)

/-- `PadicAlgCl p` is a normed algebra over `ℚ_[p]`. -/
instance normedAlgebra : NormedAlgebra ℚ_[p] (PadicAlgCl p) := spectralNorm.normedAlgebra _ _

/-- The norm on `PadicAlgCl p` is the spectral norm induced by the `p`-adic norm on `ℚ_[p]`. -/
@[simp]
theorem spectralNorm_eq (x : PadicAlgCl p) : spectralNorm ℚ_[p] (PadicAlgCl p) x = ‖x‖ := rfl

/-- The norm on `PadicAlgCl p` extends the `p`-adic norm on `ℚ_[p]`. -/
theorem norm_extends (x : ℚ_[p]) : ‖(x : PadicAlgCl p)‖ = ‖x‖ := by
  simp

/-- The underlying metric space of `PadicAlgCl p` is ultrametric. -/
instance isUltrametricDist : IsUltrametricDist (PadicAlgCl p) :=
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
  rw [valuation_coe, norm_extends, Padic.norm_p, one_div, NNReal.coe_inv,
    NNReal.coe_natCast]

open MonoidWithZeroHom.ValueGroup₀

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The valuation on `PadicAlgCl p` has rank one. -/
instance : RankOne (PadicAlgCl.valued p).v where
  hom'        := embedding
  strictMono' := embedding_strictMono
  exists_val_nontrivial := by
    use p
    have hp : Nat.Prime p := hp.1
    simp only [valuation_p, one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, inv_eq_one,
      Nat.cast_eq_one]
    exact ⟨hp.ne_zero, hp.ne_one⟩

instance : UniformContinuousConstSMul ℚ_[p] (PadicAlgCl p) :=
  uniformContinuousConstSMul_of_continuousConstSMul ℚ_[p] (PadicAlgCl p)

/-- The norm on `PadicAlgCl p` is nontrivial. -/
instance nontriviallyNormedField : NontriviallyNormedField (PadicAlgCl p) where
  non_trivial := by
    choose x hx using NontriviallyNormedField.non_trivial (α := ℚ_[p])
    use x
    rw [PadicAlgCl.norm_extends]
    exact hx

/-- `PadicAlgCl p` has characteristic zero. -/
instance charZero : CharZero (PadicAlgCl p) :=
  (RingHom.charZero_iff (algebraMap ℚ_[p] (PadicAlgCl p)).injective).mp inferInstance

end PadicAlgCl

/-- `ℂ_[p]` is the field of `p`-adic complex numbers, that is, the completion of `PadicAlgCl p` with
respect to the `p`-adic norm. -/
abbrev PadicComplex := UniformSpace.Completion (PadicAlgCl p)

/-- `ℂ_[p]` is the field of `p`-adic complex numbers. -/
notation "ℂ_[" p "]" => PadicComplex p

namespace PadicComplex

/-- `ℂ_[p]` is a valued field, where the valuation is the one extending that on `PadicAlgCl p`. -/
instance valued : Valued ℂ_[p] ℝ≥0 := Valued.valuedCompletion

/-- The valuation on `ℂ_[p]` extends the valuation on `PadicAlgCl p`. -/
theorem valuation_extends (x : PadicAlgCl p) : Valued.v (x : ℂ_[p]) = Valued.v x :=
  Valued.extensionValuation_apply_coe _

theorem coe_eq (x : PadicAlgCl p) : (x : ℂ_[p]) = algebraMap (PadicAlgCl p) ℂ_[p] x := rfl

@[simp] theorem coe_zero : ((0 : PadicAlgCl p) : ℂ_[p]) = 0 := rfl

instance : IsScalarTower ℚ_[p] (PadicAlgCl p) ℂ_[p] := IsScalarTower.of_algebraMap_eq (congrFun rfl)

@[simp, norm_cast]
lemma coe_natCast (n : ℕ) : ((n : PadicAlgCl p) : ℂ_[p]) = (n : ℂ_[p]) := by
  rw [← map_natCast (algebraMap (PadicAlgCl p) ℂ_[p]) n, coe_eq]

/-- The valuation of `p : ℂ_[p]` is `1/p`. -/
theorem valuation_p : Valued.v (p : ℂ_[p]) = 1 / (p : ℝ≥0) := by
  rw [← map_natCast (algebraMap (PadicAlgCl p) ℂ_[p]), ← coe_eq, valuation_extends,
    PadicAlgCl.valuation_p]

open MonoidWithZeroHom.ValueGroup₀

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The valuation on `ℂ_[p]` has rank one. -/
instance : RankOne (PadicComplex.valued p).v where
  hom'        := embedding
  strictMono' := embedding_strictMono
  exists_val_nontrivial := by
    use p
    have hp : Nat.Prime p := hp.1
    simp only [valuation_p, one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, inv_eq_one,
      Nat.cast_eq_one]
    exact ⟨hp.ne_zero, hp.ne_one⟩

@[simp]
theorem RankOne.hom_eq_embedding : RankOne.hom (PadicComplex.valued p).v = embedding := rfl

/-- `ℂ_[p]` is a normed field, where the norm extends from `PadicAlgCl` along completion. -/
instance normedField : NormedField ℂ_[p] := inferInstance

-- Ensure that the norm instance on `ℂ_[p]` is extended from `PadicAlgCl p`.
example : (‖·‖ : ℂ_[p] → ℝ) = (UniformSpace.Completion.instNorm (PadicAlgCl p)).norm := by
  with_reducible_and_instances rfl

/-- The norm on `ℂ_[p]` extends the norm on `PadicAlgCl p`. -/
theorem norm_extends (x : PadicAlgCl p) : ‖(x : ℂ_[p])‖ = ‖x‖ := by
  simp

/-- The norm on `ℂ_[p]` extends the norm on `ℚ_[p]`. -/
theorem norm_extends' (x : ℚ_[p]) : ‖(x : ℂ_[p])‖ = ‖x‖ := by
  simp

/-- The underlying metric space of `ℂ_[p]` is ultrametric. -/
instance isUltrametricDist : IsUltrametricDist ℂ_[p] := IsUltrametricDist.of_normedAlgebra ℚ_[p]

/-- The norm on `ℂ_[p]` is nonarchimedean. -/
theorem isNonarchimedean : IsNonarchimedean (Norm.norm : ℂ_[p] → ℝ) :=
  IsUltrametricDist.norm_add_le_max

/-- The norm on `ℂ_[p]` is compatible with the valuation. -/
theorem norm_eq_norm' : (‖·‖ : ℂ_[p] → ℝ) = Valued.v.norm := by
  apply UniformSpace.Completion.extension_unique (f := @norm (PadicAlgCl p) _) (g := Valued.v.norm)
  · exact uniformContinuous_norm
  · letI S := (Valued.toNormedField ℂ_[p] NNReal).toNormedCommRing.toNormedRing.toSeminormedRing
    letI := S.toNonUnitalSeminormedRing.toSeminormedAddCommGroup.toSeminormedAddGroup
    exact @uniformContinuous_norm ℂ_[p] this
  · intro x
    simp [Valued.v.norm_def, restrict_def]

/-- The norm on `ℂ_[p]` is compatible with the valuation. -/
theorem norm_eq_norm (x : ℂ_[p]) : ‖x‖ = Valued.v.norm x := by
  congr!
  exact norm_eq_norm' p

/-- The `ℝ≥0`-valued norm on `ℂ_[p]` extends that on `PadicAlgCl p`. -/
theorem nnnorm_extends (x : PadicAlgCl p) : ‖(x : ℂ_[p])‖₊ = ‖x‖₊ := by
  ext
  exact norm_extends p x

/-- The `ℝ≥0`-valued norm on `ℂ_[p]` extends the norm on `ℚ_[p]`. -/
theorem nnnorm_extends' (x : ℚ_[p]) : ‖(x : ℂ_[p])‖₊ = ‖x‖₊ := by
  ext
  simp

/-- The norm on `ℂ_[p]` is nontrivial. -/
instance nontriviallyNormedField : NontriviallyNormedField ℂ_[p] where
  non_trivial := by
    choose x hx using NontriviallyNormedField.non_trivial (α := ℚ_[p])
    use x
    simpa only [norm_extends']

/-- `ℂ_[p]` has characteristic zero. -/
instance charZero : CharZero ℂ_[p] :=
  (RingHom.charZero_iff (algebraMap ℚ_[p] ℂ_[p]).injective).mp inferInstance

/-- `ℂ_[p]` is algebraically closed. -/
instance isAlgClosed : IsAlgClosed ℂ_[p] :=
  IsAlgClosed.of_denseRange UniformSpace.Completion.denseRange_coe

end PadicComplex

/-- We define `𝓞_ℂ_[p]` as the valuation subring of `ℂ_[p]`, consisting of those elements with
  valuation `≤ 1`. -/
def PadicComplexInt : ValuationSubring ℂ_[p] := (PadicComplex.valued p).v.valuationSubring

/-- We define `𝓞_ℂ_[p]` as the subring of elements of `ℂ_[p]` with valuation `≤ 1`. -/
notation "𝓞_ℂ_[" p "]" => PadicComplexInt p

/-- `𝓞_ℂ_[p]` is the ring of integers of `ℂ_[p]`. -/
theorem PadicComplexInt.integers : Valuation.Integers (PadicComplex.valued p).v 𝓞_ℂ_[p] :=
  Valuation.integer.integers _
