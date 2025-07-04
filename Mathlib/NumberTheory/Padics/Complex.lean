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
# The `p`-adic complex numbers.

In this file we define the field `ℂ_[p]` of `p`-adic complex numbers and we give it both a normed
field and a valued field structure, induced by the unique extension of the `p`-adic norm to `ℂ_[p]`.

## Main Definitions
* `PadicAlg p` : the algebraic closure of `ℚ_[p]`.
* `PadicComplex p` : the type of `p`-adic complex numbers.
* `PadicComplex_integers` : the ring of integers of `ℂ_[p]`.

## Main Results

* `PadicComplex.norm_extends` : the norm on `ℂ_[p]` extends the norm on `PadicAlg p`, and hence
  the norm on `ℚ_[p]`.
* `PadicComplex.isNonarchimedean` : The norm on `ℂ_[p]` is nonarchimedean.

## Notation

We introduce the notation `ℂ_[p]` for the `p`-adic complex numbers, and `𝓞_ℂ_[p]` for its ring of
integers.

## Tags

p-adic, p adic, padic, norm, valuation, Cauchy, completion, p-adic completion
-/

noncomputable section

open Valued Valuation

open scoped NNReal

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- `PadicAlg p` is the algebraic closure of `ℚ_[p]`. -/
abbrev PadicAlg := AlgebraicClosure ℚ_[p]

namespace PadicAlg

/-- `PadicAlg p` is an algebraic extension of `ℚ_[p]`. -/
theorem isAlgebraic : Algebra.IsAlgebraic ℚ_[p] (PadicAlg p) := AlgebraicClosure.isAlgebraic _

instance : Coe ℚ_[p] (PadicAlg p) := ⟨algebraMap ℚ_[p] (PadicAlg p)⟩

theorem coe_eq : (Coe.coe : ℚ_[p] → PadicAlg p) = algebraMap ℚ_[p] (PadicAlg p) := rfl

/-- `PadicAlg p` is a normed field, where the norm is the `p`-adic norm, that is, the spectral norm
induced by the `p`-adic norm on `ℚ_[p]`. -/
instance normedField : NormedField (PadicAlg p) := spectralNorm.normedField ℚ_[p] (PadicAlg p)

/-- The norm on `PadicAlg p` is nonarchimedean. -/
theorem isNonarchimedean : IsNonarchimedean (norm : PadicAlg p → ℝ) :=
  isNonarchimedean_spectralNorm (K := ℚ_[p]) (L := PadicAlg p)

/-- The norm on `PadicAlg p` is the spectral norm induced by the `p`-adic norm on `ℚ_[p]`. -/
theorem norm_def (x : PadicAlg p) : ‖x‖ = spectralNorm ℚ_[p] (PadicAlg p) x := rfl

/-- The norm on `PadicAlg p` extends the `p`-adic norm on `ℚ_[p]`. -/
theorem norm_extends (x : ℚ_[p]) : ‖(x : PadicAlg p)‖ = ‖x‖ :=
  spectralAlgNorm_extends (K := ℚ_[p]) (L := PadicAlg p) _

instance : IsUltrametricDist (PadicAlg p) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (PadicAlg.isNonarchimedean p)

/-- `PadicAlg p` is a valued field, with the valuation corresponding to the `p`-adic norm. -/
instance valued : Valued (PadicAlg p) ℝ≥0 := NormedField.toValued

/-- The valuation of `x : PadicAlg p` agrees with its `ℝ≥0`-valued norm. -/
theorem valuation_def (x : PadicAlg p) : Valued.v x = ‖x‖₊ := rfl

/-- The coercion of the valuation of `x : PadicAlg p` to `ℝ` agrees with its norm. -/
theorem valuation_coe (x : PadicAlg p) :
  ((Valued.v x : ℝ≥0) : ℝ) = spectralNorm ℚ_[p] (PadicAlg p) x := rfl

/-- The valuation of `p : PadicAlg p` is `1/p`. -/
theorem valuation_p (p : ℕ) [Fact p.Prime] : Valued.v (p : PadicAlg p) = 1 / (p : ℝ≥0) := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlg p))]
  ext
  rw [valuation_coe, spectralNorm_extends, padicNormE.norm_p, one_div, NNReal.coe_inv,
    NNReal.coe_natCast]

/-- The valuation on `PadicAlg p` has rank one. -/
instance : RankOne (PadicAlg.valued p).v where
  hom         := MonoidWithZeroHom.id ℝ≥0
  strictMono' := strictMono_id
  nontrivial' := by
    use p
    haveI hp : Nat.Prime p := hp.1
    simp only [valuation_p, one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, inv_eq_one,
      Nat.cast_eq_one]
    exact ⟨hp.ne_zero, hp.ne_one⟩

instance : UniformContinuousConstSMul ℚ_[p] (PadicAlg p) :=
  uniformContinuousConstSMul_of_continuousConstSMul ℚ_[p] (PadicAlg p)

end PadicAlg

/-- `ℂ_[p]` is the field of `p`-adic complex numbers, that is, the completion of `PadicAlg p` with
respect to the `p`-adic norm. -/
abbrev PadicComplex := UniformSpace.Completion (PadicAlg p)

/-- `ℂ_[p]` is the field of `p`-adic complex numbers. -/
notation "ℂ_[" p "]" => PadicComplex p

namespace PadicComplex
/-- `ℂ_[p]` is a valued field, where the valuation is the one extending that on `PadicAlg p`. -/
instance valued : Valued ℂ_[p] ℝ≥0 := inferInstance

/-- The valuation on `ℂ_[p]` extends the valuation on `PadicAlg p`. -/
theorem valuation_extends (x : PadicAlg p) : Valued.v (x : ℂ_[p]) = Valued.v x :=
  Valued.extension_extends _

theorem coe_eq (x : PadicAlg p) : (x : ℂ_[p]) = algebraMap (PadicAlg p) ℂ_[p] x := rfl

theorem coe_zero : ((0 : PadicAlg p) : ℂ_[p]) = 0 := rfl

/-- `ℂ_[p]` is an algebra over `ℚ_[p]`. -/
instance : Algebra ℚ_[p] ℂ_[p] where
  smul := (UniformSpace.Completion.instSMul ℚ_[p] (PadicAlg p)).smul
  algebraMap :=
    RingHom.comp (UniformSpace.Completion.coeRingHom) (algebraMap ℚ_[p] (PadicAlg p))
  commutes' r x := by rw [mul_comm]
  smul_def' r x := by
    apply UniformSpace.Completion.ext' (continuous_const_smul r) (continuous_mul_left _)
    intro a
    have : UniformSpace.Completion.coeRingHom ((algebraMap ℚ_[p] (PadicAlg p)) r) * ↑a =
       UniformSpace.Completion.coeRingHom ((algebraMap ℚ_[p] (PadicAlg p)) r) *
       UniformSpace.Completion.coeRingHom a := rfl
    rw [← UniformSpace.Completion.coe_smul, RingHom.coe_comp, Function.comp_apply,
      this, ← map_mul, Algebra.smul_def]
    rfl

instance : IsScalarTower ℚ_[p] (PadicAlg p) ℂ_[p] := IsScalarTower.of_algebraMap_eq (congrFun rfl)

@[simp, norm_cast]
lemma coe_natCast (n : ℕ) : ((n : PadicAlg p) : ℂ_[p]) = (n : ℂ_[p])  := by
  rw [← map_natCast (algebraMap (PadicAlg p) ℂ_[p]) n, coe_eq]

/-- The valuation of `p : ℂ_[p]` is `1/p`. -/
theorem valuation_p : Valued.v (p : ℂ_[p]) = 1 / (p : ℝ≥0) := by
  have := valuation_extends p (p : PadicAlg p)
  rw [PadicAlg.valuation_p] at this
  simpa only [← map_natCast (algebraMap (PadicAlg p) ℂ_[p]), ← coe_eq]

/-- The valuation on `ℂ_[p]` has rank one. -/
instance : RankOne (PadicComplex.valued p).v where
  hom         := MonoidWithZeroHom.id ℝ≥0
  strictMono' := strictMono_id
  nontrivial' := by
    use p
    haveI hp : Nat.Prime p := hp.1
    simp only [valuation_p, one_div, ne_eq, inv_eq_zero, Nat.cast_eq_zero, inv_eq_one,
      Nat.cast_eq_one]
    exact ⟨hp.ne_zero, hp.ne_one⟩

lemma rankOne_hom_eq :
    RankOne.hom (PadicComplex.valued p).v = RankOne.hom (PadicAlg.valued p).v := rfl

/-- `ℂ_[p]` is a normed field, where the norm corresponds to the extension of the `p`-adic
  valuation. -/
instance : NormedField ℂ_[p] :=  Valued.toNormedField _ _

theorem norm_def : (Norm.norm : ℂ_[p] → ℝ) = Valued.norm := rfl

/-- The norm on `ℂ_[p]` extends the norm on `PadicAlg p`. -/
theorem norm_extends (x : PadicAlg p) : ‖(x : ℂ_[p])‖ = ‖x‖ := by
  rw [norm_def, Valued.norm, ← coe_nnnorm, valuation_extends p x, coe_nnnorm]
  rfl

/-- The `ℝ≥0`-valued norm on `ℂ_[p]` extends that on `PadicAlg p`. -/
theorem nnnorm_extends (x : PadicAlg p) : ‖(x : ℂ_[p])‖₊ = ‖x‖₊ := by ext; exact norm_extends p x

/-- The norm on `ℂ_[p]` is nonarchimedean. -/
theorem isNonarchimedean : IsNonarchimedean (Norm.norm : ℂ_[p] → ℝ) := fun x y ↦ by
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_le (Continuous.comp continuous_norm continuous_add)
      (Continuous.max (Continuous.comp (@continuous_norm ℂ_[p] _) (Continuous.fst continuous_id))
      (Continuous.comp (@continuous_norm ℂ_[p] _) (Continuous.snd continuous_id)))) (fun a b ↦ ?_)
  · rw [← UniformSpace.Completion.coe_add, norm_extends, norm_extends, norm_extends]
    exact PadicAlg.isNonarchimedean p a b

end PadicComplex

/-- We define `𝓞_ℂ_[p]` as the valuation subring of of `ℂ_[p]`, consisting of those elements with
  valuation `≤ 1`. -/
def padicComplexIntegers : ValuationSubring ℂ_[p] := (PadicComplex.valued p).v.valuationSubring

/-- We define `𝓞_ℂ_[p]` as the subring of elements of `ℂ_[p]` with valuation `≤ 1`. -/
notation "𝓞_ℂ_[" p "]" => padicComplexIntegers p

/-- `𝓞_ℂ_[p]` is the ring of integers of `ℂ_[p]`. -/
theorem PadicComplex.integers : Valuation.Integers (PadicComplex.valued p).v 𝓞_ℂ_[p] :=
  Valuation.integer.integers _
