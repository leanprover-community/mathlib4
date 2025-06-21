/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Probability.Independence.Basic

open Complex MeasureTheory Measure ProbabilityTheory

open scoped RealInnerProductSpace

variable {E F Ω : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [InnerProductSpace ℝ E]
  [InnerProductSpace ℝ F] {mE : MeasurableSpace E} {mF : MeasurableSpace F}
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → E} {Y : Ω → F}
  (t : WithLp 2 (E × F))

local instance : MeasurableSpace (WithLp 2 (E × F)) := borel (WithLp 2 (E × F))

lemma test (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ) (h : IndepFun X Y μ) :
    charFun (μ.map fun ω ↦ (WithLp.equiv 2 _).symm (X ω, Y ω)) t =
    charFun (μ.map X) t.1 * charFun (μ.map Y) t.2 := by
  change charFun (μ.map (_ ∘ _)) t = _
  rw [← map_map, (indepFun_iff_map_prod_eq_prod_map_map mX mY).1 h]
  -- simp_rw [WithLp.equiv, Equiv.refl_apply, (indepFun_iff_map_prod_eq_prod_map_map mX mY).1 h]
  simp_rw [charFun, WithLp.prod_inner_apply, ofReal_add, add_mul, exp_add]
  rw [integral_map]
  simp
  rw [← integral_prod_mul (fun x ↦ exp (⟪x, t.1⟫ * I))
      (fun x ↦ exp (⟪x, t.2⟫ * I))]

  congr 1

  conv_lhs => enter [1, 1]; change id

  rw [map_id (μ := (map X μ).prod (map Y μ))]
    -- integral_prod_mul (fun x ↦ exp (⟪x, t.1⟫ * I)) (fun x ↦ exp (⟪x, t.2⟫ * I))]

/-- The characteristic function of a product measure is the product
of the characteristic functions. -/
lemma charFun_pi {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)] (μ : (i : ι) → Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] (t : PiLp 2 E) :
    charFun (E := PiLp 2 E) (Measure.pi μ) t = ∏ i, charFun (μ i) (t i) := by
  simp_rw [charFun, PiLp.inner_apply, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, PiLp,
    WithLp, integral_fintype_prod_eq_prod (f := fun i x ↦ Complex.exp (⟪x, t i⟫ * Complex.I))]
