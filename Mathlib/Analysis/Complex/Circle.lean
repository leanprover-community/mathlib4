/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Analysis.Normed.Field.UnitBall

/-!
# The circle

This file defines `circle` to be the metric sphere (`Metric.sphere`) in `ℂ` centred at `0` of
radius `1`.  We equip it with the following structure:

* a submonoid of `ℂ`
* a group
* a topological group

We furthermore define `expMapCircle` to be the natural map `fun t ↦ exp (t * I)` from `ℝ` to
`circle`, and show that this map is a group homomorphism.

## Implementation notes

Because later (in `Geometry.Manifold.Instances.Sphere`) one wants to equip the circle with a smooth
manifold structure borrowed from `Metric.sphere`, the underlying set is
`{z : ℂ | abs (z - 0) = 1}`.  This prevents certain algebraic facts from working definitionally --
for example, the circle is not defeq to `{z : ℂ | abs z = 1}`, which is the kernel of `Complex.abs`
considered as a homomorphism from `ℂ` to `ℝ`, nor is it defeq to `{z : ℂ | normSq z = 1}`, which
is the kernel of the homomorphism `Complex.normSq` from `ℂ` to `ℝ`.

-/


noncomputable section

open Complex Metric

open ComplexConjugate

/-- The unit circle in `ℂ`, here given the structure of a submonoid of `ℂ`. -/
def circle : Submonoid ℂ :=
  Submonoid.unitSphere ℂ

@[simp]
theorem mem_circle_iff_abs {z : ℂ} : z ∈ circle ↔ abs z = 1 :=
  mem_sphere_zero_iff_norm

theorem circle_def : ↑circle = { z : ℂ | abs z = 1 } :=
  Set.ext fun _ => mem_circle_iff_abs

@[simp]
theorem abs_coe_circle (z : circle) : abs z = 1 :=
  mem_circle_iff_abs.mp z.2

theorem mem_circle_iff_normSq {z : ℂ} : z ∈ circle ↔ normSq z = 1 := by simp [Complex.abs]

@[simp]
theorem normSq_eq_of_mem_circle (z : circle) : normSq z = 1 := by simp [normSq_eq_abs]

theorem ne_zero_of_mem_circle (z : circle) : (z : ℂ) ≠ 0 :=
  ne_zero_of_mem_unit_sphere z

instance commGroup : CommGroup circle :=
  Metric.sphere.commGroup

@[simp]
theorem coe_inv_circle (z : circle) : ↑z⁻¹ = (z : ℂ)⁻¹ :=
  rfl

theorem coe_inv_circle_eq_conj (z : circle) : ↑z⁻¹ = conj (z : ℂ) := by
  rw [coe_inv_circle, inv_def, normSq_eq_of_mem_circle, inv_one, ofReal_one, mul_one]

@[simp]
theorem coe_div_circle (z w : circle) : ↑(z / w) = (z : ℂ) / w :=
  circle.subtype.map_div z w

/-- The elements of the circle embed into the units. -/
def circle.toUnits : circle →* Units ℂ :=
  unitSphereToUnits ℂ

-- written manually because `@[simps]` was slow and generated the wrong lemma
@[simp]
theorem circle.toUnits_apply (z : circle) :
    circle.toUnits z = Units.mk0 ↑z (ne_zero_of_mem_circle z) :=
  rfl

instance : CompactSpace circle :=
  Metric.sphere.compactSpace _ _

instance : TopologicalGroup circle :=
  Metric.sphere.topologicalGroup

instance : UniformGroup circle := by
  convert topologicalGroup_is_uniform_of_compactSpace circle
  exact unique_uniformity_of_compact rfl rfl

/-- If `z` is a nonzero complex number, then `conj z / z` belongs to the unit circle. -/
@[simps]
def circle.ofConjDivSelf (z : ℂ) (hz : z ≠ 0) : circle :=
  ⟨conj z / z,
    mem_circle_iff_abs.2 <| by rw [map_div₀, abs_conj, div_self]; exact Complex.abs.ne_zero hz⟩

/-- The map `fun t => exp (t * I)` from `ℝ` to the unit circle in `ℂ`. -/
def expMapCircle : C(ℝ, circle) where
  toFun t := ⟨exp (t * I), by simp [exp_mul_I, abs_cos_add_sin_mul_I]⟩

@[simp]
theorem expMapCircle_apply (t : ℝ) : ↑(expMapCircle t) = Complex.exp (t * Complex.I) :=
  rfl

@[simp]
theorem expMapCircle_zero : expMapCircle 0 = 1 :=
  Subtype.ext <| by
    rw [expMapCircle_apply, ofReal_zero, zero_mul, exp_zero, Submonoid.coe_one]

@[simp]
theorem expMapCircle_add (x y : ℝ) : expMapCircle (x + y) = expMapCircle x * expMapCircle y :=
  Subtype.ext <| by
    simp only [expMapCircle_apply, Submonoid.coe_mul, ofReal_add, add_mul, Complex.exp_add]

/-- The map `fun t => exp (t * I)` from `ℝ` to the unit circle in `ℂ`,
considered as a homomorphism of groups. -/
@[simps]
def expMapCircleHom : ℝ →+ Additive circle where
  toFun := Additive.ofMul ∘ expMapCircle
  map_zero' := expMapCircle_zero
  map_add' := expMapCircle_add

@[simp]
theorem expMapCircle_sub (x y : ℝ) : expMapCircle (x - y) = expMapCircle x / expMapCircle y :=
  expMapCircleHom.map_sub x y

@[simp]
theorem expMapCircle_neg (x : ℝ) : expMapCircle (-x) = (expMapCircle x)⁻¹ :=
  expMapCircleHom.map_neg x

@[simp]
lemma norm_circle_smul {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (u : circle) (v : E) :
    ‖u • v‖ = ‖v‖ := by
  rw [Submonoid.smul_def, norm_smul, norm_eq_of_mem_sphere, one_mul]
