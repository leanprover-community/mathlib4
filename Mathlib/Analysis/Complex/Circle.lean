/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Field.UnitBall

/-!
# The circle

This file defines `circle` to be the metric sphere (`Metric.sphere`) in `ℂ` centred at `0` of
radius `1`.  We equip it with the following structure:

* a submonoid of `ℂ`
* a group
* a topological group

We furthermore define `Circle.exp` to be the natural map `fun t ↦ exp (t * I)` from `ℝ` to
`circle`, and show that this map is a group homomorphism.

We define two additive characters onto the circle:
* `Real.fourierChar`: The character `fun x ↦ exp ((2 * π * x) * I)` (for which we introduce the
  notation `𝐞` in the scope `FourierTransform`). This uses the analyst convention that there is a
  `2 * π` in the exponent.
* `Real.probChar`: The character `fun x ↦ exp (x * I)`, which uses the probabilist convention that
  there is no `2 * π` in the exponent.

## Implementation notes

Because later (in `Geometry.Manifold.Instances.Sphere`) one wants to equip the circle with a smooth
manifold structure borrowed from `Metric.sphere`, the underlying set is
`{z : ℂ | abs (z - 0) = 1}`.  This prevents certain algebraic facts from working definitionally --
for example, the circle is not defeq to `{z : ℂ | abs z = 1}`, which is the kernel of `Complex.abs`
considered as a homomorphism from `ℂ` to `ℝ`, nor is it defeq to `{z : ℂ | normSq z = 1}`, which
is the kernel of the homomorphism `Complex.normSq` from `ℂ` to `ℝ`.

-/


noncomputable section

open Complex Function Metric

open ComplexConjugate

/-- The unit circle in `ℂ`. -/
def Circle : Type := Submonoid.unitSphere ℂ
deriving TopologicalSpace

namespace Circle
variable {x y : Circle}

instance instCoeOut : CoeOut Circle ℂ := subtypeCoe

instance instCommGroup : CommGroup Circle := Metric.sphere.instCommGroup
instance instMetricSpace : MetricSpace Circle := Subtype.metricSpace

@[ext] lemma ext : (x : ℂ) = y → x = y := Subtype.ext

lemma coe_injective : Injective ((↑) : Circle → ℂ) := fun _ _ ↦ ext

-- Not simp because `SetLike.coe_eq_coe` already proves it
lemma coe_inj : (x : ℂ) = y ↔ x = y := coe_injective.eq_iff

lemma norm_coe (z : Circle) : ‖(z : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.1 z.2

@[simp] lemma normSq_coe (z : Circle) : normSq z = 1 := by simp [normSq_eq_norm_sq]
@[simp] lemma coe_ne_zero (z : Circle) : (z : ℂ) ≠ 0 := ne_zero_of_mem_unit_sphere z
@[simp, norm_cast] lemma coe_one : ↑(1 : Circle) = (1 : ℂ) := rfl
-- Not simp because `OneMemClass.coe_eq_one` already proves it
@[norm_cast] lemma coe_eq_one : (x : ℂ) = 1 ↔ x = 1 := by rw [← coe_inj, coe_one]
@[simp, norm_cast] lemma coe_mul (z w : Circle) : ↑(z * w) = (z : ℂ) * w := rfl
@[simp, norm_cast] lemma coe_inv (z : Circle) : ↑z⁻¹ = (z : ℂ)⁻¹ := rfl
lemma coe_inv_eq_conj (z : Circle) : ↑z⁻¹ = conj (z : ℂ) := by
  rw [coe_inv, inv_def, normSq_coe, inv_one, ofReal_one, mul_one]

@[simp, norm_cast] lemma coe_div (z w : Circle) : ↑(z / w) = (z : ℂ) / w := rfl

/-- The coercion `Circle → ℂ` as a monoid homomorphism. -/
@[simps]
def coeHom : Circle →* ℂ where
  toFun := (↑)
  map_one' := coe_one
  map_mul' := coe_mul

/-- The elements of the circle embed into the units. -/
def toUnits : Circle →* Units ℂ := unitSphereToUnits ℂ

-- written manually because `@[simps]` generated the wrong lemma
@[simp] lemma toUnits_apply (z : Circle) : toUnits z = Units.mk0 ↑z z.coe_ne_zero := rfl

instance : CompactSpace Circle := Metric.sphere.compactSpace _ _
instance : IsTopologicalGroup Circle := Metric.sphere.instIsTopologicalGroup
instance instUniformSpace : UniformSpace Circle := instUniformSpaceSubtype
instance : IsUniformGroup Circle := inferInstance

/-- If `z` is a nonzero complex number, then `conj z / z` belongs to the unit circle. -/
@[simps]
def ofConjDivSelf (z : ℂ) (hz : z ≠ 0) : Circle where
  val := conj z / z
  property := mem_sphere_zero_iff_norm.2 <| by
    rw [norm_div, RCLike.norm_conj, div_self]; exact norm_ne_zero_iff.mpr hz

/-- The map `fun t => exp (t * I)` from `ℝ` to the unit circle in `ℂ`. -/
def exp : C(ℝ, Circle) where
  toFun t := ⟨(t * I).exp, by simp [Submonoid.unitSphere, exp_mul_I, norm_cos_add_sin_mul_I]⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop)
    (by simp [Submonoid.unitSphere, exp_mul_I, norm_cos_add_sin_mul_I])

@[simp, norm_cast]
theorem coe_exp (t : ℝ) : exp t = Complex.exp (t * Complex.I) := rfl

@[simp]
theorem exp_zero : exp 0 = 1 :=
  Subtype.ext <| by rw [coe_exp, ofReal_zero, zero_mul, Complex.exp_zero, coe_one]

@[simp]
theorem exp_add (x y : ℝ) : exp (x + y) = exp x * exp y :=
  Subtype.ext <| by
    simp only [coe_exp, ofReal_add, add_mul, Complex.exp_add, coe_mul]

/-- The map `fun t => exp (t * I)` from `ℝ` to the unit circle in `ℂ`,
considered as a homomorphism of groups. -/
@[simps]
def expHom : ℝ →+ Additive Circle where
  toFun := Additive.ofMul ∘ exp
  map_zero' := exp_zero
  map_add' := exp_add

@[simp] lemma exp_sub (x y : ℝ) : exp (x - y) = exp x / exp y := expHom.map_sub x y
@[simp] lemma exp_neg (x : ℝ) : exp (-x) = (exp x)⁻¹ := expHom.map_neg x

lemma exp_pi_ne_one : Circle.exp Real.pi ≠ 1 := by
  intro h
  have heq : (Circle.exp Real.pi : ℂ) = 1 := by simp [h]
  rw [Circle.coe_exp, exp_pi_mul_I] at heq
  norm_num at heq

variable {e : AddChar ℝ Circle}

@[simp]
lemma star_addChar (x : ℝ) : star ((e x) : ℂ) = e (-x) := by
  have h := Circle.coe_inv_eq_conj ⟨e x, ?_⟩
  · simp [← h, e.map_neg_eq_inv]
  · simp only [Submonoid.unitSphere, SetLike.coe_mem]

@[simp]
lemma starRingEnd_addChar (x : ℝ) : starRingEnd ℂ (e x) = e (-x) := star_addChar x

variable {α β M : Type*}

instance instSMul [SMul ℂ α] : SMul Circle α := Submonoid.smul _

instance instSMulCommClass_left [SMul ℂ β] [SMul α β] [SMulCommClass ℂ α β] :
    SMulCommClass Circle α β := Submonoid.smulCommClass_left _

instance instSMulCommClass_right [SMul ℂ β] [SMul α β] [SMulCommClass α ℂ β] :
    SMulCommClass α Circle β := Submonoid.smulCommClass_right _

instance instIsScalarTower [SMul ℂ α] [SMul ℂ β] [SMul α β] [IsScalarTower ℂ α β] :
    IsScalarTower Circle α β := Submonoid.isScalarTower _

instance instMulAction [MulAction ℂ α] : MulAction Circle α := Submonoid.mulAction _

instance instDistribMulAction [AddMonoid M] [DistribMulAction ℂ M] :
    DistribMulAction Circle M := Submonoid.distribMulAction _

lemma smul_def [SMul ℂ α] (z : Circle) (a : α) : z • a = (z : ℂ) • a := rfl

instance instContinuousSMul [TopologicalSpace α] [MulAction ℂ α] [ContinuousSMul ℂ α] :
    ContinuousSMul Circle α := Submonoid.continuousSMul

@[simp]
protected lemma norm_smul {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (u : Circle) (v : E) :
    ‖u • v‖ = ‖v‖ := by
  rw [Submonoid.smul_def, norm_smul, norm_eq_of_mem_sphere, one_mul]

end Circle

namespace Real

/-- The additive character from `ℝ` onto the circle, given by `fun x ↦ exp (2 * π * x * I)`.
Denoted as `𝐞` within the `Real.FourierTransform` namespace. This uses the analyst convention that
there is a `2 * π` in the exponent. -/
def fourierChar : AddChar ℝ Circle where
  toFun z := .exp (2 * π * z)
  map_zero_eq_one' := by rw [mul_zero, Circle.exp_zero]
  map_add_eq_mul' x y := by rw [mul_add, Circle.exp_add]

@[inherit_doc] scoped[FourierTransform] notation "𝐞" => Real.fourierChar

open FourierTransform

theorem fourierChar_apply' (x : ℝ) : 𝐞 x = Circle.exp (2 * π * x) := rfl

theorem fourierChar_apply (x : ℝ) : 𝐞 x = Complex.exp (↑(2 * π * x) * Complex.I) := rfl

@[continuity]
theorem continuous_fourierChar : Continuous 𝐞 := Circle.exp.continuous.comp (continuous_mul_left _)

theorem fourierChar_ne_one : fourierChar ≠ 1 := by
  rw [DFunLike.ne_iff]
  use 2⁻¹
  simp only [fourierChar_apply', AddChar.one_apply]
  rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  exact Circle.exp_pi_ne_one

/-- The additive character from `ℝ` onto the circle, given by `fun x ↦ exp (x * I)`. This uses the
probabilist convention that there is no `2 * π` in the exponent. -/
def probChar : AddChar ℝ Circle where
  toFun := Circle.exp
  map_zero_eq_one' := Circle.exp_zero
  map_add_eq_mul' := Circle.exp_add

theorem probChar_apply' (x : ℝ) : probChar x = Circle.exp x := rfl

theorem probChar_apply (x : ℝ) : probChar x = Complex.exp (x * Complex.I) := rfl

@[continuity]
theorem continuous_probChar : Continuous probChar := Circle.exp.continuous

theorem probChar_ne_one : probChar ≠ 1 := by
  rw [DFunLike.ne_iff]
  use Real.pi
  simpa only [probChar_apply'] using Circle.exp_pi_ne_one

end Real
