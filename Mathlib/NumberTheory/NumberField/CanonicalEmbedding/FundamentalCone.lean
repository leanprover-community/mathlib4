/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.Ideal.IsPrincipal
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.ClassGroup
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike

/-!
# Fundamental Cone

Let `K` be a number field of signature `(r₁, r₂)`. We define an action of the units `(𝓞 K)ˣ` on
the mixed space `ℝ^r₁ × ℂ^r₂` via the `mixedEmbedding`. The fundamental cone is a cone in the
mixed space that is a fundamental domain for the action of `(𝓞 K)ˣ` modulo torsion.

## Main definitions and results

* `NumberField.mixedEmbedding.unitSMul`: the action of `(𝓞 K)ˣ` on the mixed space defined, for
  `u : (𝓞 K)ˣ`, by multiplication component by component with `mixedEmbedding K u`.

* `NumberField.mixedEmbedding.fundamentalCone`: a cone in the mixed space, i.e. a subset stable
  by multiplication by a nonzero real number, see `smul_mem_of_mem`, that is also a fundamental
  domain for the action of `(𝓞 K)ˣ` modulo torsion, see `exists_unit_smul_mem` and
  `torsion_unit_smul_mem_of_mem`.

* `NumberField.mixedEmbedding.fundamentalCone.idealSet`: for `J` an integral ideal, the intersection
  between the fundamental cone and the `idealLattice` defined by the image of `J`.

* `NumberField.mixedEmbedding.fundamentalCone.idealSetEquivNorm`: for `J` an integral ideal and `n`
  a natural integer, the equivalence between the elements of `idealSet K` of norm `n` and the
  product of the set of nonzero principal ideals of `K` divisible by `J` of norm `n` and the
  torsion of `K`.

## Tags

number field, canonical embedding, units, principal ideals
-/

@[expose] public section

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace

noncomputable section UnitSMul

/-- The action of `(𝓞 K)ˣ` on the mixed space `ℝ^r₁ × ℂ^r₂` defined, for `u : (𝓞 K)ˣ`, by
multiplication component by component with `mixedEmbedding K u`. -/
@[simps]
instance unitSMul : SMul (𝓞 K)ˣ (mixedSpace K) where
  smul u x := mixedEmbedding K u * x

instance : MulAction (𝓞 K)ˣ (mixedSpace K) where
  one_smul := fun _ ↦ by simp_rw [unitSMul_smul, Units.coe_one, map_one, one_mul]
  mul_smul := fun _ _ _ ↦ by simp_rw [unitSMul_smul, Units.coe_mul, map_mul, mul_assoc]

instance : SMulZeroClass (𝓞 K)ˣ (mixedSpace K) where
  smul_zero := fun _ ↦ by simp_rw [unitSMul_smul, mul_zero]

variable {K}

theorem unit_smul_eq_zero (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    u • x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, smul_zero]⟩
  contrapose! h
  obtain ⟨w, h⟩ := exists_normAtPlace_ne_zero_iff.mpr h
  refine exists_normAtPlace_ne_zero_iff.mp ⟨w, ?_⟩
  rw [unitSMul_smul, map_mul]
  exact mul_ne_zero (by simp) h

variable [NumberField K]

theorem unit_smul_eq_iff_mul_eq {x y : 𝓞 K} {u : (𝓞 K)ˣ} :
    u • mixedEmbedding K x = mixedEmbedding K y ↔ u * x = y := by
  rw [unitSMul_smul, ← map_mul, Function.Injective.eq_iff, ← RingOfIntegers.coe_eq_algebraMap,
    ← map_mul, ← RingOfIntegers.ext_iff]
  exact mixedEmbedding_injective K

theorem norm_unit_smul (u : (𝓞 K)ˣ) (x : mixedSpace K) :
    mixedEmbedding.norm (u • x) = mixedEmbedding.norm x := by
  rw [unitSMul_smul, map_mul, norm_unit, one_mul]

end UnitSMul

noncomputable section logMap

open NumberField.Units NumberField.Units.dirichletUnitTheorem Module

variable [NumberField K] {K}

open Classical in
/-- The map from the mixed space to `logSpace K` defined in such way that: 1) it factors the map
`logEmbedding`, see `logMap_eq_logEmbedding`; 2) it is constant on the sets
`{c • x | c ∈ ℝ, c ≠ 0}` if `norm x ≠ 0`, see `logMap_real_smul`. -/
def logMap (x : mixedSpace K) : logSpace K := fun w ↦
  mult w.val * (Real.log (normAtPlace w.val x) -
    Real.log (mixedEmbedding.norm x) * (finrank ℚ K : ℝ)⁻¹)

@[simp]
theorem logMap_apply (x : mixedSpace K) (w : {w : InfinitePlace K // w ≠ w₀}) :
    logMap x w = mult w.val * (Real.log (normAtPlace w.val x) -
      Real.log (mixedEmbedding.norm x) * (finrank ℚ K : ℝ)⁻¹) := rfl

@[simp]
theorem logMap_zero : logMap (0 : mixedSpace K) = 0 := by
  ext; simp

@[simp]
theorem logMap_one : logMap (1 : mixedSpace K) = 0 := by
  ext; simp

variable {x y : mixedSpace K}

theorem logMap_mul (hx : mixedEmbedding.norm x ≠ 0) (hy : mixedEmbedding.norm y ≠ 0) :
    logMap (x * y) = logMap x + logMap y := by
  ext w
  simp_rw [Pi.add_apply, logMap_apply]
  rw [map_mul, map_mul, Real.log_mul, Real.log_mul hx hy, add_mul]
  · ring
  · exact mixedEmbedding.norm_ne_zero_iff.mp hx w
  · exact mixedEmbedding.norm_ne_zero_iff.mp hy w

theorem logMap_apply_of_norm_eq_one (hx : mixedEmbedding.norm x = 1)
    (w : {w : InfinitePlace K // w ≠ w₀}) :
    logMap x w = mult w.val * Real.log (normAtPlace w x) := by
  rw [logMap_apply, hx, Real.log_one, zero_mul, sub_zero]

@[deprecated (since := "2025-11-15")] alias logMap_apply_of_norm_one := logMap_apply_of_norm_eq_one

@[simp]
theorem logMap_eq_logEmbedding (u : (𝓞 K)ˣ) :
    logMap (mixedEmbedding K u) = logEmbedding K (Additive.ofMul u) := by
  ext; simp

theorem logMap_unit_smul (u : (𝓞 K)ˣ) (hx : mixedEmbedding.norm x ≠ 0) :
    logMap (u • x) = logEmbedding K (Additive.ofMul u) + logMap x := by
  rw [unitSMul_smul, logMap_mul (by rw [norm_unit]; norm_num) hx, logMap_eq_logEmbedding]

variable (x) in
theorem logMap_torsion_smul {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) :
    logMap (ζ • x) = logMap x := by
  ext
  simp_rw [logMap_apply, unitSMul_smul, map_mul, norm_eq_norm, Units.norm, Rat.cast_one, one_mul,
    normAtPlace_apply, (mem_torsion K).mp hζ, one_mul]

theorem logMap_real (c : ℝ) :
    logMap (c • (1 : mixedSpace K)) = 0 := by
  ext
  rw [logMap_apply, normAtPlace_smul, norm_smul, map_one, map_one, mul_one, mul_one, Real.log_pow,
    mul_comm (finrank ℚ K : ℝ) _, mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr finrank_pos.ne'),
    mul_one, sub_self, mul_zero, Pi.zero_apply]

theorem logMap_real_smul (hx : mixedEmbedding.norm x ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    logMap (c • x) = logMap x := by
  have : mixedEmbedding.norm (c • (1 : mixedSpace K)) ≠ 0 := by
    rw [norm_smul, map_one, mul_one]
    exact pow_ne_zero _ (abs_ne_zero.mpr hc)
  rw [← smul_one_mul, logMap_mul this hx, logMap_real, zero_add]

theorem logMap_eq_of_normAtPlace_eq (h : ∀ w, normAtPlace w x = normAtPlace w y) :
    logMap x = logMap y := by
  ext
  simp_rw [logMap_apply, h, norm_eq_of_normAtPlace_eq h]

end logMap

noncomputable section

open NumberField.Units NumberField.Units.dirichletUnitTheorem

variable [NumberField K]

open Classical in
/-- The fundamental cone is a cone in the mixed space, i.e. a subset fixed by multiplication by
a nonzero real number, see `smul_mem_of_mem`, that is also a fundamental domain for the action
of `(𝓞 K)ˣ` modulo torsion, see `exists_unit_smul_mem` and `torsion_smul_mem_of_mem`. -/
def fundamentalCone : Set (mixedSpace K) :=
  logMap ⁻¹' (ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ _)) \
      {x | mixedEmbedding.norm x = 0}

theorem measurableSet_fundamentalCone :
    MeasurableSet (fundamentalCone K) := by
  classical
  refine MeasurableSet.diff ?_ ?_
  · unfold logMap
    refine MeasurableSet.preimage (ZSpan.fundamentalDomain_measurableSet _) <|
      measurable_pi_iff.mpr fun w ↦ measurable_const.mul ?_
    exact (continuous_normAtPlace _).measurable.log.sub <|
      (mixedEmbedding.continuous_norm _).measurable.log.mul measurable_const
  · exact measurableSet_eq_fun (mixedEmbedding.continuous_norm K).measurable measurable_const

namespace fundamentalCone

variable {K} {x y : mixedSpace K} {c : ℝ}

theorem norm_pos_of_mem (hx : x ∈ fundamentalCone K) :
    0 < mixedEmbedding.norm x :=
  lt_of_le_of_ne (mixedEmbedding.norm_nonneg _) (Ne.symm hx.2)

theorem normAtPlace_pos_of_mem (hx : x ∈ fundamentalCone K) (w : InfinitePlace K) :
    0 < normAtPlace w x :=
  lt_of_le_of_ne (normAtPlace_nonneg _ _)
    (mixedEmbedding.norm_ne_zero_iff.mp (norm_pos_of_mem hx).ne' w).symm

theorem mem_of_normAtPlace_eq (hx : x ∈ fundamentalCone K)
    (hy : ∀ w, normAtPlace w y = normAtPlace w x) :
    y ∈ fundamentalCone K := by
  refine ⟨?_, by simpa [norm_eq_of_normAtPlace_eq hy] using hx.2⟩
  rw [Set.mem_preimage, logMap_eq_of_normAtPlace_eq hy]
  exact hx.1

theorem smul_mem_of_mem (hx : x ∈ fundamentalCone K) (hc : c ≠ 0) :
    c • x ∈ fundamentalCone K := by
  refine ⟨?_, ?_⟩
  · rw [Set.mem_preimage, logMap_real_smul hx.2 hc]
    exact hx.1
  · rw [Set.mem_setOf_eq, mixedEmbedding.norm_smul, mul_eq_zero, not_or]
    exact ⟨pow_ne_zero _ (abs_ne_zero.mpr hc), hx.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem smul_mem_iff_mem (hc : c ≠ 0) :
    c • x ∈ fundamentalCone K ↔ x ∈ fundamentalCone K := by
  refine ⟨fun h ↦ ?_, fun h ↦ smul_mem_of_mem h hc⟩
  convert smul_mem_of_mem h (inv_ne_zero hc)
  rw [eq_inv_smul_iff₀ hc]

theorem exists_unit_smul_mem (hx : mixedEmbedding.norm x ≠ 0) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ fundamentalCone K := by
  classical
  let B := (basisUnitLattice K).ofZLatticeBasis ℝ
  rsuffices ⟨⟨_, ⟨u, _, rfl⟩⟩, hu⟩ : ∃ e : unitLattice K, e + logMap x ∈ ZSpan.fundamentalDomain B
  · exact ⟨u, by rwa [Set.mem_preimage, logMap_unit_smul u hx], by simp [hx]⟩
  · obtain ⟨⟨e, h₁⟩, h₂, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)
    exact ⟨⟨e, by rwa [← Module.Basis.ofZLatticeBasis_span ℝ (unitLattice K)]⟩, h₂⟩

theorem torsion_smul_mem_of_mem (hx : x ∈ fundamentalCone K) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) :
    ζ • x ∈ fundamentalCone K := by
  constructor
  · rw [Set.mem_preimage, logMap_torsion_smul _ hζ]
    exact hx.1
  · rw [Set.mem_setOf_eq, unitSMul_smul, map_mul, norm_unit, one_mul]
    exact hx.2

theorem unit_smul_mem_iff_mem_torsion (hx : x ∈ fundamentalCone K) (u : (𝓞 K)ˣ) :
    u • x ∈ fundamentalCone K ↔ u ∈ torsion K := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ torsion_smul_mem_of_mem hx h⟩
  rw [← logEmbedding_eq_zero_iff]
  let B := (basisUnitLattice K).ofZLatticeBasis ℝ
  refine (Subtype.mk_eq_mk (h := ?_) (h' := Submodule.zero_mem _)).mp <|
    (ZSpan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)).unique ?_ ?_
  · rw [Module.Basis.ofZLatticeBasis_span ℝ (unitLattice K)]
    exact ⟨u, trivial, rfl⟩
  · rw [AddSubmonoid.mk_vadd, vadd_eq_add, ← logMap_unit_smul _ hx.2]
    exact h.1
  · rw [AddSubmonoid.mk_vadd, vadd_eq_add, zero_add]
    exact hx.1

variable (K) in
/-- The intersection between the fundamental cone and the `integerLattice`. -/
def integerSet : Set (mixedSpace K) :=
  fundamentalCone K ∩ mixedEmbedding.integerLattice K

theorem mem_integerSet {a : mixedSpace K} :
    a ∈ integerSet K ↔ a ∈ fundamentalCone K ∧ ∃ x : 𝓞 K, mixedEmbedding K x = a := by
  simp only [integerSet, Set.mem_inter_iff, SetLike.mem_coe, LinearMap.mem_range,
    AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe, RingHom.coe_comp, Function.comp_apply]

/-- If `a` is in `integerSet`, then there is a *unique* algebraic integer in `𝓞 K` such
that `mixedEmbedding K x = a`. -/
theorem existsUnique_preimage_of_mem_integerSet {a : mixedSpace K} (ha : a ∈ integerSet K) :
    ∃! x : 𝓞 K, mixedEmbedding K x = a := by
  obtain ⟨_, ⟨x, rfl⟩⟩ := mem_integerSet.mp ha
  refine Function.Injective.existsUnique_of_mem_range ?_ (Set.mem_range_self x)
  exact (mixedEmbedding_injective K).comp RingOfIntegers.coe_injective

theorem ne_zero_of_mem_integerSet (a : integerSet K) : (a : mixedSpace K) ≠ 0 := by
  by_contra!
  exact a.prop.1.2 (this.symm ▸ mixedEmbedding.norm.map_zero')

open scoped nonZeroDivisors

/-- For `a : integerSet K`, the unique nonzero algebraic integer `x` such that its image by
`mixedEmbedding` is equal to `a`. Note that we state the fact that `x ≠ 0` by saying that `x` is
a nonzero divisors since we will use later on the isomorphism
`Ideal.associatesNonZeroDivisorsEquivIsPrincipal`, see `integerSetEquiv`. -/
def preimageOfMemIntegerSet (a : integerSet K) : (𝓞 K)⁰ :=
  ⟨(mem_integerSet.mp a.prop).2.choose, mem_nonZeroDivisors_of_ne_zero (by
  simp_rw [ne_eq, ← RingOfIntegers.coe_injective.eq_iff, ← (mixedEmbedding_injective K).eq_iff,
    map_zero, (mem_integerSet.mp a.prop).2.choose_spec, ne_zero_of_mem_integerSet,
    not_false_eq_true])⟩

@[simp]
theorem mixedEmbedding_preimageOfMemIntegerSet (a : integerSet K) :
    mixedEmbedding K (preimageOfMemIntegerSet a : 𝓞 K) = (a : mixedSpace K) := by
  rw [preimageOfMemIntegerSet, (mem_integerSet.mp a.prop).2.choose_spec]

theorem preimageOfMemIntegerSet_mixedEmbedding {x : (𝓞 K)}
    (hx : mixedEmbedding K (x : 𝓞 K) ∈ integerSet K) :
    preimageOfMemIntegerSet (⟨mixedEmbedding K (x : 𝓞 K), hx⟩) = x := by
  simp_rw [RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    mixedEmbedding_preimageOfMemIntegerSet]

/-- If `x : mixedSpace K` is nonzero and the image of an algebraic integer, then there exists a
unit such that `u • x ∈ integerSet K`. -/
theorem exists_unitSMul_mem_integerSet {x : mixedSpace K} (hx : x ≠ 0)
    (hx' : x ∈ mixedEmbedding K '' (Set.range (algebraMap (𝓞 K) K))) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ integerSet K := by
  replace hx : mixedEmbedding.norm x ≠ 0 :=
      (norm_eq_zero_iff' (Set.mem_range_of_mem_image (mixedEmbedding K) _ hx')).not.mpr hx
  obtain ⟨u, hu⟩ := exists_unit_smul_mem hx
  obtain ⟨_, ⟨x, rfl⟩, _, rfl⟩ := hx'
  exact ⟨u, mem_integerSet.mpr ⟨hu, u * x, by simp_rw [unitSMul_smul, ← map_mul]⟩⟩

/-- The set `integerSet K` is stable under the action of the torsion. -/
theorem torsion_unitSMul_mem_integerSet {x : mixedSpace K} {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K)
    (hx : x ∈ integerSet K) : ζ • x ∈ integerSet K := by
  obtain ⟨a, ⟨_, rfl⟩, rfl⟩ := (mem_integerSet.mp hx).2
  refine mem_integerSet.mpr ⟨torsion_smul_mem_of_mem hx.1 hζ, ⟨ζ * a, by simp⟩⟩

/-- The action of `torsion K` on `integerSet K`. -/
@[simps]
instance integerSetTorsionSMul : SMul (torsion K) (integerSet K) where
  smul := fun ⟨ζ, hζ⟩ ⟨x, hx⟩ ↦ ⟨ζ • x, torsion_unitSMul_mem_integerSet hζ hx⟩

instance : MulAction (torsion K) (integerSet K) where
  one_smul := fun _ ↦ by
    rw [Subtype.mk_eq_mk, integerSetTorsionSMul_smul_coe, OneMemClass.coe_one, one_smul]
  mul_smul := fun _ _ _ ↦ by
    rw [Subtype.mk_eq_mk]
    simp_rw [integerSetTorsionSMul_smul_coe, Subgroup.coe_mul, mul_smul]

/-- The `mixedEmbedding.norm` of `a : integerSet K` as a natural number, see also
`intNorm_coe`. -/
def intNorm (a : integerSet K) : ℕ := (Algebra.norm ℤ (preimageOfMemIntegerSet a : 𝓞 K)).natAbs

@[simp]
theorem intNorm_coe (a : integerSet K) :
    (intNorm a : ℝ) = mixedEmbedding.norm (a : mixedSpace K) := by
  rw [intNorm, Nat.cast_natAbs, ← Rat.cast_intCast, Int.cast_abs, Algebra.coe_norm_int,
    ← norm_eq_norm, mixedEmbedding_preimageOfMemIntegerSet]

/-- The norm `intNorm` lifts to a function on `integerSet K` modulo `torsion K`. -/
def quotIntNorm :
    Quotient (MulAction.orbitRel (torsion K) (integerSet K)) → ℕ :=
  Quotient.lift (fun x ↦ intNorm x) fun a b ⟨u, hu⟩ ↦ by
    rw [← Nat.cast_inj (R := ℝ), intNorm_coe, intNorm_coe, ← hu, integerSetTorsionSMul_smul_coe,
      norm_unit_smul]

@[simp]
theorem quotIntNorm_apply (a : integerSet K) : quotIntNorm ⟦a⟧ = intNorm a := rfl

variable (K) in
/-- The map that sends an element of `a : integerSet K` to the associates class
of its preimage in `(𝓞 K)⁰`. By quotienting by the kernel of the map, which is equal to the
subgroup of torsion, we get the equivalence `integerSetQuotEquivAssociates`. -/
def integerSetToAssociates (a : integerSet K) : Associates (𝓞 K)⁰ :=
  ⟦preimageOfMemIntegerSet a⟧

@[simp]
theorem integerSetToAssociates_apply (a : integerSet K) :
    integerSetToAssociates K a = ⟦preimageOfMemIntegerSet a⟧ := rfl

variable (K) in
theorem integerSetToAssociates_surjective :
    Function.Surjective (integerSetToAssociates K) := by
  rintro ⟨x⟩
  obtain ⟨u, hu⟩ : ∃ u : (𝓞 K)ˣ, u • mixedEmbedding K (x : 𝓞 K) ∈ integerSet K := by
    refine exists_unitSMul_mem_integerSet ?_ ⟨(x : 𝓞 K), Set.mem_range_self _, rfl⟩
    exact (map_ne_zero _).mpr <| RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.coe_ne_zero _)
  refine ⟨⟨u • mixedEmbedding K (x : 𝓞 K), hu⟩,
    Quotient.sound ⟨unitsNonZeroDivisorsEquiv.symm u⁻¹, ?_⟩⟩
  simp_rw [Subtype.ext_iff, RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff,
    Submonoid.coe_mul, map_mul, mixedEmbedding_preimageOfMemIntegerSet,
    unitSMul_smul, ← map_mul, mul_comm, map_inv, val_inv_unitsNonZeroDivisorsEquiv_symm_apply_coe,
    Units.mul_inv_cancel_right]

theorem integerSetToAssociates_eq_iff (a b : integerSet K) :
    integerSetToAssociates K a = integerSetToAssociates K b ↔
      ∃ ζ : torsion K, ζ • a = b := by
  simp_rw [integerSetToAssociates_apply, Associates.quotient_mk_eq_mk,
    Associates.mk_eq_mk_iff_associated, Associated, mul_comm, Subtype.ext_iff,
    RingOfIntegers.ext_iff, ← (mixedEmbedding_injective K).eq_iff, Submonoid.coe_mul, map_mul,
    mixedEmbedding_preimageOfMemIntegerSet, integerSetTorsionSMul_smul_coe]
  refine ⟨fun ⟨u, h⟩ ↦  ⟨⟨unitsNonZeroDivisorsEquiv u, ?_⟩, by simpa using h⟩,
    fun ⟨⟨u, _⟩, h⟩ ↦ ⟨unitsNonZeroDivisorsEquiv.symm u, by simpa using h⟩⟩
  exact (unit_smul_mem_iff_mem_torsion a.prop.1 _).mp (by simpa [h] using b.prop.1)

variable (K) in
/-- The equivalence between `integerSet K` modulo `torsion K` and `Associates (𝓞 K)⁰`. -/
def integerSetQuotEquivAssociates :
    Quotient (MulAction.orbitRel (torsion K) (integerSet K)) ≃ Associates (𝓞 K)⁰ :=
  Equiv.ofBijective
    (Quotient.lift (integerSetToAssociates K)
      fun _ _ h ↦ ((integerSetToAssociates_eq_iff _ _).mpr h).symm)
    ⟨Setoid.lift_injective_iff_ker_eq_of_le _ |>.mpr <| by
        ext a b
        rw [Setoid.ker_def, eq_comm, integerSetToAssociates_eq_iff b a,
          MulAction.orbitRel_apply, MulAction.mem_orbit_iff],
        (Quot.surjective_lift _).mpr (integerSetToAssociates_surjective K)⟩

@[simp]
theorem integerSetQuotEquivAssociates_apply (a : integerSet K) :
    integerSetQuotEquivAssociates K ⟦a⟧ = ⟦preimageOfMemIntegerSet a⟧ := rfl

theorem integerSetTorsionSMul_stabilizer (a : integerSet K) :
    MulAction.stabilizer (torsion K) a = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun ζ hζ ↦ ?_
  rwa [MulAction.mem_stabilizer_iff, Subtype.ext_iff, integerSetTorsionSMul_smul_coe,
    unitSMul_smul, ← mixedEmbedding_preimageOfMemIntegerSet, ← map_mul,
    (mixedEmbedding_injective K).eq_iff, ← map_mul, ← RingOfIntegers.ext_iff, mul_eq_right₀,
    Units.val_eq_one, OneMemClass.coe_eq_one] at hζ
  exact nonZeroDivisors.coe_ne_zero _

open Submodule Ideal

variable (K) in
/-- The equivalence between `integerSet K` and the product of the set of nonzero principal
ideals of `K` and the torsion of `K`. -/
def integerSetEquiv :
    integerSet K ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val} × torsion K :=
  (MulAction.selfEquivSigmaOrbitsQuotientStabilizer (torsion K) (integerSet K)).trans
    ((Equiv.sigmaEquivProdOfEquiv (by
        intro _
        simp_rw [integerSetTorsionSMul_stabilizer]
        exact QuotientGroup.quotientBot.toEquiv)).trans
      (Equiv.prodCongrLeft (fun _ ↦ (integerSetQuotEquivAssociates K).trans
        (Ideal.associatesNonZeroDivisorsEquivIsPrincipal (𝓞 K)))))

@[simp]
theorem integerSetEquiv_apply_fst (a : integerSet K) :
    ((integerSetEquiv K a).1 : Ideal (𝓞 K)) = span {(preimageOfMemIntegerSet a : 𝓞 K)} := rfl

variable (K) in
/-- For an integer `n`, The equivalence between the elements of `integerSet K` of norm `n`
and the product of the set of nonzero principal ideals of `K` of norm `n` and the torsion of `K`. -/
def integerSetEquivNorm (n : ℕ) :
    {a : integerSet K // mixedEmbedding.norm (a : mixedSpace K) = n} ≃
      {I : (Ideal (𝓞 K))⁰ // IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) :=
  calc
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} × torsion K //
          absNorm (I.1 : Ideal (𝓞 K)) = n} :=
      Equiv.subtypeEquiv (integerSetEquiv K) fun _ ↦ by simp_rw [← intNorm_coe, intNorm,
        Nat.cast_inj, integerSetEquiv_apply_fst, absNorm_span_singleton]
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} // absNorm (I.1 : Ideal (𝓞 K)) = n} ×
          torsion K := Equiv.prodSubtypeFstEquivSubtypeProd
      (p := fun I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1} ↦ absNorm (I : Ideal (𝓞 K)) = n)
    _ ≃ {I : (Ideal (𝓞 K))⁰ // IsPrincipal (I : Ideal (𝓞 K)) ∧
          absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) := Equiv.prodCongrLeft fun _ ↦
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal (𝓞 K))⁰ ↦ IsPrincipal I.1) (fun I ↦ absNorm I.1 = n))

@[simp]
theorem integerSetEquivNorm_apply_fst {n : ℕ}
    (a : {a : integerSet K // mixedEmbedding.norm (a : mixedSpace K) = n}) :
    ((integerSetEquivNorm K n a).1 : Ideal (𝓞 K)) =
      span {(preimageOfMemIntegerSet a.val : 𝓞 K)} := by
  simp_rw [integerSetEquivNorm, Equiv.prodSubtypeFstEquivSubtypeProd, Equiv.trans_def,
    Equiv.prodCongrLeft, Equiv.trans_apply, Equiv.subtypeEquiv_apply, Equiv.coe_fn_mk,
    Equiv.subtypeSubtypeEquivSubtypeInter_apply_coe, integerSetEquiv_apply_fst]

variable (K)

/-- For `n` positive, the number of principal ideals in `𝓞 K` of norm `n` multiplied by the order
of the torsion of `K` is equal to the number of elements in `integerSet K` of norm `n`. -/
theorem card_isPrincipal_norm_eq_mul_torsion (n : ℕ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ | IsPrincipal (I : Ideal (𝓞 K)) ∧
      absNorm (I : Ideal (𝓞 K)) = n} * torsionOrder K =
        Nat.card {a : integerSet K | mixedEmbedding.norm (a : mixedSpace K) = n} := by
  rw [torsionOrder, ← Nat.card_eq_fintype_card, ← Nat.card_prod]
  exact Nat.card_congr (integerSetEquivNorm K n).symm

variable (J : (Ideal (𝓞 K))⁰)

/-- The intersection between the fundamental cone and the `idealLattice` defined by the image of
the integral ideal `J`. -/
def idealSet : Set (mixedSpace K) :=
  fundamentalCone K ∩ (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))

variable {K J} in
theorem mem_idealSet :
    x ∈ idealSet K J ↔ x ∈ fundamentalCone K ∧ ∃ a : (𝓞 K), (a : 𝓞 K) ∈ (J : Set (𝓞 K)) ∧
      mixedEmbedding K (a : 𝓞 K) = x := by
  simp_rw [idealSet, Set.mem_inter_iff, idealLattice, SetLike.mem_coe, FractionalIdeal.coe_mk0,
    LinearMap.mem_range, LinearMap.coe_comp, LinearMap.coe_restrictScalars, coe_subtype,
    Function.comp_apply, AlgHom.toLinearMap_apply, RingHom.toIntAlgHom_coe, Subtype.exists,
    FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal, exists_prop', nonempty_prop,
    exists_exists_and_eq_and]

/-- The map that sends `a : idealSet` to an element of `integerSet`. This map exists because
`J` is an integral ideal. -/
def idealSetMap : idealSet K J → integerSet K :=
  fun ⟨a, ha⟩ ↦ ⟨a, mem_integerSet.mpr ⟨(mem_idealSet.mp ha).1, (mem_idealSet.mp ha).2.choose,
    (mem_idealSet.mp ha).2.choose_spec.2⟩⟩

@[simp]
theorem idealSetMap_apply (a : idealSet K J) : (idealSetMap K J a : mixedSpace K) = a := rfl

theorem preimage_of_IdealSetMap (a : idealSet K J) :
    (preimageOfMemIntegerSet (idealSetMap K J a) : 𝓞 K) ∈ (J : Set (𝓞 K)) := by
  obtain ⟨_, ⟨x, hx₁, hx₂⟩⟩ := mem_idealSet.mp a.prop
  simp_rw [idealSetMap, ← hx₂, preimageOfMemIntegerSet_mixedEmbedding]
  exact hx₁

/-- The map `idealSetMap` is actually an equiv between `idealSet K J` and the elements of
`integerSet K` whose preimage lies in `J`. -/
def idealSetEquiv : idealSet K J ≃
    {a : integerSet K | (preimageOfMemIntegerSet a : 𝓞 K) ∈ (J : Set (𝓞 K))} :=
  Equiv.ofBijective (fun a ↦ ⟨idealSetMap K J a, preimage_of_IdealSetMap K J a⟩)
    ⟨fun _ _ h ↦ (by
        simp_rw [Subtype.ext_iff, idealSetMap_apply] at h
        rwa [Subtype.ext_iff]),
    fun ⟨a, ha₂⟩ ↦ ⟨⟨a.val, mem_idealSet.mpr ⟨a.prop.1,
        ⟨preimageOfMemIntegerSet a, ha₂, mixedEmbedding_preimageOfMemIntegerSet a⟩⟩⟩, rfl⟩⟩

variable {K J}

theorem idealSetEquiv_apply (a : idealSet K J) :
    (idealSetEquiv K J a : mixedSpace K) = a := rfl

theorem idealSetEquiv_symm_apply
    (a : {a : integerSet K // (preimageOfMemIntegerSet a : 𝓞 K) ∈ (J : Set (𝓞 K)) }) :
    ((idealSetEquiv K J).symm a : mixedSpace K) = a := by
  rw [← (idealSetEquiv_apply ((idealSetEquiv K J).symm a)), Equiv.apply_symm_apply]

theorem intNorm_idealSetEquiv_apply (a : idealSet K J) :
    intNorm (idealSetEquiv K J a).val = mixedEmbedding.norm (a : mixedSpace K) := by
  rw [intNorm_coe, idealSetEquiv_apply]

variable (K J)

set_option backward.isDefEq.respectTransparency false in
/-- For an integer `n`, The equivalence between the elements of `idealSet K` of norm `n` and
the product of the set of nonzero principal ideals of `K` divisible by `J` of norm `n` and the
torsion of `K`. -/
def idealSetEquivNorm (n : ℕ) :
    {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = n} ≃
      {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) = n} × (torsion K) :=
  calc
    _ ≃ {a : {a : integerSet K // (preimageOfMemIntegerSet a).1 ∈ J.1} //
            mixedEmbedding.norm a.1.1 = n} := by
        convert (Equiv.subtypeEquivOfSubtype (idealSetEquiv K J).symm).symm using 3
        rw [idealSetEquiv_symm_apply]
    _ ≃ {a : integerSet K // (preimageOfMemIntegerSet a).1 ∈ J.1 ∧
          mixedEmbedding.norm a.1 = n} := Equiv.subtypeSubtypeEquivSubtypeInter
        (fun a : integerSet K ↦ (preimageOfMemIntegerSet a).1 ∈ J.1)
        (fun a ↦ mixedEmbedding.norm a.1 = n)
    _ ≃ {a : {a :integerSet K // mixedEmbedding.norm a.1 = n} //
          (preimageOfMemIntegerSet a.1).1 ∈ J.1} := ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun a : integerSet K ↦ mixedEmbedding.norm a.1 = n)
        (fun a ↦ (preimageOfMemIntegerSet a).1 ∈ J.1)).trans
        (Equiv.subtypeEquivRight (fun _ ↦ by simp [and_comm]))).symm
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = n} × (torsion K) //
          J.1 ∣ I.1.1} := by
      convert Equiv.subtypeEquivOfSubtype (p := fun I ↦ J.1 ∣ I.1) (integerSetEquivNorm K n)
      rw [integerSetEquivNorm_apply_fst, dvd_span_singleton]
    _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = n} // J.1 ∣ I.1} ×
        (torsion K) := Equiv.prodSubtypeFstEquivSubtypeProd
        (p := fun I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.1 ∧ absNorm I.1 = n} ↦ J.1 ∣ I.1)
    _ ≃ {I : (Ideal (𝓞 K))⁰ // (IsPrincipal I.1 ∧ absNorm I.1 = n) ∧ J.1 ∣ I.1} × (torsion K) :=
      Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal (𝓞 K))⁰ ↦ IsPrincipal I.1 ∧ absNorm I.1 = n)
        (fun I ↦ J.1 ∣ I.1))
    _ ≃ {I : (Ideal (𝓞 K))⁰ // J.1 ∣ I.1 ∧ IsPrincipal I.1 ∧ absNorm I.1 = n} ×
          (Units.torsion K) :=
      Equiv.prodCongrLeft fun _ ↦ Equiv.subtypeEquivRight fun _ ↦ by rw [and_comm]

/-- For `s : ℝ`, the number of principal nonzero ideals in `𝓞 K` divisible par `J` of norm `≤ s`
multiplied by the order of the torsion of `K` is equal to the number of elements in `idealSet K J`
of norm `≤ s`. -/
theorem card_isPrincipal_dvd_norm_le (s : ℝ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
      absNorm (I : Ideal (𝓞 K)) ≤ s} * torsionOrder K =
        Nat.card {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) ≤ s} := by
  obtain hs | hs := le_or_gt 0 s
  · simp_rw [← intNorm_idealSetEquiv_apply, ← Nat.le_floor_iff hs]
    rw [torsionOrder, ← Nat.card_eq_fintype_card, ← Nat.card_prod]
    refine Nat.card_congr <| @Equiv.ofFiberEquiv _ (γ := Finset.Iic ⌊s⌋₊) _
      (fun I ↦ ⟨absNorm I.1.val.1, Finset.mem_Iic.mpr I.1.prop.2.2⟩)
      (fun a ↦ ⟨intNorm (idealSetEquiv K J a.1).1, Finset.mem_Iic.mpr a.prop⟩) fun ⟨i, hi⟩ ↦ ?_
    simp_rw [Subtype.mk.injEq]
    calc _ ≃ {I : {I : (Ideal (𝓞 K))⁰ // _ ∧ _ ∧ _} // absNorm I.1.1 = i} × torsion K :=
        Equiv.prodSubtypeFstEquivSubtypeProd
      _ ≃ {I : (Ideal (𝓞 K))⁰ // (_ ∧ _ ∧ absNorm I.1 ≤ ⌊s⌋₊) ∧ absNorm I.1 = i}
            × torsion K := Equiv.prodCongrLeft fun _ ↦ (Equiv.subtypeSubtypeEquivSubtypeInter
        (p := fun I : (Ideal (𝓞 K))⁰ ↦ J.1 ∣ I.1 ∧ IsPrincipal I.1 ∧ absNorm I.1 ≤ ⌊s⌋₊)
        (q := fun I ↦ absNorm I.1 = i))
      _ ≃ {I : (Ideal (𝓞 K))⁰ // J.1 ∣ I.1 ∧ IsPrincipal I.1 ∧ absNorm I.1 = i}
            × torsion K := Equiv.prodCongrLeft fun _ ↦ Equiv.subtypeEquivRight fun _ ↦ by grind
      _ ≃ {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = i} :=
            (idealSetEquivNorm K J i).symm
      _ ≃ {a : idealSet K J // intNorm (idealSetEquiv K J a).1 = i} := by
        simp_rw [← intNorm_idealSetEquiv_apply, Nat.cast_inj]
        rfl
      _ ≃ {b : {a : idealSet K J // intNorm (idealSetEquiv K J a).1 ≤ ⌊s⌋₊} //
            intNorm (idealSetEquiv K J b).1 = i} :=
        (Equiv.subtypeSubtypeEquivSubtype fun h ↦ Finset.mem_Iic.mp (h ▸ hi)).symm
  · simp_rw [lt_iff_not_ge.mp (lt_of_lt_of_le hs (Nat.cast_nonneg _)), lt_iff_not_ge.mp
      (lt_of_lt_of_le hs (mixedEmbedding.norm_nonneg _)), and_false, Nat.card_of_isEmpty,
      zero_mul]

end fundamentalCone

end

end NumberField.mixedEmbedding
