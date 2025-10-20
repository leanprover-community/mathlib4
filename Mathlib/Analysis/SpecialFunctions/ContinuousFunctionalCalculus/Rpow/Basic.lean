/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Algebra.Order.Star.Prod
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.ContinuousMap.ContinuousSqrt

/-!
# Real powers defined via the continuous functional calculus

This file defines real powers via the continuous functional calculus (CFC) and builds its API.
This allows one to take real powers of matrices, operators, elements of a C⋆-algebra, etc. The
square root is also defined via the non-unital CFC.

## Main declarations

+ `CFC.nnrpow`: the `ℝ≥0` power function based on the non-unital CFC, i.e. `cfcₙ NNReal.rpow`
  composed with `(↑) : ℝ≥0 → ℝ`.
+ `CFC.sqrt`: the square root function based on the non-unital CFC, i.e. `cfcₙ NNReal.sqrt`
+ `CFC.rpow`: the real power function based on the unital CFC, i.e. `cfc NNReal.rpow`

## Implementation notes

We define two separate versions `CFC.nnrpow` and `CFC.rpow` due to what happens at 0. Since
`NNReal.rpow 0 0 = 1`, this means that this function does not map zero to zero when the exponent
is zero, and hence `CFC.nnrpow a 0 = 0` whereas `CFC.rpow a 0 = 1`. Note that the non-unital version
only makes sense for nonnegative exponents, and hence we define it such that the exponent is in
`ℝ≥0`.

## Notation

+ We define a `Pow A ℝ` instance for `CFC.rpow`, i.e `a ^ y` with `A` an operator and `y : ℝ` works
  as expected. Likewise, we define a `Pow A ℝ≥0` instance for `CFC.nnrpow`. Note that these are
  low-priority instances, in order to avoid overriding instances such as `Pow ℝ ℝ`,
  `Pow (A × B) ℝ` or `Pow (∀ i, A i) ℝ`.

## TODO

+ Relate these to the log and exp functions
+ Lemmas about how these functions interact with commuting `a` and `b`.
+ Prove the order properties (operator monotonicity and concavity/convexity)
-/

open scoped NNReal

namespace NNReal

/-- Taking a nonnegative power of a nonnegative number. This is defined as a standalone definition
in order to speed up automation such as `cfc_cont_tac`. -/
noncomputable abbrev nnrpow (a : ℝ≥0) (b : ℝ≥0) : ℝ≥0 := a ^ (b : ℝ)

@[simp] lemma nnrpow_def (a b : ℝ≥0) : nnrpow a b = a ^ (b : ℝ) := rfl

@[fun_prop]
lemma continuous_nnrpow_const (y : ℝ≥0) : Continuous (nnrpow · y) :=
  continuous_rpow_const zero_le_coe

/- This is a "redeclaration" of the attribute to speed up the proofs in this file. -/
attribute [fun_prop] continuousOn_rpow_const

lemma monotone_nnrpow_const (y : ℝ≥0) : Monotone (nnrpow · y) :=
  monotone_rpow_of_nonneg zero_le_coe

end NNReal

namespace CFC

section NonUnital

variable {A : Type*} [PartialOrder A] [NonUnitalRing A] [TopologicalSpace A] [StarRing A]
  [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [StarOrderedRing A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]


/- ## `nnrpow` -/

/-- Real powers of operators, based on the non-unital continuous functional calculus. -/
noncomputable def nnrpow (a : A) (y : ℝ≥0) : A := cfcₙ (NNReal.nnrpow · y) a

/-- Enable `a ^ y` notation for `CFC.nnrpow`. This is a low-priority instance to make sure it does
not take priority over other instances when they are available. -/
noncomputable instance (priority := 100) : Pow A ℝ≥0 where
  pow a y := nnrpow a y

@[simp]
lemma nnrpow_eq_pow {a : A} {y : ℝ≥0} : nnrpow a y = a ^ y := rfl

@[simp, grind]
lemma nnrpow_nonneg {a : A} {x : ℝ≥0} : 0 ≤ a ^ x := cfcₙ_predicate _ a

lemma nnrpow_def {a : A} {y : ℝ≥0} : a ^ y = cfcₙ (NNReal.nnrpow · y) a := rfl

lemma nnrpow_eq_cfcₙ_real [T2Space A] [IsTopologicalRing A] (a : A)
    (y : ℝ≥0) (ha : 0 ≤ a := by cfc_tac) : a ^ y = cfcₙ (fun x : ℝ => x ^ (y : ℝ)) a := by
  rw [nnrpow_def, cfcₙ_nnreal_eq_real ..]
  refine cfcₙ_congr ?_
  intro x hx
  have : 0 ≤ x := by grind
  simp [this]

lemma nnrpow_add {a : A} {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) :
    a ^ (x + y) = a ^ x * a ^ y := by
  simp only [nnrpow_def]
  rw [← cfcₙ_mul _ _ a]
  congr! 2 with z
  exact mod_cast z.rpow_add' <| ne_of_gt (add_pos hx hy)

@[simp]
lemma nnrpow_zero {a : A} : a ^ (0 : ℝ≥0) = 0 := by
  simp [nnrpow_def, cfcₙ_apply_of_not_map_zero]

lemma nnrpow_one (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (1 : ℝ≥0) = a := by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_one, NNReal.rpow_one]
  change cfcₙ (id : ℝ≥0 → ℝ≥0) a = a
  rw [cfcₙ_id ℝ≥0 a]

lemma nnrpow_two (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (2 : ℝ≥0) = a * a := by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_ofNat, NNReal.rpow_ofNat, pow_two]
  change cfcₙ (fun z : ℝ≥0 => id z * id z) a = a * a
  rw [cfcₙ_mul id id a, cfcₙ_id ℝ≥0 a]

lemma nnrpow_three (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (3 : ℝ≥0) = a * a * a := by
  simp only [nnrpow_def, NNReal.nnrpow_def, NNReal.coe_ofNat, NNReal.rpow_ofNat, pow_three]
  change cfcₙ (fun z : ℝ≥0 => id z * (id z * id z)) a = a * a * a
  rw [cfcₙ_mul id _ a, cfcₙ_mul id _ a, ← mul_assoc, cfcₙ_id ℝ≥0 a]

@[simp]
lemma zero_nnrpow {x : ℝ≥0} : (0 : A) ^ x = 0 := by simp [nnrpow_def]

section Unique

variable [IsTopologicalRing A] [T2Space A]

@[simp]
lemma nnrpow_nnrpow {a : A} {x y : ℝ≥0} : (a ^ x) ^ y = a ^ (x * y) := by
  by_cases ha : 0 ≤ a
  case pos =>
    obtain (rfl | hx) := eq_zero_or_pos x <;> obtain (rfl | hy) := eq_zero_or_pos y
    all_goals try simp
    simp only [nnrpow_def]
    rw [← cfcₙ_comp _ _ a]
    congr! 2 with u
    ext
    simp [Real.rpow_mul]
  case neg =>
    simp [nnrpow_def, cfcₙ_apply_of_not_predicate a ha]

lemma nnrpow_nnrpow_inv (a : A) {x : ℝ≥0} (hx : x ≠ 0) (ha : 0 ≤ a := by cfc_tac) :
    (a ^ x) ^ x⁻¹ = a := by
  simp [mul_inv_cancel₀ hx, nnrpow_one _ ha]

lemma nnrpow_inv_nnrpow (a : A) {x : ℝ≥0} (hx : x ≠ 0) (ha : 0 ≤ a := by cfc_tac) :
    (a ^ x⁻¹) ^ x = a := by
  simp [inv_mul_cancel₀ hx, nnrpow_one _ ha]

lemma nnrpow_inv_eq (a b : A) {x : ℝ≥0} (hx : x ≠ 0) (ha : 0 ≤ a := by cfc_tac)
    (hb : 0 ≤ b := by cfc_tac) : a ^ x⁻¹ = b ↔ b ^ x = a :=
  ⟨fun h ↦ nnrpow_inv_nnrpow a hx ▸ congr($(h) ^ x).symm,
    fun h ↦ nnrpow_nnrpow_inv b hx ▸ congr($(h) ^ x⁻¹).symm⟩

section prod

variable {B : Type*} [PartialOrder B] [NonUnitalRing B] [TopologicalSpace B] [StarRing B]
  [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B]
  [NonUnitalContinuousFunctionalCalculus ℝ B IsSelfAdjoint]
  [NonUnitalContinuousFunctionalCalculus ℝ (A × B) IsSelfAdjoint]
  [IsTopologicalRing B] [T2Space B]
  [NonnegSpectrumClass ℝ B] [NonnegSpectrumClass ℝ (A × B)]
  [StarOrderedRing B]

/- Note that there is higher-priority instance of `Pow (A × B) ℝ≥0` coming from the `Pow` instance
for products, hence the direct use of `nnrpow` here. -/
lemma nnrpow_map_prod {a : A} {b : B} {x : ℝ≥0}
    (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    nnrpow (a, b) x = (a ^ x, b ^ x) := by
  simp only [nnrpow_def]
  unfold nnrpow
  refine cfcₙ_map_prod (S := ℝ) _ a b (by fun_prop) ?_
  rw [Prod.le_def]
  constructor <;> simp [ha, hb]

lemma nnrpow_eq_nnrpow_prod {a : A} {b : B} {x : ℝ≥0}
    (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    nnrpow (a, b) x = (a, b) ^ x := nnrpow_map_prod

end prod

section pi

variable {ι : Type*} {C : ι → Type*} [∀ i, PartialOrder (C i)] [∀ i, NonUnitalRing (C i)]
  [∀ i, TopologicalSpace (C i)] [∀ i, StarRing (C i)]
  [∀ i, StarOrderedRing (C i)] [StarOrderedRing (∀ i, C i)]
  [∀ i, Module ℝ (C i)] [∀ i, SMulCommClass ℝ (C i) (C i)] [∀ i, IsScalarTower ℝ (C i) (C i)]
  [∀ i, NonUnitalContinuousFunctionalCalculus ℝ (C i) IsSelfAdjoint]
  [NonUnitalContinuousFunctionalCalculus ℝ (∀ i, C i) IsSelfAdjoint]
  [∀ i, IsTopologicalRing (C i)] [∀ i, T2Space (C i)]
  [NonnegSpectrumClass ℝ (∀ i, C i)] [∀ i, NonnegSpectrumClass ℝ (C i)]

/- Note that there is higher-priority instance of `Pow (∀ i, C i) ℝ≥0` coming from the `Pow`
instance for pi types, hence the direct use of `nnrpow` here. -/
lemma nnrpow_map_pi {c : ∀ i, C i} {x : ℝ≥0} (hc : ∀ i, 0 ≤ c i := by cfc_tac) :
    nnrpow c x = fun i => (c i) ^ x := by
  simp only [nnrpow_def]
  unfold nnrpow
  exact cfcₙ_map_pi (S := ℝ) _ c

lemma nnrpow_eq_nnrpow_pi {c : ∀ i, C i} {x : ℝ≥0} (hc : ∀ i, 0 ≤ c i := by cfc_tac) :
    nnrpow c x = c ^ x := nnrpow_map_pi

end pi

end Unique

/- ## `sqrt` -/

section sqrt

/-- Square roots of operators, based on the non-unital continuous functional calculus. -/
noncomputable def sqrt (a : A) : A := cfcₙ NNReal.sqrt a

@[simp, grind]
lemma sqrt_nonneg (a : A) : 0 ≤ sqrt a := cfcₙ_predicate _ a

lemma sqrt_eq_nnrpow (a : A) : sqrt a = a ^ (1 / 2 : ℝ≥0) := by
  simp only [sqrt]
  congr
  ext
  exact_mod_cast NNReal.sqrt_eq_rpow _

@[simp]
lemma sqrt_zero : sqrt (0 : A) = 0 := by simp [sqrt]

variable [IsTopologicalRing A] [T2Space A]

@[simp]
lemma nnrpow_sqrt {a : A} {x : ℝ≥0} : (sqrt a) ^ x = a ^ (x / 2) := by
  rw [sqrt_eq_nnrpow, nnrpow_nnrpow, one_div_mul_eq_div 2 x]

lemma nnrpow_sqrt_two (a : A) (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ (2 : ℝ≥0) = a := by
  simp only [nnrpow_sqrt, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [nnrpow_one a]

lemma sqrt_mul_sqrt_self (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt a * sqrt a = a := by
  rw [← nnrpow_two _, nnrpow_sqrt_two _]

@[simp]
lemma sqrt_nnrpow {a : A} {x : ℝ≥0} : sqrt (a ^ x) = a ^ (x / 2) := by
  simp [sqrt_eq_nnrpow, div_eq_mul_inv]

lemma sqrt_nnrpow_two (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt (a ^ (2 : ℝ≥0)) = a := by
  simp only [sqrt_nnrpow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
  rw [nnrpow_one _]

lemma sqrt_mul_self (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt (a * a) = a := by
  rw [← nnrpow_two _, sqrt_nnrpow_two _]

lemma mul_self_eq {a b : A} (h : sqrt a = b) (ha : 0 ≤ a := by cfc_tac) :
    b * b = a :=
  h ▸ sqrt_mul_sqrt_self _ ha

lemma sqrt_unique {a b : A} (h : b * b = a) (hb : 0 ≤ b := by cfc_tac) :
    sqrt a = b :=
  h ▸ sqrt_mul_self b

lemma sqrt_eq_iff (a b : A) (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    sqrt a = b ↔ b * b = a :=
  ⟨(mul_self_eq ·), (sqrt_unique ·)⟩

lemma sqrt_eq_zero_iff (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt a = 0 ↔ a = 0 := by
  rw [sqrt_eq_iff a _, mul_zero, eq_comm]

lemma mul_self_eq_mul_self_iff (a b : A) (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    a * a = b * b ↔ a = b :=
  ⟨fun h => sqrt_mul_self a ▸ sqrt_unique h.symm, fun h => h ▸ rfl⟩

/-- Note that the hypothesis `0 ≤ a` is necessary because the continuous functional calculi over
`ℝ≥0` (for the left-hand side) and `ℝ` (for the right-hand side) use different predicates (i.e.,
`(0 ≤ ·)` versus `IsSelfAdjoint`). Consequently, if `a` is selfadjoint but not nonnegative, then
the left-hand side is zero, but the right-hand side is (provably equal to) `CFC.sqrt a⁺`. -/
lemma sqrt_eq_real_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) :
    CFC.sqrt a = cfcₙ Real.sqrt a := by
  suffices cfcₙ (fun x : ℝ ↦ √x * √x) a = cfcₙ (fun x : ℝ ↦ x) a by
    rwa [cfcₙ_mul .., cfcₙ_id' ..,
      ← sqrt_eq_iff _ (hb := cfcₙ_nonneg (fun x _ ↦ Real.sqrt_nonneg x))] at this
  exact cfcₙ_congr fun x hx ↦ Real.mul_self_sqrt <| quasispectrum_nonneg_of_nonneg a ha x hx

section prod

variable {B : Type*} [PartialOrder B] [NonUnitalRing B] [TopologicalSpace B] [StarRing B]
  [Module ℝ B] [SMulCommClass ℝ B B] [IsScalarTower ℝ B B] [StarOrderedRing B]
  [NonUnitalContinuousFunctionalCalculus ℝ B IsSelfAdjoint]
  [NonUnitalContinuousFunctionalCalculus ℝ (A × B) IsSelfAdjoint]
  [IsTopologicalRing B] [T2Space B]
  [NonnegSpectrumClass ℝ B] [NonnegSpectrumClass ℝ (A × B)]

lemma sqrt_map_prod {a : A} {b : B} (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    sqrt (a, b) = (sqrt a, sqrt b) := by
  simp only [sqrt_eq_nnrpow]
  exact nnrpow_map_prod

end prod

section pi

variable {ι : Type*} {C : ι → Type*} [∀ i, PartialOrder (C i)] [∀ i, NonUnitalRing (C i)]
  [∀ i, TopologicalSpace (C i)] [∀ i, StarRing (C i)]
  [∀ i, StarOrderedRing (C i)] [StarOrderedRing (∀ i, C i)]
  [∀ i, Module ℝ (C i)] [∀ i, SMulCommClass ℝ (C i) (C i)] [∀ i, IsScalarTower ℝ (C i) (C i)]
  [∀ i, NonUnitalContinuousFunctionalCalculus ℝ (C i) IsSelfAdjoint]
  [NonUnitalContinuousFunctionalCalculus ℝ (∀ i, C i) IsSelfAdjoint]
  [∀ i, IsTopologicalRing (C i)] [∀ i, T2Space (C i)]
  [NonnegSpectrumClass ℝ (∀ i, C i)] [∀ i, NonnegSpectrumClass ℝ (C i)]

lemma sqrt_map_pi {c : ∀ i, C i} (hc : ∀ i, 0 ≤ c i := by cfc_tac) :
    sqrt c = fun i => sqrt (c i) := by
  simp only [sqrt_eq_nnrpow]
  exact nnrpow_map_pi

end pi

/-- For an element `a` in a C⋆-algebra, TFAE:
1. `0 ≤ a`
2. `a = sqrt a * sqrt a`
3. `a = b * b` for some nonnegative `b`
4. `a = b * b` for some self-adjoint `b`
5. `a = star b * b` for some `b`
6. `a = b * star b` for some `b`
7. `a = a⁺`
8. `a` is self-adjoint and `a⁻ = 0`
9. `a` is self-adjoint and has nonnegative spectrum -/
theorem _root_.CStarAlgebra.nonneg_TFAE {a : A} :
    [ 0 ≤ a,
      a = sqrt a * sqrt a,
      ∃ b : A, 0 ≤ b ∧ a = b * b,
      ∃ b : A, IsSelfAdjoint b ∧ a = b * b,
      ∃ b : A, a = star b * b,
      ∃ b : A, a = b * star b,
      a = a⁺,
      IsSelfAdjoint a ∧ a⁻ = 0,
      IsSelfAdjoint a ∧ QuasispectrumRestricts a ContinuousMap.realToNNReal ].TFAE := by
  tfae_have 1 ↔ 9 := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts
  tfae_have 1 ↔ 7 := eq_comm.eq ▸ (CFC.posPart_eq_self a).symm
  tfae_have 1 ↔ 8 := ⟨fun h => ⟨h.isSelfAdjoint, negPart_eq_zero_iff a |>.mpr h⟩,
    fun h => negPart_eq_zero_iff a |>.mp h.2⟩
  tfae_have 1 → 2 := fun h => sqrt_mul_sqrt_self a |>.symm
  tfae_have 2 → 3 := fun h => ⟨sqrt a, sqrt_nonneg a, h⟩
  tfae_have 3 → 4 := fun ⟨b, hb⟩ => ⟨b, hb.1.isSelfAdjoint, hb.2⟩
  tfae_have 4 → 5 := fun ⟨b, hb⟩ => ⟨b, hb.1.symm ▸ hb.2⟩
  tfae_have 5 → 6 := fun ⟨b, hb⟩ => ⟨star b, star_star b |>.symm ▸ hb⟩
  tfae_have 6 → 1 := fun ⟨b, hb⟩ => hb ▸ mul_star_self_nonneg _
  tfae_finish

theorem _root_.CStarAlgebra.nonneg_iff_eq_sqrt_mul_sqrt {a : A} :
    0 ≤ a ↔ a = sqrt a * sqrt a := CStarAlgebra.nonneg_TFAE.out 0 1
theorem _root_.CStarAlgebra.nonneg_iff_exists_nonneg_and_eq_mul_self {a : A} :
    0 ≤ a ↔ ∃ b, 0 ≤ b ∧ a = b * b := CStarAlgebra.nonneg_TFAE.out 0 2
theorem _root_.CStarAlgebra.nonneg_iff_exists_isSelfAdjoint_and_eq_mul_self {a : A} :
    0 ≤ a ↔ ∃ b, IsSelfAdjoint b ∧ a = b * b := CStarAlgebra.nonneg_TFAE.out 0 3
theorem _root_.CStarAlgebra.nonneg_iff_eq_star_mul_self {a : A} :
    0 ≤ a ↔ ∃ b, a = star b * b := CStarAlgebra.nonneg_TFAE.out 0 4
theorem _root_.CStarAlgebra.nonneg_iff_eq_mul_star_self {a : A} :
    0 ≤ a ↔ ∃ b, a = b * star b := CStarAlgebra.nonneg_TFAE.out 0 5
theorem _root_.CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero {a : A} :
    0 ≤ a ↔ IsSelfAdjoint a ∧ a⁻ = 0 := CStarAlgebra.nonneg_TFAE.out 0 7

end sqrt

end NonUnital

section Unital

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

/- ## `rpow` -/

/-- Real powers of operators, based on the unital continuous functional calculus. -/
noncomputable def rpow (a : A) (y : ℝ) : A := cfc (fun x : ℝ≥0 => x ^ y) a

/-- Enable `a ^ y` notation for `CFC.rpow`. This is a low-priority instance to make sure it does
not take priority over other instances when they are available (such as `Pow ℝ ℝ`). -/
noncomputable instance (priority := 100) : Pow A ℝ where
  pow a y := rpow a y

@[simp]
lemma rpow_eq_pow {a : A} {y : ℝ} : rpow a y = a ^ y := rfl

@[simp, grind]
lemma rpow_nonneg {a : A} {y : ℝ} : 0 ≤ a ^ y := cfc_predicate _ a

lemma rpow_def {a : A} {y : ℝ} : a ^ y = cfc (fun x : ℝ≥0 => x ^ y) a := rfl

lemma rpow_one (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (1 : ℝ) = a := by
  simp only [rpow_def, NNReal.rpow_one, cfc_id' ℝ≥0 a]

@[simp]
lemma one_rpow {x : ℝ} : (1 : A) ^ x = (1 : A) := by simp [rpow_def]

lemma rpow_zero (a : A) (ha : 0 ≤ a := by cfc_tac) : a ^ (0 : ℝ) = 1 := by
  simp [rpow_def, cfc_const_one ℝ≥0 a]

lemma zero_rpow {x : ℝ} (hx : x ≠ 0) : rpow (0 : A) x = 0 := by simp [rpow, NNReal.zero_rpow hx]

lemma rpow_natCast (a : A) (n : ℕ) (ha : 0 ≤ a := by cfc_tac) : a ^ (n : ℝ) = a ^ n := by
  rw [← cfc_pow_id (R := ℝ≥0) a n, rpow_def]
  congr
  simp

@[simp]
lemma rpow_algebraMap {x : ℝ≥0} {y : ℝ} :
    (algebraMap ℝ≥0 A x) ^ y = algebraMap ℝ≥0 A (x ^ y) := by
  rw [rpow_def, cfc_algebraMap ..]

lemma rpow_add {a : A} {x y : ℝ} (ha : IsUnit a) :
    a ^ (x + y) = a ^ x * a ^ y := by
  have ha' : 0 ∉ spectrum ℝ≥0 a := spectrum.zero_notMem _ ha
  simp only [rpow_def]
  rw [← cfc_mul _ _ a]
  refine cfc_congr ?_
  intro z hz
  have : z ≠ 0 := by aesop
  simp [NNReal.rpow_add this _ _]

lemma rpow_rpow [IsTopologicalRing A] [T2Space A]
    (a : A) (x y : ℝ) (ha₁ : IsUnit a) (hx : x ≠ 0) (ha₂ : 0 ≤ a := by cfc_tac) :
    (a ^ x) ^ y = a ^ (x * y) := by
  have ha₁' : 0 ∉ spectrum ℝ≥0 a := spectrum.zero_notMem _ ha₁
  simp only [rpow_def]
  rw [← cfc_comp _ _ a ha₂]
  refine cfc_congr fun _ _ => ?_
  simp [NNReal.rpow_mul]

lemma rpow_rpow_inv [IsTopologicalRing A] [T2Space A]
    (a : A) (x : ℝ) (ha₁ : IsUnit a) (hx : x ≠ 0) (ha₂ : 0 ≤ a := by cfc_tac) :
    (a ^ x) ^ x⁻¹ = a := by
  rw [rpow_rpow a x x⁻¹ ha₁ hx ha₂, mul_inv_cancel₀ hx, rpow_one a ha₂]

lemma rpow_inv_rpow [IsTopologicalRing A] [T2Space A]
    (a : A) (x : ℝ) (ha₁ : IsUnit a) (hx : x ≠ 0) (ha₂ : 0 ≤ a := by cfc_tac) :
    (a ^ x⁻¹) ^ x = a := by
  simpa using rpow_rpow_inv a x⁻¹ ha₁ (inv_ne_zero hx) ha₂

lemma rpow_rpow_of_exponent_nonneg [IsTopologicalRing A] [T2Space A] (a : A) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (ha₂ : 0 ≤ a := by cfc_tac) : (a ^ x) ^ y = a ^ (x * y) := by
  simp only [rpow_def]
  rw [← cfc_comp _ _ a]
  refine cfc_congr fun _ _ => ?_
  simp [NNReal.rpow_mul]

lemma rpow_mul_rpow_neg {a : A} (x : ℝ) (ha : IsUnit a)
    (ha' : 0 ≤ a := by cfc_tac) : a ^ x * a ^ (-x) = 1 := by
  rw [← rpow_add ha, add_neg_cancel, rpow_zero a]

lemma rpow_neg_mul_rpow {a : A} (x : ℝ) (ha : IsUnit a)
    (ha' : 0 ≤ a := by cfc_tac) : a ^ (-x) * a ^ x = 1 := by
  rw [← rpow_add ha, neg_add_cancel, rpow_zero a]

lemma rpow_neg_one_eq_inv (a : Aˣ) (ha : (0 : A) ≤ a := by cfc_tac) :
    a ^ (-1 : ℝ) = (↑a⁻¹ : A) := by
  refine a.inv_eq_of_mul_eq_one_left ?_ |>.symm
  simpa [rpow_one (a : A)] using rpow_neg_mul_rpow 1 a.isUnit

lemma rpow_neg_one_eq_cfc_inv {A : Type*} [PartialOrder A] [NormedRing A] [StarRing A]
    [StarOrderedRing A] [NormedAlgebra ℝ A] [NonnegSpectrumClass ℝ A]
    [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] (a : A) :
    a ^ (-1 : ℝ) = cfc (·⁻¹ : ℝ≥0 → ℝ≥0) a :=
  cfc_congr fun x _ ↦ NNReal.rpow_neg_one x

lemma rpow_neg [IsTopologicalRing A] [T2Space A] (a : Aˣ) (x : ℝ)
    (ha' : (0 : A) ≤ a := by cfc_tac) : (a : A) ^ (-x) = (↑a⁻¹ : A) ^ x := by
  suffices h₁ : ContinuousOn (fun z ↦ z ^ x) (Inv.inv '' (spectrum ℝ≥0 (a : A))) by
    rw [← cfc_inv_id (R := ℝ≥0) a, rpow_def, rpow_def,
        ← cfc_comp' (fun z => z ^ x) (Inv.inv : ℝ≥0 → ℝ≥0) (a : A) h₁]
    refine cfc_congr fun _ _ => ?_
    simp [NNReal.rpow_neg, NNReal.inv_rpow]
  refine NNReal.continuousOn_rpow_const (.inl ?_)
  rintro ⟨z, hz, hz'⟩
  exact spectrum.zero_notMem ℝ≥0 a.isUnit <| inv_eq_zero.mp hz' ▸ hz

lemma rpow_intCast (a : Aˣ) (n : ℤ) (ha : (0 : A) ≤ a := by cfc_tac) :
    (a : A) ^ (n : ℝ) = (↑(a ^ n) : A) := by
  rw [← cfc_zpow (R := ℝ≥0) a n, rpow_def]
  refine cfc_congr fun _ _ => ?_
  simp

/-- `a ^ x` bundled as an element of `Aˣ` for `a : Aˣ`. -/
@[simps]
noncomputable def _root_.Units.cfcRpow (a : Aˣ) (x : ℝ) (ha : (0 : A) ≤ a := by cfc_tac) : Aˣ :=
  ⟨(a : A) ^ x, (a : A) ^ (-x), rpow_mul_rpow_neg x (by simp), rpow_neg_mul_rpow x (by simp)⟩

@[aesop safe apply, grind ←]
lemma _root_.IsUnit.cfcRpow {a : A} (ha : IsUnit a) (x : ℝ) (ha_nonneg : 0 ≤ a := by cfc_tac) :
    IsUnit (a ^ x) :=
  ha.unit.cfcRpow x |>.isUnit

lemma spectrum_rpow (a : A) (x : ℝ)
    (h : ContinuousOn (· ^ x) (spectrum ℝ≥0 a) := by cfc_cont_tac)
    (ha : 0 ≤ a := by cfc_tac) :
    spectrum ℝ≥0 (a ^ x) = (· ^ x) '' spectrum ℝ≥0 a :=
  cfc_map_spectrum (· ^ x : ℝ≥0 → ℝ≥0) a ha h

@[grind =]
lemma isUnit_rpow_iff (a : A) (y : ℝ) (hy : y ≠ 0) (ha : 0 ≤ a := by cfc_tac) :
    IsUnit (a ^ y) ↔ IsUnit a := by
  nontriviality A
  refine ⟨fun h => ?_, fun h => h.cfcRpow y ha⟩
  rw [rpow_def] at h
  by_cases hf : ContinuousOn (fun x : ℝ≥0 => x ^ y) (spectrum ℝ≥0 a)
  · rw [isUnit_cfc_iff _ a hf] at h
    refine spectrum.isUnit_of_zero_notMem ℝ≥0 ?_
    intro h0
    specialize h 0 h0
    simp only [ne_eq, NNReal.rpow_eq_zero_iff, true_and, Decidable.not_not] at h
    exact hy h
  · rw [cfc_apply_of_not_continuousOn a hf] at h
    exact False.elim <| not_isUnit_zero h

section prod

variable [IsTopologicalRing A] [T2Space A]
variable {B : Type*} [PartialOrder B] [Ring B] [StarRing B] [TopologicalSpace B]
  [StarOrderedRing B]
  [Algebra ℝ B] [ContinuousFunctionalCalculus ℝ B IsSelfAdjoint]
  [ContinuousFunctionalCalculus ℝ (A × B) IsSelfAdjoint]
  [IsTopologicalRing B] [T2Space B] [StarOrderedRing (A × B)]
  [NonnegSpectrumClass ℝ B] [NonnegSpectrumClass ℝ (A × B)]

/- Note that there is higher-priority instance of `Pow (A × B) ℝ` coming from the `Pow` instance for
products, hence the direct use of `rpow` here. -/
lemma rpow_map_prod {a : A} {b : B} {x : ℝ} (ha : IsUnit a) (hb : IsUnit b)
    (ha' : 0 ≤ a := by cfc_tac) (hb' : 0 ≤ b := by cfc_tac) :
    rpow (a, b) x = (a ^ x, b ^ x) := by
  have ha'' : 0 ∉ spectrum ℝ≥0 a := spectrum.zero_notMem _ ha
  have hb'' : 0 ∉ spectrum ℝ≥0 b := spectrum.zero_notMem _ hb
  simp only [rpow_def]
  unfold rpow
  refine cfc_map_prod (R := ℝ≥0) (S := ℝ) _ a b (by cfc_cont_tac) ?_
  rw [Prod.le_def]
  constructor <;> simp [ha', hb']

lemma rpow_eq_rpow_prod {a : A} {b : B} {x : ℝ} (ha : IsUnit a) (hb : IsUnit b)
    (ha' : 0 ≤ a := by cfc_tac) (hb' : 0 ≤ b := by cfc_tac) :
    rpow (a, b) x = (a, b) ^ x := rpow_map_prod ha hb

@[deprecated (since := "2025-05-13")] alias rpow_eq_rpow_rpod := rpow_eq_rpow_prod

end prod

section pi

variable [IsTopologicalRing A] [T2Space A]
variable {ι : Type*} {C : ι → Type*} [∀ i, PartialOrder (C i)] [∀ i, Ring (C i)]
  [∀ i, StarRing (C i)] [∀ i, TopologicalSpace (C i)] [∀ i, StarOrderedRing (C i)]
  [StarOrderedRing (∀ i, C i)]
  [∀ i, Algebra ℝ (C i)] [∀ i, ContinuousFunctionalCalculus ℝ (C i) IsSelfAdjoint]
  [ContinuousFunctionalCalculus ℝ (∀ i, C i) IsSelfAdjoint]
  [∀ i, IsTopologicalRing (C i)] [∀ i, T2Space (C i)]
  [NonnegSpectrumClass ℝ (∀ i, C i)] [∀ i, NonnegSpectrumClass ℝ (C i)]

/- Note that there is a higher-priority instance of `Pow (∀ i, B i) ℝ` coming from the `Pow`
instance for pi types, hence the direct use of `rpow` here. -/
lemma rpow_map_pi {c : ∀ i, C i} {x : ℝ} (hc : ∀ i, IsUnit (c i))
    (hc' : ∀ i, 0 ≤ c i := by cfc_tac) :
    rpow c x = fun i => (c i) ^ x := by
  have hc'' : ∀ i, 0 ∉ spectrum ℝ≥0 (c i) := fun i => spectrum.zero_notMem _ (hc i)
  simp only [rpow_def]
  unfold rpow
  exact cfc_map_pi (S := ℝ) _ c

lemma rpow_eq_rpow_pi {c : ∀ i, C i} {x : ℝ} (hc : ∀ i, IsUnit (c i))
    (hc' : ∀ i, 0 ≤ c i := by cfc_tac) :
    rpow c x = c ^ x := rpow_map_pi hc

end pi

section unital_vs_nonunital

variable [IsTopologicalRing A] [T2Space A]

-- provides instance `ContinuousFunctionalCalculus.compactSpace_spectrum`
open scoped ContinuousFunctionalCalculus

lemma nnrpow_eq_rpow {a : A} {x : ℝ≥0} (hx : 0 < x) : a ^ x = a ^ (x : ℝ) := by
  rw [nnrpow_def (A := A), rpow_def, cfcₙ_eq_cfc]

lemma sqrt_eq_rpow {a : A} : sqrt a = a ^ (1 / 2 : ℝ) := by
  have : a ^ (1 / 2 : ℝ) = a ^ ((1 / 2 : ℝ≥0) : ℝ) := rfl
  rw [this, ← nnrpow_eq_rpow (by simp), sqrt_eq_nnrpow a]

lemma sqrt_eq_cfc {a : A} : sqrt a = cfc NNReal.sqrt a := by
  unfold sqrt
  rw [cfcₙ_eq_cfc]

lemma sqrt_sq (a : A) (ha : 0 ≤ a := by cfc_tac) : sqrt (a ^ 2) = a := by
  rw [pow_two, sqrt_mul_self (A := A) a]

lemma sq_sqrt (a : A) (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ 2 = a := by
  rw [pow_two, sqrt_mul_sqrt_self (A := A) a]

lemma sq_eq_sq_iff (a b : A) (ha : 0 ≤ a := by cfc_tac) (hb : 0 ≤ b := by cfc_tac) :
    a ^ 2 = b ^ 2 ↔ a = b := by
  simp_rw [sq, mul_self_eq_mul_self_iff a b]

@[simp]
lemma sqrt_algebraMap {r : ℝ≥0} : sqrt (algebraMap ℝ≥0 A r) = algebraMap ℝ≥0 A (NNReal.sqrt r) := by
  rw [sqrt_eq_cfc, cfc_algebraMap]

@[simp]
lemma sqrt_one : sqrt (1 : A) = 1 := by simp [sqrt_eq_cfc]

lemma sqrt_eq_one_iff (a : A) (ha : 0 ≤ a := by cfc_tac) :
    sqrt a = 1 ↔ a = 1 := by
  rw [sqrt_eq_iff a _, mul_one, eq_comm]

lemma sqrt_eq_one_iff' [Nontrivial A] (a : A) :
    sqrt a = 1 ↔ a = 1 := by
  refine ⟨fun h ↦ sqrt_eq_one_iff a ?_ |>.mp h, fun h ↦ h ▸ sqrt_one⟩
  rw [sqrt, cfcₙ] at h
  cfc_tac

-- TODO: relate to a strict positivity condition
lemma sqrt_rpow {a : A} {x : ℝ} (h : IsUnit a)
    (hx : x ≠ 0) : sqrt (a ^ x) = a ^ (x / 2) := by
  by_cases hnonneg : 0 ≤ a
  case pos =>
    simp only [sqrt_eq_rpow, div_eq_mul_inv, one_mul, rpow_rpow _ _ _ h hx]
  case neg =>
    simp [sqrt_eq_cfc, rpow_def, cfc_apply_of_not_predicate a hnonneg]

-- TODO: relate to a strict positivity condition
lemma rpow_sqrt (a : A) (x : ℝ) (h : IsUnit a)
    (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ x = a ^ (x / 2) := by
  rw [sqrt_eq_rpow, div_eq_mul_inv, one_mul,
      rpow_rpow _ _ _ h (by simp), inv_mul_eq_div]

lemma sqrt_rpow_nnreal {a : A} {x : ℝ≥0} : sqrt (a ^ (x : ℝ)) = a ^ (x / 2 : ℝ) := by
  by_cases htriv : 0 ≤ a
  case neg => simp [sqrt_eq_cfc, rpow_def, cfc_apply_of_not_predicate a htriv]
  case pos =>
    cases eq_zero_or_pos x with
    | inl hx => simp [hx, rpow_zero _ htriv]
    | inr h₁ =>
      have h₂ : (x : ℝ) / 2 = NNReal.toReal (x / 2) := by simp
      have h₃ : 0 < x / 2 := by positivity
      rw [← nnrpow_eq_rpow h₁, h₂, ← nnrpow_eq_rpow h₃, sqrt_nnrpow (A := A)]

lemma rpow_sqrt_nnreal {a : A} {x : ℝ≥0}
    (ha : 0 ≤ a := by cfc_tac) : (sqrt a) ^ (x : ℝ) = a ^ (x / 2 : ℝ) := by
  by_cases hx : x = 0
  case pos =>
    have ha' : 0 ≤ sqrt a := sqrt_nonneg _
    simp [hx, rpow_zero _ ha', rpow_zero _ ha]
  case neg =>
    have h₁ : 0 ≤ (x : ℝ) := NNReal.zero_le_coe
    rw [sqrt_eq_rpow, rpow_rpow_of_exponent_nonneg _ _ _ (by simp) h₁, one_div_mul_eq_div]

@[grind =]
lemma isUnit_nnrpow_iff (a : A) (y : ℝ≥0) (hy : y ≠ 0) (ha : 0 ≤ a := by cfc_tac) :
    IsUnit (a ^ y) ↔ IsUnit a := by
  rw [nnrpow_eq_rpow (pos_of_ne_zero hy)]
  refine isUnit_rpow_iff a y ?_ ha
  exact_mod_cast hy

@[aesop safe apply]
lemma _root_.IsUnit.cfcNNRpow (a : A) (y : ℝ≥0) (ha_unit : IsUnit a) (hy : y ≠ 0)
    (ha : 0 ≤ a := by cfc_tac) : IsUnit (a ^ y) :=
  (isUnit_nnrpow_iff a y hy ha).mpr ha_unit

@[grind =]
lemma isUnit_sqrt_iff (a : A) (ha : 0 ≤ a := by cfc_tac) : IsUnit (sqrt a) ↔ IsUnit a := by
  rw [sqrt_eq_rpow]
  exact isUnit_rpow_iff a _ (by simp) ha

@[aesop safe apply]
lemma _root_.IsUnit.cfcSqrt (a : A) (ha_unit : IsUnit a) (ha : 0 ≤ a := by cfc_tac) :
    IsUnit (sqrt a) :=
  (isUnit_sqrt_iff a ha).mpr ha_unit

@[aesop safe apply]
lemma _root_.IsStrictlyPositive.nnrpow {a : A} {y : ℝ≥0} (ha : IsStrictlyPositive a) (hy : y ≠ 0) :
    IsStrictlyPositive (a ^ y) := by grind

@[aesop safe apply]
lemma _root_.IsStrictlyPositive.sqrt {a : A} (ha : IsStrictlyPositive a) :
    IsStrictlyPositive (sqrt a) := by grind

omit [T2Space A] [IsTopologicalRing A] in
@[aesop safe apply]
lemma _root_.IsStrictlyPositive.rpow {a : A} {y : ℝ} (ha : IsStrictlyPositive a) :
    IsStrictlyPositive (a ^ y) := by grind

/-- For an element `a` in a C⋆-algebra, TFAE:
1. `a` is strictly positive,
2. `sqrt a` is strictly positive and `a = sqrt a * sqrt a`,
3. `sqrt a` is invertible and `a = sqrt a * sqrt a`,
4. `a = b * b` for some strictly positive `b`,
5. `a = b * b` for some self-adjoint and invertible `b`,
6. `a = star b * b` for some invertible `b`,
7. `a = b * star b` for some invertible `b`,
8. `0 ≤ a` and `a` is invertible,
9. `a` is self-adjoint and has positive spectrum. -/
theorem _root_.CStarAlgebra.isStrictlyPositive_TFAE {a : A} :
    [IsStrictlyPositive a,
     IsStrictlyPositive (sqrt a) ∧ a = sqrt a * sqrt a,
     IsUnit (sqrt a) ∧ a = sqrt a * sqrt a,
     ∃ b, IsStrictlyPositive b ∧ a = b * b,
     ∃ b, IsUnit b ∧ IsSelfAdjoint b ∧ a = b * b,
     ∃ b, IsUnit b ∧ a = star b * b,
     ∃ b, IsUnit b ∧ a = b * star b,
     0 ≤ a ∧ IsUnit a,
     IsSelfAdjoint a ∧ ∀ x ∈ spectrum ℝ a, 0 < x].TFAE := by
  tfae_have 1 ↔ 8 := IsStrictlyPositive.iff_of_unital
  tfae_have 1 ↔ 9 := ⟨fun h => ⟨h.isSelfAdjoint,
      StarOrderedRing.isStrictlyPositive_iff_spectrum_pos a |>.mp h⟩,
    fun h => (StarOrderedRing.isStrictlyPositive_iff_spectrum_pos a).mpr h.2⟩
  tfae_have 1 → 2 := fun h => ⟨h.sqrt, sqrt_mul_sqrt_self a |>.symm⟩
  tfae_have 2 → 3 := fun h => ⟨h.1.isUnit, h.2⟩
  tfae_have 3 → 4 := fun h => ⟨sqrt a, h.1.isStrictlyPositive (sqrt_nonneg _), h.2⟩
  tfae_have 4 → 5 := fun ⟨b, hb, hab⟩ => ⟨b, hb.isUnit, hb.isSelfAdjoint, hab⟩
  tfae_have 5 → 6 := fun ⟨b, hb, hbsa, hab⟩ => ⟨b, hb, hbsa.symm ▸ hab⟩
  tfae_have 6 → 7 := fun ⟨b, hb, hab⟩ => ⟨star b, hb.star, star_star b |>.symm ▸ hab⟩
  tfae_have 7 → 8 := fun ⟨b, hb, hab⟩ => ⟨hab ▸ mul_star_self_nonneg _, hab ▸ hb.mul hb.star⟩
  tfae_finish

theorem _root_.CStarAlgebra.isStrictlyPositive_iff_isStrictlyPositive_sqrt_and_eq_sqrt_mul_sqrt
    {a : A} : IsStrictlyPositive a ↔ IsStrictlyPositive (sqrt a) ∧ a = sqrt a * sqrt a :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 1
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_isUnit_sqrt_and_eq_sqrt_mul_sqrt
    {a : A} : IsStrictlyPositive a ↔ IsUnit (sqrt a) ∧ a = sqrt a * sqrt a :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 2
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_exists_isStrictlyPositive_and_eq_mul_self
    {a : A} : IsStrictlyPositive a ↔ ∃ b, IsStrictlyPositive b ∧ a = b * b :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 3
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_exists_isUnit_and_isSelfAdjoint_and_eq_mul_self
    {a : A} : IsStrictlyPositive a ↔ ∃ b, IsUnit b ∧ IsSelfAdjoint b ∧ a = b * b :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 4
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self
    {a : A} : IsStrictlyPositive a ↔ ∃ b, IsUnit b ∧ a = star b * b :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 5
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self
    {a : A} : IsStrictlyPositive a ↔ ∃ b, IsUnit b ∧ a = b * star b :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 6
theorem _root_.CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos
    {a : A} : IsStrictlyPositive a ↔ IsSelfAdjoint a ∧ ∀ x ∈ spectrum ℝ a, 0 < x :=
  CStarAlgebra.isStrictlyPositive_TFAE.out 0 8

end unital_vs_nonunital

end Unital

end CFC
