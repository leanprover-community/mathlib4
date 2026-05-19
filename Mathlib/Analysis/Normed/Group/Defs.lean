/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.Topology.Order.Real
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Tactic.Group
public import Mathlib.Topology.MetricSpace.Defs

/-!
# (Semi)normed groups: definitions

In this file we define 10 classes:

* `Norm`, `NNNorm`: auxiliary classes endowing a type `α` with a function `norm : α → ℝ`
  (notation: `‖x‖`) and `nnnorm : α → ℝ≥0` (notation: `‖x‖₊`), respectively;
* `Seminormed...Group`: A seminormed (additive) (commutative) group is an (additive) (commutative)
  group with a norm and a compatible pseudometric space structure:
  `∀ x y, dist x y = ‖x⁻¹ * y‖` or `∀ x y, dist x y = ‖-x + y‖`, depending on the group operation.
* `Normed...Group`: A normed (additive) (commutative) group is an (additive) (commutative) group
  with a norm and a compatible metric space structure.

We also provide some instances relating these classes.

## Notes

The current convention `dist x y = ‖-x + y‖` means that the distance is invariant under left
addition. This is especially relevant in multiplicative contexts: in the Cayley graph of the
free group, for instance, we want `w` to be joined by an edge to `ws` when `s` is a generator,
so these points should be at distance `1`, and moreover left multiplication should be an isometry.
This is the case with the formula `dist x y = ‖x⁻¹ * y‖` we use, while it would be wrong with
`‖x * y⁻¹‖`.

The normed group hierarchy would lend itself well to a mixin design (that is, having
`SeminormedGroup` and `SeminormedAddGroup` not extend `Group` and `AddGroup`), but we choose not
to for performance concerns.

## Tags

normed group
-/

public section


variable {𝓕 α ι κ E F G : Type*}

open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

/-- Auxiliary class, endowing a type `E` with a function `norm : E → ℝ` with notation `‖x‖`. This
class is designed to be extended in more interesting classes specifying the properties of the norm.
-/
@[notation_class]
class Norm (E : Type*) where
  /-- the `ℝ`-valued norm function. -/
  norm : E → ℝ

/-- Auxiliary class, endowing a type `α` with a function `nnnorm : α → ℝ≥0` with notation `‖x‖₊`. -/
@[notation_class]
class NNNorm (E : Type*) where
  /-- the `ℝ≥0`-valued norm function. -/
  nnnorm : E → ℝ≥0

/-- Auxiliary class, endowing a type `α` with a function `enorm : α → ℝ≥0∞` with notation `‖x‖ₑ`. -/
@[notation_class]
class ENorm (E : Type*) where
  /-- the `ℝ≥0∞`-valued norm function. -/
  enorm : E → ℝ≥0∞

export Norm (norm)
export NNNorm (nnnorm)
export ENorm (enorm)

@[inherit_doc] notation "‖" e "‖" => norm e
@[inherit_doc] notation "‖" e "‖₊" => nnnorm e
@[inherit_doc] notation "‖" e "‖ₑ" => enorm e

section ENorm
variable {E : Type*} [NNNorm E] {x : E} {r : ℝ≥0}

instance NNNorm.toENorm : ENorm E where enorm := (‖·‖₊ : E → ℝ≥0∞)

lemma enorm_eq_nnnorm (x : E) : ‖x‖ₑ = ‖x‖₊ := rfl

@[simp] lemma toNNReal_enorm (x : E) : ‖x‖ₑ.toNNReal = ‖x‖₊ := rfl

@[simp, norm_cast] lemma coe_le_enorm : r ≤ ‖x‖ₑ ↔ r ≤ ‖x‖₊ := by simp [enorm]
@[simp, norm_cast] lemma enorm_le_coe : ‖x‖ₑ ≤ r ↔ ‖x‖₊ ≤ r := by simp [enorm]
@[simp, norm_cast] lemma coe_lt_enorm : r < ‖x‖ₑ ↔ r < ‖x‖₊ := by simp [enorm]
@[simp, norm_cast] lemma enorm_lt_coe : ‖x‖ₑ < r ↔ ‖x‖₊ < r := by simp [enorm]

@[aesop (rule_sets := [finiteness]) safe apply, simp]
lemma enorm_ne_top : ‖x‖ₑ ≠ ∞ := by simp [enorm]
@[simp] lemma enorm_lt_top : ‖x‖ₑ < ∞ := by simp [enorm]

end ENorm

/-- A type `E` equipped with a continuous map `‖·‖ₑ : E → ℝ≥0∞`

NB. We do not demand that the topology is somehow defined by the enorm:
for `ℝ≥0∞` (the motivating example behind this definition), this is not true. -/
class ContinuousENorm (E : Type*) [TopologicalSpace E] extends ENorm E where
  continuous_enorm : Continuous enorm

/-- An e-seminormed monoid is an additive monoid endowed with a continuous enorm.
Note that we do not ask for the enorm to be positive definite:
non-trivial elements may have enorm zero. -/
class IsESeminormedAddMonoid (E : Type*)
    [TopologicalSpace E] [ContinuousENorm E] [AddMonoid E] where
  enorm_zero : ‖(0 : E)‖ₑ = 0
  protected enorm_add_le : ∀ x y : E, ‖x + y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ

/-- missing doc -/
@[class_abbrev]
structure ESeminormedAddMonoid (E : Type*) [TopologicalSpace E] where
  /-- missing doc -/
  [toContinuousENorm : ContinuousENorm E]
  /-- missing doc -/
  [toAddMonoid : AddMonoid E]
  [toIsESeminormedAddMonoid : IsESeminormedAddMonoid E]

attribute [instance] ESeminormedAddMonoid.mk

/-- An enormed monoid is an additive monoid endowed with a continuous enorm,
which is positive definite: in other words, this is an `ESeminormedAddMonoid` with a positive
definiteness condition added. -/
class IsENormedAddMonoid (E : Type*) [TopologicalSpace E] [ContinuousENorm E] [AddMonoid E] where
  enorm_eq_zero : ∀ x : E, ‖x‖ₑ = 0 ↔ x = 0
  protected enorm_add_le : ∀ x y : E, ‖x + y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ

/-- missing doc -/
@[class_abbrev]
structure ENormedAddMonoid (E : Type*) [TopologicalSpace E] where
  /-- missing doc -/
  [toContinuousENorm : ContinuousENorm E]
  /-- missing doc -/
  [toAddMonoid : AddMonoid E]
  [toIsENormedAddMonoid : IsENormedAddMonoid E]

attribute [instance] ENormedAddMonoid.mk

/-- An e-seminormed monoid is a monoid endowed with a continuous enorm.
Note that we only ask for the enorm to be a semi-norm: non-trivial elements may have enorm zero. -/
@[to_additive]
class IsESeminormedMonoid (E : Type*) [TopologicalSpace E] [ContinuousENorm E] [Monoid E] where
  enorm_zero : ‖(1 : E)‖ₑ = 0
  protected enorm_mul_le : ∀ x y : E, ‖x * y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ

/-- missing doc -/
@[class_abbrev, to_additive]
structure ESeminormedMonoid (E : Type*) [TopologicalSpace E] where
  /-- missing doc -/
  [toContinuousENorm : ContinuousENorm E]
  /-- missing doc -/
  [toMonoid : Monoid E]
  [toIsESeminormedMonoid : IsESeminormedMonoid E]

attribute [instance] ESeminormedMonoid.mk

/-- An enormed monoid is a monoid endowed with a continuous enorm,
which is positive definite: in other words, this is an `ESeminormedMonoid` with a positive
definiteness condition added. -/
@[to_additive]
class IsENormedMonoid (E : Type*) [TopologicalSpace E] [ContinuousENorm E] [Monoid E] where
  enorm_eq_zero : ∀ x : E, ‖x‖ₑ = 0 ↔ x = 1
  protected enorm_mul_le : ∀ x y : E, ‖x * y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ

@[to_additive]
instance [TopologicalSpace E] [ContinuousENorm E] [Monoid E] [IsENormedMonoid E] :
    IsESeminormedMonoid E where
  enorm_zero := (‹IsENormedMonoid E›.enorm_eq_zero _).mpr rfl
  enorm_mul_le := ‹IsENormedMonoid E›.enorm_mul_le

/-- missing doc -/
@[class_abbrev, to_additive]
structure ENormedMonoid (E : Type*) [TopologicalSpace E] where
  /-- missing doc -/
  [toContinuousENorm : ContinuousENorm E]
  /-- missing doc -/
  [toMonoid : Monoid E]
  [toIsENormedMonoid : IsENormedMonoid E]

attribute [instance] ENormedMonoid.mk

/-- missing doc -/
@[class_abbrev]
structure ESeminormedAddCommMonoid (E : Type*) [TopologicalSpace E] where
  /-- missing doc -/
  [toContinuousENorm : ContinuousENorm E]
  /-- missing doc -/
  [toAddCommMonoid : AddCommMonoid E]
  [toIsESeminormedAddMonoid : IsESeminormedAddMonoid E]

attribute [instance] ESeminormedAddCommMonoid.mk

/-- missing doc -/
@[class_abbrev]
structure ENormedAddCommMonoid (E : Type*) [TopologicalSpace E] where
  /-- missing doc -/
  [toContinuousENorm : ContinuousENorm E]
  /-- missing doc -/
  [toAddCommMonoid : AddCommMonoid E]
  [toIsENormedAddMonoid : IsENormedAddMonoid E]

attribute [instance] ENormedAddCommMonoid.mk

/-- missing doc -/
@[class_abbrev, to_additive]
structure ESeminormedCommMonoid (E : Type*) [TopologicalSpace E] where
  /-- missing doc -/
  [toContinuousENorm : ContinuousENorm E]
  /-- missing doc -/
  [toCommMonoid : CommMonoid E]
  [toIsESeminormedMonoid : IsESeminormedMonoid E]

attribute [instance] ESeminormedCommMonoid.mk

/-- missing doc -/
@[class_abbrev, to_additive]
structure ENormedCommMonoid (E : Type*) [TopologicalSpace E] where
  /-- missing doc -/
  [toContinuousENorm : ContinuousENorm E]
  /-- missing doc -/
  [toCommMonoid : CommMonoid E]
  [toIsENormedMonoid : IsENormedMonoid E]

attribute [instance] ENormedCommMonoid.mk

/-- missing doc -/
class NormPseudoMetric (E : Type*) extends Norm E, PseudoMetricSpace E where

/-- missing doc -/
class NormMetric (E : Type*) extends Norm E, MetricSpace E where

attribute [instance 100] NormPseudoMetric.toNorm NormMetric.toNorm
attribute [instance 100] NormPseudoMetric.toPseudoMetricSpace NormMetric.toMetricSpace

instance (priority := 100) NormMetric.toNormPseudoMetric [NormMetric E] : NormPseudoMetric E where

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ‖-x + y‖`
defines a pseudometric space structure. -/
class IsNormedAddGroup (E : Type*) [NormPseudoMetric E] [AddGroup E] where
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y : E, dist x y = ‖-x + y‖ := by aesop

/-- missing doc -/
@[class_abbrev]
structure SeminormedAddGroup (E : Type*) where
  /-- missing doc -/
  [toNormPseudoMetric : NormPseudoMetric E]
  /-- missing doc -/
  [toAddGroup : AddGroup E]
  [toIsNormedAddGroup : IsNormedAddGroup E]

attribute [instance] SeminormedAddGroup.mk

/-- A seminormed group is a group endowed with a norm for which `dist x y = ‖x⁻¹ * y‖` defines a
pseudometric space structure. -/
@[to_additive]
class IsNormedGroup (E : Type*) [NormPseudoMetric E] [Group E] where
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y : E, dist x y = ‖x⁻¹ * y‖ := by aesop

/-- missing doc -/
@[class_abbrev, to_additive]
structure SeminormedGroup (E : Type*) where
  /-- missing doc -/
  [toNormPseudoMetric : NormPseudoMetric E]
  /-- missing doc -/
  [toGroup : Group E]
  [toIsNormedGroup : IsNormedGroup E]

attribute [instance] SeminormedGroup.mk

/-- missing doc -/
@[class_abbrev]
structure NormedAddGroup (E : Type*) where
  /-- missing doc -/
  [toNormMetric : NormMetric E]
  /-- missing doc -/
  [toAddGroup : AddGroup E]
  [toIsNormedAddGroup : IsNormedAddGroup E]

attribute [instance] NormedAddGroup.mk

/-- missing doc -/
@[class_abbrev, to_additive]
structure NormedGroup (E : Type*) where
  /-- missing doc -/
  [toNormMetric : NormMetric E]
  /-- missing doc -/
  [toGroup : Group E]
  [toIsNormedGroup : IsNormedGroup E]

attribute [instance] NormedGroup.mk

/-- missing doc -/
@[class_abbrev]
structure SeminormedAddCommGroup (E : Type*) where
  /-- missing doc -/
  [toNormPseudoMetric : NormPseudoMetric E]
  /-- missing doc -/
  [toAddCommGroup : AddCommGroup E]
  [toIsNormedAddGroup : IsNormedAddGroup E]

attribute [instance] SeminormedAddCommGroup.mk

/-- missing doc -/
@[class_abbrev, to_additive]
structure SeminormedCommGroup (E : Type*) where
  /-- missing doc -/
  [toNormPseudoMetric : NormPseudoMetric E]
  /-- missing doc -/
  [toCommGroup : CommGroup E]
  [toIsNormedGroup : IsNormedGroup E]

attribute [instance] SeminormedCommGroup.mk

/-- missing doc -/
@[class_abbrev]
structure NormedAddCommGroup (E : Type*) where
  /-- missing doc -/
  [toNormMetric : NormMetric E]
  /-- missing doc -/
  [toAddCommGroup : AddCommGroup E]
  [toIsNormedAddGroup : IsNormedAddGroup E]

attribute [instance] NormedAddCommGroup.mk

/-- missing doc -/
@[class_abbrev, to_additive]
structure NormedCommGroup (E : Type*) where
  /-- missing doc -/
  [toNormMetric : NormMetric E]
  /-- missing doc -/
  [toCommGroup : CommGroup E]
  [toIsNormedGroup : IsNormedGroup E]

attribute [instance] NormedCommGroup.mk

-- See note [reducible non-instances]
/-- missing doc -/
@[to_additive /-- missing doc -/]
abbrev NormMetric.ofMulSeparation [NormPseudoMetric E] [Group E] [IsNormedGroup E]
    (h : ∀ x : E, ‖x‖ = 0 → x = 1) :
    NormMetric E where
  toMetricSpace :=
    { eq_of_dist_eq_zero := fun hxy =>
        inv_mul_eq_one.1 <| h _ <| (IsNormedGroup.dist_eq _ _).symm.trans hxy }

-- See note [reducible non-instances]
/-- Construct a `NormedGroup` from a `SeminormedGroup` satisfying `∀ x, ‖x‖ = 0 → x = 1`. This
avoids having to go back to the `(Pseudo)MetricSpace` level when declaring a `NormedGroup`
instance as a special case of a more general `SeminormedGroup` instance. -/
@[to_additive /-- Construct a `NormedAddGroup` from a `SeminormedAddGroup`
satisfying `∀ x, ‖x‖ = 0 → x = 0`. This avoids having to go back to the `(Pseudo)MetricSpace`
level when declaring a `NormedAddGroup` instance as a special case of a more general
`SeminormedAddGroup` instance. -/]
abbrev NormedGroup.ofSeparation [SeminormedGroup E] (h : ∀ x : E, ‖x‖ = 0 → x = 1) :
    NormedGroup E where
  toNormMetric := .ofMulSeparation h

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant distance. -/
@[to_additive
  /-- Construct a seminormed group from a translation-invariant distance. -/]
abbrev IsNormedGroup.ofMulDist [NormPseudoMetric E] [Group E]
    (h₁ : ∀ x : E, ‖x‖ = dist 1 x) (h₂ : ∀ x y z : E, dist x y ≤ dist (z * x) (z * y)) :
    IsNormedGroup E where
  dist_eq x y := by
    rw [h₁]; apply le_antisymm
    · simpa only [div_eq_mul_inv, ← inv_mul_cancel x] using h₂ x y x⁻¹
    · simpa only [mul_inv_cancel, mul_one, ← mul_assoc, one_mul] using h₂ 1 (x⁻¹ * y) x

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a seminormed group from a translation-invariant pseudodistance. -/]
abbrev IsNormedGroup.ofMulDist' [NormPseudoMetric E] [Group E]
    (h₁ : ∀ x : E, ‖x‖ = dist 1 x) (h₂ : ∀ x y z : E, dist (z * x) (z * y) ≤ dist x y) :
    IsNormedGroup E where
  dist_eq x y := by
    rw [h₁]; apply le_antisymm
    · simpa only [mul_inv_cancel, mul_one, ← mul_assoc, one_mul] using h₂ 1 (x⁻¹ * y) x
    · simpa only [div_eq_mul_inv, ← inv_mul_cancel x] using h₂ x y x⁻¹

-- See note [reducible non-instances]
/-- missing doc -/
@[to_additive /-- missing doc -/]
abbrev GroupSeminorm.toNormPseudoMetric [Group E] (f : GroupSeminorm E) : NormPseudoMetric E where
  dist x y := f (x⁻¹ * y)
  norm := f
  dist_self x := by simp only [inv_mul_cancel, map_one_eq_zero]
  dist_triangle x y z := by convert map_mul_le_add f (x⁻¹ * y) (y⁻¹ * z) using 2; group
  dist_comm x y := by convert map_inv_eq_map f (y⁻¹ * x) using 2; group

/-- missing doc -/
@[to_additive /-- missing doc -/]
lemma GroupSeminorm.toIsNormedGroup [Group E] (f : GroupSeminorm E) :
    letI := f.toNormPseudoMetric
    IsNormedGroup E :=
  letI := f.toNormPseudoMetric
  { dist_eq _ _ := rfl }

-- See note [reducible non-instances]
/-- Construct a seminormed group from a seminorm, i.e., registering the pseudodistance and the
pseudometric space structure from the seminorm properties. Note that in most cases this instance
creates bad definitional equalities (e.g., it does not take into account a possibly existing
`UniformSpace` instance on `E`). -/
@[to_additive
  /-- Construct a seminormed group from a seminorm, i.e., registering the pseudodistance
and the pseudometric space structure from the seminorm properties. Note that in most cases this
instance creates bad definitional equalities (e.g., it does not take into account a possibly
existing `UniformSpace` instance on `E`). -/]
abbrev GroupSeminorm.toSeminormedGroup [Group E] (f : GroupSeminorm E) : SeminormedGroup E where
  __ := f.toNormPseudoMetric
  toIsNormedGroup := f.toIsNormedGroup

-- See note [reducible non-instances]
/-- Construct a seminormed group from a seminorm, i.e., registering the pseudodistance and the
pseudometric space structure from the seminorm properties. Note that in most cases this instance
creates bad definitional equalities (e.g., it does not take into account a possibly existing
`UniformSpace` instance on `E`). -/
@[to_additive
  /-- Construct a seminormed group from a seminorm, i.e., registering the pseudodistance
and the pseudometric space structure from the seminorm properties. Note that in most cases this
instance creates bad definitional equalities (e.g., it does not take into account a possibly
existing `UniformSpace` instance on `E`). -/]
abbrev GroupSeminorm.toSeminormedCommGroup [CommGroup E] (f : GroupSeminorm E) :
    SeminormedCommGroup E where
  __ := f.toNormPseudoMetric
  toIsNormedGroup := f.toIsNormedGroup

-- See note [reducible non-instances]
/-- missing doc -/
@[to_additive /-- missing doc -/]
abbrev GroupNorm.toNormMetric [Group E] (f : GroupNorm E) : NormMetric E :=
  { f.toGroupSeminorm.toNormPseudoMetric with
    eq_of_dist_eq_zero := fun h => inv_mul_eq_one.1 <| eq_one_of_map_eq_zero f h }

/-- missing doc -/
@[to_additive /-- missing doc -/]
lemma GroupNorm.toIsNormedGroup [Group E] (f : GroupNorm E) :
    letI := f.toNormMetric
    IsNormedGroup E :=
  letI := f.toNormMetric
  { dist_eq _ _ := rfl }

-- See note [reducible non-instances]
/-- Construct a normed group from a norm, i.e., registering the distance and the metric space
structure from the norm properties. Note that in most cases this instance creates bad definitional
equalities (e.g., it does not take into account a possibly existing `UniformSpace` instance on
`E`). -/
@[to_additive
  /-- Construct a normed group from a norm, i.e., registering the distance and the metric
space structure from the norm properties. Note that in most cases this instance creates bad
definitional equalities (e.g., it does not take into account a possibly existing `UniformSpace`
instance on `E`). -/]
abbrev GroupNorm.toNormedGroup [Group E] (f : GroupNorm E) : NormedGroup E where
  __ := f.toNormMetric
  toIsNormedGroup := f.toIsNormedGroup

-- See note [reducible non-instances]
/-- Construct a normed group from a norm, i.e., registering the distance and the metric space
structure from the norm properties. Note that in most cases this instance creates bad definitional
equalities (e.g., it does not take into account a possibly existing `UniformSpace` instance on
`E`). -/
@[to_additive
  /-- Construct a normed group from a norm, i.e., registering the distance and the metric
space structure from the norm properties. Note that in most cases this instance creates bad
definitional equalities (e.g., it does not take into account a possibly existing `UniformSpace`
instance on `E`). -/]
abbrev GroupNorm.toNormedCommGroup [CommGroup E] (f : GroupNorm E) : NormedCommGroup E where
  __ := f.toNormMetric
  toIsNormedGroup := f.toIsNormedGroup
