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

@[expose] public section


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
class ESeminormedAddMonoid (E : Type*) [TopologicalSpace E]
    extends ContinuousENorm E, AddMonoid E where
  enorm_zero : ‖(0 : E)‖ₑ = 0
  protected enorm_add_le : ∀ x y : E, ‖x + y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ

/-- An enormed monoid is an additive monoid endowed with a continuous enorm,
which is positive definite: in other words, this is an `ESeminormedAddMonoid` with a positive
definiteness condition added. -/
class ENormedAddMonoid (E : Type*) [TopologicalSpace E]
    extends ESeminormedAddMonoid E where
  enorm_eq_zero : ∀ x : E, ‖x‖ₑ = 0 ↔ x = 0

/-- An e-seminormed monoid is a monoid endowed with a continuous enorm.
Note that we only ask for the enorm to be a semi-norm: non-trivial elements may have enorm zero. -/
@[to_additive]
class ESeminormedMonoid (E : Type*) [TopologicalSpace E] extends ContinuousENorm E, Monoid E where
  enorm_zero : ‖(1 : E)‖ₑ = 0
  enorm_mul_le : ∀ x y : E, ‖x * y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ

/-- An enormed monoid is a monoid endowed with a continuous enorm,
which is positive definite: in other words, this is an `ESeminormedMonoid` with a positive
definiteness condition added. -/
@[to_additive]
class ENormedMonoid (E : Type*) [TopologicalSpace E] extends ESeminormedMonoid E where
  enorm_eq_zero : ∀ x : E, ‖x‖ₑ = 0 ↔ x = 1

/-- An e-seminormed commutative monoid is an additive commutative monoid endowed with a continuous
enorm.

We don't have `ESeminormedAddCommMonoid` extend `EMetricSpace`, since the canonical instance `ℝ≥0∞`
is not an `EMetricSpace`. This is because `ℝ≥0∞` carries the order topology, which is distinct from
the topology coming from `edist`. -/
class ESeminormedAddCommMonoid (E : Type*) [TopologicalSpace E]
  extends ESeminormedAddMonoid E, AddCommMonoid E where

/-- An enormed commutative monoid is an additive commutative monoid
endowed with a continuous enorm which is positive definite.

We don't have `ENormedAddCommMonoid` extend `EMetricSpace`, since the canonical instance `ℝ≥0∞`
is not an `EMetricSpace`. This is because `ℝ≥0∞` carries the order topology, which is distinct from
the topology coming from `edist`. -/
class ENormedAddCommMonoid (E : Type*) [TopologicalSpace E]
  extends ESeminormedAddCommMonoid E, ENormedAddMonoid E where

/-- An e-seminormed commutative monoid is a commutative monoid endowed with a continuous enorm. -/
@[to_additive]
class ESeminormedCommMonoid (E : Type*) [TopologicalSpace E]
  extends ESeminormedMonoid E, CommMonoid E where

/-- An enormed commutative monoid is a commutative monoid endowed with a continuous enorm
which is positive definite. -/
@[to_additive]
class ENormedCommMonoid (E : Type*) [TopologicalSpace E]
  extends ESeminormedCommMonoid E, ENormedMonoid E where

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ‖-x + y‖`
defines a pseudometric space structure. -/
class SeminormedAddGroup (E : Type*) extends Norm E, AddGroup E, PseudoMetricSpace E where
  dist := fun x y => ‖-x + y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖-x + y‖ := by aesop

/-- A seminormed group is a group endowed with a norm for which `dist x y = ‖x⁻¹ * y‖` defines a
pseudometric space structure. -/
@[to_additive]
class SeminormedGroup (E : Type*) extends Norm E, Group E, PseudoMetricSpace E where
  dist := fun x y => ‖x⁻¹ * y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x⁻¹ * y‖ := by aesop

/-- A normed group is an additive group endowed with a norm for which `dist x y = ‖-x + y‖` defines
a metric space structure. -/
class NormedAddGroup (E : Type*) extends Norm E, AddGroup E, MetricSpace E where
  dist := fun x y => ‖-x + y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖-x + y‖ := by aesop

/-- A normed group is a group endowed with a norm for which `dist x y = ‖x⁻¹ * y‖` defines a metric
space structure. -/
@[to_additive]
class NormedGroup (E : Type*) extends Norm E, Group E, MetricSpace E where
  dist := fun x y => ‖x⁻¹ * y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x⁻¹ * y‖ := by aesop

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ‖-x + y‖`
defines a pseudometric space structure. -/
class SeminormedAddCommGroup (E : Type*) extends Norm E, AddCommGroup E,
  PseudoMetricSpace E where
  dist := fun x y => ‖-x + y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖-x + y‖ := by aesop

/-- A seminormed group is a group endowed with a norm for which `dist x y = ‖x⁻¹ * y‖`
defines a pseudometric space structure. -/
@[to_additive]
class SeminormedCommGroup (E : Type*) extends Norm E, CommGroup E, PseudoMetricSpace E where
  dist := fun x y => ‖x⁻¹ * y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x⁻¹ * y‖ := by aesop

/-- A normed group is an additive group endowed with a norm for which `dist x y = ‖-x + y‖` defines
a metric space structure. -/
class NormedAddCommGroup (E : Type*) extends Norm E, AddCommGroup E, MetricSpace E where
  dist := fun x y => ‖-x + y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖-x + y‖ := by aesop

/-- A normed group is a group endowed with a norm for which `dist x y = ‖x⁻¹ * y‖` defines a metric
space structure. -/
@[to_additive]
class NormedCommGroup (E : Type*) extends Norm E, CommGroup E, MetricSpace E where
  dist := fun x y => ‖x⁻¹ * y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x⁻¹ * y‖ := by aesop

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) NormedGroup.toSeminormedGroup [NormedGroup E] : SeminormedGroup E :=
  { ‹NormedGroup E› with }

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) NormedCommGroup.toSeminormedCommGroup [NormedCommGroup E] :
    SeminormedCommGroup E :=
  { ‹NormedCommGroup E› with }

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedCommGroup.toSeminormedGroup [SeminormedCommGroup E] :
    SeminormedGroup E :=
  { ‹SeminormedCommGroup E› with }

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) NormedCommGroup.toNormedGroup [NormedCommGroup E] : NormedGroup E :=
  { ‹NormedCommGroup E› with }

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
  dist_eq := ‹SeminormedGroup E›.dist_eq
  toMetricSpace :=
    { eq_of_dist_eq_zero := fun hxy =>
        inv_mul_eq_one.1 <| h _ <| (‹SeminormedGroup E›.dist_eq _ _).symm.trans hxy }

-- See note [reducible non-instances]
/-- Construct a `NormedCommGroup` from a `SeminormedCommGroup` satisfying
`∀ x, ‖x‖ = 0 → x = 1`. This avoids having to go back to the `(Pseudo)MetricSpace` level when
declaring a `NormedCommGroup` instance as a special case of a more general `SeminormedCommGroup`
instance. -/
@[to_additive /-- Construct a `NormedAddCommGroup` from a
`SeminormedAddCommGroup` satisfying `∀ x, ‖x‖ = 0 → x = 0`. This avoids having to go back to the
`(Pseudo)MetricSpace` level when declaring a `NormedAddCommGroup` instance as a special case
of a more general `SeminormedAddCommGroup` instance. -/]
abbrev NormedCommGroup.ofSeparation [SeminormedCommGroup E] (h : ∀ x : E, ‖x‖ = 0 → x = 1) :
    NormedCommGroup E :=
  { ‹SeminormedCommGroup E›, NormedGroup.ofSeparation h with }

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant distance. -/
@[to_additive
  /-- Construct a seminormed group from a translation-invariant distance. -/]
abbrev SeminormedGroup.ofMulDist [Norm E] [Group E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist 1 x) (h₂ : ∀ x y z : E, dist x y ≤ dist (z * x) (z * y)) :
    SeminormedGroup E where
  dist_eq x y := by
    rw [h₁]; apply le_antisymm
    · simpa only [div_eq_mul_inv, ← inv_mul_cancel x] using h₂ x y x⁻¹
    · simpa only [mul_inv_cancel, mul_one, ← mul_assoc, one_mul] using h₂ 1 (x⁻¹ * y) x

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a seminormed group from a translation-invariant pseudodistance. -/]
abbrev SeminormedGroup.ofMulDist' [Norm E] [Group E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist 1 x) (h₂ : ∀ x y z : E, dist (z * x) (z * y) ≤ dist x y) :
    SeminormedGroup E where
  dist_eq x y := by
    rw [h₁]; apply le_antisymm
    · simpa only [mul_inv_cancel, mul_one, ← mul_assoc, one_mul] using h₂ 1 (x⁻¹ * y) x
    · simpa only [div_eq_mul_inv, ← inv_mul_cancel x] using h₂ x y x⁻¹

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a seminormed group from a translation-invariant pseudodistance. -/]
abbrev SeminormedCommGroup.ofMulDist [Norm E] [CommGroup E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist 1 x) (h₂ : ∀ x y z : E, dist x y ≤ dist (z * x) (z * y)) :
    SeminormedCommGroup E :=
  { SeminormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a seminormed group from a translation-invariant pseudodistance. -/]
abbrev SeminormedCommGroup.ofMulDist' [Norm E] [CommGroup E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist 1 x) (h₂ : ∀ x y z : E, dist (z * x) (z * y) ≤ dist x y) :
    SeminormedCommGroup E :=
  { SeminormedGroup.ofMulDist' h₁ h₂ with
    mul_comm := mul_comm }

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant distance. -/
@[to_additive
  /-- Construct a normed group from a translation-invariant distance. -/]
abbrev NormedGroup.ofMulDist [Norm E] [Group E] [MetricSpace E] (h₁ : ∀ x : E, ‖x‖ = dist 1 x)
    (h₂ : ∀ x y z : E, dist x y ≤ dist (z * x) (z * y)) : NormedGroup E :=
  { SeminormedGroup.ofMulDist h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a normed group from a translation-invariant pseudodistance. -/]
abbrev NormedGroup.ofMulDist' [Norm E] [Group E] [MetricSpace E] (h₁ : ∀ x : E, ‖x‖ = dist 1 x)
    (h₂ : ∀ x y z : E, dist (z * x) (z * y) ≤ dist x y) : NormedGroup E :=
  { SeminormedGroup.ofMulDist' h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive
/-- Construct a normed group from a translation-invariant pseudodistance. -/]
abbrev NormedCommGroup.ofMulDist [Norm E] [CommGroup E] [MetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist 1 x) (h₂ : ∀ x y z : E, dist x y ≤ dist (z * x) (z * y)) :
    NormedCommGroup E :=
  { NormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a normed group from a translation-invariant pseudodistance. -/]
abbrev NormedCommGroup.ofMulDist' [Norm E] [CommGroup E] [MetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist 1 x) (h₂ : ∀ x y z : E, dist (z * x) (z * y) ≤ dist x y) :
    NormedCommGroup E :=
  { NormedGroup.ofMulDist' h₁ h₂ with
    mul_comm := mul_comm }

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
  dist x y := f (x⁻¹ * y)
  norm := f
  dist_eq _ _ := rfl
  dist_self x := by simp only [inv_mul_cancel, map_one_eq_zero]
  dist_triangle x y z := by convert map_mul_le_add f (x⁻¹ * y) (y⁻¹ * z) using 2; group
  dist_comm x y := by convert map_inv_eq_map f (y⁻¹ * x) using 2; group

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
    SeminormedCommGroup E :=
  { f.toSeminormedGroup with
    mul_comm := mul_comm }

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
abbrev GroupNorm.toNormedGroup [Group E] (f : GroupNorm E) : NormedGroup E :=
  { f.toGroupSeminorm.toSeminormedGroup with
    eq_of_dist_eq_zero := fun h => inv_mul_eq_one.1 <| eq_one_of_map_eq_zero f h }

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
abbrev GroupNorm.toNormedCommGroup [CommGroup E] (f : GroupNorm E) : NormedCommGroup E :=
  { f.toNormedGroup with
    mul_comm := mul_comm }
