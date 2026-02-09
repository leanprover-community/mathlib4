/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.Real

/-!
# Normed (semi)groups

In this file we define 10 classes:

* `Norm`, `NNNorm`: auxiliary classes endowing a type `α` with a function `norm : α → ℝ`
  (notation: `‖x‖`) and `nnnorm : α → ℝ≥0` (notation: `‖x‖₊`), respectively;
* `Seminormed...Group`: A seminormed (additive) (commutative) group is an (additive) (commutative)
  group with a norm and a compatible pseudometric space structure:
  `∀ x y, dist x y = ‖x / y‖` or `∀ x y, dist x y = ‖x - y‖`, depending on the group operation.
* `Normed...Group`: A normed (additive) (commutative) group is an (additive) (commutative) group
  with a norm and a compatible metric space structure.

We also prove basic properties of (semi)normed groups and provide some instances.

## Notes

The current convention `dist x y = ‖x - y‖` means that the distance is invariant under right
addition, but actions in mathlib are usually from the left. This means we might want to change it to
`dist x y = ‖-x + y‖`.

The normed group hierarchy would lend itself well to a mixin design (that is, having
`SeminormedGroup` and `SeminormedAddGroup` not extend `Group` and `AddGroup`), but we choose not
to for performance concerns.

## Tags

normed group
-/

set_option linter.style.longFile 1700

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

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ‖x - y‖`
defines a pseudometric space structure. -/
class SeminormedAddGroup (E : Type*) extends Norm E, AddGroup E, PseudoMetricSpace E where
  dist := fun x y => ‖x - y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by aesop

/-- A seminormed group is a group endowed with a norm for which `dist x y = ‖x / y‖` defines a
pseudometric space structure. -/
@[to_additive]
class SeminormedGroup (E : Type*) extends Norm E, Group E, PseudoMetricSpace E where
  dist := fun x y => ‖x / y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x / y‖ := by aesop

/-- A normed group is an additive group endowed with a norm for which `dist x y = ‖x - y‖` defines a
metric space structure. -/
class NormedAddGroup (E : Type*) extends Norm E, AddGroup E, MetricSpace E where
  dist := fun x y => ‖x - y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by aesop

/-- A normed group is a group endowed with a norm for which `dist x y = ‖x / y‖` defines a metric
space structure. -/
@[to_additive]
class NormedGroup (E : Type*) extends Norm E, Group E, MetricSpace E where
  dist := fun x y => ‖x / y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x / y‖ := by aesop

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ‖x - y‖`
defines a pseudometric space structure. -/
class SeminormedAddCommGroup (E : Type*) extends Norm E, AddCommGroup E,
  PseudoMetricSpace E where
  dist := fun x y => ‖x - y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by aesop

/-- A seminormed group is a group endowed with a norm for which `dist x y = ‖x / y‖`
defines a pseudometric space structure. -/
@[to_additive]
class SeminormedCommGroup (E : Type*) extends Norm E, CommGroup E, PseudoMetricSpace E where
  dist := fun x y => ‖x / y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x / y‖ := by aesop

/-- A normed group is an additive group endowed with a norm for which `dist x y = ‖x - y‖` defines a
metric space structure. -/
class NormedAddCommGroup (E : Type*) extends Norm E, AddCommGroup E, MetricSpace E where
  dist := fun x y => ‖x - y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by aesop

/-- A normed group is a group endowed with a norm for which `dist x y = ‖x / y‖` defines a metric
space structure. -/
@[to_additive]
class NormedCommGroup (E : Type*) extends Norm E, CommGroup E, MetricSpace E where
  dist := fun x y => ‖x / y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x / y‖ := by aesop

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
        div_eq_one.1 <| h _ <| (‹SeminormedGroup E›.dist_eq _ _).symm.trans hxy }

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
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
    SeminormedGroup E where
  dist_eq x y := by
    rw [h₁]; apply le_antisymm
    · simpa only [div_eq_mul_inv, ← mul_inv_cancel y] using h₂ _ _ _
    · simpa only [div_mul_cancel, one_mul] using h₂ (x / y) 1 y

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a seminormed group from a translation-invariant pseudodistance. -/]
abbrev SeminormedGroup.ofMulDist' [Norm E] [Group E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
    SeminormedGroup E where
  dist_eq x y := by
    rw [h₁]; apply le_antisymm
    · simpa only [div_mul_cancel, one_mul] using h₂ (x / y) 1 y
    · simpa only [div_eq_mul_inv, ← mul_inv_cancel y] using h₂ _ _ _

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a seminormed group from a translation-invariant pseudodistance. -/]
abbrev SeminormedCommGroup.ofMulDist [Norm E] [CommGroup E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
    SeminormedCommGroup E :=
  { SeminormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a seminormed group from a translation-invariant pseudodistance. -/]
abbrev SeminormedCommGroup.ofMulDist' [Norm E] [CommGroup E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
    SeminormedCommGroup E :=
  { SeminormedGroup.ofMulDist' h₁ h₂ with
    mul_comm := mul_comm }

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant distance. -/
@[to_additive
  /-- Construct a normed group from a translation-invariant distance. -/]
abbrev NormedGroup.ofMulDist [Norm E] [Group E] [MetricSpace E] (h₁ : ∀ x : E, ‖x‖ = dist x 1)
    (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) : NormedGroup E :=
  { SeminormedGroup.ofMulDist h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a normed group from a translation-invariant pseudodistance. -/]
abbrev NormedGroup.ofMulDist' [Norm E] [Group E] [MetricSpace E] (h₁ : ∀ x : E, ‖x‖ = dist x 1)
    (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) : NormedGroup E :=
  { SeminormedGroup.ofMulDist' h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive
/-- Construct a normed group from a translation-invariant pseudodistance. -/]
abbrev NormedCommGroup.ofMulDist [Norm E] [CommGroup E] [MetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
    NormedCommGroup E :=
  { NormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive
  /-- Construct a normed group from a translation-invariant pseudodistance. -/]
abbrev NormedCommGroup.ofMulDist' [Norm E] [CommGroup E] [MetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
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
  dist x y := f (x / y)
  norm := f
  dist_eq _ _ := rfl
  dist_self x := by simp only [div_self', map_one_eq_zero]
  dist_triangle := le_map_div_add_map_div f
  dist_comm := map_div_rev f

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
    eq_of_dist_eq_zero := fun h => div_eq_one.1 <| eq_one_of_map_eq_zero f h }

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

section Discrete

variable {G : Type*}

/-- The trivial norm on a group that already has a discrete topology,
where every distinct element is 1 away from another.
This takes an explicit `DiscreteTopology` instance to ensure that the forgetful
inheritance to topology matches. -/
@[to_additive /-- The trivial seminorm on an additive group that already has a discrete topology,
where every distinct element is 1 away from another.
This takes an explicit `DiscreteTopology` instance to ensure that the forgetful
inheritance to topology matches. -/]
def SeminormedGroup.ofDiscreteTopology [TopologicalSpace G] [DiscreteTopology G]
    [Group G] [DecidableEq G] : SeminormedGroup G where
  __ := PseudoMetricSpace.ofDiscreteTopology (X := G)
  norm x := if x = 1 then 0 else 1
  dist_eq x y := by
    rw [PseudoMetricSpace.ofDiscreteTopology_dist_def]
    split_ifs <;>
    simp_all [div_eq_one]

/-- The trivial norm on a group that already has a discrete topology,
where every distinct element is 1 away from another.
This takes an explicit `DiscreteTopology` instance to ensure that the forgetful
inheritance to topology matches. -/
@[to_additive /-- The trivial norm on an additive group that already has a discrete topology,
where every distinct element is 1 away from another.
This takes an explicit `DiscreteTopology` instance to ensure that the forgetful
inheritance to topology matches. -/]
def NormedGroup.ofDiscreteTopology [TopologicalSpace G] [DiscreteTopology G]
    [Group G] [DecidableEq G] : NormedGroup G where
  __ := MetricSpace.ofDiscreteTopology (X := G)
  __ := SeminormedGroup.ofDiscreteTopology

variable [TopologicalSpace G] [DiscreteTopology G] [Group G] [DecidableEq G]

@[to_additive]
lemma SeminormedGroup.ofDiscreteTopology_norm_def (x : G) :
    letI := SeminormedGroup.ofDiscreteTopology (G := G)
    ‖x‖ = if x = 1 then 0 else 1 :=
  rfl

@[to_additive]
lemma NormedGroup.ofDiscreteTopology_norm_def (x : G) :
    letI := NormedGroup.ofDiscreteTopology (G := G)
    ‖x‖ = if x = 1 then 0 else 1 :=
  rfl

end Discrete

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E}
  {a a₁ a₂ b c d : E} {r r₁ r₂ : ℝ}

@[to_additive]
theorem dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖ :=
  SeminormedGroup.dist_eq _ _

@[to_additive]
theorem dist_eq_norm_div' (a b : E) : dist a b = ‖b / a‖ := by rw [dist_comm, dist_eq_norm_div]

alias dist_eq_norm := dist_eq_norm_sub

alias dist_eq_norm' := dist_eq_norm_sub'

@[to_additive of_forall_le_norm]
lemma DiscreteTopology.of_forall_le_norm' (hpos : 0 < r) (hr : ∀ x : E, x ≠ 1 → r ≤ ‖x‖) :
    DiscreteTopology E :=
  .of_forall_le_dist hpos fun x y hne ↦ by
    simp only [dist_eq_norm_div]
    exact hr _ (div_ne_one.2 hne)

@[to_additive (attr := simp)]
theorem dist_one_right (a : E) : dist a 1 = ‖a‖ := by rw [dist_eq_norm_div, div_one]

@[to_additive]
theorem inseparable_one_iff_norm {a : E} : Inseparable a 1 ↔ ‖a‖ = 0 := by
  rw [Metric.inseparable_iff, dist_one_right]

@[to_additive]
lemma dist_one_left (a : E) : dist 1 a = ‖a‖ := by rw [dist_comm, dist_one_right]

@[to_additive (attr := simp)]
lemma dist_one : dist (1 : E) = norm := funext dist_one_left

@[to_additive]
theorem norm_div_rev (a b : E) : ‖a / b‖ = ‖b / a‖ := by
  simpa only [dist_eq_norm_div] using dist_comm a b

@[to_additive (attr := simp) norm_neg]
theorem norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖ := by simpa using norm_div_rev 1 a

@[to_additive (attr := simp) norm_abs_zsmul]
theorem norm_zpow_abs (a : E) (n : ℤ) : ‖a ^ |n|‖ = ‖a ^ n‖ := by
  rcases le_total 0 n with hn | hn <;> simp [hn, abs_of_nonneg, abs_of_nonpos]

@[to_additive (attr := simp) norm_natAbs_smul]
theorem norm_pow_natAbs (a : E) (n : ℤ) : ‖a ^ n.natAbs‖ = ‖a ^ n‖ := by
  rw [← zpow_natCast, ← Int.abs_eq_natAbs, norm_zpow_abs]

@[to_additive norm_isUnit_zsmul]
theorem norm_zpow_isUnit (a : E) {n : ℤ} (hn : IsUnit n) : ‖a ^ n‖ = ‖a‖ := by
  rw [← norm_pow_natAbs, Int.isUnit_iff_natAbs_eq.mp hn, pow_one]

@[simp]
theorem norm_units_zsmul {E : Type*} [SeminormedAddGroup E] (n : ℤˣ) (a : E) : ‖n • a‖ = ‖a‖ :=
  norm_isUnit_zsmul a n.isUnit

open scoped symmDiff in
@[to_additive]
theorem dist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    dist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖ := by
  rw [dist_eq_norm_div, Set.apply_mulIndicator_symmDiff norm_inv']

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add_le /-- **Triangle inequality** for the norm. -/]
theorem norm_mul_le' (a b : E) : ‖a * b‖ ≤ ‖a‖ + ‖b‖ := by
  simpa [dist_eq_norm_div] using dist_triangle a 1 b⁻¹

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add_le_of_le /-- **Triangle inequality** for the norm. -/]
theorem norm_mul_le_of_le' (h₁ : ‖a₁‖ ≤ r₁) (h₂ : ‖a₂‖ ≤ r₂) : ‖a₁ * a₂‖ ≤ r₁ + r₂ :=
  (norm_mul_le' a₁ a₂).trans <| add_le_add h₁ h₂

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add₃_le /-- **Triangle inequality** for the norm. -/]
lemma norm_mul₃_le' : ‖a * b * c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := norm_mul_le_of_le' (norm_mul_le' _ _) le_rfl

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add₄_le /-- **Triangle inequality** for the norm. -/]
lemma norm_mul₄_le' : ‖a * b * c * d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ :=
  norm_mul_le_of_le' norm_mul₃_le' le_rfl

@[to_additive]
lemma norm_div_le_norm_div_add_norm_div (a b c : E) : ‖a / c‖ ≤ ‖a / b‖ + ‖b / c‖ := by
  simpa only [dist_eq_norm_div] using dist_triangle a b c

@[to_additive]
lemma norm_le_norm_div_add (a b : E) : ‖a‖ ≤ ‖a / b‖ + ‖b‖ := by
  simpa only [div_one] using norm_div_le_norm_div_add_norm_div a b 1

@[to_additive (attr := simp) norm_nonneg]
theorem norm_nonneg' (a : E) : 0 ≤ ‖a‖ := by
  rw [← dist_one_right]
  exact dist_nonneg

attribute [bound] norm_nonneg
attribute [grind .] norm_nonneg

@[to_additive (attr := simp) abs_norm]
theorem abs_norm' (z : E) : |‖z‖| = ‖z‖ := abs_of_nonneg <| norm_nonneg' _

@[to_additive (attr := simp) norm_zero]
theorem norm_one' : ‖(1 : E)‖ = 0 := by rw [← dist_one_right, dist_self]

@[to_additive]
theorem ne_one_of_norm_ne_zero : ‖a‖ ≠ 0 → a ≠ 1 :=
  mt <| by
    rintro rfl
    exact norm_one'

@[to_additive (attr := nontriviality) norm_of_subsingleton]
theorem norm_of_subsingleton' [Subsingleton E] (a : E) : ‖a‖ = 0 := by
  rw [Subsingleton.elim a 1, norm_one']

@[to_additive zero_lt_one_add_norm_sq]
theorem zero_lt_one_add_norm_sq' (x : E) : 0 < 1 + ‖x‖ ^ 2 := by
  positivity

@[to_additive]
theorem norm_div_le (a b : E) : ‖a / b‖ ≤ ‖a‖ + ‖b‖ := by
  simpa [dist_eq_norm_div] using dist_triangle a 1 b

attribute [bound] norm_sub_le

@[to_additive]
theorem norm_div_le_of_le {r₁ r₂ : ℝ} (H₁ : ‖a₁‖ ≤ r₁) (H₂ : ‖a₂‖ ≤ r₂) : ‖a₁ / a₂‖ ≤ r₁ + r₂ :=
  (norm_div_le a₁ a₂).trans <| add_le_add H₁ H₂

@[to_additive dist_le_norm_add_norm]
theorem dist_le_norm_add_norm' (a b : E) : dist a b ≤ ‖a‖ + ‖b‖ := by
  rw [dist_eq_norm_div]
  apply norm_div_le

@[to_additive abs_norm_sub_norm_le]
theorem abs_norm_sub_norm_le' (a b : E) : |‖a‖ - ‖b‖| ≤ ‖a / b‖ := by
  simpa [dist_eq_norm_div] using abs_dist_sub_le a b 1

@[to_additive norm_sub_norm_le]
theorem norm_sub_norm_le' (a b : E) : ‖a‖ - ‖b‖ ≤ ‖a / b‖ :=
  (le_abs_self _).trans (abs_norm_sub_norm_le' a b)

@[to_additive (attr := bound)]
theorem norm_sub_le_norm_mul (a b : E) : ‖a‖ - ‖b‖ ≤ ‖a * b‖ := by
  simpa using norm_mul_le' (a * b) (b⁻¹)

@[to_additive dist_norm_norm_le]
theorem dist_norm_norm_le' (a b : E) : dist ‖a‖ ‖b‖ ≤ ‖a / b‖ :=
  abs_norm_sub_norm_le' a b

@[to_additive]
theorem norm_le_norm_add_norm_div' (u v : E) : ‖u‖ ≤ ‖v‖ + ‖u / v‖ := by
  rw [add_comm]
  refine (norm_mul_le' _ _).trans_eq' ?_
  rw [div_mul_cancel]

@[to_additive]
theorem norm_le_norm_add_norm_div (u v : E) : ‖v‖ ≤ ‖u‖ + ‖u / v‖ := by
  rw [norm_div_rev]
  exact norm_le_norm_add_norm_div' v u

alias norm_le_insert' := norm_le_norm_add_norm_sub'
alias norm_le_insert := norm_le_norm_add_norm_sub

@[to_additive]
theorem norm_le_mul_norm_add (u v : E) : ‖u‖ ≤ ‖u * v‖ + ‖v‖ :=
  calc
    ‖u‖ = ‖u * v / v‖ := by rw [mul_div_cancel_right]
    _ ≤ ‖u * v‖ + ‖v‖ := norm_div_le _ _

/-- An analogue of `norm_le_mul_norm_add` for the multiplication from the left. -/
@[to_additive /-- An analogue of `norm_le_add_norm_add` for the addition from the left. -/]
theorem norm_le_mul_norm_add' (u v : E) : ‖v‖ ≤ ‖u * v‖ + ‖u‖ :=
  calc
    ‖v‖ = ‖u⁻¹ * (u * v)‖ := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    _ ≤ ‖u⁻¹‖ + ‖u * v‖ := norm_mul_le' u⁻¹ (u * v)
    _ = ‖u * v‖ + ‖u‖ := by rw [norm_inv', add_comm]

@[to_additive]
lemma norm_mul_eq_norm_right {x : E} (y : E) (h : ‖x‖ = 0) : ‖x * y‖ = ‖y‖ := by
  apply le_antisymm ?_ ?_
  · simpa [h] using norm_mul_le' x y
  · simpa [h] using norm_le_mul_norm_add' x y

@[to_additive]
lemma norm_mul_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 0) : ‖x * y‖ = ‖x‖ := by
  apply le_antisymm ?_ ?_
  · simpa [h] using norm_mul_le' x y
  · simpa [h] using norm_le_mul_norm_add x y

@[to_additive]
lemma norm_div_eq_norm_right {x : E} (y : E) (h : ‖x‖ = 0) : ‖x / y‖ = ‖y‖ := by
  apply le_antisymm ?_ ?_
  · simpa [h] using norm_div_le x y
  · simpa [h, norm_div_rev x y] using norm_sub_norm_le' y x

@[to_additive]
lemma norm_div_eq_norm_left (x : E) {y : E} (h : ‖y‖ = 0) : ‖x / y‖ = ‖x‖ := by
  apply le_antisymm ?_ ?_
  · simpa [h] using norm_div_le x y
  · simpa [h] using norm_sub_norm_le' x y

@[to_additive ball_eq]
theorem ball_eq' (y : E) (ε : ℝ) : ball y ε = { x | ‖x / y‖ < ε } :=
  Set.ext fun a => by simp [dist_eq_norm_div]

@[to_additive]
theorem ball_one_eq (r : ℝ) : ball (1 : E) r = { x | ‖x‖ < r } :=
  Set.ext fun a => by simp

@[to_additive mem_ball_iff_norm]
theorem mem_ball_iff_norm'' : b ∈ ball a r ↔ ‖b / a‖ < r := by rw [mem_ball, dist_eq_norm_div]

@[to_additive mem_ball_iff_norm']
theorem mem_ball_iff_norm''' : b ∈ ball a r ↔ ‖a / b‖ < r := by rw [mem_ball', dist_eq_norm_div]

@[to_additive]
theorem mem_ball_one_iff : a ∈ ball (1 : E) r ↔ ‖a‖ < r := by rw [mem_ball, dist_one_right]

@[to_additive mem_closedBall_iff_norm]
theorem mem_closedBall_iff_norm'' : b ∈ closedBall a r ↔ ‖b / a‖ ≤ r := by
  rw [mem_closedBall, dist_eq_norm_div]

@[to_additive]
theorem mem_closedBall_one_iff : a ∈ closedBall (1 : E) r ↔ ‖a‖ ≤ r := by
  rw [mem_closedBall, dist_one_right]

@[to_additive mem_closedBall_iff_norm']
theorem mem_closedBall_iff_norm''' : b ∈ closedBall a r ↔ ‖a / b‖ ≤ r := by
  rw [mem_closedBall', dist_eq_norm_div]

@[to_additive norm_le_of_mem_closedBall]
theorem norm_le_of_mem_closedBall' (h : b ∈ closedBall a r) : ‖b‖ ≤ ‖a‖ + r :=
  (norm_le_norm_add_norm_div' _ _).trans <| add_le_add_right (by rwa [← dist_eq_norm_div]) _

@[to_additive norm_le_norm_add_const_of_dist_le]
theorem norm_le_norm_add_const_of_dist_le' : dist a b ≤ r → ‖a‖ ≤ ‖b‖ + r :=
  norm_le_of_mem_closedBall'

@[to_additive norm_lt_of_mem_ball]
theorem norm_lt_of_mem_ball' (h : b ∈ ball a r) : ‖b‖ < ‖a‖ + r :=
  (norm_le_norm_add_norm_div' _ _).trans_lt <| add_lt_add_right (by rwa [← dist_eq_norm_div]) _

@[to_additive]
theorem norm_div_sub_norm_div_le_norm_div (u v w : E) : ‖u / w‖ - ‖v / w‖ ≤ ‖u / v‖ := by
  simpa only [div_div_div_cancel_right] using norm_sub_norm_le' (u / w) (v / w)

@[to_additive norm_add_sub_norm_sub_le_two_mul]
lemma norm_mul_sub_norm_div_le_two_mul {E : Type*} [SeminormedGroup E] (u v : E) :
    ‖u * v‖ - ‖u / v‖ ≤ 2 * ‖v‖ := by
  simpa [-tsub_le_iff_right, tsub_le_iff_left, two_mul, add_assoc]
    using norm_mul₃_le' (a := (u / v)) (b := v) (c := v)

@[to_additive norm_add_sub_norm_sub_le_two_mul_min]
lemma norm_mul_sub_norm_div_le_two_mul_min {E : Type*} [SeminormedCommGroup E] (u v : E) :
    ‖u * v‖ - ‖u / v‖ ≤ 2 * min ‖u‖ ‖v‖ := by
  rw [mul_min_of_nonneg _ _ (by positivity)]
  refine le_min ?_ (norm_mul_sub_norm_div_le_two_mul u v)
  rw [norm_div_rev, mul_comm]
  exact norm_mul_sub_norm_div_le_two_mul _ _

-- Higher priority to fire before `mem_sphere`.
@[to_additive (attr := simp high) mem_sphere_iff_norm]
theorem mem_sphere_iff_norm' : b ∈ sphere a r ↔ ‖b / a‖ = r := by simp [dist_eq_norm_div]

@[to_additive] -- `simp` can prove this
theorem mem_sphere_one_iff_norm : a ∈ sphere (1 : E) r ↔ ‖a‖ = r := by simp

@[to_additive (attr := simp) norm_eq_of_mem_sphere]
theorem norm_eq_of_mem_sphere' (x : sphere (1 : E) r) : ‖(x : E)‖ = r :=
  mem_sphere_one_iff_norm.mp x.2

@[to_additive]
theorem ne_one_of_mem_sphere (hr : r ≠ 0) (x : sphere (1 : E) r) : (x : E) ≠ 1 :=
  ne_one_of_norm_ne_zero <| by rwa [norm_eq_of_mem_sphere' x]

@[to_additive ne_zero_of_mem_unit_sphere]
theorem ne_one_of_mem_unit_sphere (x : sphere (1 : E) 1) : (x : E) ≠ 1 :=
  ne_one_of_mem_sphere one_ne_zero _

variable (E)

/-- The norm of a seminormed group as a group seminorm. -/
@[to_additive /-- The norm of a seminormed group as an additive group seminorm. -/]
def normGroupSeminorm : GroupSeminorm E :=
  ⟨norm, norm_one', norm_mul_le', norm_inv'⟩

@[to_additive (attr := simp)]
theorem coe_normGroupSeminorm : ⇑(normGroupSeminorm E) = norm :=
  rfl

variable {E}

@[to_additive]
theorem NormedCommGroup.tendsto_nhds_one {f : α → E} {l : Filter α} :
    Tendsto f l (𝓝 1) ↔ ∀ ε > 0, ∀ᶠ x in l, ‖f x‖ < ε :=
  Metric.tendsto_nhds.trans <| by simp only [dist_one_right]

@[to_additive]
theorem NormedCommGroup.tendsto_nhds_nhds {f : E → F} {x : E} {y : F} :
    Tendsto f (𝓝 x) (𝓝 y) ↔ ∀ ε > 0, ∃ δ > 0, ∀ x', ‖x' / x‖ < δ → ‖f x' / y‖ < ε := by
  simp_rw [Metric.tendsto_nhds_nhds, dist_eq_norm_div]

@[to_additive]
theorem NormedCommGroup.nhds_basis_norm_lt (x : E) :
    (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { y | ‖y / x‖ < ε } := by
  simp_rw [← ball_eq']
  exact Metric.nhds_basis_ball

@[to_additive]
theorem NormedCommGroup.nhds_one_basis_norm_lt :
    (𝓝 (1 : E)).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { y | ‖y‖ < ε } := by
  convert NormedCommGroup.nhds_basis_norm_lt (1 : E)
  simp

@[to_additive]
theorem NormedCommGroup.uniformity_basis_dist :
    (𝓤 E).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : E × E | ‖p.fst / p.snd‖ < ε } := by
  convert Metric.uniformity_basis_dist (α := E) using 1
  simp [dist_eq_norm_div]

open Finset

variable [FunLike 𝓕 E F]

section NNNorm

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedGroup.toNNNorm : NNNorm E :=
  ⟨fun a => ⟨‖a‖, norm_nonneg' a⟩⟩

@[to_additive (attr := simp, norm_cast) coe_nnnorm]
theorem coe_nnnorm' (a : E) : (‖a‖₊ : ℝ) = ‖a‖ := rfl

@[to_additive (attr := simp) coe_comp_nnnorm]
theorem coe_comp_nnnorm' : (toReal : ℝ≥0 → ℝ) ∘ (nnnorm : E → ℝ≥0) = norm :=
  rfl

@[to_additive (attr := simp) norm_toNNReal]
theorem norm_toNNReal' : ‖a‖.toNNReal = ‖a‖₊ :=
  @Real.toNNReal_coe ‖a‖₊

@[to_additive (attr := simp) toReal_enorm]
lemma toReal_enorm' (x : E) : ‖x‖ₑ.toReal = ‖x‖ := by simp [enorm]

@[to_additive (attr := simp) ofReal_norm]
lemma ofReal_norm' (x : E) : .ofReal ‖x‖ = ‖x‖ₑ := by
  simp [enorm, ENNReal.ofReal, Real.toNNReal, nnnorm]

@[to_additive enorm_eq_iff_norm_eq]
theorem enorm'_eq_iff_norm_eq {x : E} {y : F} : ‖x‖ₑ = ‖y‖ₑ ↔ ‖x‖ = ‖y‖ := by
  simp only [← ofReal_norm']
  refine ⟨fun h ↦ ?_, fun h ↦ by congr⟩
  exact (Real.toNNReal_eq_toNNReal_iff (norm_nonneg' _) (norm_nonneg' _)).mp (ENNReal.coe_inj.mp h)

@[to_additive enorm_le_iff_norm_le]
theorem enorm'_le_iff_norm_le {x : E} {y : F} : ‖x‖ₑ ≤ ‖y‖ₑ ↔ ‖x‖ ≤ ‖y‖ := by
  simp only [← ofReal_norm']
  refine ⟨fun h ↦ ?_, fun h ↦ by gcongr⟩
  rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg' _)] at h
  exact h

@[to_additive]
theorem nndist_eq_nnnorm_div (a b : E) : nndist a b = ‖a / b‖₊ :=
  NNReal.eq <| dist_eq_norm_div _ _

alias nndist_eq_nnnorm := nndist_eq_nnnorm_sub

@[to_additive (attr := simp)]
theorem nndist_one_right (a : E) : nndist a 1 = ‖a‖₊ := by simp [nndist_eq_nnnorm_div]

@[to_additive (attr := simp)]
lemma edist_one_right (a : E) : edist a 1 = ‖a‖ₑ := by simp [edist_nndist, nndist_one_right, enorm]

@[to_additive (attr := simp) nnnorm_zero]
theorem nnnorm_one' : ‖(1 : E)‖₊ = 0 := NNReal.eq norm_one'

@[to_additive]
theorem ne_one_of_nnnorm_ne_zero {a : E} : ‖a‖₊ ≠ 0 → a ≠ 1 :=
  mt <| by
    rintro rfl
    exact nnnorm_one'

@[to_additive nnnorm_add_le]
theorem nnnorm_mul_le' (a b : E) : ‖a * b‖₊ ≤ ‖a‖₊ + ‖b‖₊ :=
  NNReal.coe_le_coe.1 <| norm_mul_le' a b

@[to_additive norm_nsmul_le]
lemma norm_pow_le_mul_norm : ∀ {n : ℕ}, ‖a ^ n‖ ≤ n * ‖a‖
  | 0 => by simp
  | n + 1 => by simpa [pow_succ, add_mul] using norm_mul_le_of_le' norm_pow_le_mul_norm le_rfl

@[to_additive nnnorm_nsmul_le]
lemma nnnorm_pow_le_mul_norm {n : ℕ} : ‖a ^ n‖₊ ≤ n * ‖a‖₊ := by
  simpa only [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast] using norm_pow_le_mul_norm

@[to_additive (attr := simp) nnnorm_neg]
theorem nnnorm_inv' (a : E) : ‖a⁻¹‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_inv' a

@[to_additive (attr := simp) nnnorm_abs_zsmul]
theorem nnnorm_zpow_abs (a : E) (n : ℤ) : ‖a ^ |n|‖₊ = ‖a ^ n‖₊ :=
  NNReal.eq <| norm_zpow_abs a n

@[to_additive (attr := simp) nnnorm_natAbs_smul]
theorem nnnorm_pow_natAbs (a : E) (n : ℤ) : ‖a ^ n.natAbs‖₊ = ‖a ^ n‖₊ :=
  NNReal.eq <| norm_pow_natAbs a n

@[to_additive nnnorm_isUnit_zsmul]
theorem nnnorm_zpow_isUnit (a : E) {n : ℤ} (hn : IsUnit n) : ‖a ^ n‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_zpow_isUnit a hn

@[simp]
theorem nnnorm_units_zsmul {E : Type*} [SeminormedAddGroup E] (n : ℤˣ) (a : E) : ‖n • a‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_isUnit_zsmul a n.isUnit

@[to_additive (attr := simp)]
theorem nndist_one_left (a : E) : nndist 1 a = ‖a‖₊ := by simp [nndist_eq_nnnorm_div]

@[to_additive (attr := simp)]
theorem edist_one_left (a : E) : edist 1 a = ‖a‖₊ := by
  rw [edist_nndist, nndist_one_left]

open scoped symmDiff in
@[to_additive]
theorem nndist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    nndist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊ :=
  NNReal.eq <| dist_mulIndicator s t f x

@[to_additive]
theorem nnnorm_div_le (a b : E) : ‖a / b‖₊ ≤ ‖a‖₊ + ‖b‖₊ :=
  NNReal.coe_le_coe.1 <| norm_div_le _ _

@[to_additive]
lemma enorm_div_le : ‖a / b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := by
  simpa [enorm, ← ENNReal.coe_add] using nnnorm_div_le a b

@[to_additive nndist_nnnorm_nnnorm_le]
theorem nndist_nnnorm_nnnorm_le' (a b : E) : nndist ‖a‖₊ ‖b‖₊ ≤ ‖a / b‖₊ :=
  NNReal.coe_le_coe.1 <| dist_norm_norm_le' a b

@[to_additive]
theorem nnnorm_le_nnnorm_add_nnnorm_div (a b : E) : ‖b‖₊ ≤ ‖a‖₊ + ‖a / b‖₊ :=
  norm_le_norm_add_norm_div _ _

@[to_additive]
theorem nnnorm_le_nnnorm_add_nnnorm_div' (a b : E) : ‖a‖₊ ≤ ‖b‖₊ + ‖a / b‖₊ :=
  norm_le_norm_add_norm_div' _ _

alias nnnorm_le_insert' := nnnorm_le_nnnorm_add_nnnorm_sub'

alias nnnorm_le_insert := nnnorm_le_nnnorm_add_nnnorm_sub

@[to_additive]
theorem nnnorm_le_mul_nnnorm_add (a b : E) : ‖a‖₊ ≤ ‖a * b‖₊ + ‖b‖₊ :=
  norm_le_mul_norm_add _ _

/-- An analogue of `nnnorm_le_mul_nnnorm_add` for the multiplication from the left. -/
@[to_additive /-- An analogue of `nnnorm_le_add_nnnorm_add` for the addition from the left. -/]
theorem nnnorm_le_mul_nnnorm_add' (a b : E) : ‖b‖₊ ≤ ‖a * b‖₊ + ‖a‖₊ :=
  norm_le_mul_norm_add' _ _

@[to_additive]
lemma nnnorm_mul_eq_nnnorm_right {x : E} (y : E) (h : ‖x‖₊ = 0) : ‖x * y‖₊ = ‖y‖₊ :=
  NNReal.eq <| norm_mul_eq_norm_right _ <| congr_arg NNReal.toReal h

@[to_additive]
lemma nnnorm_mul_eq_nnnorm_left (x : E) {y : E} (h : ‖y‖₊ = 0) : ‖x * y‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_mul_eq_norm_left _ <| congr_arg NNReal.toReal h

@[to_additive]
lemma nnnorm_div_eq_nnnorm_right {x : E} (y : E) (h : ‖x‖₊ = 0) : ‖x / y‖₊ = ‖y‖₊ :=
  NNReal.eq <| norm_div_eq_norm_right _ <| congr_arg NNReal.toReal h

@[to_additive]
lemma nnnorm_div_eq_nnnorm_left (x : E) {y : E} (h : ‖y‖₊ = 0) : ‖x / y‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_div_eq_norm_left _ <| congr_arg NNReal.toReal h

/-- The nonnegative norm seen as an `ENNReal` and then as a `Real` is equal to the norm. -/
@[to_additive toReal_coe_nnnorm /-- The nonnegative norm seen as an `ENNReal` and
then as a `Real` is equal to the norm. -/]
theorem toReal_coe_nnnorm' (a : E) : (‖a‖₊ : ℝ≥0∞).toReal = ‖a‖ := rfl

open scoped symmDiff in
@[to_additive]
theorem edist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    edist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊ := by
  rw [edist_nndist, nndist_mulIndicator]

@[to_additive nontrivialTopology_iff_exists_nnnorm_ne_zero]
theorem nontrivialTopology_iff_exists_nnnorm_ne_zero' :
    NontrivialTopology E ↔ ∃ x : E, ‖x‖₊ ≠ 0 := by
  simp_rw [TopologicalSpace.nontrivial_iff_exists_not_inseparable, Metric.inseparable_iff_nndist,
    nndist_eq_nnnorm_div]
  exact ⟨fun ⟨x, y, hxy⟩ => ⟨_, hxy⟩, fun ⟨x, hx⟩ => ⟨x, 1, by simpa using hx⟩⟩

@[to_additive indiscreteTopology_iff_forall_nnnorm_eq_zero]
theorem indiscreteTopology_iff_forall_nnnorm_eq_zero' :
    IndiscreteTopology E ↔ ∀ x : E, ‖x‖₊ = 0 := by
  simpa using nontrivialTopology_iff_exists_nnnorm_ne_zero' (E := E).not

variable (E) in
@[to_additive exists_nnnorm_ne_zero]
theorem exists_nnnorm_ne_zero' [NontrivialTopology E] : ∃ x : E, ‖x‖₊ ≠ 0 :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) nnnorm_eq_zero]
theorem IndiscreteTopology.nnnorm_eq_zero' [IndiscreteTopology E] : ∀ x : E, ‖x‖₊ = 0 :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_nnnorm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_nnnorm_ne_zero
attribute [to_additive existing NontrivialTopology.of_exists_nnnorm_ne_zero]
  NontrivialTopology.of_exists_nnnorm_ne_zero'

alias ⟨_, IndiscreteTopology.of_forall_nnnorm_eq_zero'⟩ :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero'
alias ⟨_, IndiscreteTopology.of_forall_nnnorm_eq_zero⟩ :=
  indiscreteTopology_iff_forall_nnnorm_eq_zero
attribute [to_additive existing IndiscreteTopology.of_forall_nnnorm_eq_zero]
  IndiscreteTopology.of_forall_nnnorm_eq_zero'

@[to_additive nontrivialTopology_iff_exists_norm_ne_zero]
theorem nontrivialTopology_iff_exists_norm_ne_zero' :
    NontrivialTopology E ↔ ∃ x : E, ‖x‖ ≠ 0 := by
  simp [nontrivialTopology_iff_exists_nnnorm_ne_zero', ← NNReal.ne_iff]

@[to_additive indiscreteTopology_iff_forall_norm_eq_zero]
theorem indiscreteTopology_iff_forall_norm_eq_zero' :
    IndiscreteTopology E ↔ ∀ x : E, ‖x‖ = 0 := by
  simpa using nontrivialTopology_iff_exists_norm_ne_zero' (E := E).not

variable (E) in
@[to_additive exists_norm_ne_zero]
theorem exists_norm_ne_zero' [NontrivialTopology E] : ∃ x : E, ‖x‖ ≠ 0 :=
  nontrivialTopology_iff_exists_norm_ne_zero'.1 ‹_›

@[to_additive (attr := nontriviality) IndiscreteTopology.norm_eq_zero]
theorem IndiscreteTopology.norm_eq_zero' [IndiscreteTopology E] : ∀ x : E, ‖x‖ = 0 :=
  indiscreteTopology_iff_forall_norm_eq_zero'.1 ‹_›

alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero'⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero'
alias ⟨_, NontrivialTopology.of_exists_norm_ne_zero⟩ :=
  nontrivialTopology_iff_exists_norm_ne_zero
attribute [to_additive existing NontrivialTopology.of_exists_norm_ne_zero]
  NontrivialTopology.of_exists_norm_ne_zero'

alias ⟨_, IndiscreteTopology.of_forall_norm_eq_zero'⟩ :=
  indiscreteTopology_iff_forall_norm_eq_zero'
alias ⟨_, IndiscreteTopology.of_forall_norm_eq_zero⟩ :=
  indiscreteTopology_iff_forall_norm_eq_zero
attribute [to_additive existing IndiscreteTopology.of_forall_norm_eq_zero]
  IndiscreteTopology.of_forall_norm_eq_zero'

end NNNorm

section ENorm

@[to_additive (attr := simp) enorm_zero]
lemma enorm_one' {E : Type*} [TopologicalSpace E] [ESeminormedMonoid E] : ‖(1 : E)‖ₑ = 0 := by
  rw [ESeminormedMonoid.enorm_zero]

@[to_additive exists_enorm_lt]
lemma exists_enorm_lt' (E : Type*) [TopologicalSpace E] [ESeminormedMonoid E]
    [hbot : NeBot (𝓝[≠] (1 : E))] {c : ℝ≥0∞} (hc : c ≠ 0) : ∃ x ≠ (1 : E), ‖x‖ₑ < c :=
  frequently_iff_neBot.mpr hbot |>.and_eventually
    (ContinuousENorm.continuous_enorm.tendsto' 1 0 (by simp) |>.eventually_lt_const hc.bot_lt)
    |>.exists

@[to_additive (attr := simp) enorm_neg]
lemma enorm_inv' (a : E) : ‖a⁻¹‖ₑ = ‖a‖ₑ := by simp [enorm]

@[to_additive ofReal_norm_eq_enorm]
lemma ofReal_norm_eq_enorm' (a : E) : .ofReal ‖a‖ = ‖a‖ₑ := ENNReal.ofReal_eq_coe_nnreal _

instance : ENorm ℝ≥0∞ where
  enorm x := x

@[simp] lemma enorm_eq_self (x : ℝ≥0∞) : ‖x‖ₑ = x := rfl

@[to_additive]
theorem edist_eq_enorm_div (a b : E) : edist a b = ‖a / b‖ₑ := by
  rw [edist_dist, dist_eq_norm_div, ofReal_norm_eq_enorm']

@[to_additive]
theorem edist_one_eq_enorm (x : E) : edist x 1 = ‖x‖ₑ := by rw [edist_eq_enorm_div, div_one]

@[to_additive]
lemma enorm_div_rev {E : Type*} [SeminormedGroup E] (a b : E) : ‖a / b‖ₑ = ‖b / a‖ₑ := by
  rw [← edist_eq_enorm_div, edist_comm, edist_eq_enorm_div]

@[to_additive]
theorem mem_eball_one_iff {r : ℝ≥0∞} : a ∈ eball 1 r ↔ ‖a‖ₑ < r := by
  rw [Metric.mem_eball, edist_one_eq_enorm]

@[deprecated (since := "2026-01-24")]
alias mem_emetric_ball_zero_iff := mem_eball_zero_iff

@[to_additive existing, deprecated (since := "2026-01-24")]
alias mem_emetric_ball_one_iff := mem_eball_one_iff

end ENorm

section ContinuousENorm

variable {E : Type*} [TopologicalSpace E] [ContinuousENorm E]

@[continuity, fun_prop]
lemma continuous_enorm : Continuous fun a : E ↦ ‖a‖ₑ := ContinuousENorm.continuous_enorm

variable {X : Type*} [TopologicalSpace X] {f : X → E} {s : Set X} {a : X}

@[fun_prop]
lemma Continuous.enorm : Continuous f → Continuous (‖f ·‖ₑ) :=
  continuous_enorm.comp

lemma ContinuousAt.enorm {a : X} (h : ContinuousAt f a) : ContinuousAt (‖f ·‖ₑ) a := by fun_prop

@[fun_prop]
lemma ContinuousWithinAt.enorm {s : Set X} {a : X} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (‖f ·‖ₑ) s a :=
  (ContinuousENorm.continuous_enorm.continuousWithinAt).comp (t := Set.univ) h
    (fun _ _ ↦ by trivial)

@[fun_prop]
lemma ContinuousOn.enorm (h : ContinuousOn f s) : ContinuousOn (‖f ·‖ₑ) s :=
  (ContinuousENorm.continuous_enorm.continuousOn).comp (t := Set.univ) h <| Set.mapsTo_univ _ _

end ContinuousENorm

section ESeminormedMonoid

variable {E : Type*} [TopologicalSpace E] [ESeminormedMonoid E]

@[to_additive enorm_add_le]
lemma enorm_mul_le' (a b : E) : ‖a * b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := ESeminormedMonoid.enorm_mul_le a b

@[to_additive enorm_add_le_of_le]
theorem enorm_mul_le_of_le' {r₁ r₂ : ℝ≥0∞} {a₁ a₂ : E}
    (h₁ : ‖a₁‖ₑ ≤ r₁) (h₂ : ‖a₂‖ₑ ≤ r₂) : ‖a₁ * a₂‖ₑ ≤ r₁ + r₂ :=
  (enorm_mul_le' a₁ a₂).trans <| add_le_add h₁ h₂

@[to_additive enorm_add₃_le]
lemma enorm_mul₃_le' {a b c : E} : ‖a * b * c‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ :=
  enorm_mul_le_of_le' (enorm_mul_le' _ _) le_rfl

@[to_additive enorm_add₄_le]
lemma enorm_mul₄_le' {a b c d : E} : ‖a * b * c * d‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ + ‖d‖ₑ :=
  enorm_mul_le_of_le' enorm_mul₃_le' le_rfl

end ESeminormedMonoid

section ENormedMonoid

variable {E : Type*} [TopologicalSpace E] [ENormedMonoid E]

@[to_additive (attr := simp) enorm_eq_zero]
lemma enorm_eq_zero' {a : E} : ‖a‖ₑ = 0 ↔ a = 1 := by
  simp [ENormedMonoid.enorm_eq_zero]

@[to_additive enorm_ne_zero]
lemma enorm_ne_zero' {a : E} : ‖a‖ₑ ≠ 0 ↔ a ≠ 1 :=
  enorm_eq_zero'.ne

@[to_additive (attr := simp) enorm_pos]
lemma enorm_pos' {a : E} : 0 < ‖a‖ₑ ↔ a ≠ 1 :=
  pos_iff_ne_zero.trans enorm_ne_zero'

end ENormedMonoid

instance : ENormedAddCommMonoid ℝ≥0∞ where
  continuous_enorm := continuous_id
  enorm_zero := by simp
  enorm_eq_zero := by simp
  enorm_add_le := by simp

open Set in
@[to_additive]
lemma SeminormedGroup.disjoint_nhds (x : E) (f : Filter E) :
    Disjoint (𝓝 x) f ↔ ∃ δ > 0, ∀ᶠ y in f, δ ≤ ‖y / x‖ := by
  simp [NormedCommGroup.nhds_basis_norm_lt x |>.disjoint_iff_left, compl_setOf, eventually_iff]

@[to_additive]
lemma SeminormedGroup.disjoint_nhds_one (f : Filter E) :
    Disjoint (𝓝 1) f ↔ ∃ δ > 0, ∀ᶠ y in f, δ ≤ ‖y‖ := by
  simpa using disjoint_nhds 1 f

end SeminormedGroup

section Induced

variable (E F)
variable [FunLike 𝓕 E F]

-- See note [reducible non-instances]
/-- A group homomorphism from a `Group` to a `SeminormedGroup` induces a `SeminormedGroup`
structure on the domain. -/
@[to_additive /-- A group homomorphism from an `AddGroup` to a
`SeminormedAddGroup` induces a `SeminormedAddGroup` structure on the domain. -/]
abbrev SeminormedGroup.induced [Group E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedGroup E :=
  { PseudoMetricSpace.induced f toPseudoMetricSpace with
    norm := fun x => ‖f x‖
    dist_eq := fun x y => by simp only [map_div, ← dist_eq_norm_div]; rfl }

-- See note [reducible non-instances]
/-- A group homomorphism from a `CommGroup` to a `SeminormedGroup` induces a
`SeminormedCommGroup` structure on the domain. -/
@[to_additive /-- A group homomorphism from an `AddCommGroup` to a
`SeminormedAddGroup` induces a `SeminormedAddCommGroup` structure on the domain. -/]
abbrev SeminormedCommGroup.induced
    [CommGroup E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedCommGroup E :=
  { SeminormedGroup.induced E F f with
    mul_comm := mul_comm }

-- See note [reducible non-instances].
/-- An injective group homomorphism from a `Group` to a `NormedGroup` induces a `NormedGroup`
structure on the domain. -/
@[to_additive /-- An injective group homomorphism from an `AddGroup` to a
`NormedAddGroup` induces a `NormedAddGroup` structure on the domain. -/]
abbrev NormedGroup.induced
    [Group E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) (h : Injective f) :
    NormedGroup E :=
  { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with }

-- See note [reducible non-instances].
/-- An injective group homomorphism from a `CommGroup` to a `NormedGroup` induces a
`NormedCommGroup` structure on the domain. -/
@[to_additive /-- An injective group homomorphism from a `CommGroup` to a
`NormedCommGroup` induces a `NormedCommGroup` structure on the domain. -/]
abbrev NormedCommGroup.induced [CommGroup E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕)
    (h : Injective f) : NormedCommGroup E :=
  { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with
    mul_comm := mul_comm }

end Induced

namespace Real

variable {r : ℝ}

instance norm : Norm ℝ where
  norm r := |r|

@[simp]
theorem norm_eq_abs (r : ℝ) : ‖r‖ = |r| :=
  rfl

instance normedAddCommGroup : NormedAddCommGroup ℝ :=
  ⟨fun _r _y => rfl⟩

theorem norm_of_nonneg (hr : 0 ≤ r) : ‖r‖ = r :=
  abs_of_nonneg hr

theorem norm_of_nonpos (hr : r ≤ 0) : ‖r‖ = -r :=
  abs_of_nonpos hr

theorem le_norm_self (r : ℝ) : r ≤ ‖r‖ :=
  le_abs_self r

lemma norm_natCast (n : ℕ) : ‖(n : ℝ)‖ = n := abs_of_nonneg n.cast_nonneg
@[simp 1100] lemma nnnorm_natCast (n : ℕ) : ‖(n : ℝ)‖₊ = n := NNReal.eq <| norm_natCast _
@[simp 1100] lemma enorm_natCast (n : ℕ) : ‖(n : ℝ)‖ₑ = n := by simp [enorm]

@[simp 1100] lemma norm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℝ)‖ = ofNat(n) := norm_natCast n

@[simp 1100] lemma nnnorm_ofNat (n : ℕ) [n.AtLeastTwo] :
    ‖(ofNat(n) : ℝ)‖₊ = ofNat(n) := nnnorm_natCast n

lemma norm_two : ‖(2 : ℝ)‖ = 2 := abs_of_pos zero_lt_two
lemma nnnorm_two : ‖(2 : ℝ)‖₊ = 2 := NNReal.eq <| by simp

@[simp 1100, norm_cast]
lemma norm_nnratCast (q : ℚ≥0) : ‖(q : ℝ)‖ = q := norm_of_nonneg q.cast_nonneg

@[simp 1100, norm_cast]
lemma nnnorm_nnratCast (q : ℚ≥0) : ‖(q : ℝ)‖₊ = q := by simp [nnnorm, -norm_eq_abs]

theorem nnnorm_of_nonneg (hr : 0 ≤ r) : ‖r‖₊ = ⟨r, hr⟩ :=
  NNReal.eq <| norm_of_nonneg hr

lemma enorm_of_nonneg (hr : 0 ≤ r) : ‖r‖ₑ = .ofReal r := by
  simp [enorm, nnnorm_of_nonneg hr, ENNReal.ofReal, toNNReal, hr]

lemma enorm_ofReal_of_nonneg {a : ℝ} (ha : 0 ≤ a) : ‖ENNReal.ofReal a‖ₑ = ‖a‖ₑ := by
  simp [Real.enorm_of_nonneg, ha]

@[simp] lemma nnnorm_abs (r : ℝ) : ‖|r|‖₊ = ‖r‖₊ := by simp [nnnorm]
@[simp] lemma enorm_abs (r : ℝ) : ‖|r|‖ₑ = ‖r‖ₑ := by simp [enorm]

theorem enorm_eq_ofReal (hr : 0 ≤ r) : ‖r‖ₑ = .ofReal r := by
  rw [← ofReal_norm_eq_enorm, norm_of_nonneg hr]

theorem enorm_eq_ofReal_abs (r : ℝ) : ‖r‖ₑ = ENNReal.ofReal |r| := by
  rw [← enorm_eq_ofReal (abs_nonneg _), enorm_abs]

theorem toNNReal_eq_nnnorm_of_nonneg (hr : 0 ≤ r) : r.toNNReal = ‖r‖₊ := by
  rw [Real.toNNReal_of_nonneg hr]
  congr
  rw [Real.norm_eq_abs r, abs_of_nonneg hr]

theorem ofReal_le_enorm (r : ℝ) : ENNReal.ofReal r ≤ ‖r‖ₑ := by
  rw [enorm_eq_ofReal_abs]; gcongr; exact le_abs_self _

end Real

namespace NNReal

instance : NNNorm ℝ≥0 where
  nnnorm x := x

@[simp] lemma nnnorm_eq_self (x : ℝ≥0) : ‖x‖₊ = x := rfl

end NNReal

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a b : E} {r : ℝ}
variable {ε : Type*} [TopologicalSpace ε] [ESeminormedCommMonoid ε]

@[to_additive]
theorem dist_inv (x y : E) : dist x⁻¹ y = dist x y⁻¹ := by
  simp_rw [dist_eq_norm_div, ← norm_inv' (x⁻¹ / y), inv_div, div_inv_eq_mul, mul_comm]

theorem norm_multiset_sum_le {E} [SeminormedAddCommGroup E] (m : Multiset E) :
    ‖m.sum‖ ≤ (m.map fun x => ‖x‖).sum :=
  m.le_sum_of_subadditive norm norm_zero.le norm_add_le

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddCommMonoid ε] in
theorem enorm_multisetSum_le (m : Multiset ε) :
    ‖m.sum‖ₑ ≤ (m.map fun x => ‖x‖ₑ).sum :=
  m.le_sum_of_subadditive enorm enorm_zero.le enorm_add_le

@[to_additive existing]
theorem norm_multiset_prod_le (m : Multiset E) : ‖m.prod‖ ≤ (m.map fun x => ‖x‖).sum :=
  m.apply_prod_le_sum_map _ norm_one'.le norm_mul_le'

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedCommMonoid ε] in
@[to_additive existing]
theorem enorm_multisetProd_le (m : Multiset ε) :
    ‖m.prod‖ₑ ≤ (m.map fun x => ‖x‖ₑ).sum :=
  m.apply_prod_le_sum_map _ enorm_one'.le enorm_mul_le'

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddCommMonoid ε] in
@[bound]
theorem enorm_sum_le (s : Finset ι) (f : ι → ε) :
    ‖∑ i ∈ s, f i‖ₑ ≤ ∑ i ∈ s, ‖f i‖ₑ :=
  s.le_sum_of_subadditive enorm enorm_zero.le enorm_add_le f

@[bound]
theorem norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ :=
  s.le_sum_of_subadditive norm norm_zero.le norm_add_le f

@[to_additive existing]
theorem enorm_prod_le (s : Finset ι) (f : ι → ε) : ‖∏ i ∈ s, f i‖ₑ ≤ ∑ i ∈ s, ‖f i‖ₑ :=
  s.apply_prod_le_sum_apply _ enorm_one'.le enorm_mul_le'

@[to_additive existing]
theorem norm_prod_le (s : Finset ι) (f : ι → E) : ‖∏ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ :=
  s.apply_prod_le_sum_apply _ norm_one'.le norm_mul_le'

@[to_additive]
theorem enorm_prod_le_of_le (s : Finset ι) {f : ι → ε} {n : ι → ℝ≥0∞} (h : ∀ b ∈ s, ‖f b‖ₑ ≤ n b) :
    ‖∏ b ∈ s, f b‖ₑ ≤ ∑ b ∈ s, n b :=
  (enorm_prod_le s f).trans <| Finset.sum_le_sum h

@[to_additive]
theorem norm_prod_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ} (h : ∀ b ∈ s, ‖f b‖ ≤ n b) :
    ‖∏ b ∈ s, f b‖ ≤ ∑ b ∈ s, n b :=
  (norm_prod_le s f).trans <| Finset.sum_le_sum h

@[to_additive]
theorem dist_prod_prod_le_of_le (s : Finset ι) {f a : ι → E} {d : ι → ℝ}
    (h : ∀ b ∈ s, dist (f b) (a b) ≤ d b) :
    dist (∏ b ∈ s, f b) (∏ b ∈ s, a b) ≤ ∑ b ∈ s, d b := by
  simp only [dist_eq_norm_div, ← Finset.prod_div_distrib] at *
  exact norm_prod_le_of_le s h

@[to_additive]
theorem dist_prod_prod_le (s : Finset ι) (f a : ι → E) :
    dist (∏ b ∈ s, f b) (∏ b ∈ s, a b) ≤ ∑ b ∈ s, dist (f b) (a b) :=
  dist_prod_prod_le_of_le s fun _ _ => le_rfl

@[to_additive]
theorem mul_mem_ball_iff_norm : a * b ∈ ball a r ↔ ‖b‖ < r := by
  rw [mem_ball_iff_norm'', mul_div_cancel_left]

@[to_additive]
theorem mul_mem_closedBall_iff_norm : a * b ∈ closedBall a r ↔ ‖b‖ ≤ r := by
  rw [mem_closedBall_iff_norm'', mul_div_cancel_left]

-- Higher priority to apply this before the equivalent lemma `Metric.preimage_mul_left_ball`.
@[to_additive (attr := simp high)]
theorem preimage_mul_ball (a b : E) (r : ℝ) : (b * ·) ⁻¹' ball a r = ball (a / b) r := by
  ext c
  simp only [dist_eq_norm_div, Set.mem_preimage, mem_ball, div_div_eq_mul_div, mul_comm]

-- Higher priority to apply this before the equivalent lemma `Metric.preimage_mul_left_closedBall`.
@[to_additive (attr := simp high)]
theorem preimage_mul_closedBall (a b : E) (r : ℝ) :
    (b * ·) ⁻¹' closedBall a r = closedBall (a / b) r := by
  ext c
  simp only [dist_eq_norm_div, Set.mem_preimage, mem_closedBall, div_div_eq_mul_div, mul_comm]

@[to_additive (attr := simp)]
theorem preimage_mul_sphere (a b : E) (r : ℝ) : (b * ·) ⁻¹' sphere a r = sphere (a / b) r := by
  ext c
  simp only [Set.mem_preimage, mem_sphere_iff_norm', div_div_eq_mul_div, mul_comm]


@[to_additive]
theorem pow_mem_closedBall {n : ℕ} (h : a ∈ closedBall b r) :
    a ^ n ∈ closedBall (b ^ n) (n • r) := by
  simp only [mem_closedBall, dist_eq_norm_div, ← div_pow] at h ⊢
  refine norm_pow_le_mul_norm.trans ?_
  simpa only [nsmul_eq_mul] using mul_le_mul_of_nonneg_left h n.cast_nonneg

@[to_additive]
theorem pow_mem_ball {n : ℕ} (hn : 0 < n) (h : a ∈ ball b r) : a ^ n ∈ ball (b ^ n) (n • r) := by
  simp only [mem_ball, dist_eq_norm_div, ← div_pow] at h ⊢
  refine lt_of_le_of_lt norm_pow_le_mul_norm ?_
  replace hn : 0 < (n : ℝ) := by norm_cast
  rw [nsmul_eq_mul]
  nlinarith

@[to_additive]
theorem mul_mem_closedBall_mul_iff {c : E} : a * c ∈ closedBall (b * c) r ↔ a ∈ closedBall b r := by
  simp only [mem_closedBall, dist_eq_norm_div, mul_div_mul_right_eq_div]

@[to_additive]
theorem mul_mem_ball_mul_iff {c : E} : a * c ∈ ball (b * c) r ↔ a ∈ ball b r := by
  simp only [mem_ball, dist_eq_norm_div, mul_div_mul_right_eq_div]

@[to_additive]
theorem smul_closedBall'' : a • closedBall b r = closedBall (a • b) r := by
  ext
  simp [mem_closedBall, Set.mem_smul_set, dist_eq_norm_div, div_eq_inv_mul, ←
    eq_inv_mul_iff_mul_eq, mul_assoc]

@[to_additive]
theorem smul_ball'' : a • ball b r = ball (a • b) r := by
  ext
  simp [mem_ball, Set.mem_smul_set, dist_eq_norm_div, _root_.div_eq_inv_mul,
    ← eq_inv_mul_iff_mul_eq, mul_assoc]

@[to_additive]
theorem nnnorm_multiset_prod_le (m : Multiset E) : ‖m.prod‖₊ ≤ (m.map fun x => ‖x‖₊).sum :=
  NNReal.coe_le_coe.1 <| by
    push_cast
    rw [Multiset.map_map]
    exact norm_multiset_prod_le _

@[to_additive]
theorem nnnorm_prod_le (s : Finset ι) (f : ι → E) : ‖∏ a ∈ s, f a‖₊ ≤ ∑ a ∈ s, ‖f a‖₊ :=
  NNReal.coe_le_coe.1 <| by
    push_cast
    exact norm_prod_le _ _

@[to_additive]
theorem nnnorm_prod_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ≥0} (h : ∀ b ∈ s, ‖f b‖₊ ≤ n b) :
    ‖∏ b ∈ s, f b‖₊ ≤ ∑ b ∈ s, n b :=
  (norm_prod_le_of_le s h).trans_eq (NNReal.coe_sum ..).symm

@[to_additive (attr := simp high) norm_norm] -- Higher priority as a shortcut lemma.
lemma norm_norm' (x : E) : ‖‖x‖‖ = ‖x‖ := Real.norm_of_nonneg (norm_nonneg' _)

@[to_additive (attr := simp) nnnorm_norm]
lemma nnnorm_norm' (x : E) : ‖‖x‖‖₊ = ‖x‖₊ := by simp [nnnorm]

@[to_additive (attr := simp) enorm_norm]
lemma enorm_norm' (x : E) : ‖‖x‖‖ₑ = ‖x‖ₑ := by simp [enorm]

lemma enorm_enorm {ε : Type*} [ENorm ε] (x : ε) : ‖‖x‖ₑ‖ₑ = ‖x‖ₑ := by simp [enorm]

end SeminormedCommGroup

section NormedGroup

variable [NormedGroup E] {a b : E}

@[to_additive (attr := simp) norm_le_zero_iff]
lemma norm_le_zero_iff' : ‖a‖ ≤ 0 ↔ a = 1 := by rw [← dist_one_right, dist_le_zero]

@[to_additive (attr := simp) norm_pos_iff]
lemma norm_pos_iff' : 0 < ‖a‖ ↔ a ≠ 1 := by rw [← not_le, norm_le_zero_iff']

@[to_additive (attr := simp) norm_eq_zero]
lemma norm_eq_zero' : ‖a‖ = 0 ↔ a = 1 := (norm_nonneg' a).ge_iff_eq'.symm.trans norm_le_zero_iff'

@[to_additive norm_ne_zero_iff]
lemma norm_ne_zero_iff' : ‖a‖ ≠ 0 ↔ a ≠ 1 := norm_eq_zero'.not

@[to_additive]
theorem norm_div_eq_zero_iff : ‖a / b‖ = 0 ↔ a = b := by rw [norm_eq_zero', div_eq_one]

@[to_additive]
theorem norm_div_pos_iff : 0 < ‖a / b‖ ↔ a ≠ b := by
  rw [(norm_nonneg' _).lt_iff_ne, ne_comm]
  exact norm_div_eq_zero_iff.not

@[to_additive eq_of_norm_sub_le_zero]
theorem eq_of_norm_div_le_zero (h : ‖a / b‖ ≤ 0) : a = b := by
  rwa [← div_eq_one, ← norm_le_zero_iff']

alias ⟨eq_of_norm_div_eq_zero, _⟩ := norm_div_eq_zero_iff

attribute [to_additive] eq_of_norm_div_eq_zero

@[to_additive]
theorem eq_one_or_norm_pos (a : E) : a = 1 ∨ 0 < ‖a‖ := by
  simpa [eq_comm] using (norm_nonneg' a).eq_or_lt

@[to_additive]
theorem eq_one_or_nnnorm_pos (a : E) : a = 1 ∨ 0 < ‖a‖₊ :=
  eq_one_or_norm_pos a

@[to_additive (attr := simp) nnnorm_eq_zero]
theorem nnnorm_eq_zero' : ‖a‖₊ = 0 ↔ a = 1 := by
  rw [← NNReal.coe_eq_zero, coe_nnnorm', norm_eq_zero']

@[to_additive nnnorm_ne_zero_iff]
theorem nnnorm_ne_zero_iff' : ‖a‖₊ ≠ 0 ↔ a ≠ 1 :=
  nnnorm_eq_zero'.not

@[to_additive (attr := simp) nnnorm_pos]
lemma nnnorm_pos' : 0 < ‖a‖₊ ↔ a ≠ 1 := pos_iff_ne_zero.trans nnnorm_ne_zero_iff'

variable (E)

/-- The norm of a normed group as a group norm. -/
@[to_additive /-- The norm of a normed group as an additive group norm. -/]
def normGroupNorm : GroupNorm E :=
  { normGroupSeminorm _ with eq_one_of_map_eq_zero' := fun _ => norm_eq_zero'.1 }

@[simp]
theorem coe_normGroupNorm : ⇑(normGroupNorm E) = norm :=
  rfl

end NormedGroup

section NormedAddGroup

variable [NormedAddGroup E] [TopologicalSpace α] {f : α → E}

/-! Some relations with `HasCompactSupport` -/

theorem hasCompactSupport_norm_iff : (HasCompactSupport fun x => ‖f x‖) ↔ HasCompactSupport f :=
  hasCompactSupport_comp_left norm_eq_zero

alias ⟨_, HasCompactSupport.norm⟩ := hasCompactSupport_norm_iff

end NormedAddGroup

lemma tendsto_norm_atTop_atTop : Tendsto (norm : ℝ → ℝ) atTop atTop := tendsto_abs_atTop_atTop

/-! ### `positivity` extensions -/

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: multiplicative norms are always nonnegative, and positive
on non-one inputs. -/
@[positivity ‖_‖]
meta def evalMulNorm : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Norm.norm $E $_n $a) =>
    let _seminormedGroup_E ← synthInstanceQ q(SeminormedGroup $E)
    assertInstancesCommute
    -- Check whether we are in a normed group and whether the context contains a `a ≠ 1` assumption
    let o : Option (Q(NormedGroup $E) × Q($a ≠ 1)) := ← do
      let .some normedGroup_E ← trySynthInstanceQ q(NormedGroup $E) | return none
      let some pa ← findLocalDeclWithTypeQ? q($a ≠ 1) | return none
      return some (normedGroup_E, pa)
    match o with
    -- If so, return a proof of `0 < ‖a‖`
    | some (_normedGroup_E, pa) =>
      assertInstancesCommute
      return .positive q(norm_pos_iff'.2 $pa)
    -- Else, return a proof of `0 ≤ ‖a‖`
    | none => return .nonnegative q(norm_nonneg' $a)
  | _, _, _ => throwError "not `‖·‖`"

/-- Extension for the `positivity` tactic: additive norms are always nonnegative, and positive
on non-zero inputs. -/
@[positivity ‖_‖]
meta def evalAddNorm : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Norm.norm $E $_n $a) =>
    let _seminormedAddGroup_E ← synthInstanceQ q(SeminormedAddGroup $E)
    assertInstancesCommute
    -- Check whether we are in a normed group and whether the context contains a `a ≠ 0` assumption
    let o : Option (Q(NormedAddGroup $E) × Q($a ≠ 0)) := ← do
      let .some normedAddGroup_E ← trySynthInstanceQ q(NormedAddGroup $E) | return none
      let some pa ← findLocalDeclWithTypeQ? q($a ≠ 0) | return none
      return some (normedAddGroup_E, pa)
    match o with
    -- If so, return a proof of `0 < ‖a‖`
    | some (_normedAddGroup_E, pa) =>
      assertInstancesCommute
      return .positive q(norm_pos_iff.2 $pa)
    -- Else, return a proof of `0 ≤ ‖a‖`
    | none => return .nonnegative q(norm_nonneg $a)
  | _, _, _ => throwError "not `‖·‖`"

end Mathlib.Meta.Positivity
