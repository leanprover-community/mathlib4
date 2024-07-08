/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Sequences

#align_import analysis.normed.group.basic from "leanprover-community/mathlib"@"41bef4ae1254365bc190aee63b947674d2977f01"

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

## TODO
This file is huge; move material into separate files,
such as `Mathlib/Analysis/Normed/Group/Lemmas.lean`.

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


variable {𝓕 𝕜 α ι κ E F G : Type*}

open Filter Function Metric Bornology

open ENNReal Filter NNReal Uniformity Pointwise Topology

/-- Auxiliary class, endowing a type `E` with a function `norm : E → ℝ` with notation `‖x‖`. This
class is designed to be extended in more interesting classes specifying the properties of the norm.
-/
@[notation_class]
class Norm (E : Type*) where
  /-- the `ℝ`-valued norm function. -/
  norm : E → ℝ
#align has_norm Norm

/-- Auxiliary class, endowing a type `α` with a function `nnnorm : α → ℝ≥0` with notation `‖x‖₊`. -/
@[notation_class]
class NNNorm (E : Type*) where
  /-- the `ℝ≥0`-valued norm function. -/
  nnnorm : E → ℝ≥0
#align has_nnnorm NNNorm

export Norm (norm)

export NNNorm (nnnorm)

@[inherit_doc]
notation "‖" e "‖" => norm e

@[inherit_doc]
notation "‖" e "‖₊" => nnnorm e

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ‖x - y‖`
defines a pseudometric space structure. -/
class SeminormedAddGroup (E : Type*) extends Norm E, AddGroup E, PseudoMetricSpace E where
  dist := fun x y => ‖x - y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by aesop
#align seminormed_add_group SeminormedAddGroup

/-- A seminormed group is a group endowed with a norm for which `dist x y = ‖x / y‖` defines a
pseudometric space structure. -/
@[to_additive]
class SeminormedGroup (E : Type*) extends Norm E, Group E, PseudoMetricSpace E where
  dist := fun x y => ‖x / y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x / y‖ := by aesop
#align seminormed_group SeminormedGroup

/-- A normed group is an additive group endowed with a norm for which `dist x y = ‖x - y‖` defines a
metric space structure. -/
class NormedAddGroup (E : Type*) extends Norm E, AddGroup E, MetricSpace E where
  dist := fun x y => ‖x - y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by aesop
#align normed_add_group NormedAddGroup

/-- A normed group is a group endowed with a norm for which `dist x y = ‖x / y‖` defines a metric
space structure. -/
@[to_additive]
class NormedGroup (E : Type*) extends Norm E, Group E, MetricSpace E where
  dist := fun x y => ‖x / y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x / y‖ := by aesop
#align normed_group NormedGroup

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ‖x - y‖`
defines a pseudometric space structure. -/
class SeminormedAddCommGroup (E : Type*) extends Norm E, AddCommGroup E,
  PseudoMetricSpace E where
  dist := fun x y => ‖x - y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by aesop
#align seminormed_add_comm_group SeminormedAddCommGroup

/-- A seminormed group is a group endowed with a norm for which `dist x y = ‖x / y‖`
defines a pseudometric space structure. -/
@[to_additive]
class SeminormedCommGroup (E : Type*) extends Norm E, CommGroup E, PseudoMetricSpace E where
  dist := fun x y => ‖x / y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x / y‖ := by aesop
#align seminormed_comm_group SeminormedCommGroup

/-- A normed group is an additive group endowed with a norm for which `dist x y = ‖x - y‖` defines a
metric space structure. -/
class NormedAddCommGroup (E : Type*) extends Norm E, AddCommGroup E, MetricSpace E where
  dist := fun x y => ‖x - y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x - y‖ := by aesop
#align normed_add_comm_group NormedAddCommGroup

/-- A normed group is a group endowed with a norm for which `dist x y = ‖x / y‖` defines a metric
space structure. -/
@[to_additive]
class NormedCommGroup (E : Type*) extends Norm E, CommGroup E, MetricSpace E where
  dist := fun x y => ‖x / y‖
  /-- The distance function is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = ‖x / y‖ := by aesop
#align normed_comm_group NormedCommGroup

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) NormedGroup.toSeminormedGroup [NormedGroup E] : SeminormedGroup E :=
  { ‹NormedGroup E› with }
#align normed_group.to_seminormed_group NormedGroup.toSeminormedGroup
#align normed_add_group.to_seminormed_add_group NormedAddGroup.toSeminormedAddGroup

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) NormedCommGroup.toSeminormedCommGroup [NormedCommGroup E] :
    SeminormedCommGroup E :=
  { ‹NormedCommGroup E› with }
#align normed_comm_group.to_seminormed_comm_group NormedCommGroup.toSeminormedCommGroup
#align normed_add_comm_group.to_seminormed_add_comm_group NormedAddCommGroup.toSeminormedAddCommGroup

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedCommGroup.toSeminormedGroup [SeminormedCommGroup E] :
    SeminormedGroup E :=
  { ‹SeminormedCommGroup E› with }
#align seminormed_comm_group.to_seminormed_group SeminormedCommGroup.toSeminormedGroup
#align seminormed_add_comm_group.to_seminormed_add_group SeminormedAddCommGroup.toSeminormedAddGroup

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) NormedCommGroup.toNormedGroup [NormedCommGroup E] : NormedGroup E :=
  { ‹NormedCommGroup E› with }
#align normed_comm_group.to_normed_group NormedCommGroup.toNormedGroup
#align normed_add_comm_group.to_normed_add_group NormedAddCommGroup.toNormedAddGroup

-- See note [reducible non-instances]
/-- Construct a `NormedGroup` from a `SeminormedGroup` satisfying `∀ x, ‖x‖ = 0 → x = 1`. This
avoids having to go back to the `(Pseudo)MetricSpace` level when declaring a `NormedGroup`
instance as a special case of a more general `SeminormedGroup` instance. -/
@[to_additive (attr := reducible) "Construct a `NormedAddGroup` from a `SeminormedAddGroup`
satisfying `∀ x, ‖x‖ = 0 → x = 0`. This avoids having to go back to the `(Pseudo)MetricSpace`
level when declaring a `NormedAddGroup` instance as a special case of a more general
`SeminormedAddGroup` instance."]
def NormedGroup.ofSeparation [SeminormedGroup E] (h : ∀ x : E, ‖x‖ = 0 → x = 1) :
    NormedGroup E where
  dist_eq := ‹SeminormedGroup E›.dist_eq
  toMetricSpace :=
    { eq_of_dist_eq_zero := fun hxy =>
        div_eq_one.1 <| h _ <| by exact (‹SeminormedGroup E›.dist_eq _ _).symm.trans hxy }
      -- Porting note: the `rwa` no longer worked, but it was easy enough to provide the term.
      -- however, notice that if you make `x` and `y` accessible, then the following does work:
      -- `have := ‹SeminormedGroup E›.dist_eq x y; rwa [← this]`, so I'm not sure why the `rwa`
      -- was broken.
#align normed_group.of_separation NormedGroup.ofSeparation
#align normed_add_group.of_separation NormedAddGroup.ofSeparation

-- See note [reducible non-instances]
/-- Construct a `NormedCommGroup` from a `SeminormedCommGroup` satisfying
`∀ x, ‖x‖ = 0 → x = 1`. This avoids having to go back to the `(Pseudo)MetricSpace` level when
declaring a `NormedCommGroup` instance as a special case of a more general `SeminormedCommGroup`
instance. -/
@[to_additive (attr := reducible) "Construct a `NormedAddCommGroup` from a
`SeminormedAddCommGroup` satisfying `∀ x, ‖x‖ = 0 → x = 0`. This avoids having to go back to the
`(Pseudo)MetricSpace` level when declaring a `NormedAddCommGroup` instance as a special case
of a more general `SeminormedAddCommGroup` instance."]
def NormedCommGroup.ofSeparation [SeminormedCommGroup E] (h : ∀ x : E, ‖x‖ = 0 → x = 1) :
    NormedCommGroup E :=
  { ‹SeminormedCommGroup E›, NormedGroup.ofSeparation h with }
#align normed_comm_group.of_separation NormedCommGroup.ofSeparation
#align normed_add_comm_group.of_separation NormedAddCommGroup.ofSeparation

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant distance. -/
@[to_additive (attr := reducible)
  "Construct a seminormed group from a translation-invariant distance."]
def SeminormedGroup.ofMulDist [Norm E] [Group E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
    SeminormedGroup E where
  dist_eq x y := by
    rw [h₁]; apply le_antisymm
    · simpa only [div_eq_mul_inv, ← mul_right_inv y] using h₂ _ _ _
    · simpa only [div_mul_cancel, one_mul] using h₂ (x / y) 1 y
#align seminormed_group.of_mul_dist SeminormedGroup.ofMulDist
#align seminormed_add_group.of_add_dist SeminormedAddGroup.ofAddDist

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive (attr := reducible)
  "Construct a seminormed group from a translation-invariant pseudodistance."]
def SeminormedGroup.ofMulDist' [Norm E] [Group E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
    SeminormedGroup E where
  dist_eq x y := by
    rw [h₁]; apply le_antisymm
    · simpa only [div_mul_cancel, one_mul] using h₂ (x / y) 1 y
    · simpa only [div_eq_mul_inv, ← mul_right_inv y] using h₂ _ _ _
#align seminormed_group.of_mul_dist' SeminormedGroup.ofMulDist'
#align seminormed_add_group.of_add_dist' SeminormedAddGroup.ofAddDist'

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive (attr := reducible)
  "Construct a seminormed group from a translation-invariant pseudodistance."]
def SeminormedCommGroup.ofMulDist [Norm E] [CommGroup E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
    SeminormedCommGroup E :=
  { SeminormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }
#align seminormed_comm_group.of_mul_dist SeminormedCommGroup.ofMulDist
#align seminormed_add_comm_group.of_add_dist SeminormedAddCommGroup.ofAddDist

-- See note [reducible non-instances]
/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive (attr := reducible)
  "Construct a seminormed group from a translation-invariant pseudodistance."]
def SeminormedCommGroup.ofMulDist' [Norm E] [CommGroup E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
    SeminormedCommGroup E :=
  { SeminormedGroup.ofMulDist' h₁ h₂ with
    mul_comm := mul_comm }
#align seminormed_comm_group.of_mul_dist' SeminormedCommGroup.ofMulDist'
#align seminormed_add_comm_group.of_add_dist' SeminormedAddCommGroup.ofAddDist'

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant distance. -/
@[to_additive (attr := reducible)
  "Construct a normed group from a translation-invariant distance."]
def NormedGroup.ofMulDist [Norm E] [Group E] [MetricSpace E] (h₁ : ∀ x : E, ‖x‖ = dist x 1)
    (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) : NormedGroup E :=
  { SeminormedGroup.ofMulDist h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
#align normed_group.of_mul_dist NormedGroup.ofMulDist
#align normed_add_group.of_add_dist NormedAddGroup.ofAddDist

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive (attr := reducible)
  "Construct a normed group from a translation-invariant pseudodistance."]
def NormedGroup.ofMulDist' [Norm E] [Group E] [MetricSpace E] (h₁ : ∀ x : E, ‖x‖ = dist x 1)
    (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) : NormedGroup E :=
  { SeminormedGroup.ofMulDist' h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
#align normed_group.of_mul_dist' NormedGroup.ofMulDist'
#align normed_add_group.of_add_dist' NormedAddGroup.ofAddDist'

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive (attr := reducible)
"Construct a normed group from a translation-invariant pseudodistance."]
def NormedCommGroup.ofMulDist [Norm E] [CommGroup E] [MetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
    NormedCommGroup E :=
  { NormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }
#align normed_comm_group.of_mul_dist NormedCommGroup.ofMulDist
#align normed_add_comm_group.of_add_dist NormedAddCommGroup.ofAddDist

-- See note [reducible non-instances]
/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive (attr := reducible)
  "Construct a normed group from a translation-invariant pseudodistance."]
def NormedCommGroup.ofMulDist' [Norm E] [CommGroup E] [MetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
    NormedCommGroup E :=
  { NormedGroup.ofMulDist' h₁ h₂ with
    mul_comm := mul_comm }
#align normed_comm_group.of_mul_dist' NormedCommGroup.ofMulDist'
#align normed_add_comm_group.of_add_dist' NormedAddCommGroup.ofAddDist'

-- See note [reducible non-instances]
/-- Construct a seminormed group from a seminorm, i.e., registering the pseudodistance and the
pseudometric space structure from the seminorm properties. Note that in most cases this instance
creates bad definitional equalities (e.g., it does not take into account a possibly existing
`UniformSpace` instance on `E`). -/
@[to_additive (attr := reducible)
  "Construct a seminormed group from a seminorm, i.e., registering the pseudodistance
and the pseudometric space structure from the seminorm properties. Note that in most cases this
instance creates bad definitional equalities (e.g., it does not take into account a possibly
existing `UniformSpace` instance on `E`)."]
def GroupSeminorm.toSeminormedGroup [Group E] (f : GroupSeminorm E) : SeminormedGroup E where
  dist x y := f (x / y)
  norm := f
  dist_eq x y := rfl
  dist_self x := by simp only [div_self', map_one_eq_zero]
  dist_triangle := le_map_div_add_map_div f
  dist_comm := map_div_rev f
  edist_dist x y := by exact ENNReal.coe_nnreal_eq _
  -- Porting note: how did `mathlib3` solve this automatically?
#align group_seminorm.to_seminormed_group GroupSeminorm.toSeminormedGroup
#align add_group_seminorm.to_seminormed_add_group AddGroupSeminorm.toSeminormedAddGroup

-- See note [reducible non-instances]
/-- Construct a seminormed group from a seminorm, i.e., registering the pseudodistance and the
pseudometric space structure from the seminorm properties. Note that in most cases this instance
creates bad definitional equalities (e.g., it does not take into account a possibly existing
`UniformSpace` instance on `E`). -/
@[to_additive (attr := reducible)
  "Construct a seminormed group from a seminorm, i.e., registering the pseudodistance
and the pseudometric space structure from the seminorm properties. Note that in most cases this
instance creates bad definitional equalities (e.g., it does not take into account a possibly
existing `UniformSpace` instance on `E`)."]
def GroupSeminorm.toSeminormedCommGroup [CommGroup E] (f : GroupSeminorm E) :
    SeminormedCommGroup E :=
  { f.toSeminormedGroup with
    mul_comm := mul_comm }
#align group_seminorm.to_seminormed_comm_group GroupSeminorm.toSeminormedCommGroup
#align add_group_seminorm.to_seminormed_add_comm_group AddGroupSeminorm.toSeminormedAddCommGroup

-- See note [reducible non-instances]
/-- Construct a normed group from a norm, i.e., registering the distance and the metric space
structure from the norm properties. Note that in most cases this instance creates bad definitional
equalities (e.g., it does not take into account a possibly existing `UniformSpace` instance on
`E`). -/
@[to_additive (attr := reducible)
  "Construct a normed group from a norm, i.e., registering the distance and the metric
space structure from the norm properties. Note that in most cases this instance creates bad
definitional equalities (e.g., it does not take into account a possibly existing `UniformSpace`
instance on `E`)."]
def GroupNorm.toNormedGroup [Group E] (f : GroupNorm E) : NormedGroup E :=
  { f.toGroupSeminorm.toSeminormedGroup with
    eq_of_dist_eq_zero := fun h => div_eq_one.1 <| eq_one_of_map_eq_zero f h }
#align group_norm.to_normed_group GroupNorm.toNormedGroup
#align add_group_norm.to_normed_add_group AddGroupNorm.toNormedAddGroup

-- See note [reducible non-instances]
/-- Construct a normed group from a norm, i.e., registering the distance and the metric space
structure from the norm properties. Note that in most cases this instance creates bad definitional
equalities (e.g., it does not take into account a possibly existing `UniformSpace` instance on
`E`). -/
@[to_additive (attr := reducible)
  "Construct a normed group from a norm, i.e., registering the distance and the metric
space structure from the norm properties. Note that in most cases this instance creates bad
definitional equalities (e.g., it does not take into account a possibly existing `UniformSpace`
instance on `E`)."]
def GroupNorm.toNormedCommGroup [CommGroup E] (f : GroupNorm E) : NormedCommGroup E :=
  { f.toNormedGroup with
    mul_comm := mul_comm }
#align group_norm.to_normed_comm_group GroupNorm.toNormedCommGroup
#align add_group_norm.to_normed_add_comm_group AddGroupNorm.toNormedAddCommGroup

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E}
  {a a₁ a₂ b b₁ b₂ : E} {r r₁ r₂ : ℝ}

@[to_additive]
theorem dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖ :=
  SeminormedGroup.dist_eq _ _
#align dist_eq_norm_div dist_eq_norm_div
#align dist_eq_norm_sub dist_eq_norm_sub

@[to_additive]
theorem dist_eq_norm_div' (a b : E) : dist a b = ‖b / a‖ := by rw [dist_comm, dist_eq_norm_div]
#align dist_eq_norm_div' dist_eq_norm_div'
#align dist_eq_norm_sub' dist_eq_norm_sub'

alias dist_eq_norm := dist_eq_norm_sub
#align dist_eq_norm dist_eq_norm

alias dist_eq_norm' := dist_eq_norm_sub'
#align dist_eq_norm' dist_eq_norm'

@[to_additive of_forall_le_norm]
lemma DiscreteTopology.of_forall_le_norm' (hpos : 0 < r) (hr : ∀ x : E, x ≠ 1 → r ≤ ‖x‖) :
    DiscreteTopology E :=
  .of_forall_le_dist hpos fun x y hne ↦ by
    simp only [dist_eq_norm_div]
    exact hr _ (div_ne_one.2 hne)

@[to_additive (attr := simp)]
theorem dist_one_right (a : E) : dist a 1 = ‖a‖ := by rw [dist_eq_norm_div, div_one]
#align dist_one_right dist_one_right
#align dist_zero_right dist_zero_right

@[to_additive]
theorem inseparable_one_iff_norm {a : E} : Inseparable a 1 ↔ ‖a‖ = 0 := by
  rw [Metric.inseparable_iff, dist_one_right]

@[to_additive (attr := simp)]
theorem dist_one_left : dist (1 : E) = norm :=
  funext fun a => by rw [dist_comm, dist_one_right]
#align dist_one_left dist_one_left
#align dist_zero_left dist_zero_left

@[to_additive]
theorem norm_div_rev (a b : E) : ‖a / b‖ = ‖b / a‖ := by
  simpa only [dist_eq_norm_div] using dist_comm a b
#align norm_div_rev norm_div_rev
#align norm_sub_rev norm_sub_rev

@[to_additive (attr := simp) norm_neg]
theorem norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖ := by simpa using norm_div_rev 1 a
#align norm_inv' norm_inv'
#align norm_neg norm_neg

open scoped symmDiff in
@[to_additive]
theorem dist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    dist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖ := by
  rw [dist_eq_norm_div, Set.apply_mulIndicator_symmDiff norm_inv']

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add_le "**Triangle inequality** for the norm."]
theorem norm_mul_le' (a b : E) : ‖a * b‖ ≤ ‖a‖ + ‖b‖ := by
  simpa [dist_eq_norm_div] using dist_triangle a 1 b⁻¹
#align norm_mul_le' norm_mul_le'
#align norm_add_le norm_add_le

@[to_additive]
theorem norm_mul_le_of_le (h₁ : ‖a₁‖ ≤ r₁) (h₂ : ‖a₂‖ ≤ r₂) : ‖a₁ * a₂‖ ≤ r₁ + r₂ :=
  (norm_mul_le' a₁ a₂).trans <| add_le_add h₁ h₂
#align norm_mul_le_of_le norm_mul_le_of_le
#align norm_add_le_of_le norm_add_le_of_le

@[to_additive norm_add₃_le]
theorem norm_mul₃_le (a b c : E) : ‖a * b * c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
  norm_mul_le_of_le (norm_mul_le' _ _) le_rfl
#align norm_mul₃_le norm_mul₃_le
#align norm_add₃_le norm_add₃_le

@[to_additive]
lemma norm_div_le_norm_div_add_norm_div (a b c : E) : ‖a / c‖ ≤ ‖a / b‖ + ‖b / c‖ := by
  simpa only [dist_eq_norm_div] using dist_triangle a b c

@[to_additive (attr := simp) norm_nonneg]
theorem norm_nonneg' (a : E) : 0 ≤ ‖a‖ := by
  rw [← dist_one_right]
  exact dist_nonneg
#align norm_nonneg' norm_nonneg'
#align norm_nonneg norm_nonneg

@[to_additive (attr := simp) abs_norm]
theorem abs_norm' (z : E) : |‖z‖| = ‖z‖ := abs_of_nonneg <| norm_nonneg' _
#align abs_norm abs_norm

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: multiplicative norms are nonnegative, via
`norm_nonneg'`. -/
@[positivity Norm.norm _]
def evalMulNorm : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Norm.norm $β $instDist $a) =>
    let _inst ← synthInstanceQ q(SeminormedGroup $β)
    assertInstancesCommute
    pure (.nonnegative q(norm_nonneg' $a))
  | _, _, _ => throwError "not ‖ · ‖"

/-- Extension for the `positivity` tactic: additive norms are nonnegative, via `norm_nonneg`. -/
@[positivity Norm.norm _]
def evalAddNorm : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Norm.norm $β $instDist $a) =>
    let _inst ← synthInstanceQ q(SeminormedAddGroup $β)
    assertInstancesCommute
    pure (.nonnegative q(norm_nonneg $a))
  | _, _, _ => throwError "not ‖ · ‖"

end Mathlib.Meta.Positivity

@[to_additive (attr := simp) norm_zero]
theorem norm_one' : ‖(1 : E)‖ = 0 := by rw [← dist_one_right, dist_self]
#align norm_one' norm_one'
#align norm_zero norm_zero

@[to_additive]
theorem ne_one_of_norm_ne_zero : ‖a‖ ≠ 0 → a ≠ 1 :=
  mt <| by
    rintro rfl
    exact norm_one'
#align ne_one_of_norm_ne_zero ne_one_of_norm_ne_zero
#align ne_zero_of_norm_ne_zero ne_zero_of_norm_ne_zero

@[to_additive (attr := nontriviality) norm_of_subsingleton]
theorem norm_of_subsingleton' [Subsingleton E] (a : E) : ‖a‖ = 0 := by
  rw [Subsingleton.elim a 1, norm_one']
#align norm_of_subsingleton' norm_of_subsingleton'
#align norm_of_subsingleton norm_of_subsingleton

@[to_additive zero_lt_one_add_norm_sq]
theorem zero_lt_one_add_norm_sq' (x : E) : 0 < 1 + ‖x‖ ^ 2 := by
  positivity
#align zero_lt_one_add_norm_sq' zero_lt_one_add_norm_sq'
#align zero_lt_one_add_norm_sq zero_lt_one_add_norm_sq

@[to_additive]
theorem norm_div_le (a b : E) : ‖a / b‖ ≤ ‖a‖ + ‖b‖ := by
  simpa [dist_eq_norm_div] using dist_triangle a 1 b
#align norm_div_le norm_div_le
#align norm_sub_le norm_sub_le

@[to_additive]
theorem norm_div_le_of_le {r₁ r₂ : ℝ} (H₁ : ‖a₁‖ ≤ r₁) (H₂ : ‖a₂‖ ≤ r₂) : ‖a₁ / a₂‖ ≤ r₁ + r₂ :=
  (norm_div_le a₁ a₂).trans <| add_le_add H₁ H₂
#align norm_div_le_of_le norm_div_le_of_le
#align norm_sub_le_of_le norm_sub_le_of_le

@[to_additive dist_le_norm_add_norm]
theorem dist_le_norm_add_norm' (a b : E) : dist a b ≤ ‖a‖ + ‖b‖ := by
  rw [dist_eq_norm_div]
  apply norm_div_le
#align dist_le_norm_add_norm' dist_le_norm_add_norm'
#align dist_le_norm_add_norm dist_le_norm_add_norm

@[to_additive abs_norm_sub_norm_le]
theorem abs_norm_sub_norm_le' (a b : E) : |‖a‖ - ‖b‖| ≤ ‖a / b‖ := by
  simpa [dist_eq_norm_div] using abs_dist_sub_le a b 1
#align abs_norm_sub_norm_le' abs_norm_sub_norm_le'
#align abs_norm_sub_norm_le abs_norm_sub_norm_le

@[to_additive norm_sub_norm_le]
theorem norm_sub_norm_le' (a b : E) : ‖a‖ - ‖b‖ ≤ ‖a / b‖ :=
  (le_abs_self _).trans (abs_norm_sub_norm_le' a b)
#align norm_sub_norm_le' norm_sub_norm_le'
#align norm_sub_norm_le norm_sub_norm_le

@[to_additive dist_norm_norm_le]
theorem dist_norm_norm_le' (a b : E) : dist ‖a‖ ‖b‖ ≤ ‖a / b‖ :=
  abs_norm_sub_norm_le' a b
#align dist_norm_norm_le' dist_norm_norm_le'
#align dist_norm_norm_le dist_norm_norm_le

@[to_additive]
theorem norm_le_norm_add_norm_div' (u v : E) : ‖u‖ ≤ ‖v‖ + ‖u / v‖ := by
  rw [add_comm]
  refine (norm_mul_le' _ _).trans_eq' ?_
  rw [div_mul_cancel]
#align norm_le_norm_add_norm_div' norm_le_norm_add_norm_div'
#align norm_le_norm_add_norm_sub' norm_le_norm_add_norm_sub'

@[to_additive]
theorem norm_le_norm_add_norm_div (u v : E) : ‖v‖ ≤ ‖u‖ + ‖u / v‖ := by
  rw [norm_div_rev]
  exact norm_le_norm_add_norm_div' v u
#align norm_le_norm_add_norm_div norm_le_norm_add_norm_div
#align norm_le_norm_add_norm_sub norm_le_norm_add_norm_sub

alias norm_le_insert' := norm_le_norm_add_norm_sub'
#align norm_le_insert' norm_le_insert'

alias norm_le_insert := norm_le_norm_add_norm_sub
#align norm_le_insert norm_le_insert

@[to_additive]
theorem norm_le_mul_norm_add (u v : E) : ‖u‖ ≤ ‖u * v‖ + ‖v‖ :=
  calc
    ‖u‖ = ‖u * v / v‖ := by rw [mul_div_cancel_right]
    _ ≤ ‖u * v‖ + ‖v‖ := norm_div_le _ _
#align norm_le_mul_norm_add norm_le_mul_norm_add
#align norm_le_add_norm_add norm_le_add_norm_add

@[to_additive ball_eq]
theorem ball_eq' (y : E) (ε : ℝ) : ball y ε = { x | ‖x / y‖ < ε } :=
  Set.ext fun a => by simp [dist_eq_norm_div]
#align ball_eq' ball_eq'
#align ball_eq ball_eq

@[to_additive]
theorem ball_one_eq (r : ℝ) : ball (1 : E) r = { x | ‖x‖ < r } :=
  Set.ext fun a => by simp
#align ball_one_eq ball_one_eq
#align ball_zero_eq ball_zero_eq

@[to_additive mem_ball_iff_norm]
theorem mem_ball_iff_norm'' : b ∈ ball a r ↔ ‖b / a‖ < r := by rw [mem_ball, dist_eq_norm_div]
#align mem_ball_iff_norm'' mem_ball_iff_norm''
#align mem_ball_iff_norm mem_ball_iff_norm

@[to_additive mem_ball_iff_norm']
theorem mem_ball_iff_norm''' : b ∈ ball a r ↔ ‖a / b‖ < r := by rw [mem_ball', dist_eq_norm_div]
#align mem_ball_iff_norm''' mem_ball_iff_norm'''
#align mem_ball_iff_norm' mem_ball_iff_norm'

@[to_additive] -- Porting note (#10618): `simp` can prove it
theorem mem_ball_one_iff : a ∈ ball (1 : E) r ↔ ‖a‖ < r := by rw [mem_ball, dist_one_right]
#align mem_ball_one_iff mem_ball_one_iff
#align mem_ball_zero_iff mem_ball_zero_iff

@[to_additive mem_closedBall_iff_norm]
theorem mem_closedBall_iff_norm'' : b ∈ closedBall a r ↔ ‖b / a‖ ≤ r := by
  rw [mem_closedBall, dist_eq_norm_div]
#align mem_closed_ball_iff_norm'' mem_closedBall_iff_norm''
#align mem_closed_ball_iff_norm mem_closedBall_iff_norm

@[to_additive] -- Porting note (#10618): `simp` can prove it
theorem mem_closedBall_one_iff : a ∈ closedBall (1 : E) r ↔ ‖a‖ ≤ r := by
  rw [mem_closedBall, dist_one_right]
#align mem_closed_ball_one_iff mem_closedBall_one_iff
#align mem_closed_ball_zero_iff mem_closedBall_zero_iff

@[to_additive mem_closedBall_iff_norm']
theorem mem_closedBall_iff_norm''' : b ∈ closedBall a r ↔ ‖a / b‖ ≤ r := by
  rw [mem_closedBall', dist_eq_norm_div]
#align mem_closed_ball_iff_norm''' mem_closedBall_iff_norm'''
#align mem_closed_ball_iff_norm' mem_closedBall_iff_norm'

@[to_additive norm_le_of_mem_closedBall]
theorem norm_le_of_mem_closedBall' (h : b ∈ closedBall a r) : ‖b‖ ≤ ‖a‖ + r :=
  (norm_le_norm_add_norm_div' _ _).trans <| add_le_add_left (by rwa [← dist_eq_norm_div]) _
#align norm_le_of_mem_closed_ball' norm_le_of_mem_closedBall'
#align norm_le_of_mem_closed_ball norm_le_of_mem_closedBall

@[to_additive norm_le_norm_add_const_of_dist_le]
theorem norm_le_norm_add_const_of_dist_le' : dist a b ≤ r → ‖a‖ ≤ ‖b‖ + r :=
  norm_le_of_mem_closedBall'
#align norm_le_norm_add_const_of_dist_le' norm_le_norm_add_const_of_dist_le'
#align norm_le_norm_add_const_of_dist_le norm_le_norm_add_const_of_dist_le

@[to_additive norm_lt_of_mem_ball]
theorem norm_lt_of_mem_ball' (h : b ∈ ball a r) : ‖b‖ < ‖a‖ + r :=
  (norm_le_norm_add_norm_div' _ _).trans_lt <| add_lt_add_left (by rwa [← dist_eq_norm_div]) _
#align norm_lt_of_mem_ball' norm_lt_of_mem_ball'
#align norm_lt_of_mem_ball norm_lt_of_mem_ball

@[to_additive]
theorem norm_div_sub_norm_div_le_norm_div (u v w : E) : ‖u / w‖ - ‖v / w‖ ≤ ‖u / v‖ := by
  simpa only [div_div_div_cancel_right'] using norm_sub_norm_le' (u / w) (v / w)
#align norm_div_sub_norm_div_le_norm_div norm_div_sub_norm_div_le_norm_div
#align norm_sub_sub_norm_sub_le_norm_sub norm_sub_sub_norm_sub_le_norm_sub

@[to_additive (attr := simp 1001) mem_sphere_iff_norm]
-- Porting note: increase priority so the left-hand side doesn't reduce
theorem mem_sphere_iff_norm' : b ∈ sphere a r ↔ ‖b / a‖ = r := by simp [dist_eq_norm_div]
#align mem_sphere_iff_norm' mem_sphere_iff_norm'
#align mem_sphere_iff_norm mem_sphere_iff_norm

@[to_additive] -- `simp` can prove this
theorem mem_sphere_one_iff_norm : a ∈ sphere (1 : E) r ↔ ‖a‖ = r := by simp [dist_eq_norm_div]
#align mem_sphere_one_iff_norm mem_sphere_one_iff_norm
#align mem_sphere_zero_iff_norm mem_sphere_zero_iff_norm

@[to_additive (attr := simp) norm_eq_of_mem_sphere]
theorem norm_eq_of_mem_sphere' (x : sphere (1 : E) r) : ‖(x : E)‖ = r :=
  mem_sphere_one_iff_norm.mp x.2
#align norm_eq_of_mem_sphere' norm_eq_of_mem_sphere'
#align norm_eq_of_mem_sphere norm_eq_of_mem_sphere

@[to_additive]
theorem ne_one_of_mem_sphere (hr : r ≠ 0) (x : sphere (1 : E) r) : (x : E) ≠ 1 :=
  ne_one_of_norm_ne_zero <| by rwa [norm_eq_of_mem_sphere' x]
#align ne_one_of_mem_sphere ne_one_of_mem_sphere
#align ne_zero_of_mem_sphere ne_zero_of_mem_sphere

@[to_additive ne_zero_of_mem_unit_sphere]
theorem ne_one_of_mem_unit_sphere (x : sphere (1 : E) 1) : (x : E) ≠ 1 :=
  ne_one_of_mem_sphere one_ne_zero _
#align ne_one_of_mem_unit_sphere ne_one_of_mem_unit_sphere
#align ne_zero_of_mem_unit_sphere ne_zero_of_mem_unit_sphere

variable (E)

/-- The norm of a seminormed group as a group seminorm. -/
@[to_additive "The norm of a seminormed group as an additive group seminorm."]
def normGroupSeminorm : GroupSeminorm E :=
  ⟨norm, norm_one', norm_mul_le', norm_inv'⟩
#align norm_group_seminorm normGroupSeminorm
#align norm_add_group_seminorm normAddGroupSeminorm

@[to_additive (attr := simp)]
theorem coe_normGroupSeminorm : ⇑(normGroupSeminorm E) = norm :=
  rfl
#align coe_norm_group_seminorm coe_normGroupSeminorm
#align coe_norm_add_group_seminorm coe_normAddGroupSeminorm

variable {E}

@[to_additive]
theorem NormedCommGroup.tendsto_nhds_one {f : α → E} {l : Filter α} :
    Tendsto f l (𝓝 1) ↔ ∀ ε > 0, ∀ᶠ x in l, ‖f x‖ < ε :=
  Metric.tendsto_nhds.trans <| by simp only [dist_one_right]
#align normed_comm_group.tendsto_nhds_one NormedCommGroup.tendsto_nhds_one
#align normed_add_comm_group.tendsto_nhds_zero NormedAddCommGroup.tendsto_nhds_zero

@[to_additive]
theorem NormedCommGroup.tendsto_nhds_nhds {f : E → F} {x : E} {y : F} :
    Tendsto f (𝓝 x) (𝓝 y) ↔ ∀ ε > 0, ∃ δ > 0, ∀ x', ‖x' / x‖ < δ → ‖f x' / y‖ < ε := by
  simp_rw [Metric.tendsto_nhds_nhds, dist_eq_norm_div]
#align normed_comm_group.tendsto_nhds_nhds NormedCommGroup.tendsto_nhds_nhds
#align normed_add_comm_group.tendsto_nhds_nhds NormedAddCommGroup.tendsto_nhds_nhds

@[to_additive]
theorem NormedCommGroup.nhds_basis_norm_lt (x : E) :
    (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { y | ‖y / x‖ < ε } := by
  simp_rw [← ball_eq']
  exact Metric.nhds_basis_ball
#align normed_comm_group.nhds_basis_norm_lt NormedCommGroup.nhds_basis_norm_lt
#align normed_add_comm_group.nhds_basis_norm_lt NormedAddCommGroup.nhds_basis_norm_lt

@[to_additive]
theorem NormedCommGroup.nhds_one_basis_norm_lt :
    (𝓝 (1 : E)).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { y | ‖y‖ < ε } := by
  convert NormedCommGroup.nhds_basis_norm_lt (1 : E)
  simp
#align normed_comm_group.nhds_one_basis_norm_lt NormedCommGroup.nhds_one_basis_norm_lt
#align normed_add_comm_group.nhds_zero_basis_norm_lt NormedAddCommGroup.nhds_zero_basis_norm_lt

@[to_additive]
theorem NormedCommGroup.uniformity_basis_dist :
    (𝓤 E).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : E × E | ‖p.fst / p.snd‖ < ε } := by
  convert Metric.uniformity_basis_dist (α := E) using 1
  simp [dist_eq_norm_div]
#align normed_comm_group.uniformity_basis_dist NormedCommGroup.uniformity_basis_dist
#align normed_add_comm_group.uniformity_basis_dist NormedAddCommGroup.uniformity_basis_dist

open Finset

variable [FunLike 𝓕 E F]

section NNNorm

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedGroup.toNNNorm : NNNorm E :=
  ⟨fun a => ⟨‖a‖, norm_nonneg' a⟩⟩
#align seminormed_group.to_has_nnnorm SeminormedGroup.toNNNorm
#align seminormed_add_group.to_has_nnnorm SeminormedAddGroup.toNNNorm

@[to_additive (attr := simp, norm_cast) coe_nnnorm]
theorem coe_nnnorm' (a : E) : (‖a‖₊ : ℝ) = ‖a‖ :=
  rfl
#align coe_nnnorm' coe_nnnorm'
#align coe_nnnorm coe_nnnorm

@[to_additive (attr := simp) coe_comp_nnnorm]
theorem coe_comp_nnnorm' : (toReal : ℝ≥0 → ℝ) ∘ (nnnorm : E → ℝ≥0) = norm :=
  rfl
#align coe_comp_nnnorm' coe_comp_nnnorm'
#align coe_comp_nnnorm coe_comp_nnnorm

@[to_additive norm_toNNReal]
theorem norm_toNNReal' : ‖a‖.toNNReal = ‖a‖₊ :=
  @Real.toNNReal_coe ‖a‖₊
#align norm_to_nnreal' norm_toNNReal'
#align norm_to_nnreal norm_toNNReal

@[to_additive]
theorem nndist_eq_nnnorm_div (a b : E) : nndist a b = ‖a / b‖₊ :=
  NNReal.eq <| dist_eq_norm_div _ _
#align nndist_eq_nnnorm_div nndist_eq_nnnorm_div
#align nndist_eq_nnnorm_sub nndist_eq_nnnorm_sub

alias nndist_eq_nnnorm := nndist_eq_nnnorm_sub
#align nndist_eq_nnnorm nndist_eq_nnnorm

@[to_additive (attr := simp) nnnorm_zero]
theorem nnnorm_one' : ‖(1 : E)‖₊ = 0 :=
  NNReal.eq norm_one'
#align nnnorm_one' nnnorm_one'
#align nnnorm_zero nnnorm_zero

@[to_additive]
theorem ne_one_of_nnnorm_ne_zero {a : E} : ‖a‖₊ ≠ 0 → a ≠ 1 :=
  mt <| by
    rintro rfl
    exact nnnorm_one'
#align ne_one_of_nnnorm_ne_zero ne_one_of_nnnorm_ne_zero
#align ne_zero_of_nnnorm_ne_zero ne_zero_of_nnnorm_ne_zero

@[to_additive nnnorm_add_le]
theorem nnnorm_mul_le' (a b : E) : ‖a * b‖₊ ≤ ‖a‖₊ + ‖b‖₊ :=
  NNReal.coe_le_coe.1 <| norm_mul_le' a b
#align nnnorm_mul_le' nnnorm_mul_le'
#align nnnorm_add_le nnnorm_add_le

@[to_additive (attr := simp) nnnorm_neg]
theorem nnnorm_inv' (a : E) : ‖a⁻¹‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_inv' a
#align nnnorm_inv' nnnorm_inv'
#align nnnorm_neg nnnorm_neg

open scoped symmDiff in
@[to_additive]
theorem nndist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    nndist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊ :=
  NNReal.eq <| dist_mulIndicator s t f x

@[to_additive]
theorem nnnorm_div_le (a b : E) : ‖a / b‖₊ ≤ ‖a‖₊ + ‖b‖₊ :=
  NNReal.coe_le_coe.1 <| norm_div_le _ _
#align nnnorm_div_le nnnorm_div_le
#align nnnorm_sub_le nnnorm_sub_le

@[to_additive nndist_nnnorm_nnnorm_le]
theorem nndist_nnnorm_nnnorm_le' (a b : E) : nndist ‖a‖₊ ‖b‖₊ ≤ ‖a / b‖₊ :=
  NNReal.coe_le_coe.1 <| dist_norm_norm_le' a b
#align nndist_nnnorm_nnnorm_le' nndist_nnnorm_nnnorm_le'
#align nndist_nnnorm_nnnorm_le nndist_nnnorm_nnnorm_le

@[to_additive]
theorem nnnorm_le_nnnorm_add_nnnorm_div (a b : E) : ‖b‖₊ ≤ ‖a‖₊ + ‖a / b‖₊ :=
  norm_le_norm_add_norm_div _ _
#align nnnorm_le_nnnorm_add_nnnorm_div nnnorm_le_nnnorm_add_nnnorm_div
#align nnnorm_le_nnnorm_add_nnnorm_sub nnnorm_le_nnnorm_add_nnnorm_sub

@[to_additive]
theorem nnnorm_le_nnnorm_add_nnnorm_div' (a b : E) : ‖a‖₊ ≤ ‖b‖₊ + ‖a / b‖₊ :=
  norm_le_norm_add_norm_div' _ _
#align nnnorm_le_nnnorm_add_nnnorm_div' nnnorm_le_nnnorm_add_nnnorm_div'
#align nnnorm_le_nnnorm_add_nnnorm_sub' nnnorm_le_nnnorm_add_nnnorm_sub'

alias nnnorm_le_insert' := nnnorm_le_nnnorm_add_nnnorm_sub'
#align nnnorm_le_insert' nnnorm_le_insert'

alias nnnorm_le_insert := nnnorm_le_nnnorm_add_nnnorm_sub
#align nnnorm_le_insert nnnorm_le_insert

@[to_additive]
theorem nnnorm_le_mul_nnnorm_add (a b : E) : ‖a‖₊ ≤ ‖a * b‖₊ + ‖b‖₊ :=
  norm_le_mul_norm_add _ _
#align nnnorm_le_mul_nnnorm_add nnnorm_le_mul_nnnorm_add
#align nnnorm_le_add_nnnorm_add nnnorm_le_add_nnnorm_add

@[to_additive ofReal_norm_eq_coe_nnnorm]
theorem ofReal_norm_eq_coe_nnnorm' (a : E) : ENNReal.ofReal ‖a‖ = ‖a‖₊ :=
  ENNReal.ofReal_eq_coe_nnreal _
#align of_real_norm_eq_coe_nnnorm' ofReal_norm_eq_coe_nnnorm'
#align of_real_norm_eq_coe_nnnorm ofReal_norm_eq_coe_nnnorm

/-- The non negative norm seen as an `ENNReal` and then as a `Real` is equal to the norm. -/
@[to_additive toReal_coe_nnnorm "The non negative norm seen as an `ENNReal` and
then as a `Real` is equal to the norm."]
theorem toReal_coe_nnnorm' (a : E) : (‖a‖₊ : ℝ≥0∞).toReal = ‖a‖ := rfl

@[to_additive]
theorem edist_eq_coe_nnnorm_div (a b : E) : edist a b = ‖a / b‖₊ := by
  rw [edist_dist, dist_eq_norm_div, ofReal_norm_eq_coe_nnnorm']
#align edist_eq_coe_nnnorm_div edist_eq_coe_nnnorm_div
#align edist_eq_coe_nnnorm_sub edist_eq_coe_nnnorm_sub

@[to_additive edist_eq_coe_nnnorm]
theorem edist_eq_coe_nnnorm' (x : E) : edist x 1 = (‖x‖₊ : ℝ≥0∞) := by
  rw [edist_eq_coe_nnnorm_div, div_one]
#align edist_eq_coe_nnnorm' edist_eq_coe_nnnorm'
#align edist_eq_coe_nnnorm edist_eq_coe_nnnorm

open scoped symmDiff in
@[to_additive]
theorem edist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    edist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊ := by
  rw [edist_nndist, nndist_mulIndicator]

@[to_additive]
theorem mem_emetric_ball_one_iff {r : ℝ≥0∞} : a ∈ EMetric.ball (1 : E) r ↔ ↑‖a‖₊ < r := by
  rw [EMetric.mem_ball, edist_eq_coe_nnnorm']
#align mem_emetric_ball_one_iff mem_emetric_ball_one_iff
#align mem_emetric_ball_zero_iff mem_emetric_ball_zero_iff

end NNNorm

@[to_additive]
theorem tendsto_iff_norm_div_tendsto_zero {f : α → E} {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖f e / b‖) a (𝓝 0) := by
  simp only [← dist_eq_norm_div, ← tendsto_iff_dist_tendsto_zero]
#align tendsto_iff_norm_tendsto_one tendsto_iff_norm_div_tendsto_zero
#align tendsto_iff_norm_tendsto_zero tendsto_iff_norm_sub_tendsto_zero

@[to_additive]
theorem tendsto_one_iff_norm_tendsto_zero {f : α → E} {a : Filter α} :
    Tendsto f a (𝓝 1) ↔ Tendsto (‖f ·‖) a (𝓝 0) :=
  tendsto_iff_norm_div_tendsto_zero.trans <| by simp only [div_one]
#align tendsto_one_iff_norm_tendsto_one tendsto_one_iff_norm_tendsto_zero
#align tendsto_zero_iff_norm_tendsto_zero tendsto_zero_iff_norm_tendsto_zero

@[to_additive]
theorem comap_norm_nhds_one : comap norm (𝓝 0) = 𝓝 (1 : E) := by
  simpa only [dist_one_right] using nhds_comap_dist (1 : E)
#align comap_norm_nhds_one comap_norm_nhds_one
#align comap_norm_nhds_zero comap_norm_nhds_zero

/-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a real
function `a` which tends to `0`, then `f` tends to `1` (neutral element of `SeminormedGroup`).
In this pair of lemmas (`squeeze_one_norm'` and `squeeze_one_norm`), following a convention of
similar lemmas in `Topology.MetricSpace.Basic` and `Topology.Algebra.Order`, the `'` version is
phrased using "eventually" and the non-`'` version is phrased absolutely. -/
@[to_additive "Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a
real function `a` which tends to `0`, then `f` tends to `0`. In this pair of lemmas
(`squeeze_zero_norm'` and `squeeze_zero_norm`), following a convention of similar lemmas in
`Topology.MetricSpace.Pseudo.Defs` and `Topology.Algebra.Order`, the `'` version is phrased using
\"eventually\" and the non-`'` version is phrased absolutely."]
theorem squeeze_one_norm' {f : α → E} {a : α → ℝ} {t₀ : Filter α} (h : ∀ᶠ n in t₀, ‖f n‖ ≤ a n)
    (h' : Tendsto a t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 1) :=
  tendsto_one_iff_norm_tendsto_zero.2 <|
    squeeze_zero' (eventually_of_forall fun _n => norm_nonneg' _) h h'
#align squeeze_one_norm' squeeze_one_norm'
#align squeeze_zero_norm' squeeze_zero_norm'

/-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real function `a` which
tends to `0`, then `f` tends to `1`. -/
@[to_additive "Special case of the sandwich theorem: if the norm of `f` is bounded by a real
function `a` which tends to `0`, then `f` tends to `0`."]
theorem squeeze_one_norm {f : α → E} {a : α → ℝ} {t₀ : Filter α} (h : ∀ n, ‖f n‖ ≤ a n) :
    Tendsto a t₀ (𝓝 0) → Tendsto f t₀ (𝓝 1) :=
  squeeze_one_norm' <| eventually_of_forall h
#align squeeze_one_norm squeeze_one_norm
#align squeeze_zero_norm squeeze_zero_norm

@[to_additive]
theorem tendsto_norm_div_self (x : E) : Tendsto (fun a => ‖a / x‖) (𝓝 x) (𝓝 0) := by
  simpa [dist_eq_norm_div] using
    tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (x : E)) (𝓝 x) _)
#align tendsto_norm_div_self tendsto_norm_div_self
#align tendsto_norm_sub_self tendsto_norm_sub_self

@[to_additive tendsto_norm]
theorem tendsto_norm' {x : E} : Tendsto (fun a => ‖a‖) (𝓝 x) (𝓝 ‖x‖) := by
  simpa using tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (1 : E)) _ _)
#align tendsto_norm' tendsto_norm'
#align tendsto_norm tendsto_norm

@[to_additive]
theorem tendsto_norm_one : Tendsto (fun a : E => ‖a‖) (𝓝 1) (𝓝 0) := by
  simpa using tendsto_norm_div_self (1 : E)
#align tendsto_norm_one tendsto_norm_one
#align tendsto_norm_zero tendsto_norm_zero

@[to_additive (attr := continuity) continuous_norm]
theorem continuous_norm' : Continuous fun a : E => ‖a‖ := by
  simpa using continuous_id.dist (continuous_const : Continuous fun _a => (1 : E))
#align continuous_norm' continuous_norm'
#align continuous_norm continuous_norm

@[to_additive (attr := continuity) continuous_nnnorm]
theorem continuous_nnnorm' : Continuous fun a : E => ‖a‖₊ :=
  continuous_norm'.subtype_mk _
#align continuous_nnnorm' continuous_nnnorm'
#align continuous_nnnorm continuous_nnnorm

@[to_additive]
theorem mem_closure_one_iff_norm {x : E} : x ∈ closure ({1} : Set E) ↔ ‖x‖ = 0 := by
  rw [← closedBall_zero', mem_closedBall_one_iff, (norm_nonneg' x).le_iff_eq]
#align mem_closure_one_iff_norm mem_closure_one_iff_norm
#align mem_closure_zero_iff_norm mem_closure_zero_iff_norm

@[to_additive]
theorem closure_one_eq : closure ({1} : Set E) = { x | ‖x‖ = 0 } :=
  Set.ext fun _x => mem_closure_one_iff_norm
#align closure_one_eq closure_one_eq
#align closure_zero_eq closure_zero_eq

section

variable {l : Filter α} {f : α → E}

@[to_additive Filter.Tendsto.norm]
theorem Filter.Tendsto.norm' (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ‖f x‖) l (𝓝 ‖a‖) :=
  tendsto_norm'.comp h
#align filter.tendsto.norm' Filter.Tendsto.norm'
#align filter.tendsto.norm Filter.Tendsto.norm

@[to_additive Filter.Tendsto.nnnorm]
theorem Filter.Tendsto.nnnorm' (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ‖f x‖₊) l (𝓝 ‖a‖₊) :=
  Tendsto.comp continuous_nnnorm'.continuousAt h
#align filter.tendsto.nnnorm' Filter.Tendsto.nnnorm'
#align filter.tendsto.nnnorm Filter.Tendsto.nnnorm

end

section

variable [TopologicalSpace α] {f : α → E}

@[to_additive (attr := fun_prop) Continuous.norm]
theorem Continuous.norm' : Continuous f → Continuous fun x => ‖f x‖ :=
  continuous_norm'.comp
#align continuous.norm' Continuous.norm'
#align continuous.norm Continuous.norm

@[to_additive (attr := fun_prop) Continuous.nnnorm]
theorem Continuous.nnnorm' : Continuous f → Continuous fun x => ‖f x‖₊ :=
  continuous_nnnorm'.comp
#align continuous.nnnorm' Continuous.nnnorm'
#align continuous.nnnorm Continuous.nnnorm

@[to_additive (attr := fun_prop) ContinuousAt.norm]
theorem ContinuousAt.norm' {a : α} (h : ContinuousAt f a) : ContinuousAt (fun x => ‖f x‖) a :=
  Tendsto.norm' h
#align continuous_at.norm' ContinuousAt.norm'
#align continuous_at.norm ContinuousAt.norm

@[to_additive (attr := fun_prop) ContinuousAt.nnnorm]
theorem ContinuousAt.nnnorm' {a : α} (h : ContinuousAt f a) : ContinuousAt (fun x => ‖f x‖₊) a :=
  Tendsto.nnnorm' h
#align continuous_at.nnnorm' ContinuousAt.nnnorm'
#align continuous_at.nnnorm ContinuousAt.nnnorm

@[to_additive ContinuousWithinAt.norm]
theorem ContinuousWithinAt.norm' {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => ‖f x‖) s a :=
  Tendsto.norm' h
#align continuous_within_at.norm' ContinuousWithinAt.norm'
#align continuous_within_at.norm ContinuousWithinAt.norm

@[to_additive ContinuousWithinAt.nnnorm]
theorem ContinuousWithinAt.nnnorm' {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => ‖f x‖₊) s a :=
  Tendsto.nnnorm' h
#align continuous_within_at.nnnorm' ContinuousWithinAt.nnnorm'
#align continuous_within_at.nnnorm ContinuousWithinAt.nnnorm

@[to_additive (attr := fun_prop) ContinuousOn.norm]
theorem ContinuousOn.norm' {s : Set α} (h : ContinuousOn f s) : ContinuousOn (fun x => ‖f x‖) s :=
  fun x hx => (h x hx).norm'
#align continuous_on.norm' ContinuousOn.norm'
#align continuous_on.norm ContinuousOn.norm

@[to_additive (attr := fun_prop) ContinuousOn.nnnorm]
theorem ContinuousOn.nnnorm' {s : Set α} (h : ContinuousOn f s) :
    ContinuousOn (fun x => ‖f x‖₊) s := fun x hx => (h x hx).nnnorm'
#align continuous_on.nnnorm' ContinuousOn.nnnorm'
#align continuous_on.nnnorm ContinuousOn.nnnorm

end

/-- If `‖y‖ → ∞`, then we can assume `y ≠ x` for any fixed `x`. -/
@[to_additive eventually_ne_of_tendsto_norm_atTop "If `‖y‖→∞`, then we can assume `y≠x` for any
fixed `x`"]
theorem eventually_ne_of_tendsto_norm_atTop' {l : Filter α} {f : α → E}
    (h : Tendsto (fun y => ‖f y‖) l atTop) (x : E) : ∀ᶠ y in l, f y ≠ x :=
  (h.eventually_ne_atTop _).mono fun _x => ne_of_apply_ne norm
#align eventually_ne_of_tendsto_norm_at_top' eventually_ne_of_tendsto_norm_atTop'
#align eventually_ne_of_tendsto_norm_at_top eventually_ne_of_tendsto_norm_atTop

@[to_additive]
theorem SeminormedCommGroup.mem_closure_iff :
    a ∈ closure s ↔ ∀ ε, 0 < ε → ∃ b ∈ s, ‖a / b‖ < ε := by
  simp [Metric.mem_closure_iff, dist_eq_norm_div]
#align seminormed_comm_group.mem_closure_iff SeminormedCommGroup.mem_closure_iff
#align seminormed_add_comm_group.mem_closure_iff SeminormedAddCommGroup.mem_closure_iff

@[to_additive norm_le_zero_iff']
theorem norm_le_zero_iff''' [T0Space E] {a : E} : ‖a‖ ≤ 0 ↔ a = 1 := by
  letI : NormedGroup E :=
    { ‹SeminormedGroup E› with toMetricSpace := MetricSpace.ofT0PseudoMetricSpace E }
  rw [← dist_one_right, dist_le_zero]
#align norm_le_zero_iff''' norm_le_zero_iff'''
#align norm_le_zero_iff' norm_le_zero_iff'

@[to_additive norm_eq_zero']
theorem norm_eq_zero''' [T0Space E] {a : E} : ‖a‖ = 0 ↔ a = 1 :=
  (norm_nonneg' a).le_iff_eq.symm.trans norm_le_zero_iff'''
#align norm_eq_zero''' norm_eq_zero'''
#align norm_eq_zero' norm_eq_zero'

@[to_additive norm_pos_iff']
theorem norm_pos_iff''' [T0Space E] {a : E} : 0 < ‖a‖ ↔ a ≠ 1 := by
  rw [← not_le, norm_le_zero_iff''']
#align norm_pos_iff''' norm_pos_iff'''
#align norm_pos_iff' norm_pos_iff'

@[to_additive]
theorem SeminormedGroup.tendstoUniformlyOn_one {f : ι → κ → G} {s : Set κ} {l : Filter ι} :
    TendstoUniformlyOn f 1 l s ↔ ∀ ε > 0, ∀ᶠ i in l, ∀ x ∈ s, ‖f i x‖ < ε := by
  #adaptation_note /-- nightly-2024-03-11.
  Originally this was `simp_rw` instead of `simp only`,
  but this creates a bad proof term with nested `OfNat.ofNat` that trips up `@[to_additive]`. -/
  simp only [tendstoUniformlyOn_iff, Pi.one_apply, dist_one_left]
#align seminormed_group.tendsto_uniformly_on_one SeminormedGroup.tendstoUniformlyOn_one
#align seminormed_add_group.tendsto_uniformly_on_zero SeminormedAddGroup.tendstoUniformlyOn_zero

@[to_additive]
theorem SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one {f : ι → κ → G}
    {l : Filter ι} {l' : Filter κ} :
    UniformCauchySeqOnFilter f l l' ↔
      TendstoUniformlyOnFilter (fun n : ι × ι => fun z => f n.fst z / f n.snd z) 1 (l ×ˢ l) l' := by
  refine ⟨fun hf u hu => ?_, fun hf u hu => ?_⟩
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine
      (hf { p : G × G | dist p.fst p.snd < ε } <| dist_mem_uniformity hε).mono fun x hx =>
        H 1 (f x.fst.fst x.snd / f x.fst.snd x.snd) ?_
    simpa [dist_eq_norm_div, norm_div_rev] using hx
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine
      (hf { p : G × G | dist p.fst p.snd < ε } <| dist_mem_uniformity hε).mono fun x hx =>
        H (f x.fst.fst x.snd) (f x.fst.snd x.snd) ?_
    simpa [dist_eq_norm_div, norm_div_rev] using hx
#align seminormed_group.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_one SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one
#align seminormed_add_group.uniform_cauchy_seq_on_filter_iff_tendsto_uniformly_on_filter_zero SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero

@[to_additive]
theorem SeminormedGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_one {f : ι → κ → G} {s : Set κ}
    {l : Filter ι} :
    UniformCauchySeqOn f l s ↔
      TendstoUniformlyOn (fun n : ι × ι => fun z => f n.fst z / f n.snd z) 1 (l ×ˢ l) s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter,
    uniformCauchySeqOn_iff_uniformCauchySeqOnFilter,
    SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one]
#align seminormed_group.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_one SeminormedGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_one
#align seminormed_add_group.uniform_cauchy_seq_on_iff_tendsto_uniformly_on_zero SeminormedAddGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_zero

end SeminormedGroup

section Induced

variable (E F)
variable [FunLike 𝓕 E F]

-- See note [reducible non-instances]
/-- A group homomorphism from a `Group` to a `SeminormedGroup` induces a `SeminormedGroup`
structure on the domain. -/
@[to_additive (attr := reducible) "A group homomorphism from an `AddGroup` to a
`SeminormedAddGroup` induces a `SeminormedAddGroup` structure on the domain."]
def SeminormedGroup.induced [Group E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedGroup E :=
  { PseudoMetricSpace.induced f toPseudoMetricSpace with
    -- Porting note: needed to add the instance explicitly, and `‹PseudoMetricSpace F›` failed
    norm := fun x => ‖f x‖
    dist_eq := fun x y => by simp only [map_div, ← dist_eq_norm_div]; rfl }
#align seminormed_group.induced SeminormedGroup.induced
#align seminormed_add_group.induced SeminormedAddGroup.induced

-- See note [reducible non-instances]
/-- A group homomorphism from a `CommGroup` to a `SeminormedGroup` induces a
`SeminormedCommGroup` structure on the domain. -/
@[to_additive (attr := reducible) "A group homomorphism from an `AddCommGroup` to a
`SeminormedAddGroup` induces a `SeminormedAddCommGroup` structure on the domain."]
def SeminormedCommGroup.induced
    [CommGroup E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedCommGroup E :=
  { SeminormedGroup.induced E F f with
    mul_comm := mul_comm }
#align seminormed_comm_group.induced SeminormedCommGroup.induced
#align seminormed_add_comm_group.induced SeminormedAddCommGroup.induced

-- See note [reducible non-instances].
/-- An injective group homomorphism from a `Group` to a `NormedGroup` induces a `NormedGroup`
structure on the domain. -/
@[to_additive (attr := reducible) "An injective group homomorphism from an `AddGroup` to a
`NormedAddGroup` induces a `NormedAddGroup` structure on the domain."]
def NormedGroup.induced
    [Group E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) (h : Injective f) :
    NormedGroup E :=
  { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with }
#align normed_group.induced NormedGroup.induced
#align normed_add_group.induced NormedAddGroup.induced

-- See note [reducible non-instances].
/-- An injective group homomorphism from a `CommGroup` to a `NormedGroup` induces a
`NormedCommGroup` structure on the domain. -/
@[to_additive (attr := reducible) "An injective group homomorphism from a `CommGroup` to a
`NormedCommGroup` induces a `NormedCommGroup` structure on the domain."]
def NormedCommGroup.induced [CommGroup E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕)
    (h : Injective f) : NormedCommGroup E :=
  { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with
    mul_comm := mul_comm }
#align normed_comm_group.induced NormedCommGroup.induced
#align normed_add_comm_group.induced NormedAddCommGroup.induced

end Induced

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a a₁ a₂ b b₁ b₂ : E} {r r₁ r₂ : ℝ}

@[to_additive]
theorem dist_inv (x y : E) : dist x⁻¹ y = dist x y⁻¹ := by
  simp_rw [dist_eq_norm_div, ← norm_inv' (x⁻¹ / y), inv_div, div_inv_eq_mul, mul_comm]
#align dist_inv dist_inv
#align dist_neg dist_neg

theorem norm_multiset_sum_le {E} [SeminormedAddCommGroup E] (m : Multiset E) :
    ‖m.sum‖ ≤ (m.map fun x => ‖x‖).sum :=
  m.le_sum_of_subadditive norm norm_zero norm_add_le
#align norm_multiset_sum_le norm_multiset_sum_le

@[to_additive existing]
theorem norm_multiset_prod_le (m : Multiset E) : ‖m.prod‖ ≤ (m.map fun x => ‖x‖).sum := by
  rw [← Multiplicative.ofAdd_le, ofAdd_multiset_prod, Multiset.map_map]
  refine Multiset.le_prod_of_submultiplicative (Multiplicative.ofAdd ∘ norm) ?_ (fun x y => ?_) _
  · simp only [comp_apply, norm_one', ofAdd_zero]
  · exact norm_mul_le' x y
#align norm_multiset_prod_le norm_multiset_prod_le

-- Porting note: had to add `ι` here because otherwise the universe order gets switched compared to
-- `norm_prod_le` below
theorem norm_sum_le {ι E} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ :=
  s.le_sum_of_subadditive norm norm_zero norm_add_le f
#align norm_sum_le norm_sum_le

@[to_additive existing]
theorem norm_prod_le (s : Finset ι) (f : ι → E) : ‖∏ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := by
  rw [← Multiplicative.ofAdd_le, ofAdd_sum]
  refine Finset.le_prod_of_submultiplicative (Multiplicative.ofAdd ∘ norm) ?_ (fun x y => ?_) _ _
  · simp only [comp_apply, norm_one', ofAdd_zero]
  · exact norm_mul_le' x y
#align norm_prod_le norm_prod_le

@[to_additive]
theorem norm_prod_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ} (h : ∀ b ∈ s, ‖f b‖ ≤ n b) :
    ‖∏ b ∈ s, f b‖ ≤ ∑ b ∈ s, n b :=
  (norm_prod_le s f).trans <| Finset.sum_le_sum h
#align norm_prod_le_of_le norm_prod_le_of_le
#align norm_sum_le_of_le norm_sum_le_of_le

@[to_additive]
theorem dist_prod_prod_le_of_le (s : Finset ι) {f a : ι → E} {d : ι → ℝ}
    (h : ∀ b ∈ s, dist (f b) (a b) ≤ d b) :
    dist (∏ b ∈ s, f b) (∏ b ∈ s, a b) ≤ ∑ b ∈ s, d b := by
  simp only [dist_eq_norm_div, ← Finset.prod_div_distrib] at *
  exact norm_prod_le_of_le s h
#align dist_prod_prod_le_of_le dist_prod_prod_le_of_le
#align dist_sum_sum_le_of_le dist_sum_sum_le_of_le

@[to_additive]
theorem dist_prod_prod_le (s : Finset ι) (f a : ι → E) :
    dist (∏ b ∈ s, f b) (∏ b ∈ s, a b) ≤ ∑ b ∈ s, dist (f b) (a b) :=
  dist_prod_prod_le_of_le s fun _ _ => le_rfl
#align dist_prod_prod_le dist_prod_prod_le
#align dist_sum_sum_le dist_sum_sum_le

@[to_additive]
theorem mul_mem_ball_iff_norm : a * b ∈ ball a r ↔ ‖b‖ < r := by
  rw [mem_ball_iff_norm'', mul_div_cancel_left]
#align mul_mem_ball_iff_norm mul_mem_ball_iff_norm
#align add_mem_ball_iff_norm add_mem_ball_iff_norm

@[to_additive]
theorem mul_mem_closedBall_iff_norm : a * b ∈ closedBall a r ↔ ‖b‖ ≤ r := by
  rw [mem_closedBall_iff_norm'', mul_div_cancel_left]
#align mul_mem_closed_ball_iff_norm mul_mem_closedBall_iff_norm
#align add_mem_closed_ball_iff_norm add_mem_closedBall_iff_norm

@[to_additive (attr := simp 1001)]
-- Porting note: increase priority so that the left-hand side doesn't simplify
theorem preimage_mul_ball (a b : E) (r : ℝ) : (b * ·) ⁻¹' ball a r = ball (a / b) r := by
  ext c
  simp only [dist_eq_norm_div, Set.mem_preimage, mem_ball, div_div_eq_mul_div, mul_comm]
#align preimage_mul_ball preimage_mul_ball
#align preimage_add_ball preimage_add_ball

@[to_additive (attr := simp 1001)]
-- Porting note: increase priority so that the left-hand side doesn't simplify
theorem preimage_mul_closedBall (a b : E) (r : ℝ) :
    (b * ·) ⁻¹' closedBall a r = closedBall (a / b) r := by
  ext c
  simp only [dist_eq_norm_div, Set.mem_preimage, mem_closedBall, div_div_eq_mul_div, mul_comm]
#align preimage_mul_closed_ball preimage_mul_closedBall
#align preimage_add_closed_ball preimage_add_closedBall

@[to_additive (attr := simp)]
theorem preimage_mul_sphere (a b : E) (r : ℝ) : (b * ·) ⁻¹' sphere a r = sphere (a / b) r := by
  ext c
  simp only [Set.mem_preimage, mem_sphere_iff_norm', div_div_eq_mul_div, mul_comm]
#align preimage_mul_sphere preimage_mul_sphere
#align preimage_add_sphere preimage_add_sphere

@[to_additive norm_nsmul_le]
theorem norm_pow_le_mul_norm (n : ℕ) (a : E) : ‖a ^ n‖ ≤ n * ‖a‖ := by
  induction' n with n ih; · simp
  simpa only [pow_succ, Nat.cast_succ, add_mul, one_mul] using norm_mul_le_of_le ih le_rfl
#align norm_pow_le_mul_norm norm_pow_le_mul_norm
#align norm_nsmul_le norm_nsmul_le

@[to_additive nnnorm_nsmul_le]
theorem nnnorm_pow_le_mul_norm (n : ℕ) (a : E) : ‖a ^ n‖₊ ≤ n * ‖a‖₊ := by
  simpa only [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_natCast] using
    norm_pow_le_mul_norm n a
#align nnnorm_pow_le_mul_norm nnnorm_pow_le_mul_norm
#align nnnorm_nsmul_le nnnorm_nsmul_le

@[to_additive]
theorem pow_mem_closedBall {n : ℕ} (h : a ∈ closedBall b r) :
    a ^ n ∈ closedBall (b ^ n) (n • r) := by
  simp only [mem_closedBall, dist_eq_norm_div, ← div_pow] at h ⊢
  refine (norm_pow_le_mul_norm n (a / b)).trans ?_
  simpa only [nsmul_eq_mul] using mul_le_mul_of_nonneg_left h n.cast_nonneg
#align pow_mem_closed_ball pow_mem_closedBall
#align nsmul_mem_closed_ball nsmul_mem_closedBall

@[to_additive]
theorem pow_mem_ball {n : ℕ} (hn : 0 < n) (h : a ∈ ball b r) : a ^ n ∈ ball (b ^ n) (n • r) := by
  simp only [mem_ball, dist_eq_norm_div, ← div_pow] at h ⊢
  refine lt_of_le_of_lt (norm_pow_le_mul_norm n (a / b)) ?_
  replace hn : 0 < (n : ℝ) := by norm_cast
  rw [nsmul_eq_mul]
  nlinarith
#align pow_mem_ball pow_mem_ball
#align nsmul_mem_ball nsmul_mem_ball

@[to_additive] -- Porting note (#10618): `simp` can prove this
theorem mul_mem_closedBall_mul_iff {c : E} : a * c ∈ closedBall (b * c) r ↔ a ∈ closedBall b r := by
  simp only [mem_closedBall, dist_eq_norm_div, mul_div_mul_right_eq_div]
#align mul_mem_closed_ball_mul_iff mul_mem_closedBall_mul_iff
#align add_mem_closed_ball_add_iff add_mem_closedBall_add_iff

@[to_additive] -- Porting note (#10618): `simp` can prove this
theorem mul_mem_ball_mul_iff {c : E} : a * c ∈ ball (b * c) r ↔ a ∈ ball b r := by
  simp only [mem_ball, dist_eq_norm_div, mul_div_mul_right_eq_div]
#align mul_mem_ball_mul_iff mul_mem_ball_mul_iff
#align add_mem_ball_add_iff add_mem_ball_add_iff

@[to_additive]
theorem smul_closedBall'' : a • closedBall b r = closedBall (a • b) r := by
  ext
  simp [mem_closedBall, Set.mem_smul_set, dist_eq_norm_div, _root_.div_eq_inv_mul, ←
    eq_inv_mul_iff_mul_eq, mul_assoc]
  -- Porting note: `ENNReal.div_eq_inv_mul` should be `protected`?
#align smul_closed_ball'' smul_closedBall''
#align vadd_closed_ball'' vadd_closedBall''

@[to_additive]
theorem smul_ball'' : a • ball b r = ball (a • b) r := by
  ext
  simp [mem_ball, Set.mem_smul_set, dist_eq_norm_div, _root_.div_eq_inv_mul,
    ← eq_inv_mul_iff_mul_eq, mul_assoc]
#align smul_ball'' smul_ball''
#align vadd_ball'' vadd_ball''

open Finset

@[to_additive]
theorem controlled_prod_of_mem_closure {s : Subgroup E} (hg : a ∈ closure (s : Set E)) {b : ℕ → ℝ}
    (b_pos : ∀ n, 0 < b n) :
    ∃ v : ℕ → E,
      Tendsto (fun n => ∏ i ∈ range (n + 1), v i) atTop (𝓝 a) ∧
        (∀ n, v n ∈ s) ∧ ‖v 0 / a‖ < b 0 ∧ ∀ n, 0 < n → ‖v n‖ < b n := by
  obtain ⟨u : ℕ → E, u_in : ∀ n, u n ∈ s, lim_u : Tendsto u atTop (𝓝 a)⟩ :=
    mem_closure_iff_seq_limit.mp hg
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ n ≥ n₀, ‖u n / a‖ < b 0 :=
    haveI : { x | ‖x / a‖ < b 0 } ∈ 𝓝 a := by
      simp_rw [← dist_eq_norm_div]
      exact Metric.ball_mem_nhds _ (b_pos _)
    Filter.tendsto_atTop'.mp lim_u _ this
  set z : ℕ → E := fun n => u (n + n₀)
  have lim_z : Tendsto z atTop (𝓝 a) := lim_u.comp (tendsto_add_atTop_nat n₀)
  have mem_𝓤 : ∀ n, { p : E × E | ‖p.1 / p.2‖ < b (n + 1) } ∈ 𝓤 E := fun n => by
    simpa [← dist_eq_norm_div] using Metric.dist_mem_uniformity (b_pos <| n + 1)
  obtain ⟨φ : ℕ → ℕ, φ_extr : StrictMono φ, hφ : ∀ n, ‖z (φ <| n + 1) / z (φ n)‖ < b (n + 1)⟩ :=
    lim_z.cauchySeq.subseq_mem mem_𝓤
  set w : ℕ → E := z ∘ φ
  have hw : Tendsto w atTop (𝓝 a) := lim_z.comp φ_extr.tendsto_atTop
  set v : ℕ → E := fun i => if i = 0 then w 0 else w i / w (i - 1)
  refine ⟨v, Tendsto.congr (Finset.eq_prod_range_div' w) hw, ?_, hn₀ _ (n₀.le_add_left _), ?_⟩
  · rintro ⟨⟩
    · change w 0 ∈ s
      apply u_in
    · apply s.div_mem <;> apply u_in
  · intro l hl
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := Nat.exists_eq_succ_of_ne_zero hl.ne'
    apply hφ
#align controlled_prod_of_mem_closure controlled_prod_of_mem_closure
#align controlled_sum_of_mem_closure controlled_sum_of_mem_closure

@[to_additive]
theorem controlled_prod_of_mem_closure_range {j : E →* F} {b : F}
    (hb : b ∈ closure (j.range : Set F)) {f : ℕ → ℝ} (b_pos : ∀ n, 0 < f n) :
    ∃ a : ℕ → E,
      Tendsto (fun n => ∏ i ∈ range (n + 1), j (a i)) atTop (𝓝 b) ∧
        ‖j (a 0) / b‖ < f 0 ∧ ∀ n, 0 < n → ‖j (a n)‖ < f n := by
  obtain ⟨v, sum_v, v_in, hv₀, hv_pos⟩ := controlled_prod_of_mem_closure hb b_pos
  choose g hg using v_in
  exact
    ⟨g, by simpa [← hg] using sum_v, by simpa [hg 0] using hv₀,
      fun n hn => by simpa [hg] using hv_pos n hn⟩
#align controlled_prod_of_mem_closure_range controlled_prod_of_mem_closure_range
#align controlled_sum_of_mem_closure_range controlled_sum_of_mem_closure_range

@[to_additive]
theorem nnnorm_multiset_prod_le (m : Multiset E) : ‖m.prod‖₊ ≤ (m.map fun x => ‖x‖₊).sum :=
  NNReal.coe_le_coe.1 <| by
    push_cast
    rw [Multiset.map_map]
    exact norm_multiset_prod_le _
#align nnnorm_multiset_prod_le nnnorm_multiset_prod_le
#align nnnorm_multiset_sum_le nnnorm_multiset_sum_le

@[to_additive]
theorem nnnorm_prod_le (s : Finset ι) (f : ι → E) : ‖∏ a ∈ s, f a‖₊ ≤ ∑ a ∈ s, ‖f a‖₊ :=
  NNReal.coe_le_coe.1 <| by
    push_cast
    exact norm_prod_le _ _
#align nnnorm_prod_le nnnorm_prod_le
#align nnnorm_sum_le nnnorm_sum_le

@[to_additive]
theorem nnnorm_prod_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ≥0} (h : ∀ b ∈ s, ‖f b‖₊ ≤ n b) :
    ‖∏ b ∈ s, f b‖₊ ≤ ∑ b ∈ s, n b :=
  (norm_prod_le_of_le s h).trans_eq NNReal.coe_sum.symm
#align nnnorm_prod_le_of_le nnnorm_prod_le_of_le
#align nnnorm_sum_le_of_le nnnorm_sum_le_of_le

namespace Real

instance norm : Norm ℝ where
  norm r := |r|

@[simp]
theorem norm_eq_abs (r : ℝ) : ‖r‖ = |r| :=
  rfl
#align real.norm_eq_abs Real.norm_eq_abs

instance normedAddCommGroup : NormedAddCommGroup ℝ :=
  ⟨fun _r _y => rfl⟩

theorem norm_of_nonneg (hr : 0 ≤ r) : ‖r‖ = r :=
  abs_of_nonneg hr
#align real.norm_of_nonneg Real.norm_of_nonneg

theorem norm_of_nonpos (hr : r ≤ 0) : ‖r‖ = -r :=
  abs_of_nonpos hr
#align real.norm_of_nonpos Real.norm_of_nonpos

theorem le_norm_self (r : ℝ) : r ≤ ‖r‖ :=
  le_abs_self r
#align real.le_norm_self Real.le_norm_self

-- Porting note (#10618): `simp` can prove this
theorem norm_natCast (n : ℕ) : ‖(n : ℝ)‖ = n :=
  abs_of_nonneg n.cast_nonneg
#align real.norm_coe_nat Real.norm_natCast

@[simp]
theorem nnnorm_natCast (n : ℕ) : ‖(n : ℝ)‖₊ = n :=
  NNReal.eq <| norm_natCast _
#align real.nnnorm_coe_nat Real.nnnorm_natCast

@[deprecated (since := "2024-04-05")] alias norm_coe_nat := norm_natCast
@[deprecated (since := "2024-04-05")] alias nnnorm_coe_nat := nnnorm_natCast

-- Porting note (#10618): `simp` can prove this
theorem norm_two : ‖(2 : ℝ)‖ = 2 :=
  abs_of_pos zero_lt_two
#align real.norm_two Real.norm_two

@[simp]
theorem nnnorm_two : ‖(2 : ℝ)‖₊ = 2 :=
  NNReal.eq <| by simp
#align real.nnnorm_two Real.nnnorm_two

theorem nnnorm_of_nonneg (hr : 0 ≤ r) : ‖r‖₊ = ⟨r, hr⟩ :=
  NNReal.eq <| norm_of_nonneg hr
#align real.nnnorm_of_nonneg Real.nnnorm_of_nonneg

@[simp]
theorem nnnorm_abs (r : ℝ) : ‖|r|‖₊ = ‖r‖₊ := by simp [nnnorm]
#align real.nnnorm_abs Real.nnnorm_abs

theorem ennnorm_eq_ofReal (hr : 0 ≤ r) : (‖r‖₊ : ℝ≥0∞) = ENNReal.ofReal r := by
  rw [← ofReal_norm_eq_coe_nnnorm, norm_of_nonneg hr]
#align real.ennnorm_eq_of_real Real.ennnorm_eq_ofReal

theorem ennnorm_eq_ofReal_abs (r : ℝ) : (‖r‖₊ : ℝ≥0∞) = ENNReal.ofReal |r| := by
  rw [← Real.nnnorm_abs r, Real.ennnorm_eq_ofReal (abs_nonneg _)]
#align real.ennnorm_eq_of_real_abs Real.ennnorm_eq_ofReal_abs

theorem toNNReal_eq_nnnorm_of_nonneg (hr : 0 ≤ r) : r.toNNReal = ‖r‖₊ := by
  rw [Real.toNNReal_of_nonneg hr]
  ext
  rw [coe_mk, coe_nnnorm r, Real.norm_eq_abs r, abs_of_nonneg hr]
  -- Porting note: this is due to the change from `Subtype.val` to `NNReal.toReal` for the coercion
#align real.to_nnreal_eq_nnnorm_of_nonneg Real.toNNReal_eq_nnnorm_of_nonneg

theorem ofReal_le_ennnorm (r : ℝ) : ENNReal.ofReal r ≤ ‖r‖₊ := by
  obtain hr | hr := le_total 0 r
  · exact (Real.ennnorm_eq_ofReal hr).ge
  · rw [ENNReal.ofReal_eq_zero.2 hr]
    exact bot_le
#align real.of_real_le_ennnorm Real.ofReal_le_ennnorm
-- Porting note: should this be renamed to `Real.ofReal_le_nnnorm`?

end Real

namespace NNReal

instance : NNNorm ℝ≥0 where
  nnnorm x := x

@[simp] lemma nnnorm_eq_self (x : ℝ≥0) : ‖x‖₊ = x := rfl

end NNReal

end SeminormedCommGroup

section NormedGroup

variable [NormedGroup E] [NormedGroup F] {a b : E}

@[to_additive (attr := simp) norm_eq_zero]
theorem norm_eq_zero'' : ‖a‖ = 0 ↔ a = 1 :=
  norm_eq_zero'''
#align norm_eq_zero'' norm_eq_zero''
#align norm_eq_zero norm_eq_zero

@[to_additive norm_ne_zero_iff]
theorem norm_ne_zero_iff' : ‖a‖ ≠ 0 ↔ a ≠ 1 :=
  norm_eq_zero''.not
#align norm_ne_zero_iff' norm_ne_zero_iff'
#align norm_ne_zero_iff norm_ne_zero_iff

@[to_additive (attr := simp) norm_pos_iff]
theorem norm_pos_iff'' : 0 < ‖a‖ ↔ a ≠ 1 :=
  norm_pos_iff'''
#align norm_pos_iff'' norm_pos_iff''
#align norm_pos_iff norm_pos_iff

@[to_additive (attr := simp) norm_le_zero_iff]
theorem norm_le_zero_iff'' : ‖a‖ ≤ 0 ↔ a = 1 :=
  norm_le_zero_iff'''
#align norm_le_zero_iff'' norm_le_zero_iff''
#align norm_le_zero_iff norm_le_zero_iff

@[to_additive]
theorem norm_div_eq_zero_iff : ‖a / b‖ = 0 ↔ a = b := by rw [norm_eq_zero'', div_eq_one]
#align norm_div_eq_zero_iff norm_div_eq_zero_iff
#align norm_sub_eq_zero_iff norm_sub_eq_zero_iff

@[to_additive]
theorem norm_div_pos_iff : 0 < ‖a / b‖ ↔ a ≠ b := by
  rw [(norm_nonneg' _).lt_iff_ne, ne_comm]
  exact norm_div_eq_zero_iff.not
#align norm_div_pos_iff norm_div_pos_iff
#align norm_sub_pos_iff norm_sub_pos_iff

@[to_additive eq_of_norm_sub_le_zero]
theorem eq_of_norm_div_le_zero (h : ‖a / b‖ ≤ 0) : a = b := by
  rwa [← div_eq_one, ← norm_le_zero_iff'']
#align eq_of_norm_div_le_zero eq_of_norm_div_le_zero
#align eq_of_norm_sub_le_zero eq_of_norm_sub_le_zero

alias ⟨eq_of_norm_div_eq_zero, _⟩ := norm_div_eq_zero_iff
#align eq_of_norm_div_eq_zero eq_of_norm_div_eq_zero

attribute [to_additive] eq_of_norm_div_eq_zero

@[to_additive (attr := simp) nnnorm_eq_zero]
theorem nnnorm_eq_zero' : ‖a‖₊ = 0 ↔ a = 1 := by
  rw [← NNReal.coe_eq_zero, coe_nnnorm', norm_eq_zero'']
#align nnnorm_eq_zero' nnnorm_eq_zero'
#align nnnorm_eq_zero nnnorm_eq_zero

@[to_additive nnnorm_ne_zero_iff]
theorem nnnorm_ne_zero_iff' : ‖a‖₊ ≠ 0 ↔ a ≠ 1 :=
  nnnorm_eq_zero'.not
#align nnnorm_ne_zero_iff' nnnorm_ne_zero_iff'
#align nnnorm_ne_zero_iff nnnorm_ne_zero_iff

@[to_additive (attr := simp) nnnorm_pos]
lemma nnnorm_pos' : 0 < ‖a‖₊ ↔ a ≠ 1 := pos_iff_ne_zero.trans nnnorm_ne_zero_iff'

@[to_additive]
theorem tendsto_norm_div_self_punctured_nhds (a : E) :
    Tendsto (fun x => ‖x / a‖) (𝓝[≠] a) (𝓝[>] 0) :=
  (tendsto_norm_div_self a).inf <|
    tendsto_principal_principal.2 fun _x hx => norm_pos_iff''.2 <| div_ne_one.2 hx
#align tendsto_norm_div_self_punctured_nhds tendsto_norm_div_self_punctured_nhds
#align tendsto_norm_sub_self_punctured_nhds tendsto_norm_sub_self_punctured_nhds

@[to_additive]
theorem tendsto_norm_nhdsWithin_one : Tendsto (norm : E → ℝ) (𝓝[≠] 1) (𝓝[>] 0) :=
  tendsto_norm_one.inf <| tendsto_principal_principal.2 fun _x => norm_pos_iff''.2
#align tendsto_norm_nhds_within_one tendsto_norm_nhdsWithin_one
#align tendsto_norm_nhds_within_zero tendsto_norm_nhdsWithin_zero

variable (E)

/-- The norm of a normed group as a group norm. -/
@[to_additive "The norm of a normed group as an additive group norm."]
def normGroupNorm : GroupNorm E :=
  { normGroupSeminorm _ with eq_one_of_map_eq_zero' := fun _ => norm_eq_zero''.1 }
#align norm_group_norm normGroupNorm
#align norm_add_group_norm normAddGroupNorm

@[simp]
theorem coe_normGroupNorm : ⇑(normGroupNorm E) = norm :=
  rfl
#align coe_norm_group_norm coe_normGroupNorm

@[to_additive comap_norm_nhdsWithin_Ioi_zero]
lemma comap_norm_nhdsWithin_Ioi_zero' : comap norm (𝓝[>] 0) = 𝓝[≠] (1 : E) := by
  simp [nhdsWithin, comap_norm_nhds_one, Set.preimage, Set.compl_def]

end NormedGroup

section NormedAddGroup

variable [NormedAddGroup E] [TopologicalSpace α] {f : α → E}

/-! Some relations with `HasCompactSupport` -/

theorem hasCompactSupport_norm_iff : (HasCompactSupport fun x => ‖f x‖) ↔ HasCompactSupport f :=
  hasCompactSupport_comp_left norm_eq_zero
#align has_compact_support_norm_iff hasCompactSupport_norm_iff

alias ⟨_, HasCompactSupport.norm⟩ := hasCompactSupport_norm_iff
#align has_compact_support.norm HasCompactSupport.norm

end NormedAddGroup

/-! ### Subgroups of normed groups -/


namespace Subgroup

section SeminormedGroup

variable [SeminormedGroup E] {s : Subgroup E}

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
@[to_additive "A subgroup of a seminormed group is also a seminormed group, with the restriction of
the norm."]
instance seminormedGroup : SeminormedGroup s :=
  SeminormedGroup.induced _ _ s.subtype
#align subgroup.seminormed_group Subgroup.seminormedGroup
#align add_subgroup.seminormed_add_group AddSubgroup.seminormedAddGroup

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[to_additive (attr := simp) "If `x` is an element of a subgroup `s` of a seminormed group `E`, its
norm in `s` is equal to its norm in `E`."]
theorem coe_norm (x : s) : ‖x‖ = ‖(x : E)‖ :=
  rfl
#align subgroup.coe_norm Subgroup.coe_norm
#align add_subgroup.coe_norm AddSubgroup.coe_norm

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`.

This is a reversed version of the `simp` lemma `Subgroup.coe_norm` for use by `norm_cast`. -/
@[to_additive (attr := norm_cast) "If `x` is an element of a subgroup `s` of a seminormed group `E`,
its norm in `s` is equal to its norm in `E`.

This is a reversed version of the `simp` lemma `AddSubgroup.coe_norm` for use by `norm_cast`."]
theorem norm_coe {s : Subgroup E} (x : s) : ‖(x : E)‖ = ‖x‖ :=
  rfl
#align subgroup.norm_coe Subgroup.norm_coe
#align add_subgroup.norm_coe AddSubgroup.norm_coe

end SeminormedGroup

@[to_additive]
instance seminormedCommGroup [SeminormedCommGroup E] {s : Subgroup E} : SeminormedCommGroup s :=
  SeminormedCommGroup.induced _ _ s.subtype
#align subgroup.seminormed_comm_group Subgroup.seminormedCommGroup
#align add_subgroup.seminormed_add_comm_group AddSubgroup.seminormedAddCommGroup

@[to_additive]
instance normedGroup [NormedGroup E] {s : Subgroup E} : NormedGroup s :=
  NormedGroup.induced _ _ s.subtype Subtype.coe_injective
#align subgroup.normed_group Subgroup.normedGroup
#align add_subgroup.normed_add_group AddSubgroup.normedAddGroup

@[to_additive]
instance normedCommGroup [NormedCommGroup E] {s : Subgroup E} : NormedCommGroup s :=
  NormedCommGroup.induced _ _ s.subtype Subtype.coe_injective
#align subgroup.normed_comm_group Subgroup.normedCommGroup
#align add_subgroup.normed_add_comm_group AddSubgroup.normedAddCommGroup

end Subgroup
