/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
import Mathlib.Analysis.Normed.Group.Seminorm
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.IsometricSMul
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

open BigOperators ENNReal Filter NNReal Uniformity Pointwise Topology

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
@[to_additive (attr := reducible) "Construct a `NormedAddGroup` from a `SeminormedAddGroup`
satisfying `∀ x, ‖x‖ = 0 → x = 0`. This avoids having to go back to the `(Pseudo)MetricSpace`
level when declaring a `NormedAddGroup` instance as a special case of a more general
`SeminormedAddGroup` instance."]
def NormedGroup.ofSeparation [SeminormedGroup E] (h : ∀ x : E, ‖x‖ = 0 → x = 1) : NormedGroup E :=
  { ‹SeminormedGroup E› with
    toMetricSpace :=
      { eq_of_dist_eq_zero := fun hxy =>
          div_eq_one.1 <| h _ <| by exact (‹SeminormedGroup E›.dist_eq _ _).symm.trans hxy } }
        -- porting note: the `rwa` no longer worked, but it was easy enough to provide the term.
        -- however, notice that if you make `x` and `y` accessible, then the following does work:
        -- `have := ‹SeminormedGroup E›.dist_eq x y; rwa [←this]`, so I'm not sure why the `rwa`
        -- was broken.

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

/-- Construct a seminormed group from a multiplication-invariant distance. -/
@[to_additive "Construct a seminormed group from a translation-invariant distance."]
def SeminormedGroup.ofMulDist [Norm E] [Group E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
    SeminormedGroup E where
  dist_eq x y := by
    rw [h₁]; apply le_antisymm
    · simpa only [div_eq_mul_inv, ← mul_right_inv y] using h₂ _ _ _
    · simpa only [div_mul_cancel', one_mul] using h₂ (x / y) 1 y

/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a seminormed group from a translation-invariant pseudodistance."]
def SeminormedGroup.ofMulDist' [Norm E] [Group E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
    SeminormedGroup E where
  dist_eq x y := by
    rw [h₁]; apply le_antisymm
    · simpa only [div_mul_cancel', one_mul] using h₂ (x / y) 1 y
    · simpa only [div_eq_mul_inv, ← mul_right_inv y] using h₂ _ _ _

/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a seminormed group from a translation-invariant pseudodistance."]
def SeminormedCommGroup.ofMulDist [Norm E] [CommGroup E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
    SeminormedCommGroup E :=
  { SeminormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }

/-- Construct a seminormed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a seminormed group from a translation-invariant pseudodistance."]
def SeminormedCommGroup.ofMulDist' [Norm E] [CommGroup E] [PseudoMetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
    SeminormedCommGroup E :=
  { SeminormedGroup.ofMulDist' h₁ h₂ with
    mul_comm := mul_comm }

/-- Construct a normed group from a multiplication-invariant distance. -/
@[to_additive "Construct a normed group from a translation-invariant distance."]
def NormedGroup.ofMulDist [Norm E] [Group E] [MetricSpace E] (h₁ : ∀ x : E, ‖x‖ = dist x 1)
    (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) : NormedGroup E :=
  { SeminormedGroup.ofMulDist h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a normed group from a translation-invariant pseudodistance."]
def NormedGroup.ofMulDist' [Norm E] [Group E] [MetricSpace E] (h₁ : ∀ x : E, ‖x‖ = dist x 1)
    (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) : NormedGroup E :=
  { SeminormedGroup.ofMulDist' h₁ h₂ with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a normed group from a translation-invariant pseudodistance."]
def NormedCommGroup.ofMulDist [Norm E] [CommGroup E] [MetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist x y ≤ dist (x * z) (y * z)) :
    NormedCommGroup E :=
  { NormedGroup.ofMulDist h₁ h₂ with
    mul_comm := mul_comm }

/-- Construct a normed group from a multiplication-invariant pseudodistance. -/
@[to_additive "Construct a normed group from a translation-invariant pseudodistance."]
def NormedCommGroup.ofMulDist' [Norm E] [CommGroup E] [MetricSpace E]
    (h₁ : ∀ x : E, ‖x‖ = dist x 1) (h₂ : ∀ x y z : E, dist (x * z) (y * z) ≤ dist x y) :
    NormedCommGroup E :=
  { NormedGroup.ofMulDist' h₁ h₂ with
    mul_comm := mul_comm }

/-- Construct a seminormed group from a seminorm, i.e., registering the pseudodistance and the
pseudometric space structure from the seminorm properties. Note that in most cases this instance
creates bad definitional equalities (e.g., it does not take into account a possibly existing
`UniformSpace` instance on `E`). -/
@[to_additive "Construct a seminormed group from a seminorm, i.e., registering the pseudodistance
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
  -- porting note: how did `mathlib3` solve this automatically?

/-- Construct a seminormed group from a seminorm, i.e., registering the pseudodistance and the
pseudometric space structure from the seminorm properties. Note that in most cases this instance
creates bad definitional equalities (e.g., it does not take into account a possibly existing
`UniformSpace` instance on `E`). -/
@[to_additive "Construct a seminormed group from a seminorm, i.e., registering the pseudodistance
and the pseudometric space structure from the seminorm properties. Note that in most cases this
instance creates bad definitional equalities (e.g., it does not take into account a possibly
existing `UniformSpace` instance on `E`)."]
def GroupSeminorm.toSeminormedCommGroup [CommGroup E] (f : GroupSeminorm E) :
    SeminormedCommGroup E :=
  { f.toSeminormedGroup with
    mul_comm := mul_comm }

/-- Construct a normed group from a norm, i.e., registering the distance and the metric space
structure from the norm properties. Note that in most cases this instance creates bad definitional
equalities (e.g., it does not take into account a possibly existing `UniformSpace` instance on
`E`). -/
@[to_additive "Construct a normed group from a norm, i.e., registering the distance and the metric
space structure from the norm properties. Note that in most cases this instance creates bad
definitional equalities (e.g., it does not take into account a possibly existing `UniformSpace`
instance on `E`)."]
def GroupNorm.toNormedGroup [Group E] (f : GroupNorm E) : NormedGroup E :=
  { f.toGroupSeminorm.toSeminormedGroup with
    eq_of_dist_eq_zero := fun h => div_eq_one.1 <| eq_one_of_map_eq_zero f h }

/-- Construct a normed group from a norm, i.e., registering the distance and the metric space
structure from the norm properties. Note that in most cases this instance creates bad definitional
equalities (e.g., it does not take into account a possibly existing `UniformSpace` instance on
`E`). -/
@[to_additive "Construct a normed group from a norm, i.e., registering the distance and the metric
space structure from the norm properties. Note that in most cases this instance creates bad
definitional equalities (e.g., it does not take into account a possibly existing `UniformSpace`
instance on `E`)."]
def GroupNorm.toNormedCommGroup [CommGroup E] (f : GroupNorm E) : NormedCommGroup E :=
  { f.toNormedGroup with
    mul_comm := mul_comm }

instance PUnit.normedAddCommGroup : NormedAddCommGroup PUnit where
  norm := Function.const _ 0
  dist_eq _ _ := rfl

@[simp]
theorem PUnit.norm_eq_zero (r : PUnit) : ‖r‖ = 0 :=
  rfl

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E}
  {a a₁ a₂ b b₁ b₂ : E} {r r₁ r₂ : ℝ}

@[to_additive]
theorem dist_eq_norm_div (a b : E) : dist a b = ‖a / b‖ :=
  SeminormedGroup.dist_eq _ _

@[to_additive]
theorem dist_eq_norm_div' (a b : E) : dist a b = ‖b / a‖ := by rw [dist_comm, dist_eq_norm_div]

alias dist_eq_norm := dist_eq_norm_sub

alias dist_eq_norm' := dist_eq_norm_sub'

@[to_additive]
instance NormedGroup.to_isometricSMul_right : IsometricSMul Eᵐᵒᵖ E :=
  ⟨fun a => Isometry.of_dist_eq fun b c => by simp [dist_eq_norm_div]⟩

@[to_additive (attr := simp)]
theorem dist_one_right (a : E) : dist a 1 = ‖a‖ := by rw [dist_eq_norm_div, div_one]

@[to_additive (attr := simp)]
theorem dist_one_left : dist (1 : E) = norm :=
  funext fun a => by rw [dist_comm, dist_one_right]

@[to_additive]
theorem Isometry.norm_map_of_map_one {f : E → F} (hi : Isometry f) (h₁ : f 1 = 1) (x : E) :
    ‖f x‖ = ‖x‖ := by rw [← dist_one_right, ← h₁, hi.dist_eq, dist_one_right]

@[to_additive (attr := simp) comap_norm_atTop]
theorem comap_norm_atTop' : comap norm atTop = cobounded E := by
  simpa only [dist_one_right] using comap_dist_right_atTop (1 : E)

@[to_additive (attr := simp) tendsto_norm_atTop_iff_cobounded]
theorem tendsto_norm_atTop_iff_cobounded' {f : α → E} {l : Filter α} :
    Tendsto (‖f ·‖) l atTop ↔ Tendsto f l (cobounded E) := by
  rw [← comap_norm_atTop', tendsto_comap_iff]; rfl

@[to_additive tendsto_norm_cobounded_atTop]
theorem tendsto_norm_cobounded_atTop' : Tendsto norm (cobounded E) atTop :=
  tendsto_norm_atTop_iff_cobounded'.2 tendsto_id

@[to_additive tendsto_norm_cocompact_atTop]
theorem tendsto_norm_cocompact_atTop' [ProperSpace E] : Tendsto norm (cocompact E) atTop :=
  cobounded_eq_cocompact (α := E) ▸ tendsto_norm_cobounded_atTop'

@[to_additive]
theorem norm_div_rev (a b : E) : ‖a / b‖ = ‖b / a‖ := by
  simpa only [dist_eq_norm_div] using dist_comm a b

@[to_additive (attr := simp) norm_neg]
theorem norm_inv' (a : E) : ‖a⁻¹‖ = ‖a‖ := by simpa using norm_div_rev 1 a

@[to_additive]
theorem dist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    dist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖ := by
  rw [dist_eq_norm_div, Set.apply_mulIndicator_symmDiff norm_inv']

@[to_additive (attr := simp)]
theorem dist_mul_self_right (a b : E) : dist b (a * b) = ‖a‖ := by
  rw [← dist_one_left, ← dist_mul_right 1 a b, one_mul]

@[to_additive (attr := simp)]
theorem dist_mul_self_left (a b : E) : dist (a * b) b = ‖a‖ := by
  rw [dist_comm, dist_mul_self_right]

@[to_additive (attr := simp)]
theorem dist_div_eq_dist_mul_left (a b c : E) : dist (a / b) c = dist a (c * b) := by
  rw [← dist_mul_right _ _ b, div_mul_cancel']

@[to_additive (attr := simp)]
theorem dist_div_eq_dist_mul_right (a b c : E) : dist a (b / c) = dist (a * c) b := by
  rw [← dist_mul_right _ _ c, div_mul_cancel']

/-- In a (semi)normed group, inversion `x ↦ x⁻¹` tends to infinity at infinity. TODO: use
`Bornology.cobounded` instead of `Filter.comap Norm.norm Filter.atTop`. -/
@[to_additive "In a (semi)normed group, negation `x ↦ -x` tends to infinity at infinity. TODO: use
`Bornology.cobounded` instead of `Filter.comap Norm.norm Filter.atTop`."]
theorem Filter.tendsto_inv_cobounded :
    Tendsto (Inv.inv : E → E) (comap norm atTop) (comap norm atTop) := by
  simpa only [norm_inv', tendsto_comap_iff, (· ∘ ·)] using tendsto_comap

/-- **Triangle inequality** for the norm. -/
@[to_additive norm_add_le "**Triangle inequality** for the norm."]
theorem norm_mul_le' (a b : E) : ‖a * b‖ ≤ ‖a‖ + ‖b‖ := by
  simpa [dist_eq_norm_div] using dist_triangle a 1 b⁻¹

@[to_additive]
theorem norm_mul_le_of_le (h₁ : ‖a₁‖ ≤ r₁) (h₂ : ‖a₂‖ ≤ r₂) : ‖a₁ * a₂‖ ≤ r₁ + r₂ :=
  (norm_mul_le' a₁ a₂).trans <| add_le_add h₁ h₂

@[to_additive norm_add₃_le]
theorem norm_mul₃_le (a b c : E) : ‖a * b * c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
  norm_mul_le_of_le (norm_mul_le' _ _) le_rfl

@[to_additive (attr := simp) norm_nonneg]
theorem norm_nonneg' (a : E) : 0 ≤ ‖a‖ := by
  rw [← dist_one_right]
  exact dist_nonneg

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: multiplicative norms are nonnegative, via
`norm_nonneg'`. -/
@[positivity Norm.norm _]
def evalMulNorm : PositivityExt where eval {_ _} _zα _pα e := do
  let .app _ a ← whnfR e | throwError "not ‖ · ‖"
  let p ← mkAppM ``norm_nonneg' #[a]
  pure (.nonnegative p)

/-- Extension for the `positivity` tactic: additive norms are nonnegative, via `norm_nonneg`. -/
@[positivity Norm.norm _]
def evalAddNorm : PositivityExt where eval {_ _} _zα _pα e := do
  let .app _ a ← whnfR e | throwError "not ‖ · ‖"
  let p ← mkAppM ``norm_nonneg #[a]
  pure (.nonnegative p)

end Mathlib.Meta.Positivity

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

@[to_additive dist_norm_norm_le]
theorem dist_norm_norm_le' (a b : E) : dist ‖a‖ ‖b‖ ≤ ‖a / b‖ :=
  abs_norm_sub_norm_le' a b

@[to_additive]
theorem norm_le_norm_add_norm_div' (u v : E) : ‖u‖ ≤ ‖v‖ + ‖u / v‖ := by
  rw [add_comm]
  refine' (norm_mul_le' _ _).trans_eq' _
  rw [div_mul_cancel']

@[to_additive]
theorem norm_le_norm_add_norm_div (u v : E) : ‖v‖ ≤ ‖u‖ + ‖u / v‖ := by
  rw [norm_div_rev]
  exact norm_le_norm_add_norm_div' v u

alias norm_le_insert' := norm_le_norm_add_norm_sub'

alias norm_le_insert := norm_le_norm_add_norm_sub

@[to_additive]
theorem norm_le_mul_norm_add (u v : E) : ‖u‖ ≤ ‖u * v‖ + ‖v‖ :=
  calc
    ‖u‖ = ‖u * v / v‖ := by rw [mul_div_cancel'']
    _ ≤ ‖u * v‖ + ‖v‖ := norm_div_le _ _

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

@[to_additive] -- porting note: `simp` can prove it
theorem mem_ball_one_iff : a ∈ ball (1 : E) r ↔ ‖a‖ < r := by rw [mem_ball, dist_one_right]

@[to_additive mem_closedBall_iff_norm]
theorem mem_closedBall_iff_norm'' : b ∈ closedBall a r ↔ ‖b / a‖ ≤ r := by
  rw [mem_closedBall, dist_eq_norm_div]

@[to_additive] -- porting note: `simp` can prove it
theorem mem_closedBall_one_iff : a ∈ closedBall (1 : E) r ↔ ‖a‖ ≤ r := by
  rw [mem_closedBall, dist_one_right]

@[to_additive mem_closedBall_iff_norm']
theorem mem_closedBall_iff_norm''' : b ∈ closedBall a r ↔ ‖a / b‖ ≤ r := by
  rw [mem_closedBall', dist_eq_norm_div]

@[to_additive norm_le_of_mem_closedBall]
theorem norm_le_of_mem_closedBall' (h : b ∈ closedBall a r) : ‖b‖ ≤ ‖a‖ + r :=
  (norm_le_norm_add_norm_div' _ _).trans <| add_le_add_left (by rwa [← dist_eq_norm_div]) _

@[to_additive norm_le_norm_add_const_of_dist_le]
theorem norm_le_norm_add_const_of_dist_le' : dist a b ≤ r → ‖a‖ ≤ ‖b‖ + r :=
  norm_le_of_mem_closedBall'

@[to_additive norm_lt_of_mem_ball]
theorem norm_lt_of_mem_ball' (h : b ∈ ball a r) : ‖b‖ < ‖a‖ + r :=
  (norm_le_norm_add_norm_div' _ _).trans_lt <| add_lt_add_left (by rwa [← dist_eq_norm_div]) _

@[to_additive]
theorem norm_div_sub_norm_div_le_norm_div (u v w : E) : ‖u / w‖ - ‖v / w‖ ≤ ‖u / v‖ := by
  simpa only [div_div_div_cancel_right'] using norm_sub_norm_le' (u / w) (v / w)

@[to_additive isBounded_iff_forall_norm_le]
theorem isBounded_iff_forall_norm_le' : Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C := by
  simpa only [Set.subset_def, mem_closedBall_one_iff] using isBounded_iff_subset_closedBall (1 : E)

alias ⟨Bornology.IsBounded.exists_norm_le', _⟩ := isBounded_iff_forall_norm_le'

alias ⟨Bornology.IsBounded.exists_norm_le, _⟩ := isBounded_iff_forall_norm_le

attribute [to_additive existing exists_norm_le] Bornology.IsBounded.exists_norm_le'

@[to_additive exists_pos_norm_le]
theorem Bornology.IsBounded.exists_pos_norm_le' (hs : IsBounded s) : ∃ R > 0, ∀ x ∈ s, ‖x‖ ≤ R :=
  let ⟨R₀, hR₀⟩ := hs.exists_norm_le'
  ⟨max R₀ 1, by positivity, fun x hx => (hR₀ x hx).trans <| le_max_left _ _⟩

@[to_additive (attr := simp 1001) mem_sphere_iff_norm]
-- porting note: increase priority so the left-hand side doesn't reduce
theorem mem_sphere_iff_norm' : b ∈ sphere a r ↔ ‖b / a‖ = r := by simp [dist_eq_norm_div]

@[to_additive] -- `simp` can prove this
theorem mem_sphere_one_iff_norm : a ∈ sphere (1 : E) r ↔ ‖a‖ = r := by simp [dist_eq_norm_div]

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
@[to_additive "The norm of a seminormed group as an additive group seminorm."]
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
theorem NormedCommGroup.cauchySeq_iff [Nonempty α] [SemilatticeSup α] {u : α → E} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → ‖u m / u n‖ < ε := by
  simp [Metric.cauchySeq_iff, dist_eq_norm_div]

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

/-- A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant `C` such that
for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. The analogous condition for a linear map of
(semi)normed spaces is in `Mathlib/Analysis/NormedSpace/OperatorNorm.lean`. -/
@[to_additive "A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant
`C` such that for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. The analogous condition for a linear map of
(semi)normed spaces is in `Mathlib/Analysis/NormedSpace/OperatorNorm.lean`."]
theorem MonoidHomClass.lipschitz_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ)
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : LipschitzWith (Real.toNNReal C) f :=
  LipschitzWith.of_dist_le' fun x y => by simpa only [dist_eq_norm_div, map_div] using h (x / y)

@[to_additive]
theorem lipschitzOnWith_iff_norm_div_le {f : E → F} {C : ℝ≥0} :
    LipschitzOnWith C f s ↔ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ‖f x / f y‖ ≤ C * ‖x / y‖ := by
  simp only [lipschitzOnWith_iff_dist_le_mul, dist_eq_norm_div]

alias ⟨LipschitzOnWith.norm_div_le, _⟩ := lipschitzOnWith_iff_norm_div_le

attribute [to_additive] LipschitzOnWith.norm_div_le

@[to_additive]
theorem LipschitzOnWith.norm_div_le_of_le {f : E → F} {C : ℝ≥0} (h : LipschitzOnWith C f s)
    (ha : a ∈ s) (hb : b ∈ s) (hr : ‖a / b‖ ≤ r) : ‖f a / f b‖ ≤ C * r :=
  (h.norm_div_le ha hb).trans <| by gcongr

@[to_additive]
theorem lipschitzWith_iff_norm_div_le {f : E → F} {C : ℝ≥0} :
    LipschitzWith C f ↔ ∀ x y, ‖f x / f y‖ ≤ C * ‖x / y‖ := by
  simp only [lipschitzWith_iff_dist_le_mul, dist_eq_norm_div]

alias ⟨LipschitzWith.norm_div_le, _⟩ := lipschitzWith_iff_norm_div_le

attribute [to_additive] LipschitzWith.norm_div_le

@[to_additive]
theorem LipschitzWith.norm_div_le_of_le {f : E → F} {C : ℝ≥0} (h : LipschitzWith C f)
    (hr : ‖a / b‖ ≤ r) : ‖f a / f b‖ ≤ C * r :=
  (h.norm_div_le _ _).trans <| by gcongr

/-- A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C` such that
for all `x`, one has `‖f x‖ ≤ C * ‖x‖`. -/
@[to_additive "A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C`
such that for all `x`, one has `‖f x‖ ≤ C * ‖x‖`"]
theorem MonoidHomClass.continuous_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ)
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : Continuous f :=
  (MonoidHomClass.lipschitz_of_bound f C h).continuous

@[to_additive]
theorem MonoidHomClass.uniformContinuous_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ)
    (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : UniformContinuous f :=
  (MonoidHomClass.lipschitz_of_bound f C h).uniformContinuous

@[to_additive IsCompact.exists_bound_of_continuousOn]
theorem IsCompact.exists_bound_of_continuousOn' [TopologicalSpace α] {s : Set α} (hs : IsCompact s)
    {f : α → E} (hf : ContinuousOn f s) : ∃ C, ∀ x ∈ s, ‖f x‖ ≤ C :=
  (isBounded_iff_forall_norm_le'.1 (hs.image_of_continuousOn hf).isBounded).imp fun _C hC _x hx =>
    hC _ <| Set.mem_image_of_mem _ hx

@[to_additive]
theorem HasCompactMulSupport.exists_bound_of_continuous [TopologicalSpace α]
    {f : α → E} (hf : HasCompactMulSupport f) (h'f : Continuous f) : ∃ C, ∀ x, ‖f x‖ ≤ C := by
  simpa using (hf.isCompact_range h'f).isBounded.exists_norm_le'

@[to_additive]
theorem MonoidHomClass.isometry_iff_norm [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    Isometry f ↔ ∀ x, ‖f x‖ = ‖x‖ := by
  simp only [isometry_iff_dist_eq, dist_eq_norm_div, ← map_div]
  refine' ⟨fun h x => _, fun h x y => h _⟩
  simpa using h x 1

alias ⟨_, MonoidHomClass.isometry_of_norm⟩ := MonoidHomClass.isometry_iff_norm

attribute [to_additive] MonoidHomClass.isometry_of_norm

section NNNorm

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedGroup.toNNNorm : NNNorm E :=
  ⟨fun a => ⟨‖a‖, norm_nonneg' a⟩⟩

@[to_additive (attr := simp, norm_cast) coe_nnnorm]
theorem coe_nnnorm' (a : E) : (‖a‖₊ : ℝ) = ‖a‖ :=
  rfl

@[to_additive (attr := simp) coe_comp_nnnorm]
theorem coe_comp_nnnorm' : (toReal : ℝ≥0 → ℝ) ∘ (nnnorm : E → ℝ≥0) = norm :=
  rfl

@[to_additive norm_toNNReal]
theorem norm_toNNReal' : ‖a‖.toNNReal = ‖a‖₊ :=
  @Real.toNNReal_coe ‖a‖₊

@[to_additive]
theorem nndist_eq_nnnorm_div (a b : E) : nndist a b = ‖a / b‖₊ :=
  NNReal.eq <| dist_eq_norm_div _ _

alias nndist_eq_nnnorm := nndist_eq_nnnorm_sub

@[to_additive (attr := simp) nnnorm_zero]
theorem nnnorm_one' : ‖(1 : E)‖₊ = 0 :=
  NNReal.eq norm_one'

@[to_additive]
theorem ne_one_of_nnnorm_ne_zero {a : E} : ‖a‖₊ ≠ 0 → a ≠ 1 :=
  mt <| by
    rintro rfl
    exact nnnorm_one'

@[to_additive nnnorm_add_le]
theorem nnnorm_mul_le' (a b : E) : ‖a * b‖₊ ≤ ‖a‖₊ + ‖b‖₊ :=
  NNReal.coe_le_coe.1 <| norm_mul_le' a b

@[to_additive (attr := simp) nnnorm_neg]
theorem nnnorm_inv' (a : E) : ‖a⁻¹‖₊ = ‖a‖₊ :=
  NNReal.eq <| norm_inv' a

@[to_additive]
theorem nndist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    nndist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊ :=
  NNReal.eq <| dist_mulIndicator s t f x

@[to_additive]
theorem nnnorm_div_le (a b : E) : ‖a / b‖₊ ≤ ‖a‖₊ + ‖b‖₊ :=
  NNReal.coe_le_coe.1 <| norm_div_le _ _

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

@[to_additive ofReal_norm_eq_coe_nnnorm]
theorem ofReal_norm_eq_coe_nnnorm' (a : E) : ENNReal.ofReal ‖a‖ = ‖a‖₊ :=
  ENNReal.ofReal_eq_coe_nnreal _

@[to_additive]
theorem edist_eq_coe_nnnorm_div (a b : E) : edist a b = ‖a / b‖₊ := by
  rw [edist_dist, dist_eq_norm_div, ofReal_norm_eq_coe_nnnorm']

@[to_additive edist_eq_coe_nnnorm]
theorem edist_eq_coe_nnnorm' (x : E) : edist x 1 = (‖x‖₊ : ℝ≥0∞) := by
  rw [edist_eq_coe_nnnorm_div, div_one]

@[to_additive]
theorem edist_mulIndicator (s t : Set α) (f : α → E) (x : α) :
    edist (s.mulIndicator f x) (t.mulIndicator f x) = ‖(s ∆ t).mulIndicator f x‖₊ := by
  rw [edist_nndist, nndist_mulIndicator]

@[to_additive]
theorem mem_emetric_ball_one_iff {r : ℝ≥0∞} : a ∈ EMetric.ball (1 : E) r ↔ ↑‖a‖₊ < r := by
  rw [EMetric.mem_ball, edist_eq_coe_nnnorm']

@[to_additive]
theorem MonoidHomClass.lipschitz_of_bound_nnnorm [MonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ≥0)
    (h : ∀ x, ‖f x‖₊ ≤ C * ‖x‖₊) : LipschitzWith C f :=
  @Real.toNNReal_coe C ▸ MonoidHomClass.lipschitz_of_bound f C h

@[to_additive]
theorem MonoidHomClass.antilipschitz_of_bound [MonoidHomClass 𝓕 E F] (f : 𝓕) {K : ℝ≥0}
    (h : ∀ x, ‖x‖ ≤ K * ‖f x‖) : AntilipschitzWith K f :=
  AntilipschitzWith.of_le_mul_dist fun x y => by
    simpa only [dist_eq_norm_div, map_div] using h (x / y)

@[to_additive LipschitzWith.norm_le_mul]
theorem LipschitzWith.norm_le_mul' {f : E → F} {K : ℝ≥0} (h : LipschitzWith K f) (hf : f 1 = 1)
    (x) : ‖f x‖ ≤ K * ‖x‖ := by simpa only [dist_one_right, hf] using h.dist_le_mul x 1

@[to_additive LipschitzWith.nnorm_le_mul]
theorem LipschitzWith.nnorm_le_mul' {f : E → F} {K : ℝ≥0} (h : LipschitzWith K f) (hf : f 1 = 1)
    (x) : ‖f x‖₊ ≤ K * ‖x‖₊ :=
  h.norm_le_mul' hf x

@[to_additive AntilipschitzWith.le_mul_norm]
theorem AntilipschitzWith.le_mul_norm' {f : E → F} {K : ℝ≥0} (h : AntilipschitzWith K f)
    (hf : f 1 = 1) (x) : ‖x‖ ≤ K * ‖f x‖ := by
  simpa only [dist_one_right, hf] using h.le_mul_dist x 1

@[to_additive AntilipschitzWith.le_mul_nnnorm]
theorem AntilipschitzWith.le_mul_nnnorm' {f : E → F} {K : ℝ≥0} (h : AntilipschitzWith K f)
    (hf : f 1 = 1) (x) : ‖x‖₊ ≤ K * ‖f x‖₊ :=
  h.le_mul_norm' hf x

@[to_additive]
theorem OneHomClass.bound_of_antilipschitz [OneHomClass 𝓕 E F] (f : 𝓕) {K : ℝ≥0}
    (h : AntilipschitzWith K f) (x) : ‖x‖ ≤ K * ‖f x‖ :=
  h.le_mul_nnnorm' (map_one f) x

end NNNorm

@[to_additive]
theorem tendsto_iff_norm_div_tendsto_zero {f : α → E} {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ‖f e / b‖) a (𝓝 0) := by
  simp only [← dist_eq_norm_div, ← tendsto_iff_dist_tendsto_zero]

@[to_additive]
theorem tendsto_one_iff_norm_tendsto_zero {f : α → E} {a : Filter α} :
    Tendsto f a (𝓝 1) ↔ Tendsto (‖f ·‖) a (𝓝 0) :=
  tendsto_iff_norm_div_tendsto_zero.trans <| by simp only [div_one]

@[to_additive]
theorem comap_norm_nhds_one : comap norm (𝓝 0) = 𝓝 (1 : E) := by
  simpa only [dist_one_right] using nhds_comap_dist (1 : E)

/-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a real
function `a` which tends to `0`, then `f` tends to `1`. In this pair of lemmas (`squeeze_one_norm'`
and `squeeze_one_norm`), following a convention of similar lemmas in `Topology.MetricSpace.Basic`
and `Topology.Algebra.Order`, the `'` version is phrased using "eventually" and the non-`'` version
is phrased absolutely. -/
@[to_additive "Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a
real function `a` which tends to `0`, then `f` tends to `1`. In this pair of lemmas
(`squeeze_zero_norm'` and `squeeze_zero_norm`), following a convention of similar lemmas in
`Topology.MetricSpace.PseudoMetric` and `Topology.Algebra.Order`, the `'` version is phrased using
\"eventually\" and the non-`'` version is phrased absolutely."]
theorem squeeze_one_norm' {f : α → E} {a : α → ℝ} {t₀ : Filter α} (h : ∀ᶠ n in t₀, ‖f n‖ ≤ a n)
    (h' : Tendsto a t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 1) :=
  tendsto_one_iff_norm_tendsto_zero.2 <|
    squeeze_zero' (eventually_of_forall fun _n => norm_nonneg' _) h h'

/-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real function `a` which
tends to `0`, then `f` tends to `1`. -/
@[to_additive "Special case of the sandwich theorem: if the norm of `f` is bounded by a real
function `a` which tends to `0`, then `f` tends to `0`."]
theorem squeeze_one_norm {f : α → E} {a : α → ℝ} {t₀ : Filter α} (h : ∀ n, ‖f n‖ ≤ a n) :
    Tendsto a t₀ (𝓝 0) → Tendsto f t₀ (𝓝 1) :=
  squeeze_one_norm' <| eventually_of_forall h

@[to_additive]
theorem tendsto_norm_div_self (x : E) : Tendsto (fun a => ‖a / x‖) (𝓝 x) (𝓝 0) := by
  simpa [dist_eq_norm_div] using
    tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (x : E)) (𝓝 x) _)

@[to_additive tendsto_norm]
theorem tendsto_norm' {x : E} : Tendsto (fun a => ‖a‖) (𝓝 x) (𝓝 ‖x‖) := by
  simpa using tendsto_id.dist (tendsto_const_nhds : Tendsto (fun _a => (1 : E)) _ _)

@[to_additive]
theorem tendsto_norm_one : Tendsto (fun a : E => ‖a‖) (𝓝 1) (𝓝 0) := by
  simpa using tendsto_norm_div_self (1 : E)

@[to_additive (attr := continuity) continuous_norm]
theorem continuous_norm' : Continuous fun a : E => ‖a‖ := by
  simpa using continuous_id.dist (continuous_const : Continuous fun _a => (1 : E))

@[to_additive (attr := continuity) continuous_nnnorm]
theorem continuous_nnnorm' : Continuous fun a : E => ‖a‖₊ :=
  continuous_norm'.subtype_mk _

@[to_additive lipschitzWith_one_norm]
theorem lipschitzWith_one_norm' : LipschitzWith 1 (norm : E → ℝ) := by
  simpa only [dist_one_left] using LipschitzWith.dist_right (1 : E)

@[to_additive lipschitzWith_one_nnnorm]
theorem lipschitzWith_one_nnnorm' : LipschitzWith 1 (NNNorm.nnnorm : E → ℝ≥0) :=
  lipschitzWith_one_norm'

@[to_additive uniformContinuous_norm]
theorem uniformContinuous_norm' : UniformContinuous (norm : E → ℝ) :=
  lipschitzWith_one_norm'.uniformContinuous

@[to_additive uniformContinuous_nnnorm]
theorem uniformContinuous_nnnorm' : UniformContinuous fun a : E => ‖a‖₊ :=
  uniformContinuous_norm'.subtype_mk _

@[to_additive]
theorem mem_closure_one_iff_norm {x : E} : x ∈ closure ({1} : Set E) ↔ ‖x‖ = 0 := by
  rw [← closedBall_zero', mem_closedBall_one_iff, (norm_nonneg' x).le_iff_eq]

@[to_additive]
theorem closure_one_eq : closure ({1} : Set E) = { x | ‖x‖ = 0 } :=
  Set.ext fun _x => mem_closure_one_iff_norm

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to one
and a bounded function tends to one. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `‖op x y‖ ≤ A * ‖x‖ * ‖y‖` for some constant A instead of
multiplication so that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
@[to_additive "A helper lemma used to prove that the (scalar or usual) product of a function that
tends to zero and a bounded function tends to zero. This lemma is formulated for any binary
operation `op : E → F → G` with an estimate `‖op x y‖ ≤ A * ‖x‖ * ‖y‖` for some constant A instead
of multiplication so that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`."]
theorem Filter.Tendsto.op_one_isBoundedUnder_le' {f : α → E} {g : α → F} {l : Filter α}
    (hf : Tendsto f l (𝓝 1)) (hg : IsBoundedUnder (· ≤ ·) l (norm ∘ g)) (op : E → F → G)
    (h_op : ∃ A, ∀ x y, ‖op x y‖ ≤ A * ‖x‖ * ‖y‖) : Tendsto (fun x => op (f x) (g x)) l (𝓝 1) := by
  cases' h_op with A h_op
  rcases hg with ⟨C, hC⟩; rw [eventually_map] at hC
  rw [NormedCommGroup.tendsto_nhds_one] at hf ⊢
  intro ε ε₀
  rcases exists_pos_mul_lt ε₀ (A * C) with ⟨δ, δ₀, hδ⟩
  filter_upwards [hf δ δ₀, hC] with i hf hg
  refine' (h_op _ _).trans_lt _
  cases' le_total A 0 with hA hA
  · exact (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hA <| norm_nonneg' _) <|
      norm_nonneg' _).trans_lt ε₀
  calc
    A * ‖f i‖ * ‖g i‖ ≤ A * δ * C := by gcongr; exact hg
    _ = A * C * δ := (mul_right_comm _ _ _)
    _ < ε := hδ

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to one
and a bounded function tends to one. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `‖op x y‖ ≤ ‖x‖ * ‖y‖` instead of multiplication so that it
can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
@[to_additive "A helper lemma used to prove that the (scalar or usual) product of a function that
tends to zero and a bounded function tends to zero. This lemma is formulated for any binary
operation `op : E → F → G` with an estimate `‖op x y‖ ≤ ‖x‖ * ‖y‖` instead of multiplication so
that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`."]
theorem Filter.Tendsto.op_one_isBoundedUnder_le {f : α → E} {g : α → F} {l : Filter α}
    (hf : Tendsto f l (𝓝 1)) (hg : IsBoundedUnder (· ≤ ·) l (norm ∘ g)) (op : E → F → G)
    (h_op : ∀ x y, ‖op x y‖ ≤ ‖x‖ * ‖y‖) : Tendsto (fun x => op (f x) (g x)) l (𝓝 1) :=
  hf.op_one_isBoundedUnder_le' hg op ⟨1, fun x y => (one_mul ‖x‖).symm ▸ h_op x y⟩

section

variable {l : Filter α} {f : α → E}

@[to_additive Filter.Tendsto.norm]
theorem Filter.Tendsto.norm' (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ‖f x‖) l (𝓝 ‖a‖) :=
  tendsto_norm'.comp h

@[to_additive Filter.Tendsto.nnnorm]
theorem Filter.Tendsto.nnnorm' (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ‖f x‖₊) l (𝓝 ‖a‖₊) :=
  Tendsto.comp continuous_nnnorm'.continuousAt h

end

section

variable [TopologicalSpace α] {f : α → E}

@[to_additive Continuous.norm]
theorem Continuous.norm' : Continuous f → Continuous fun x => ‖f x‖ :=
  continuous_norm'.comp

@[to_additive Continuous.nnnorm]
theorem Continuous.nnnorm' : Continuous f → Continuous fun x => ‖f x‖₊ :=
  continuous_nnnorm'.comp

@[to_additive ContinuousAt.norm]
theorem ContinuousAt.norm' {a : α} (h : ContinuousAt f a) : ContinuousAt (fun x => ‖f x‖) a :=
  Tendsto.norm' h

@[to_additive ContinuousAt.nnnorm]
theorem ContinuousAt.nnnorm' {a : α} (h : ContinuousAt f a) : ContinuousAt (fun x => ‖f x‖₊) a :=
  Tendsto.nnnorm' h

@[to_additive ContinuousWithinAt.norm]
theorem ContinuousWithinAt.norm' {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => ‖f x‖) s a :=
  Tendsto.norm' h

@[to_additive ContinuousWithinAt.nnnorm]
theorem ContinuousWithinAt.nnnorm' {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => ‖f x‖₊) s a :=
  Tendsto.nnnorm' h

@[to_additive ContinuousOn.norm]
theorem ContinuousOn.norm' {s : Set α} (h : ContinuousOn f s) : ContinuousOn (fun x => ‖f x‖) s :=
  fun x hx => (h x hx).norm'

@[to_additive ContinuousOn.nnnorm]
theorem ContinuousOn.nnnorm' {s : Set α} (h : ContinuousOn f s) :
    ContinuousOn (fun x => ‖f x‖₊) s := fun x hx => (h x hx).nnnorm'

end

/-- If `‖y‖ → ∞`, then we can assume `y ≠ x` for any fixed `x`. -/
@[to_additive eventually_ne_of_tendsto_norm_atTop "If `‖y‖→∞`, then we can assume `y≠x` for any
fixed `x`"]
theorem eventually_ne_of_tendsto_norm_atTop' {l : Filter α} {f : α → E}
    (h : Tendsto (fun y => ‖f y‖) l atTop) (x : E) : ∀ᶠ y in l, f y ≠ x :=
  (h.eventually_ne_atTop _).mono fun _x => ne_of_apply_ne norm

@[to_additive]
theorem SeminormedCommGroup.mem_closure_iff : a ∈ closure s ↔ ∀ ε, 0 < ε → ∃ b ∈ s, ‖a / b‖ < ε :=
  by simp [Metric.mem_closure_iff, dist_eq_norm_div]

@[to_additive norm_le_zero_iff']
theorem norm_le_zero_iff''' [T0Space E] {a : E} : ‖a‖ ≤ 0 ↔ a = 1 := by
  letI : NormedGroup E :=
    { ‹SeminormedGroup E› with toMetricSpace := MetricSpace.ofT0PseudoMetricSpace E }
  rw [← dist_one_right, dist_le_zero]

@[to_additive norm_eq_zero']
theorem norm_eq_zero''' [T0Space E] {a : E} : ‖a‖ = 0 ↔ a = 1 :=
  (norm_nonneg' a).le_iff_eq.symm.trans norm_le_zero_iff'''

@[to_additive norm_pos_iff']
theorem norm_pos_iff''' [T0Space E] {a : E} : 0 < ‖a‖ ↔ a ≠ 1 := by
  rw [← not_le, norm_le_zero_iff''']

@[to_additive]
theorem SeminormedGroup.tendstoUniformlyOn_one {f : ι → κ → G} {s : Set κ} {l : Filter ι} :
    TendstoUniformlyOn f 1 l s ↔ ∀ ε > 0, ∀ᶠ i in l, ∀ x ∈ s, ‖f i x‖ < ε := by
  simp_rw [tendstoUniformlyOn_iff, Pi.one_apply, dist_one_left]

@[to_additive]
theorem SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one {f : ι → κ → G}
    {l : Filter ι} {l' : Filter κ} :
    UniformCauchySeqOnFilter f l l' ↔
      TendstoUniformlyOnFilter (fun n : ι × ι => fun z => f n.fst z / f n.snd z) 1 (l ×ˢ l) l' := by
  refine' ⟨fun hf u hu => _, fun hf u hu => _⟩
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine'
      (hf { p : G × G | dist p.fst p.snd < ε } <| dist_mem_uniformity hε).mono fun x hx =>
        H 1 (f x.fst.fst x.snd / f x.fst.snd x.snd) _
    simpa [dist_eq_norm_div, norm_div_rev] using hx
  · obtain ⟨ε, hε, H⟩ := uniformity_basis_dist.mem_uniformity_iff.mp hu
    refine'
      (hf { p : G × G | dist p.fst p.snd < ε } <| dist_mem_uniformity hε).mono fun x hx =>
        H (f x.fst.fst x.snd) (f x.fst.snd x.snd) _
    simpa [dist_eq_norm_div, norm_div_rev] using hx

@[to_additive]
theorem SeminormedGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_one {f : ι → κ → G} {s : Set κ}
    {l : Filter ι} :
    UniformCauchySeqOn f l s ↔
      TendstoUniformlyOn (fun n : ι × ι => fun z => f n.fst z / f n.snd z) 1 (l ×ˢ l) s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter,
    uniformCauchySeqOn_iff_uniformCauchySeqOnFilter,
    SeminormedGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_one]

end SeminormedGroup

section Induced

variable (E F)

-- See note [reducible non-instances]
/-- A group homomorphism from a `Group` to a `SeminormedGroup` induces a `SeminormedGroup`
structure on the domain. -/
@[to_additive (attr := reducible) "A group homomorphism from an `AddGroup` to a
`SeminormedAddGroup` induces a `SeminormedAddGroup` structure on the domain."]
def SeminormedGroup.induced [Group E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedGroup E :=
  { PseudoMetricSpace.induced f toPseudoMetricSpace with
    -- porting note: needed to add the instance explicitly, and `‹PseudoMetricSpace F›` failed
    norm := fun x => ‖f x‖
    dist_eq := fun x y => by simp only [map_div, ← dist_eq_norm_div]; rfl }

-- See note [reducible non-instances]
/-- A group homomorphism from a `CommGroup` to a `SeminormedGroup` induces a
`SeminormedCommGroup` structure on the domain. -/
@[to_additive (attr := reducible) "A group homomorphism from an `AddCommGroup` to a
`SeminormedAddGroup` induces a `SeminormedAddCommGroup` structure on the domain."]
def SeminormedCommGroup.induced [CommGroup E] [SeminormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) :
    SeminormedCommGroup E :=
  { SeminormedGroup.induced E F f with
    mul_comm := mul_comm }

-- See note [reducible non-instances].
/-- An injective group homomorphism from a `Group` to a `NormedGroup` induces a `NormedGroup`
structure on the domain. -/
@[to_additive (attr := reducible) "An injective group homomorphism from an `AddGroup` to a
`NormedAddGroup` induces a `NormedAddGroup` structure on the domain."]
def NormedGroup.induced [Group E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕) (h : Injective f) :
    NormedGroup E :=
  { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with }

-- See note [reducible non-instances].
/-- An injective group homomorphism from a `CommGroup` to a `NormedGroup` induces a
`NormedCommGroup` structure on the domain. -/
@[to_additive (attr := reducible) "An injective group homomorphism from a `CommGroup` to a
`NormedCommGroup` induces a `NormedCommGroup` structure on the domain."]
def NormedCommGroup.induced [CommGroup E] [NormedGroup F] [MonoidHomClass 𝓕 E F] (f : 𝓕)
    (h : Injective f) : NormedCommGroup E :=
  { SeminormedGroup.induced E F f, MetricSpace.induced f h _ with
    mul_comm := mul_comm }

end Induced

section SeminormedCommGroup

variable [SeminormedCommGroup E] [SeminormedCommGroup F] {a a₁ a₂ b b₁ b₂ : E} {r r₁ r₂ : ℝ}

@[to_additive]
instance NormedGroup.to_isometricSMul_left : IsometricSMul E E :=
  ⟨fun a => Isometry.of_dist_eq fun b c => by simp [dist_eq_norm_div]⟩

@[to_additive]
theorem dist_inv (x y : E) : dist x⁻¹ y = dist x y⁻¹ := by
  simp_rw [dist_eq_norm_div, ← norm_inv' (x⁻¹ / y), inv_div, div_inv_eq_mul, mul_comm]

@[to_additive (attr := simp)]
theorem dist_self_mul_right (a b : E) : dist a (a * b) = ‖b‖ := by
  rw [← dist_one_left, ← dist_mul_left a 1 b, mul_one]

@[to_additive (attr := simp)]
theorem dist_self_mul_left (a b : E) : dist (a * b) a = ‖b‖ := by
  rw [dist_comm, dist_self_mul_right]

@[to_additive (attr := simp 1001)]
-- porting note: increase priority because `simp` can prove this
theorem dist_self_div_right (a b : E) : dist a (a / b) = ‖b‖ := by
  rw [div_eq_mul_inv, dist_self_mul_right, norm_inv']

@[to_additive (attr := simp 1001)]
-- porting note: increase priority because `simp` can prove this
theorem dist_self_div_left (a b : E) : dist (a / b) a = ‖b‖ := by
  rw [dist_comm, dist_self_div_right]

@[to_additive]
theorem dist_mul_mul_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ * a₂) (b₁ * b₂) ≤ dist a₁ b₁ + dist a₂ b₂ := by
  simpa only [dist_mul_left, dist_mul_right] using dist_triangle (a₁ * a₂) (b₁ * a₂) (b₁ * b₂)

@[to_additive]
theorem dist_mul_mul_le_of_le (h₁ : dist a₁ b₁ ≤ r₁) (h₂ : dist a₂ b₂ ≤ r₂) :
    dist (a₁ * a₂) (b₁ * b₂) ≤ r₁ + r₂ :=
  (dist_mul_mul_le a₁ a₂ b₁ b₂).trans <| add_le_add h₁ h₂

@[to_additive]
theorem dist_div_div_le (a₁ a₂ b₁ b₂ : E) : dist (a₁ / a₂) (b₁ / b₂) ≤ dist a₁ b₁ + dist a₂ b₂ := by
  simpa only [div_eq_mul_inv, dist_inv_inv] using dist_mul_mul_le a₁ a₂⁻¹ b₁ b₂⁻¹

@[to_additive]
theorem dist_div_div_le_of_le (h₁ : dist a₁ b₁ ≤ r₁) (h₂ : dist a₂ b₂ ≤ r₂) :
    dist (a₁ / a₂) (b₁ / b₂) ≤ r₁ + r₂ :=
  (dist_div_div_le a₁ a₂ b₁ b₂).trans <| add_le_add h₁ h₂

@[to_additive]
theorem abs_dist_sub_le_dist_mul_mul (a₁ a₂ b₁ b₂ : E) :
    |dist a₁ b₁ - dist a₂ b₂| ≤ dist (a₁ * a₂) (b₁ * b₂) := by
  simpa only [dist_mul_left, dist_mul_right, dist_comm b₂] using
    abs_dist_sub_le (a₁ * a₂) (b₁ * b₂) (b₁ * a₂)

theorem norm_multiset_sum_le {E} [SeminormedAddCommGroup E] (m : Multiset E) :
    ‖m.sum‖ ≤ (m.map fun x => ‖x‖).sum :=
  m.le_sum_of_subadditive norm norm_zero norm_add_le

@[to_additive existing]
theorem norm_multiset_prod_le (m : Multiset E) : ‖m.prod‖ ≤ (m.map fun x => ‖x‖).sum := by
  rw [← Multiplicative.ofAdd_le, ofAdd_multiset_prod, Multiset.map_map]
  refine' Multiset.le_prod_of_submultiplicative (Multiplicative.ofAdd ∘ norm) _ (fun x y => _) _
  · simp only [comp_apply, norm_one', ofAdd_zero]
  · exact norm_mul_le' x y

-- porting note: had to add `ι` here because otherwise the universe order gets switched compared to
-- `norm_prod_le` below
theorem norm_sum_le {ι E} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E) :
    ‖∑ i in s, f i‖ ≤ ∑ i in s, ‖f i‖ :=
  s.le_sum_of_subadditive norm norm_zero norm_add_le f

@[to_additive existing]
theorem norm_prod_le (s : Finset ι) (f : ι → E) : ‖∏ i in s, f i‖ ≤ ∑ i in s, ‖f i‖ := by
  rw [← Multiplicative.ofAdd_le, ofAdd_sum]
  refine' Finset.le_prod_of_submultiplicative (Multiplicative.ofAdd ∘ norm) _ (fun x y => _) _ _
  · simp only [comp_apply, norm_one', ofAdd_zero]
  · exact norm_mul_le' x y

@[to_additive]
theorem norm_prod_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ} (h : ∀ b ∈ s, ‖f b‖ ≤ n b) :
    ‖∏ b in s, f b‖ ≤ ∑ b in s, n b :=
  (norm_prod_le s f).trans <| Finset.sum_le_sum h

@[to_additive]
theorem dist_prod_prod_le_of_le (s : Finset ι) {f a : ι → E} {d : ι → ℝ}
    (h : ∀ b ∈ s, dist (f b) (a b) ≤ d b) :
    dist (∏ b in s, f b) (∏ b in s, a b) ≤ ∑ b in s, d b := by
  simp only [dist_eq_norm_div, ← Finset.prod_div_distrib] at *
  exact norm_prod_le_of_le s h

@[to_additive]
theorem dist_prod_prod_le (s : Finset ι) (f a : ι → E) :
    dist (∏ b in s, f b) (∏ b in s, a b) ≤ ∑ b in s, dist (f b) (a b) :=
  dist_prod_prod_le_of_le s fun _ _ => le_rfl

@[to_additive]
theorem mul_mem_ball_iff_norm : a * b ∈ ball a r ↔ ‖b‖ < r := by
  rw [mem_ball_iff_norm'', mul_div_cancel''']

@[to_additive]
theorem mul_mem_closedBall_iff_norm : a * b ∈ closedBall a r ↔ ‖b‖ ≤ r := by
  rw [mem_closedBall_iff_norm'', mul_div_cancel''']

@[to_additive (attr := simp 1001)]
-- porting note: increase priority so that the left-hand side doesn't simplify
theorem preimage_mul_ball (a b : E) (r : ℝ) : (· * ·) b ⁻¹' ball a r = ball (a / b) r := by
  ext c
  simp only [dist_eq_norm_div, Set.mem_preimage, mem_ball, div_div_eq_mul_div, mul_comm]

@[to_additive (attr := simp 1001)]
-- porting note: increase priority so that the left-hand side doesn't simplify
theorem preimage_mul_closedBall (a b : E) (r : ℝ) :
    (· * ·) b ⁻¹' closedBall a r = closedBall (a / b) r := by
  ext c
  simp only [dist_eq_norm_div, Set.mem_preimage, mem_closedBall, div_div_eq_mul_div, mul_comm]

@[to_additive (attr := simp)]
theorem preimage_mul_sphere (a b : E) (r : ℝ) : (· * ·) b ⁻¹' sphere a r = sphere (a / b) r := by
  ext c
  simp only [Set.mem_preimage, mem_sphere_iff_norm', div_div_eq_mul_div, mul_comm]

@[to_additive norm_nsmul_le]
theorem norm_pow_le_mul_norm (n : ℕ) (a : E) : ‖a ^ n‖ ≤ n * ‖a‖ := by
  induction' n with n ih; · simp
  simpa only [pow_succ', Nat.cast_succ, add_mul, one_mul] using norm_mul_le_of_le ih le_rfl

@[to_additive nnnorm_nsmul_le]
theorem nnnorm_pow_le_mul_norm (n : ℕ) (a : E) : ‖a ^ n‖₊ ≤ n * ‖a‖₊ := by
  simpa only [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_nat_cast] using
    norm_pow_le_mul_norm n a

@[to_additive]
theorem pow_mem_closedBall {n : ℕ} (h : a ∈ closedBall b r) :
    a ^ n ∈ closedBall (b ^ n) (n • r) := by
  simp only [mem_closedBall, dist_eq_norm_div, ← div_pow] at h ⊢
  refine' (norm_pow_le_mul_norm n (a / b)).trans _
  simpa only [nsmul_eq_mul] using mul_le_mul_of_nonneg_left h n.cast_nonneg

@[to_additive]
theorem pow_mem_ball {n : ℕ} (hn : 0 < n) (h : a ∈ ball b r) : a ^ n ∈ ball (b ^ n) (n • r) := by
  simp only [mem_ball, dist_eq_norm_div, ← div_pow] at h ⊢
  refine' lt_of_le_of_lt (norm_pow_le_mul_norm n (a / b)) _
  replace hn : 0 < (n : ℝ)
  · norm_cast
  rw [nsmul_eq_mul]
  nlinarith

@[to_additive] -- porting note: `simp` can prove this
theorem mul_mem_closedBall_mul_iff {c : E} : a * c ∈ closedBall (b * c) r ↔ a ∈ closedBall b r := by
  simp only [mem_closedBall, dist_eq_norm_div, mul_div_mul_right_eq_div]

@[to_additive] -- porting note: `simp` can prove this
theorem mul_mem_ball_mul_iff {c : E} : a * c ∈ ball (b * c) r ↔ a ∈ ball b r := by
  simp only [mem_ball, dist_eq_norm_div, mul_div_mul_right_eq_div]

@[to_additive]
theorem smul_closedBall'' : a • closedBall b r = closedBall (a • b) r := by
  ext
  simp [mem_closedBall, Set.mem_smul_set, dist_eq_norm_div, _root_.div_eq_inv_mul, ←
    eq_inv_mul_iff_mul_eq, mul_assoc]
  -- porting note: `ENNReal.div_eq_inv_mul` should be `protected`?

@[to_additive]
theorem smul_ball'' : a • ball b r = ball (a • b) r := by
  ext
  simp [mem_ball, Set.mem_smul_set, dist_eq_norm_div, _root_.div_eq_inv_mul,
    ← eq_inv_mul_iff_mul_eq, mul_assoc]

open Finset

@[to_additive]
theorem controlled_prod_of_mem_closure {s : Subgroup E} (hg : a ∈ closure (s : Set E)) {b : ℕ → ℝ}
    (b_pos : ∀ n, 0 < b n) :
    ∃ v : ℕ → E,
      Tendsto (fun n => ∏ i in range (n + 1), v i) atTop (𝓝 a) ∧
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
  refine' ⟨v, Tendsto.congr (Finset.eq_prod_range_div' w) hw, _, hn₀ _ (n₀.le_add_left _), _⟩
  · rintro ⟨⟩
    · change w 0 ∈ s
      apply u_in
    · apply s.div_mem <;> apply u_in
  · intro l hl
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1
    exact Nat.exists_eq_succ_of_ne_zero hl.ne'
    apply hφ

@[to_additive]
theorem controlled_prod_of_mem_closure_range {j : E →* F} {b : F}
    (hb : b ∈ closure (j.range : Set F)) {f : ℕ → ℝ} (b_pos : ∀ n, 0 < f n) :
    ∃ a : ℕ → E,
      Tendsto (fun n => ∏ i in range (n + 1), j (a i)) atTop (𝓝 b) ∧
        ‖j (a 0) / b‖ < f 0 ∧ ∀ n, 0 < n → ‖j (a n)‖ < f n := by
  obtain ⟨v, sum_v, v_in, hv₀, hv_pos⟩ := controlled_prod_of_mem_closure hb b_pos
  choose g hg using v_in
  exact
    ⟨g, by simpa [← hg] using sum_v, by simpa [hg 0] using hv₀,
      fun n hn => by simpa [hg] using hv_pos n hn⟩

@[to_additive]
theorem nndist_mul_mul_le (a₁ a₂ b₁ b₂ : E) :
    nndist (a₁ * a₂) (b₁ * b₂) ≤ nndist a₁ b₁ + nndist a₂ b₂ :=
  NNReal.coe_le_coe.1 <| dist_mul_mul_le a₁ a₂ b₁ b₂

@[to_additive]
theorem edist_mul_mul_le (a₁ a₂ b₁ b₂ : E) :
    edist (a₁ * a₂) (b₁ * b₂) ≤ edist a₁ b₁ + edist a₂ b₂ := by
  simp only [edist_nndist]
  norm_cast
  apply nndist_mul_mul_le

@[to_additive]
theorem nnnorm_multiset_prod_le (m : Multiset E) : ‖m.prod‖₊ ≤ (m.map fun x => ‖x‖₊).sum :=
  NNReal.coe_le_coe.1 <| by
    push_cast
    rw [Multiset.map_map]
    exact norm_multiset_prod_le _

@[to_additive]
theorem nnnorm_prod_le (s : Finset ι) (f : ι → E) : ‖∏ a in s, f a‖₊ ≤ ∑ a in s, ‖f a‖₊ :=
  NNReal.coe_le_coe.1 <| by
    push_cast
    exact norm_prod_le _ _

@[to_additive]
theorem nnnorm_prod_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ≥0} (h : ∀ b ∈ s, ‖f b‖₊ ≤ n b) :
    ‖∏ b in s, f b‖₊ ≤ ∑ b in s, n b :=
  (norm_prod_le_of_le s h).trans_eq NNReal.coe_sum.symm

namespace Real

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

-- porting note: `simp` can prove this
theorem norm_coe_nat (n : ℕ) : ‖(n : ℝ)‖ = n :=
  abs_of_nonneg n.cast_nonneg

@[simp]
theorem nnnorm_coe_nat (n : ℕ) : ‖(n : ℝ)‖₊ = n :=
  NNReal.eq <| norm_coe_nat _

-- porting note: `simp` can prove this
theorem norm_two : ‖(2 : ℝ)‖ = 2 :=
  abs_of_pos zero_lt_two

@[simp]
theorem nnnorm_two : ‖(2 : ℝ)‖₊ = 2 :=
  NNReal.eq <| by simp

theorem nnnorm_of_nonneg (hr : 0 ≤ r) : ‖r‖₊ = ⟨r, hr⟩ :=
  NNReal.eq <| norm_of_nonneg hr

@[simp]
theorem nnnorm_abs (r : ℝ) : ‖|r|‖₊ = ‖r‖₊ := by simp [nnnorm]

theorem ennnorm_eq_ofReal (hr : 0 ≤ r) : (‖r‖₊ : ℝ≥0∞) = ENNReal.ofReal r := by
  rw [← ofReal_norm_eq_coe_nnnorm, norm_of_nonneg hr]

theorem ennnorm_eq_ofReal_abs (r : ℝ) : (‖r‖₊ : ℝ≥0∞) = ENNReal.ofReal |r| := by
  rw [← Real.nnnorm_abs r, Real.ennnorm_eq_ofReal (abs_nonneg _)]

theorem toNNReal_eq_nnnorm_of_nonneg (hr : 0 ≤ r) : r.toNNReal = ‖r‖₊ := by
  rw [Real.toNNReal_of_nonneg hr]
  ext
  rw [coe_mk, coe_nnnorm r, Real.norm_eq_abs r, abs_of_nonneg hr]
  -- porting note: this is due to the change from `Subtype.val` to `NNReal.toReal` for the coercion

theorem ofReal_le_ennnorm (r : ℝ) : ENNReal.ofReal r ≤ ‖r‖₊ := by
  obtain hr | hr := le_total 0 r
  · exact (Real.ennnorm_eq_ofReal hr).ge
  · rw [ENNReal.ofReal_eq_zero.2 hr]
    exact bot_le
-- porting note: should this be renamed to `Real.ofReal_le_nnnorm`?

end Real

namespace Int

instance normedAddCommGroup : NormedAddCommGroup ℤ where
  norm n := ‖(n : ℝ)‖
  dist_eq m n := by simp only [Int.dist_eq, norm, Int.cast_sub]

@[norm_cast]
theorem norm_cast_real (m : ℤ) : ‖(m : ℝ)‖ = ‖m‖ :=
  rfl

theorem norm_eq_abs (n : ℤ) : ‖n‖ = |n| :=
  show ‖(n : ℝ)‖ = |n| by rw [Real.norm_eq_abs, cast_abs]
-- porting note: I'm not sure why this isn't `rfl` anymore, but I suspect it's about coercions

@[simp]
theorem norm_coe_nat (n : ℕ) : ‖(n : ℤ)‖ = n := by simp [Int.norm_eq_abs]

theorem _root_.NNReal.coe_natAbs (n : ℤ) : (n.natAbs : ℝ≥0) = ‖n‖₊ :=
  NNReal.eq <|
    calc
      ((n.natAbs : ℝ≥0) : ℝ) = (n.natAbs : ℤ) := by simp only [Int.cast_ofNat, NNReal.coe_nat_cast]
      _ = |n| := by simp only [Int.coe_natAbs, Int.cast_abs]
      _ = ‖n‖ := (norm_eq_abs n).symm

theorem abs_le_floor_nnreal_iff (z : ℤ) (c : ℝ≥0) : |z| ≤ ⌊c⌋₊ ↔ ‖z‖₊ ≤ c := by
  rw [Int.abs_eq_natAbs, Int.ofNat_le, Nat.le_floor_iff (zero_le c), NNReal.coe_natAbs z]

end Int

namespace Rat

instance normedAddCommGroup : NormedAddCommGroup ℚ where
  norm r := ‖(r : ℝ)‖
  dist_eq r₁ r₂ := by simp only [Rat.dist_eq, norm, Rat.cast_sub]

@[norm_cast, simp 1001]
-- porting note: increase priority to prevent the left-hand side from simplifying
theorem norm_cast_real (r : ℚ) : ‖(r : ℝ)‖ = ‖r‖ :=
  rfl

@[norm_cast, simp]
theorem _root_.Int.norm_cast_rat (m : ℤ) : ‖(m : ℚ)‖ = ‖m‖ := by
  rw [← Rat.norm_cast_real, ← Int.norm_cast_real]; congr 1

end Rat

-- Now that we've installed the norm on `ℤ`,
-- we can state some lemmas about `zsmul`.
section

variable [SeminormedCommGroup α]

@[to_additive norm_zsmul_le]
theorem norm_zpow_le_mul_norm (n : ℤ) (a : α) : ‖a ^ n‖ ≤ ‖n‖ * ‖a‖ := by
  rcases n.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simpa using norm_pow_le_mul_norm n a

@[to_additive nnnorm_zsmul_le]
theorem nnnorm_zpow_le_mul_norm (n : ℤ) (a : α) : ‖a ^ n‖₊ ≤ ‖n‖₊ * ‖a‖₊ := by
  simpa only [← NNReal.coe_le_coe, NNReal.coe_mul] using norm_zpow_le_mul_norm n a

end

namespace LipschitzWith

variable [PseudoEMetricSpace α] {K Kf Kg : ℝ≥0} {f g : α → E}

@[to_additive]
theorem inv (hf : LipschitzWith K f) : LipschitzWith K fun x => (f x)⁻¹ := fun x y =>
  (edist_inv_inv _ _).trans_le <| hf x y

@[to_additive add]
theorem mul' (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf + Kg) fun x => f x * g x := fun x y =>
  calc
    edist (f x * g x) (f y * g y) ≤ edist (f x) (f y) + edist (g x) (g y) :=
      edist_mul_mul_le _ _ _ _
    _ ≤ Kf * edist x y + Kg * edist x y := (add_le_add (hf x y) (hg x y))
    _ = (Kf + Kg) * edist x y := (add_mul _ _ _).symm

@[to_additive]
theorem div (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf + Kg) fun x => f x / g x := by
  simpa only [div_eq_mul_inv] using hf.mul' hg.inv

end LipschitzWith

namespace AntilipschitzWith

variable [PseudoEMetricSpace α] {K Kf Kg : ℝ≥0} {f g : α → E}

@[to_additive]
theorem mul_lipschitzWith (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg g) (hK : Kg < Kf⁻¹) :
    AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ fun x => f x * g x := by
  letI : PseudoMetricSpace α := PseudoEMetricSpace.toPseudoMetricSpace hf.edist_ne_top
  refine' AntilipschitzWith.of_le_mul_dist fun x y => _
  rw [NNReal.coe_inv, ← _root_.div_eq_inv_mul]
  rw [le_div_iff (NNReal.coe_pos.2 <| tsub_pos_iff_lt.2 hK)]
  rw [mul_comm, NNReal.coe_sub hK.le, _root_.sub_mul]
  -- porting note: `ENNReal.sub_mul` should be `protected`?
  calc
    ↑Kf⁻¹ * dist x y - Kg * dist x y ≤ dist (f x) (f y) - dist (g x) (g y) :=
      sub_le_sub (hf.mul_le_dist x y) (hg.dist_le_mul x y)
    _ ≤ _ := le_trans (le_abs_self _) (abs_dist_sub_le_dist_mul_mul _ _ _ _)

@[to_additive]
theorem mul_div_lipschitzWith (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg (g / f))
    (hK : Kg < Kf⁻¹) : AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ g := by
  simpa only [Pi.div_apply, mul_div_cancel'_right] using hf.mul_lipschitzWith hg hK

@[to_additive le_mul_norm_sub]
theorem le_mul_norm_div {f : E → F} (hf : AntilipschitzWith K f) (x y : E) :
    ‖x / y‖ ≤ K * ‖f x / f y‖ := by simp [← dist_eq_norm_div, hf.le_mul_dist x y]

end AntilipschitzWith

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedCommGroup.to_lipschitzMul : LipschitzMul E :=
  ⟨⟨1 + 1, LipschitzWith.prod_fst.mul' LipschitzWith.prod_snd⟩⟩

-- See note [lower instance priority]
/-- A seminormed group is a uniform group, i.e., multiplication and division are uniformly
continuous. -/
@[to_additive "A seminormed group is a uniform additive group, i.e., addition and subtraction are
uniformly continuous."]
instance (priority := 100) SeminormedCommGroup.to_uniformGroup : UniformGroup E :=
  ⟨(LipschitzWith.prod_fst.div LipschitzWith.prod_snd).uniformContinuous⟩

-- short-circuit type class inference
-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) SeminormedCommGroup.toTopologicalGroup : TopologicalGroup E :=
  inferInstance

@[to_additive]
theorem cauchySeq_prod_of_eventually_eq {u v : ℕ → E} {N : ℕ} (huv : ∀ n ≥ N, u n = v n)
    (hv : CauchySeq fun n => ∏ k in range (n + 1), v k) :
    CauchySeq fun n => ∏ k in range (n + 1), u k := by
  let d : ℕ → E := fun n => ∏ k in range (n + 1), u k / v k
  rw [show (fun n => ∏ k in range (n + 1), u k) = d * fun n => ∏ k in range (n + 1), v k
      by ext n; simp]
  suffices ∀ n ≥ N, d n = d N by exact (tendsto_atTop_of_eventually_const this).cauchySeq.mul hv
  intro n hn
  dsimp
  rw [eventually_constant_prod _ (add_le_add_right hn 1)]
  intro m hm
  simp [huv m (le_of_lt hm)]

end SeminormedCommGroup

section NormedGroup

variable [NormedGroup E] [NormedGroup F] {a b : E}

@[to_additive (attr := simp) norm_eq_zero]
theorem norm_eq_zero'' : ‖a‖ = 0 ↔ a = 1 :=
  norm_eq_zero'''

@[to_additive norm_ne_zero_iff]
theorem norm_ne_zero_iff' : ‖a‖ ≠ 0 ↔ a ≠ 1 :=
  norm_eq_zero''.not

@[to_additive (attr := simp) norm_pos_iff]
theorem norm_pos_iff'' : 0 < ‖a‖ ↔ a ≠ 1 :=
  norm_pos_iff'''

@[to_additive (attr := simp) norm_le_zero_iff]
theorem norm_le_zero_iff'' : ‖a‖ ≤ 0 ↔ a = 1 :=
  norm_le_zero_iff'''

@[to_additive]
theorem norm_div_eq_zero_iff : ‖a / b‖ = 0 ↔ a = b := by rw [norm_eq_zero'', div_eq_one]

@[to_additive]
theorem norm_div_pos_iff : 0 < ‖a / b‖ ↔ a ≠ b := by
  rw [(norm_nonneg' _).lt_iff_ne, ne_comm]
  exact norm_div_eq_zero_iff.not

@[to_additive eq_of_norm_sub_le_zero]
theorem eq_of_norm_div_le_zero (h : ‖a / b‖ ≤ 0) : a = b := by
  rwa [← div_eq_one, ← norm_le_zero_iff'']

alias ⟨eq_of_norm_div_eq_zero, _⟩ := norm_div_eq_zero_iff

attribute [to_additive] eq_of_norm_div_eq_zero

@[to_additive (attr := simp) nnnorm_eq_zero]
theorem nnnorm_eq_zero' : ‖a‖₊ = 0 ↔ a = 1 := by
  rw [← NNReal.coe_eq_zero, coe_nnnorm', norm_eq_zero'']

@[to_additive nnnorm_ne_zero_iff]
theorem nnnorm_ne_zero_iff' : ‖a‖₊ ≠ 0 ↔ a ≠ 1 :=
  nnnorm_eq_zero'.not

@[to_additive]
theorem tendsto_norm_div_self_punctured_nhds (a : E) :
    Tendsto (fun x => ‖x / a‖) (𝓝[≠] a) (𝓝[>] 0) :=
  (tendsto_norm_div_self a).inf <|
    tendsto_principal_principal.2 fun _x hx => norm_pos_iff''.2 <| div_ne_one.2 hx

@[to_additive]
theorem tendsto_norm_nhdsWithin_one : Tendsto (norm : E → ℝ) (𝓝[≠] 1) (𝓝[>] 0) :=
  tendsto_norm_one.inf <| tendsto_principal_principal.2 fun _x => norm_pos_iff''.2

variable (E)

/-- The norm of a normed group as a group norm. -/
@[to_additive "The norm of a normed group as an additive group norm."]
def normGroupNorm : GroupNorm E :=
  { normGroupSeminorm _ with eq_one_of_map_eq_zero' := fun _ => norm_eq_zero''.1 }

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

theorem Continuous.bounded_above_of_compact_support (hf : Continuous f) (h : HasCompactSupport f) :
    ∃ C, ∀ x, ‖f x‖ ≤ C := by
  simpa [bddAbove_def] using hf.norm.bddAbove_range_of_hasCompactSupport h.norm

end NormedAddGroup

section NormedAddGroupSource

variable [NormedAddGroup α] {f : α → E}

@[to_additive]
theorem HasCompactMulSupport.exists_pos_le_norm [One E] (hf : HasCompactMulSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : α, R ≤ ‖x‖ → f x = 1 := by
  obtain ⟨K, ⟨hK1, hK2⟩⟩ := exists_compact_iff_hasCompactMulSupport.mpr hf
  obtain ⟨S, hS, hS'⟩ := hK1.isBounded.exists_pos_norm_le
  refine' ⟨S + 1, by positivity, fun x hx => hK2 x ((mt <| hS' x) _)⟩
  -- porting note: `ENNReal.add_lt_add` should be `protected`?
  -- [context: we used `_root_.add_lt_add` in a previous version of this proof]
  contrapose! hx
  exact lt_add_of_le_of_pos hx zero_lt_one

end NormedAddGroupSource

/-! ### `ULift` -/


namespace ULift

section Norm

variable [Norm E]

instance norm : Norm (ULift E) :=
  ⟨fun x => ‖x.down‖⟩

theorem norm_def (x : ULift E) : ‖x‖ = ‖x.down‖ :=
  rfl

@[simp]
theorem norm_up (x : E) : ‖ULift.up x‖ = ‖x‖ :=
  rfl

@[simp]
theorem norm_down (x : ULift E) : ‖x.down‖ = ‖x‖ :=
  rfl

end Norm

section NNNorm

variable [NNNorm E]

instance nnnorm : NNNorm (ULift E) :=
  ⟨fun x => ‖x.down‖₊⟩

theorem nnnorm_def (x : ULift E) : ‖x‖₊ = ‖x.down‖₊ :=
  rfl

@[simp]
theorem nnnorm_up (x : E) : ‖ULift.up x‖₊ = ‖x‖₊ :=
  rfl

@[simp]
theorem nnnorm_down (x : ULift E) : ‖x.down‖₊ = ‖x‖₊ :=
  rfl

end NNNorm

@[to_additive]
instance seminormedGroup [SeminormedGroup E] : SeminormedGroup (ULift E) :=
  SeminormedGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }

@[to_additive]
instance seminormedCommGroup [SeminormedCommGroup E] : SeminormedCommGroup (ULift E) :=
  SeminormedCommGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }

@[to_additive]
instance normedGroup [NormedGroup E] : NormedGroup (ULift E) :=
  NormedGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }
  down_injective

@[to_additive]
instance normedCommGroup [NormedCommGroup E] : NormedCommGroup (ULift E) :=
  NormedCommGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }
  down_injective

end ULift

/-! ### `Additive`, `Multiplicative` -/


section AdditiveMultiplicative

open Additive Multiplicative

section Norm

variable [Norm E]

instance Additive.toNorm : Norm (Additive E) :=
  ‹Norm E›

instance Multiplicative.toNorm : Norm (Multiplicative E) :=
  ‹Norm E›

@[simp]
theorem norm_toMul (x) : ‖(toMul x : E)‖ = ‖x‖ :=
  rfl

@[simp]
theorem norm_ofMul (x : E) : ‖ofMul x‖ = ‖x‖ :=
  rfl

@[simp]
theorem norm_toAdd (x) : ‖(toAdd x : E)‖ = ‖x‖ :=
  rfl

@[simp]
theorem norm_ofAdd (x : E) : ‖ofAdd x‖ = ‖x‖ :=
  rfl

end Norm

section NNNorm

variable [NNNorm E]

instance Additive.toNNNorm : NNNorm (Additive E) :=
  ‹NNNorm E›

instance Multiplicative.toNNNorm : NNNorm (Multiplicative E) :=
  ‹NNNorm E›

@[simp]
theorem nnnorm_toMul (x) : ‖(toMul x : E)‖₊ = ‖x‖₊ :=
  rfl

@[simp]
theorem nnnorm_ofMul (x : E) : ‖ofMul x‖₊ = ‖x‖₊ :=
  rfl

@[simp]
theorem nnnorm_toAdd (x) : ‖(toAdd x : E)‖₊ = ‖x‖₊ :=
  rfl

@[simp]
theorem nnnorm_ofAdd (x : E) : ‖ofAdd x‖₊ = ‖x‖₊ :=
  rfl

end NNNorm

instance Additive.seminormedAddGroup [SeminormedGroup E] : SeminormedAddGroup (Additive E) where
  dist_eq := fun x y => dist_eq_norm_div (toMul x) (toMul y)


instance Multiplicative.seminormedGroup [SeminormedAddGroup E] :
    SeminormedGroup (Multiplicative E) where
  dist_eq := fun x y => dist_eq_norm_sub (toMul x) (toMul y)

instance Additive.seminormedCommGroup [SeminormedCommGroup E] :
    SeminormedAddCommGroup (Additive E) :=
  { Additive.seminormedAddGroup with
    add_comm := add_comm }

instance Multiplicative.seminormedAddCommGroup [SeminormedAddCommGroup E] :
    SeminormedCommGroup (Multiplicative E) :=
  { Multiplicative.seminormedGroup with
    mul_comm := mul_comm }

instance Additive.normedAddGroup [NormedGroup E] : NormedAddGroup (Additive E) :=
  { Additive.seminormedAddGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

instance Multiplicative.normedGroup [NormedAddGroup E] : NormedGroup (Multiplicative E) :=
  { Multiplicative.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

instance Additive.normedAddCommGroup [NormedCommGroup E] : NormedAddCommGroup (Additive E) :=
  { Additive.seminormedAddGroup with
    add_comm := add_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

instance Multiplicative.normedCommGroup [NormedAddCommGroup E] :
    NormedCommGroup (Multiplicative E) :=
  { Multiplicative.seminormedGroup with
    mul_comm := mul_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

end AdditiveMultiplicative

/-! ### Order dual -/


section OrderDual

open OrderDual

section Norm

variable [Norm E]

instance OrderDual.toNorm : Norm Eᵒᵈ :=
  ‹Norm E›

@[simp]
theorem norm_toDual (x : E) : ‖toDual x‖ = ‖x‖ :=
  rfl

@[simp]
theorem norm_ofDual (x : Eᵒᵈ) : ‖ofDual x‖ = ‖x‖ :=
  rfl

end Norm

section NNNorm

variable [NNNorm E]

instance OrderDual.toNNNorm : NNNorm Eᵒᵈ :=
  ‹NNNorm E›

@[simp]
theorem nnnorm_toDual (x : E) : ‖toDual x‖₊ = ‖x‖₊ :=
  rfl

@[simp]
theorem nnnorm_ofDual (x : Eᵒᵈ) : ‖ofDual x‖₊ = ‖x‖₊ :=
  rfl

end NNNorm

namespace OrderDual

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) seminormedGroup [SeminormedGroup E] : SeminormedGroup Eᵒᵈ :=
  ‹SeminormedGroup E›

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) seminormedCommGroup [SeminormedCommGroup E] :
    SeminormedCommGroup Eᵒᵈ :=
  ‹SeminormedCommGroup E›

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) normedGroup [NormedGroup E] : NormedGroup Eᵒᵈ :=
  ‹NormedGroup E›

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) normedCommGroup [NormedCommGroup E] : NormedCommGroup Eᵒᵈ :=
  ‹NormedCommGroup E›

end OrderDual

end OrderDual

/-! ### Binary product of normed groups -/


section Norm

variable [Norm E] [Norm F] {x : E × F} {r : ℝ}

instance Prod.toNorm : Norm (E × F) :=
  ⟨fun x => ‖x.1‖ ⊔ ‖x.2‖⟩

theorem Prod.norm_def (x : E × F) : ‖x‖ = max ‖x.1‖ ‖x.2‖ :=
  rfl

theorem norm_fst_le (x : E × F) : ‖x.1‖ ≤ ‖x‖ :=
  le_max_left _ _

theorem norm_snd_le (x : E × F) : ‖x.2‖ ≤ ‖x‖ :=
  le_max_right _ _

theorem norm_prod_le_iff : ‖x‖ ≤ r ↔ ‖x.1‖ ≤ r ∧ ‖x.2‖ ≤ r :=
  max_le_iff

end Norm

section SeminormedGroup

variable [SeminormedGroup E] [SeminormedGroup F]

/-- Product of seminormed groups, using the sup norm. -/
@[to_additive "Product of seminormed groups, using the sup norm."]
instance Prod.seminormedGroup : SeminormedGroup (E × F) :=
  ⟨fun x y => by
    simp only [Prod.norm_def, Prod.dist_eq, dist_eq_norm_div, Prod.fst_div, Prod.snd_div]⟩

@[to_additive Prod.nnnorm_def']
theorem Prod.nnorm_def (x : E × F) : ‖x‖₊ = max ‖x.1‖₊ ‖x.2‖₊ :=
  rfl

end SeminormedGroup

namespace Prod

/-- Product of seminormed groups, using the sup norm. -/
@[to_additive "Product of seminormed groups, using the sup norm."]
instance seminormedCommGroup [SeminormedCommGroup E] [SeminormedCommGroup F] :
    SeminormedCommGroup (E × F) :=
  { Prod.seminormedGroup with
    mul_comm := mul_comm }

/-- Product of normed groups, using the sup norm. -/
@[to_additive "Product of normed groups, using the sup norm."]
instance normedGroup [NormedGroup E] [NormedGroup F] : NormedGroup (E × F) :=
  { Prod.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Product of normed groups, using the sup norm. -/
@[to_additive "Product of normed groups, using the sup norm."]
instance normedCommGroup [NormedCommGroup E] [NormedCommGroup F] : NormedCommGroup (E × F) :=
  { Prod.seminormedGroup with
    mul_comm := mul_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-! ### Finite product of normed groups -/

end Prod

section Pi

variable {π : ι → Type*} [Fintype ι]

section SeminormedGroup

variable [∀ i, SeminormedGroup (π i)] [SeminormedGroup E] (f : ∀ i, π i) {x : ∀ i, π i} {r : ℝ}

/-- Finite product of seminormed groups, using the sup norm. -/
@[to_additive "Finite product of seminormed groups, using the sup norm."]
instance Pi.seminormedGroup : SeminormedGroup (∀ i, π i) where
  norm f := ↑(Finset.univ.sup fun b => ‖f b‖₊)
  dist_eq x y :=
    congr_arg (toReal : ℝ≥0 → ℝ) <|
      congr_arg (Finset.sup Finset.univ) <|
        funext fun a => show nndist (x a) (y a) = ‖x a / y a‖₊ from nndist_eq_nnnorm_div (x a) (y a)

@[to_additive Pi.norm_def]
theorem Pi.norm_def' : ‖f‖ = ↑(Finset.univ.sup fun b => ‖f b‖₊) :=
  rfl

@[to_additive Pi.nnnorm_def]
theorem Pi.nnnorm_def' : ‖f‖₊ = Finset.univ.sup fun b => ‖f b‖₊ :=
  Subtype.eta _ _

/-- The seminorm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
@[to_additive pi_norm_le_iff_of_nonneg "The seminorm of an element in a product space is `≤ r` if
and only if the norm of each component is."]
theorem pi_norm_le_iff_of_nonneg' (hr : 0 ≤ r) : ‖x‖ ≤ r ↔ ∀ i, ‖x i‖ ≤ r := by
  simp only [← dist_one_right, dist_pi_le_iff hr, Pi.one_apply]

@[to_additive pi_nnnorm_le_iff]
theorem pi_nnnorm_le_iff' {r : ℝ≥0} : ‖x‖₊ ≤ r ↔ ∀ i, ‖x i‖₊ ≤ r :=
  pi_norm_le_iff_of_nonneg' r.coe_nonneg

@[to_additive pi_norm_le_iff_of_nonempty]
theorem pi_norm_le_iff_of_nonempty' [Nonempty ι] : ‖f‖ ≤ r ↔ ∀ b, ‖f b‖ ≤ r := by
  by_cases hr : 0 ≤ r
  · exact pi_norm_le_iff_of_nonneg' hr
  · exact
      iff_of_false (fun h => hr <| (norm_nonneg' _).trans h) fun h =>
        hr <| (norm_nonneg' _).trans <| h <| Classical.arbitrary _

/-- The seminorm of an element in a product space is `< r` if and only if the norm of each
component is. -/
@[to_additive pi_norm_lt_iff "The seminorm of an element in a product space is `< r` if and only
if the norm of each component is."]
theorem pi_norm_lt_iff' (hr : 0 < r) : ‖x‖ < r ↔ ∀ i, ‖x i‖ < r := by
  simp only [← dist_one_right, dist_pi_lt_iff hr, Pi.one_apply]

@[to_additive pi_nnnorm_lt_iff]
theorem pi_nnnorm_lt_iff' {r : ℝ≥0} (hr : 0 < r) : ‖x‖₊ < r ↔ ∀ i, ‖x i‖₊ < r :=
  pi_norm_lt_iff' hr

@[to_additive norm_le_pi_norm]
theorem norm_le_pi_norm' (i : ι) : ‖f i‖ ≤ ‖f‖ :=
  (pi_norm_le_iff_of_nonneg' <| norm_nonneg' _).1 le_rfl i

@[to_additive nnnorm_le_pi_nnnorm]
theorem nnnorm_le_pi_nnnorm' (i : ι) : ‖f i‖₊ ≤ ‖f‖₊ :=
  norm_le_pi_norm' _ i

@[to_additive pi_norm_const_le]
theorem pi_norm_const_le' (a : E) : ‖fun _ : ι => a‖ ≤ ‖a‖ :=
  (pi_norm_le_iff_of_nonneg' <| norm_nonneg' _).2 fun _ => le_rfl

@[to_additive pi_nnnorm_const_le]
theorem pi_nnnorm_const_le' (a : E) : ‖fun _ : ι => a‖₊ ≤ ‖a‖₊ :=
  pi_norm_const_le' _

@[to_additive (attr := simp) pi_norm_const]
theorem pi_norm_const' [Nonempty ι] (a : E) : ‖fun _i : ι => a‖ = ‖a‖ := by
  simpa only [← dist_one_right] using dist_pi_const a 1

@[to_additive (attr := simp) pi_nnnorm_const]
theorem pi_nnnorm_const' [Nonempty ι] (a : E) : ‖fun _i : ι => a‖₊ = ‖a‖₊ :=
  NNReal.eq <| pi_norm_const' a

/-- The $L^1$ norm is less than the $L^\infty$ norm scaled by the cardinality. -/
@[to_additive Pi.sum_norm_apply_le_norm "The $L^1$ norm is less than the $L^\\infty$ norm scaled by
the cardinality."]
theorem Pi.sum_norm_apply_le_norm' : ∑ i, ‖f i‖ ≤ Fintype.card ι • ‖f‖ :=
  Finset.sum_le_card_nsmul _ _ _ fun i _hi => norm_le_pi_norm' _ i

/-- The $L^1$ norm is less than the $L^\infty$ norm scaled by the cardinality. -/
@[to_additive Pi.sum_nnnorm_apply_le_nnnorm "The $L^1$ norm is less than the $L^\\infty$ norm
scaled by the cardinality."]
theorem Pi.sum_nnnorm_apply_le_nnnorm' : ∑ i, ‖f i‖₊ ≤ Fintype.card ι • ‖f‖₊ :=
  NNReal.coe_sum.trans_le <| Pi.sum_norm_apply_le_norm' _

end SeminormedGroup

/-- Finite product of seminormed groups, using the sup norm. -/
@[to_additive "Finite product of seminormed groups, using the sup norm."]
instance Pi.seminormedCommGroup [∀ i, SeminormedCommGroup (π i)] : SeminormedCommGroup (∀ i, π i) :=
  { Pi.seminormedGroup with
    mul_comm := mul_comm }

/-- Finite product of normed groups, using the sup norm. -/
@[to_additive "Finite product of seminormed groups, using the sup norm."]
instance Pi.normedGroup [∀ i, NormedGroup (π i)] : NormedGroup (∀ i, π i) :=
  { Pi.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Finite product of normed groups, using the sup norm. -/
@[to_additive "Finite product of seminormed groups, using the sup norm."]
instance Pi.normedCommGroup [∀ i, NormedCommGroup (π i)] : NormedCommGroup (∀ i, π i) :=
  { Pi.seminormedGroup with
    mul_comm := mul_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

end Pi

/-! ### Multiplicative opposite -/


namespace MulOpposite

/-- The (additive) norm on the multiplicative opposite is the same as the norm on the original type.

Note that we do not provide this more generally as `Norm Eᵐᵒᵖ`, as this is not always a good
choice of norm in the multiplicative `SeminormedGroup E` case.

We could repeat this instance to provide a `[SeminormedGroup E] : SeminormedGroup Eᵃᵒᵖ` instance,
but that case would likely never be used.
-/
instance seminormedAddGroup [SeminormedAddGroup E] : SeminormedAddGroup Eᵐᵒᵖ where
  norm x := ‖x.unop‖
  dist_eq _ _ := dist_eq_norm _ _
  toPseudoMetricSpace := MulOpposite.instPseudoMetricSpaceMulOpposite

theorem norm_op [SeminormedAddGroup E] (a : E) : ‖MulOpposite.op a‖ = ‖a‖ :=
  rfl

theorem norm_unop [SeminormedAddGroup E] (a : Eᵐᵒᵖ) : ‖MulOpposite.unop a‖ = ‖a‖ :=
  rfl

theorem nnnorm_op [SeminormedAddGroup E] (a : E) : ‖MulOpposite.op a‖₊ = ‖a‖₊ :=
  rfl

theorem nnnorm_unop [SeminormedAddGroup E] (a : Eᵐᵒᵖ) : ‖MulOpposite.unop a‖₊ = ‖a‖₊ :=
  rfl

instance normedAddGroup [NormedAddGroup E] : NormedAddGroup Eᵐᵒᵖ :=
  { MulOpposite.seminormedAddGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

instance seminormedAddCommGroup [SeminormedAddCommGroup E] : SeminormedAddCommGroup Eᵐᵒᵖ where
  dist_eq _ _ := dist_eq_norm _ _

instance normedAddCommGroup [NormedAddCommGroup E] : NormedAddCommGroup Eᵐᵒᵖ :=
  { MulOpposite.seminormedAddCommGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

end MulOpposite

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

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[to_additive (attr := simp) "If `x` is an element of a subgroup `s` of a seminormed group `E`, its
norm in `s` is equal to its norm in `E`."]
theorem coe_norm (x : s) : ‖x‖ = ‖(x : E)‖ :=
  rfl

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`.

This is a reversed version of the `simp` lemma `Subgroup.coe_norm` for use by `norm_cast`. -/
@[to_additive (attr := norm_cast) "If `x` is an element of a subgroup `s` of a seminormed group `E`,
its norm in `s` is equal to its norm in `E`.

This is a reversed version of the `simp` lemma `AddSubgroup.coe_norm` for use by `norm_cast`."]
theorem norm_coe {s : Subgroup E} (x : s) : ‖(x : E)‖ = ‖x‖ :=
  rfl

end SeminormedGroup

@[to_additive]
instance seminormedCommGroup [SeminormedCommGroup E] {s : Subgroup E} : SeminormedCommGroup s :=
  SeminormedCommGroup.induced _ _ s.subtype

@[to_additive]
instance normedGroup [NormedGroup E] {s : Subgroup E} : NormedGroup s :=
  NormedGroup.induced _ _ s.subtype Subtype.coe_injective

@[to_additive]
instance normedCommGroup [NormedCommGroup E] {s : Subgroup E} : NormedCommGroup s :=
  NormedCommGroup.induced _ _ s.subtype Subtype.coe_injective

end Subgroup

/-! ### Submodules of normed groups -/


namespace Submodule

-- See note [implicit instance arguments]
/-- A submodule of a seminormed group is also a seminormed group, with the restriction of the norm.
-/
instance seminormedAddCommGroup [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E]
    (s : Submodule 𝕜 E) : SeminormedAddCommGroup s :=
  SeminormedAddCommGroup.induced _ _ s.subtype.toAddMonoidHom

-- See note [implicit instance arguments].
/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `s` is equal to its
norm in `E`. -/
@[simp]
theorem coe_norm [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] {s : Submodule 𝕜 E}
    (x : s) : ‖x‖ = ‖(x : E)‖ :=
  rfl

-- See note [implicit instance arguments].
/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `E` is equal to its
norm in `s`.

This is a reversed version of the `simp` lemma `Submodule.coe_norm` for use by `norm_cast`. -/
@[norm_cast]
theorem norm_coe [Ring 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] {s : Submodule 𝕜 E}
    (x : s) : ‖(x : E)‖ = ‖x‖ :=
  rfl

-- See note [implicit instance arguments].
/-- A submodule of a normed group is also a normed group, with the restriction of the norm. -/
instance normedAddCommGroup [Ring 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
    (s : Submodule 𝕜 E) : NormedAddCommGroup s :=
  { Submodule.seminormedAddCommGroup s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

end Submodule
