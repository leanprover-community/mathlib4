/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Product of normed groups and other constructions

This file constructs the infinity norm on finite products of normed groups and provides instances
for type synonyms.
-/

@[expose] public section

open NNReal

variable {ι E F : Type*} {G : ι → Type*}

/-! ### `PUnit` -/

namespace PUnit

instance : NormMetric PUnit where
  norm := Function.const _ 0

instance : IsNormedAddGroup PUnit where
  dist_eq _ _ := rfl

@[simp] lemma norm_eq_zero (x : PUnit) : ‖x‖ = 0 := rfl

end PUnit

/-! ### `ULift` -/

namespace ULift
section Norm
variable [Norm E]

instance norm : Norm (ULift E) where norm x := ‖x.down‖

lemma norm_def (x : ULift E) : ‖x‖ = ‖x.down‖ := rfl

@[simp] lemma norm_up (x : E) : ‖ULift.up x‖ = ‖x‖ := rfl

@[simp] lemma norm_down (x : ULift E) : ‖x.down‖ = ‖x‖ := rfl

end Norm

section NNNorm
variable [NNNorm E]

instance nnnorm : NNNorm (ULift E) where nnnorm x := ‖x.down‖₊

lemma nnnorm_def (x : ULift E) : ‖x‖₊ = ‖x.down‖₊ := rfl

@[simp] lemma nnnorm_up (x : E) : ‖ULift.up x‖₊ = ‖x‖₊ := rfl

@[simp] lemma nnnorm_down (x : ULift E) : ‖x.down‖₊ = ‖x‖₊ := rfl

end NNNorm

instance [NormPseudoMetric E] : NormPseudoMetric (ULift E) :=
  NormPseudoMetric.induced _ _ ULift.down

instance [NormMetric E] : NormMetric (ULift E) :=
  NormMetric.induced _ _ ULift.down ULift.down_injective

@[to_additive]
instance [NormPseudoMetric E] [Group E] [IsNormedGroup E] : IsNormedGroup (ULift E) :=
  IsNormedGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }

end ULift

/-! ### `Additive`, `Multiplicative` -/

section AdditiveMultiplicative

open Additive Multiplicative

section Norm
variable [Norm E]

instance Additive.toNorm : Norm (Additive E) := ‹Norm E›
instance Multiplicative.toNorm : Norm (Multiplicative E) := ‹Norm E›

@[simp] lemma norm_toMul (x : Additive E) : ‖(x.toMul : E)‖ = ‖x‖ := rfl

@[simp] lemma norm_ofMul (x : E) : ‖ofMul x‖ = ‖x‖ := rfl

@[simp] lemma norm_toAdd (x : Multiplicative E) : ‖(x.toAdd : E)‖ = ‖x‖ := rfl

@[simp] lemma norm_ofAdd (x : E) : ‖ofAdd x‖ = ‖x‖ := rfl

end Norm

section NNNorm
variable [NNNorm E]

instance Additive.toNNNorm : NNNorm (Additive E) := ‹NNNorm E›

instance Multiplicative.toNNNorm : NNNorm (Multiplicative E) := ‹NNNorm E›

@[simp] lemma nnnorm_toMul (x : Additive E) : ‖(x.toMul : E)‖₊ = ‖x‖₊ := rfl

@[simp] lemma nnnorm_ofMul (x : E) : ‖ofMul x‖₊ = ‖x‖₊ := rfl

@[simp] lemma nnnorm_toAdd (x : Multiplicative E) : ‖(x.toAdd : E)‖₊ = ‖x‖₊ := rfl

@[simp] lemma nnnorm_ofAdd (x : E) : ‖ofAdd x‖₊ = ‖x‖₊ := rfl

end NNNorm

namespace Additive

instance [NormPseudoMetric E] : NormPseudoMetric (Additive E) where
instance [NormMetric E] : NormMetric (Additive E) where

instance [NormPseudoMetric E] [Group E] [IsNormedGroup E] : IsNormedAddGroup (Additive E) where
  dist_eq x y := dist_eq_norm_inv_mul x.toMul y.toMul

end Additive

namespace Additive

instance [NormPseudoMetric E] : NormPseudoMetric (Additive E) where
instance [NormMetric E] : NormMetric (Additive E) where

instance [NormPseudoMetric E] [Group E] [IsNormedGroup E] : IsNormedAddGroup (Additive E) where
  dist_eq x y := dist_eq_norm_inv_mul x.toMul y.toMul

end Additive

namespace Multiplicative

instance [NormPseudoMetric E] : NormPseudoMetric (Multiplicative E) where
instance [NormMetric E] : NormMetric (Multiplicative E) where

instance [NormPseudoMetric E] [AddGroup E] [IsNormedAddGroup E] : IsNormedGroup (Multiplicative E) where
  dist_eq x y := dist_eq_norm_neg_add x.toAdd y.toAdd

end Multiplicative

end AdditiveMultiplicative

/-! ### Order dual -/

section OrderDual
open OrderDual

section Norm
variable [Norm E]

instance OrderDual.toNorm : Norm Eᵒᵈ := ‹Norm E›

@[simp] lemma norm_toDual (x : E) : ‖toDual x‖ = ‖x‖ := rfl

@[simp] lemma norm_ofDual (x : Eᵒᵈ) : ‖ofDual x‖ = ‖x‖ := rfl

end Norm

section NNNorm
variable [NNNorm E]

instance OrderDual.toNNNorm : NNNorm Eᵒᵈ := ‹NNNorm E›

@[simp] lemma nnnorm_toDual (x : E) : ‖toDual x‖₊ = ‖x‖₊ := rfl

@[simp] lemma nnnorm_ofDual (x : Eᵒᵈ) : ‖ofDual x‖₊ = ‖x‖₊ := rfl

end NNNorm

namespace OrderDual

-- See note [lower instance priority]
instance (priority := 100) [NormPseudoMetric E] : NormPseudoMetric Eᵒᵈ where

-- See note [lower instance priority]
instance (priority := 100) [NormMetric E] : NormMetric Eᵒᵈ where

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) [NormPseudoMetric E] [Group E] [IsNormedGroup E] : IsNormedGroup Eᵒᵈ where
  dist_eq := IsNormedGroup.dist_eq (E := E)

end OrderDual
end OrderDual

/-! ### Binary product of normed groups -/

section Norm
variable [Norm E] [Norm F] {x : E × F} {r : ℝ}

instance Prod.toNorm : Norm (E × F) where norm x := ‖x.1‖ ⊔ ‖x.2‖

lemma Prod.norm_def (x : E × F) : ‖x‖ = max ‖x.1‖ ‖x.2‖ := rfl

@[simp] lemma Prod.norm_mk (x : E) (y : F) : ‖(x, y)‖ = max ‖x‖ ‖y‖ := rfl

lemma norm_fst_le (x : E × F) : ‖x.1‖ ≤ ‖x‖ := le_max_left _ _

lemma norm_snd_le (x : E × F) : ‖x.2‖ ≤ ‖x‖ := le_max_right _ _

lemma norm_prod_le_iff : ‖x‖ ≤ r ↔ ‖x.1‖ ≤ r ∧ ‖x.2‖ ≤ r := max_le_iff

end Norm

namespace Prod

instance [NormPseudoMetric E] [NormPseudoMetric F] : NormPseudoMetric (E × F) where
instance [NormMetric E] [NormMetric F] : NormMetric (E × F) where

section SeminormedGroup

variable [NormPseudoMetric E] [Group E] [IsNormedGroup E] [NormPseudoMetric F] [Group F] [IsNormedGroup F]

/-- Product of seminormed groups, using the sup norm. -/
@[to_additive /-- Product of seminormed groups, using the sup norm. -/]
instance : IsNormedGroup (E × F) where
  dist_eq x y := by simp [Prod.norm_def, Prod.dist_eq, dist_eq_norm_inv_mul]

/-- Multiplicative version of `Prod.nnnorm_def`.
Earlier, this name was used for the additive version. -/
@[to_additive nnnorm_def]
lemma nnnorm_def' (x : E × F) : ‖x‖₊ = max ‖x.1‖₊ ‖x.2‖₊ := rfl

/-- Multiplicative version of `Prod.nnnorm_mk`. -/
@[to_additive (attr := simp) nnnorm_mk]
lemma nnnorm_mk' (x : E) (y : F) : ‖(x, y)‖₊ = max ‖x‖₊ ‖y‖₊ := rfl

end SeminormedGroup

end Prod

/-! ### Finite product of normed groups -/

section Pi
variable [Fintype ι]

section SeminormedGroup
variable [∀ i, NormPseudoMetric (G i)] [∀ i, Group (G i)] [∀ i, IsNormedGroup (G i)] [NormPseudoMetric E] [Group E] [IsNormedGroup E] (f : ∀ i, G i) {x : ∀ i, G i} {r : ℝ}

@[to_additive Pi.instNormPseudoMetric]
instance Pi.instNormPseudoMetric' : NormPseudoMetric (∀ i, G i) where
  norm f := ↑(Finset.univ.sup fun b => ‖f b‖₊)

/-- Finite product of seminormed groups, using the sup norm. -/
@[to_additive /-- Finite product of seminormed groups, using the sup norm. -/]
instance Pi.instIsNormedGroup : IsNormedGroup (∀ i, G i) where
  dist_eq x y :=
    congr_arg (toReal : ℝ≥0 → ℝ) <|
      congr_arg (Finset.sup Finset.univ) <| funext fun a =>
        show nndist (x a) (y a) = ‖(x a)⁻¹ * y a‖₊ from nndist_eq_nnnorm_inv_mul (x a) (y a)

@[to_additive Pi.norm_def]
lemma Pi.norm_def' : ‖f‖ = ↑(Finset.univ.sup fun b => ‖f b‖₊) := rfl

@[to_additive Pi.nnnorm_def]
lemma Pi.nnnorm_def' : ‖f‖₊ = Finset.univ.sup fun b => ‖f b‖₊ := Subtype.eta _ _

/-- The seminorm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
@[to_additive pi_norm_le_iff_of_nonneg /-- The seminorm of an element in a product space is `≤ r` if
and only if the norm of each component is. -/]
lemma pi_norm_le_iff_of_nonneg' (hr : 0 ≤ r) : ‖x‖ ≤ r ↔ ∀ i, ‖x i‖ ≤ r := by
  simp only [← dist_one_right, dist_pi_le_iff hr, Pi.one_apply]

@[to_additive pi_nnnorm_le_iff]
lemma pi_nnnorm_le_iff' {r : ℝ≥0} : ‖x‖₊ ≤ r ↔ ∀ i, ‖x i‖₊ ≤ r :=
  pi_norm_le_iff_of_nonneg' r.coe_nonneg

@[to_additive pi_norm_le_iff_of_nonempty]
lemma pi_norm_le_iff_of_nonempty' [Nonempty ι] : ‖f‖ ≤ r ↔ ∀ b, ‖f b‖ ≤ r := by
  by_cases hr : 0 ≤ r
  · exact pi_norm_le_iff_of_nonneg' hr
  · exact
      iff_of_false (fun h => hr <| (norm_nonneg' _).trans h) fun h =>
        hr <| (norm_nonneg' _).trans <| h <| Classical.arbitrary _

/-- The seminorm of an element in a product space is `< r` if and only if the norm of each
component is. -/
@[to_additive pi_norm_lt_iff /-- The seminorm of an element in a product space is `< r` if and only
if the norm of each component is. -/]
lemma pi_norm_lt_iff' (hr : 0 < r) : ‖x‖ < r ↔ ∀ i, ‖x i‖ < r := by
  simp only [← dist_one_right, dist_pi_lt_iff hr, Pi.one_apply]

@[to_additive pi_nnnorm_lt_iff]
lemma pi_nnnorm_lt_iff' {r : ℝ≥0} (hr : 0 < r) : ‖x‖₊ < r ↔ ∀ i, ‖x i‖₊ < r :=
  pi_norm_lt_iff' hr

@[to_additive norm_le_pi_norm]
lemma norm_le_pi_norm' (i : ι) : ‖f i‖ ≤ ‖f‖ :=
  (pi_norm_le_iff_of_nonneg' <| norm_nonneg' _).1 le_rfl i

@[to_additive nnnorm_le_pi_nnnorm]
lemma nnnorm_le_pi_nnnorm' (i : ι) : ‖f i‖₊ ≤ ‖f‖₊ :=
  norm_le_pi_norm' _ i

@[to_additive pi_norm_const_le]
lemma pi_norm_const_le' (a : E) : ‖fun _ : ι => a‖ ≤ ‖a‖ :=
  (pi_norm_le_iff_of_nonneg' <| norm_nonneg' _).2 fun _ => le_rfl

@[to_additive pi_nnnorm_const_le]
lemma pi_nnnorm_const_le' (a : E) : ‖fun _ : ι => a‖₊ ≤ ‖a‖₊ :=
  pi_norm_const_le' _

@[to_additive (attr := simp) pi_norm_const]
lemma pi_norm_const' [Nonempty ι] (a : E) : ‖fun _i : ι => a‖ = ‖a‖ := by
  simpa only [← dist_one_right] using dist_pi_const a 1

@[to_additive (attr := simp) pi_nnnorm_const]
lemma pi_nnnorm_const' [Nonempty ι] (a : E) : ‖fun _i : ι => a‖₊ = ‖a‖₊ :=
  NNReal.eq <| pi_norm_const' a

/-- The $L^1$ norm is less than the $L^\infty$ norm scaled by the cardinality. -/
@[to_additive Pi.sum_norm_apply_le_norm /-- The $L^1$ norm is less than the $L^\infty$ norm scaled
by the cardinality. -/]
lemma Pi.sum_norm_apply_le_norm' : ∑ i, ‖f i‖ ≤ Fintype.card ι • ‖f‖ :=
  Finset.sum_le_card_nsmul _ _ _ fun i _hi => norm_le_pi_norm' _ i

/-- The $L^1$ norm is less than the $L^\infty$ norm scaled by the cardinality. -/
@[to_additive Pi.sum_nnnorm_apply_le_nnnorm /-- The $L^1$ norm is less than the $L^\infty$ norm
scaled by the cardinality. -/]
lemma Pi.sum_nnnorm_apply_le_nnnorm' : ∑ i, ‖f i‖₊ ≤ Fintype.card ι • ‖f‖₊ :=
  (NNReal.coe_sum ..).trans_le <| Pi.sum_norm_apply_le_norm' _

end SeminormedGroup

@[to_additive Pi.instNormMetric]
instance Pi.instNormMetric' [∀ i, NormMetric (G i)] [∀ i, Group (G i)] [∀ i, IsNormedGroup (G i)] : NormMetric (∀ i, G i) where
  norm f := ↑(Finset.univ.sup fun b => ‖f b‖₊)

theorem Pi.nnnorm_single [DecidableEq ι] [∀ i, NormMetric (G i)] [∀ i, AddCommGroup (G i)] [∀ i, IsNormedAddGroup (G i)] {i : ι} (y : G i) :
    ‖Pi.single i y‖₊ = ‖y‖₊ := by
  have H : ∀ b, ‖single i y b‖₊ = single (M := fun _ ↦ ℝ≥0) i ‖y‖₊ b := by
    intro b
    refine Pi.apply_single (fun i (x : G i) ↦ ‖x‖₊) ?_ i y b
    simp
  simp [Pi.nnnorm_def, H, Pi.single_apply, Finset.sup_ite, Finset.filter_eq']

lemma Pi.enorm_single [DecidableEq ι] [∀ i, NormMetric (G i)] [∀ i, AddCommGroup (G i)] [∀ i, IsNormedAddGroup (G i)] {i : ι} (y : G i) :
    ‖Pi.single i y‖ₑ = ‖y‖ₑ := by simp [enorm, Pi.nnnorm_single]

theorem Pi.norm_single [DecidableEq ι] [∀ i, NormMetric (G i)] [∀ i, AddCommGroup (G i)] [∀ i, IsNormedAddGroup (G i)] {i : ι} (y : G i) :
    ‖Pi.single i y‖ = ‖y‖ :=
  congr_arg Subtype.val <| Pi.nnnorm_single y

end Pi

/-! ### Multiplicative opposite -/

namespace MulOpposite

instance instNorm [Norm E] : Norm Eᵐᵒᵖ where
  norm x := ‖x.unop‖

instance instNormPseudoMetric [NormPseudoMetric E] : NormPseudoMetric Eᵐᵒᵖ where
instance instNormMetric [NormMetric E] : NormMetric Eᵐᵒᵖ where

/-- The (additive) norm on the multiplicative opposite is the same as the norm on the original type.

Note that we do not provide this more generally as `Norm Eᵐᵒᵖ`, as this is not always a good
choice of norm in the multiplicative `SeminormedGroup E` case.

We could repeat this instance to provide a `[NormPseudoMetric E] [Group E] [IsNormedGroup E] : SeminormedGroup Eᵃᵒᵖ` instance,
but that case would likely never be used.
-/
instance instIsNormedAddGroup [NormPseudoMetric E] [AddGroup E] [IsNormedAddGroup E] : IsNormedAddGroup Eᵐᵒᵖ where
  dist_eq _ _ := dist_eq_norm_neg_add (E := E) _ _

lemma norm_op [NormPseudoMetric E] [AddGroup E] [IsNormedAddGroup E] (a : E) : ‖MulOpposite.op a‖ = ‖a‖ := rfl

lemma norm_unop [NormPseudoMetric E] [AddGroup E] [IsNormedAddGroup E] (a : Eᵐᵒᵖ) : ‖MulOpposite.unop a‖ = ‖a‖ := rfl

lemma nnnorm_op [NormPseudoMetric E] [AddGroup E] [IsNormedAddGroup E] (a : E) : ‖MulOpposite.op a‖₊ = ‖a‖₊ := rfl

lemma nnnorm_unop [NormPseudoMetric E] [AddGroup E] [IsNormedAddGroup E] (a : Eᵐᵒᵖ) : ‖MulOpposite.unop a‖₊ = ‖a‖₊ := rfl

end MulOpposite
