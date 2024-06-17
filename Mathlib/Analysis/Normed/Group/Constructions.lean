/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.PUnitInstances
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Product of normed groups and other constructions

This file constructs the infinity norm on finite products of normed groups and provides instances
for type synonyms.
-/

open NNReal

variable {ι E F : Type*} {π : ι → Type*}

/-! ### `PUnit` -/

namespace PUnit

instance normedAddCommGroup : NormedAddCommGroup PUnit where
  norm := Function.const _ 0
  dist_eq _ _ := rfl

@[simp] lemma norm_eq_zero (x : PUnit) : ‖x‖ = 0 := rfl
#align punit.norm_eq_zero PUnit.norm_eq_zero

end PUnit

/-! ### `ULift` -/

namespace ULift
section Norm
variable [Norm E]

instance norm : Norm (ULift E) where norm x := ‖x.down‖

lemma norm_def (x : ULift E) : ‖x‖ = ‖x.down‖ := rfl
#align ulift.norm_def ULift.norm_def

@[simp] lemma norm_up (x : E) : ‖ULift.up x‖ = ‖x‖ := rfl
#align ulift.norm_up ULift.norm_up

@[simp] lemma norm_down (x : ULift E) : ‖x.down‖ = ‖x‖ := rfl
#align ulift.norm_down ULift.norm_down

end Norm

section NNNorm
variable [NNNorm E]

instance nnnorm : NNNorm (ULift E) where nnnorm x := ‖x.down‖₊

lemma nnnorm_def (x : ULift E) : ‖x‖₊ = ‖x.down‖₊ := rfl
#align ulift.nnnorm_def ULift.nnnorm_def

@[simp] lemma nnnorm_up (x : E) : ‖ULift.up x‖₊ = ‖x‖₊ := rfl
#align ulift.nnnorm_up ULift.nnnorm_up

@[simp] lemma nnnorm_down (x : ULift E) : ‖x.down‖₊ = ‖x‖₊ := rfl
#align ulift.nnnorm_down ULift.nnnorm_down

end NNNorm

@[to_additive]
instance seminormedGroup [SeminormedGroup E] : SeminormedGroup (ULift E) :=
  SeminormedGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }
#align ulift.seminormed_group ULift.seminormedGroup
#align ulift.seminormed_add_group ULift.seminormedAddGroup

@[to_additive]
instance seminormedCommGroup [SeminormedCommGroup E] : SeminormedCommGroup (ULift E) :=
  SeminormedCommGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }
#align ulift.seminormed_comm_group ULift.seminormedCommGroup
#align ulift.seminormed_add_comm_group ULift.seminormedAddCommGroup

@[to_additive]
instance normedGroup [NormedGroup E] : NormedGroup (ULift E) :=
  NormedGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }
  down_injective
#align ulift.normed_group ULift.normedGroup
#align ulift.normed_add_group ULift.normedAddGroup

@[to_additive]
instance normedCommGroup [NormedCommGroup E] : NormedCommGroup (ULift E) :=
  NormedCommGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }
  down_injective
#align ulift.normed_comm_group ULift.normedCommGroup
#align ulift.normed_add_comm_group ULift.normedAddCommGroup

end ULift

/-! ### `Additive`, `Multiplicative` -/

section AdditiveMultiplicative

open Additive Multiplicative

section Norm
variable [Norm E]

instance Additive.toNorm : Norm (Additive E) := ‹Norm E›
instance Multiplicative.toNorm : Norm (Multiplicative E) := ‹Norm E›

@[simp] lemma norm_toMul (x) : ‖(toMul x : E)‖ = ‖x‖ := rfl
#align norm_to_mul norm_toMul

@[simp] lemma norm_ofMul (x : E) : ‖ofMul x‖ = ‖x‖ := rfl
#align norm_of_mul norm_ofMul

@[simp] lemma norm_toAdd (x) : ‖(toAdd x : E)‖ = ‖x‖ := rfl
#align norm_to_add norm_toAdd

@[simp] lemma norm_ofAdd (x : E) : ‖ofAdd x‖ = ‖x‖ := rfl
#align norm_of_add norm_ofAdd

end Norm

section NNNorm
variable [NNNorm E]

instance Additive.toNNNorm : NNNorm (Additive E) := ‹NNNorm E›

instance Multiplicative.toNNNorm : NNNorm (Multiplicative E) := ‹NNNorm E›

@[simp] lemma nnnorm_toMul (x) : ‖(toMul x : E)‖₊ = ‖x‖₊ := rfl
#align nnnorm_to_mul nnnorm_toMul

@[simp] lemma nnnorm_ofMul (x : E) : ‖ofMul x‖₊ = ‖x‖₊ := rfl
#align nnnorm_of_mul nnnorm_ofMul

@[simp] lemma nnnorm_toAdd (x) : ‖(toAdd x : E)‖₊ = ‖x‖₊ := rfl
#align nnnorm_to_add nnnorm_toAdd

@[simp] lemma nnnorm_ofAdd (x : E) : ‖ofAdd x‖₊ = ‖x‖₊ := rfl
#align nnnorm_of_add nnnorm_ofAdd

end NNNorm

instance Additive.seminormedAddGroup [SeminormedGroup E] : SeminormedAddGroup (Additive E) where
  dist_eq x y := dist_eq_norm_div (toMul x) (toMul y)


instance Multiplicative.seminormedGroup [SeminormedAddGroup E] :
    SeminormedGroup (Multiplicative E) where
  dist_eq x y := dist_eq_norm_sub (toMul x) (toMul y)

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

instance OrderDual.toNorm : Norm Eᵒᵈ := ‹Norm E›

@[simp] lemma norm_toDual (x : E) : ‖toDual x‖ = ‖x‖ := rfl
#align norm_to_dual norm_toDual

@[simp] lemma norm_ofDual (x : Eᵒᵈ) : ‖ofDual x‖ = ‖x‖ := rfl
#align norm_of_dual norm_ofDual

end Norm

section NNNorm
variable [NNNorm E]

instance OrderDual.toNNNorm : NNNorm Eᵒᵈ := ‹NNNorm E›

@[simp] lemma nnnorm_toDual (x : E) : ‖toDual x‖₊ = ‖x‖₊ := rfl
#align nnnorm_to_dual nnnorm_toDual

@[simp] lemma nnnorm_ofDual (x : Eᵒᵈ) : ‖ofDual x‖₊ = ‖x‖₊ := rfl
#align nnnorm_of_dual nnnorm_ofDual

end NNNorm

namespace OrderDual

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) seminormedGroup [SeminormedGroup E] : SeminormedGroup Eᵒᵈ :=
  ‹SeminormedGroup E›

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) seminormedCommGroup [SeminormedCommGroup E] : SeminormedCommGroup Eᵒᵈ :=
  ‹SeminormedCommGroup E›

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) normedGroup [NormedGroup E] : NormedGroup Eᵒᵈ := ‹NormedGroup E›

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) normedCommGroup [NormedCommGroup E] : NormedCommGroup Eᵒᵈ :=
  ‹NormedCommGroup E›

end OrderDual
end OrderDual

/-! ### Binary product of normed groups -/

section Norm
variable [Norm E] [Norm F] {x : E × F} {r : ℝ}

instance Prod.toNorm : Norm (E × F) where norm x := ‖x.1‖ ⊔ ‖x.2‖

lemma Prod.norm_def (x : E × F) : ‖x‖ = max ‖x.1‖ ‖x.2‖ := rfl
#align prod.norm_def Prod.norm_def

lemma norm_fst_le (x : E × F) : ‖x.1‖ ≤ ‖x‖ := le_max_left _ _
#align norm_fst_le norm_fst_le

lemma norm_snd_le (x : E × F) : ‖x.2‖ ≤ ‖x‖ := le_max_right _ _
#align norm_snd_le norm_snd_le

lemma norm_prod_le_iff : ‖x‖ ≤ r ↔ ‖x.1‖ ≤ r ∧ ‖x.2‖ ≤ r := max_le_iff
#align norm_prod_le_iff norm_prod_le_iff

end Norm

section SeminormedGroup
variable [SeminormedGroup E] [SeminormedGroup F]

/-- Product of seminormed groups, using the sup norm. -/
@[to_additive "Product of seminormed groups, using the sup norm."]
instance Prod.seminormedGroup : SeminormedGroup (E × F) where
  dist_eq x y := by
    simp only [Prod.norm_def, Prod.dist_eq, dist_eq_norm_div, Prod.fst_div, Prod.snd_div]

@[to_additive Prod.nnnorm_def']
lemma Prod.nnorm_def (x : E × F) : ‖x‖₊ = max ‖x.1‖₊ ‖x.2‖₊ := rfl
#align prod.nnorm_def Prod.nnorm_def
#align prod.nnnorm_def' Prod.nnnorm_def'

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

end Prod

/-! ### Finite product of normed groups -/

section Pi
variable [Fintype ι]

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
lemma Pi.norm_def' : ‖f‖ = ↑(Finset.univ.sup fun b => ‖f b‖₊) := rfl
#align pi.norm_def' Pi.norm_def'
#align pi.norm_def Pi.norm_def

@[to_additive Pi.nnnorm_def]
lemma Pi.nnnorm_def' : ‖f‖₊ = Finset.univ.sup fun b => ‖f b‖₊ := Subtype.eta _ _
#align pi.nnnorm_def' Pi.nnnorm_def'
#align pi.nnnorm_def Pi.nnnorm_def

/-- The seminorm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
@[to_additive pi_norm_le_iff_of_nonneg "The seminorm of an element in a product space is `≤ r` if
and only if the norm of each component is."]
lemma pi_norm_le_iff_of_nonneg' (hr : 0 ≤ r) : ‖x‖ ≤ r ↔ ∀ i, ‖x i‖ ≤ r := by
  simp only [← dist_one_right, dist_pi_le_iff hr, Pi.one_apply]
#align pi_norm_le_iff_of_nonneg' pi_norm_le_iff_of_nonneg'
#align pi_norm_le_iff_of_nonneg pi_norm_le_iff_of_nonneg

@[to_additive pi_nnnorm_le_iff]
lemma pi_nnnorm_le_iff' {r : ℝ≥0} : ‖x‖₊ ≤ r ↔ ∀ i, ‖x i‖₊ ≤ r :=
  pi_norm_le_iff_of_nonneg' r.coe_nonneg
#align pi_nnnorm_le_iff' pi_nnnorm_le_iff'
#align pi_nnnorm_le_iff pi_nnnorm_le_iff

@[to_additive pi_norm_le_iff_of_nonempty]
lemma pi_norm_le_iff_of_nonempty' [Nonempty ι] : ‖f‖ ≤ r ↔ ∀ b, ‖f b‖ ≤ r := by
  by_cases hr : 0 ≤ r
  · exact pi_norm_le_iff_of_nonneg' hr
  · exact
      iff_of_false (fun h => hr <| (norm_nonneg' _).trans h) fun h =>
        hr <| (norm_nonneg' _).trans <| h <| Classical.arbitrary _
#align pi_norm_le_iff_of_nonempty' pi_norm_le_iff_of_nonempty'
#align pi_norm_le_iff_of_nonempty pi_norm_le_iff_of_nonempty

/-- The seminorm of an element in a product space is `< r` if and only if the norm of each
component is. -/
@[to_additive pi_norm_lt_iff "The seminorm of an element in a product space is `< r` if and only
if the norm of each component is."]
lemma pi_norm_lt_iff' (hr : 0 < r) : ‖x‖ < r ↔ ∀ i, ‖x i‖ < r := by
  simp only [← dist_one_right, dist_pi_lt_iff hr, Pi.one_apply]
#align pi_norm_lt_iff' pi_norm_lt_iff'
#align pi_norm_lt_iff pi_norm_lt_iff

@[to_additive pi_nnnorm_lt_iff]
lemma pi_nnnorm_lt_iff' {r : ℝ≥0} (hr : 0 < r) : ‖x‖₊ < r ↔ ∀ i, ‖x i‖₊ < r :=
  pi_norm_lt_iff' hr
#align pi_nnnorm_lt_iff' pi_nnnorm_lt_iff'
#align pi_nnnorm_lt_iff pi_nnnorm_lt_iff

@[to_additive norm_le_pi_norm]
lemma norm_le_pi_norm' (i : ι) : ‖f i‖ ≤ ‖f‖ :=
  (pi_norm_le_iff_of_nonneg' <| norm_nonneg' _).1 le_rfl i
#align norm_le_pi_norm' norm_le_pi_norm'
#align norm_le_pi_norm norm_le_pi_norm

@[to_additive nnnorm_le_pi_nnnorm]
lemma nnnorm_le_pi_nnnorm' (i : ι) : ‖f i‖₊ ≤ ‖f‖₊ :=
  norm_le_pi_norm' _ i
#align nnnorm_le_pi_nnnorm' nnnorm_le_pi_nnnorm'
#align nnnorm_le_pi_nnnorm nnnorm_le_pi_nnnorm

@[to_additive pi_norm_const_le]
lemma pi_norm_const_le' (a : E) : ‖fun _ : ι => a‖ ≤ ‖a‖ :=
  (pi_norm_le_iff_of_nonneg' <| norm_nonneg' _).2 fun _ => le_rfl
#align pi_norm_const_le' pi_norm_const_le'
#align pi_norm_const_le pi_norm_const_le

@[to_additive pi_nnnorm_const_le]
lemma pi_nnnorm_const_le' (a : E) : ‖fun _ : ι => a‖₊ ≤ ‖a‖₊ :=
  pi_norm_const_le' _
#align pi_nnnorm_const_le' pi_nnnorm_const_le'
#align pi_nnnorm_const_le pi_nnnorm_const_le

@[to_additive (attr := simp) pi_norm_const]
lemma pi_norm_const' [Nonempty ι] (a : E) : ‖fun _i : ι => a‖ = ‖a‖ := by
  simpa only [← dist_one_right] using dist_pi_const a 1
#align pi_norm_const' pi_norm_const'
#align pi_norm_const pi_norm_const

@[to_additive (attr := simp) pi_nnnorm_const]
lemma pi_nnnorm_const' [Nonempty ι] (a : E) : ‖fun _i : ι => a‖₊ = ‖a‖₊ :=
  NNReal.eq <| pi_norm_const' a
#align pi_nnnorm_const' pi_nnnorm_const'
#align pi_nnnorm_const pi_nnnorm_const

/-- The $L^1$ norm is less than the $L^\infty$ norm scaled by the cardinality. -/
@[to_additive Pi.sum_norm_apply_le_norm "The $L^1$ norm is less than the $L^\\infty$ norm scaled by
the cardinality."]
lemma Pi.sum_norm_apply_le_norm' : ∑ i, ‖f i‖ ≤ Fintype.card ι • ‖f‖ :=
  Finset.sum_le_card_nsmul _ _ _ fun i _hi => norm_le_pi_norm' _ i
#align pi.sum_norm_apply_le_norm' Pi.sum_norm_apply_le_norm'
#align pi.sum_norm_apply_le_norm Pi.sum_norm_apply_le_norm

/-- The $L^1$ norm is less than the $L^\infty$ norm scaled by the cardinality. -/
@[to_additive Pi.sum_nnnorm_apply_le_nnnorm "The $L^1$ norm is less than the $L^\\infty$ norm
scaled by the cardinality."]
lemma Pi.sum_nnnorm_apply_le_nnnorm' : ∑ i, ‖f i‖₊ ≤ Fintype.card ι • ‖f‖₊ :=
  NNReal.coe_sum.trans_le <| Pi.sum_norm_apply_le_norm' _
#align pi.sum_nnnorm_apply_le_nnnorm' Pi.sum_nnnorm_apply_le_nnnorm'
#align pi.sum_nnnorm_apply_le_nnnorm Pi.sum_nnnorm_apply_le_nnnorm

end SeminormedGroup

/-- Finite product of seminormed groups, using the sup norm. -/
@[to_additive "Finite product of seminormed groups, using the sup norm."]
instance Pi.seminormedCommGroup [∀ i, SeminormedCommGroup (π i)] : SeminormedCommGroup (∀ i, π i) :=
  { Pi.seminormedGroup with
    mul_comm := mul_comm }
#align pi.seminormed_comm_group Pi.seminormedCommGroup
#align pi.seminormed_add_comm_group Pi.seminormedAddCommGroup

/-- Finite product of normed groups, using the sup norm. -/
@[to_additive "Finite product of seminormed groups, using the sup norm."]
instance Pi.normedGroup [∀ i, NormedGroup (π i)] : NormedGroup (∀ i, π i) :=
  { Pi.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
#align pi.normed_group Pi.normedGroup
#align pi.normed_add_group Pi.normedAddGroup

/-- Finite product of normed groups, using the sup norm. -/
@[to_additive "Finite product of seminormed groups, using the sup norm."]
instance Pi.normedCommGroup [∀ i, NormedCommGroup (π i)] : NormedCommGroup (∀ i, π i) :=
  { Pi.seminormedGroup with
    mul_comm := mul_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
#align pi.normed_comm_group Pi.normedCommGroup
#align pi.normed_add_comm_group Pi.normedAddCommGroup

end Pi

/-! ### Multiplicative opposite -/

namespace MulOpposite

/-- The (additive) norm on the multiplicative opposite is the same as the norm on the original type.

Note that we do not provide this more generally as `Norm Eᵐᵒᵖ`, as this is not always a good
choice of norm in the multiplicative `SeminormedGroup E` case.

We could repeat this instance to provide a `[SeminormedGroup E] : SeminormedGroup Eᵃᵒᵖ` instance,
but that case would likely never be used.
-/
instance instSeminormedAddGroup [SeminormedAddGroup E] : SeminormedAddGroup Eᵐᵒᵖ where
  __ := instPseudoMetricSpace
  norm x := ‖x.unop‖
  dist_eq _ _ := dist_eq_norm _ _

lemma norm_op [SeminormedAddGroup E] (a : E) : ‖MulOpposite.op a‖ = ‖a‖ := rfl
#align mul_opposite.norm_op MulOpposite.norm_op

lemma norm_unop [SeminormedAddGroup E] (a : Eᵐᵒᵖ) : ‖MulOpposite.unop a‖ = ‖a‖ := rfl
#align mul_opposite.norm_unop MulOpposite.norm_unop

lemma nnnorm_op [SeminormedAddGroup E] (a : E) : ‖MulOpposite.op a‖₊ = ‖a‖₊ := rfl
#align mul_opposite.nnnorm_op MulOpposite.nnnorm_op

lemma nnnorm_unop [SeminormedAddGroup E] (a : Eᵐᵒᵖ) : ‖MulOpposite.unop a‖₊ = ‖a‖₊ := rfl
#align mul_opposite.nnnorm_unop MulOpposite.nnnorm_unop

instance instNormedAddGroup [NormedAddGroup E] : NormedAddGroup Eᵐᵒᵖ where
  __ := instMetricSpace
  __ := instSeminormedAddGroup

instance instSeminormedAddCommGroup [SeminormedAddCommGroup E] : SeminormedAddCommGroup Eᵐᵒᵖ where
  dist_eq _ _ := dist_eq_norm _ _

instance instNormedAddCommGroup [NormedAddCommGroup E] : NormedAddCommGroup Eᵐᵒᵖ where
  __ := instSeminormedAddCommGroup
  __ := instNormedAddGroup

end MulOpposite
