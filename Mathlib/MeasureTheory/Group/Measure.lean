/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module measure_theory.group.measure
! leanprover-community/mathlib commit fd5edc43dc4f10b85abfe544b88f82cf13c5f844
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Dynamics.Ergodic.MeasurePreserving
import Mathbin.MeasureTheory.Measure.Regular
import Mathbin.MeasureTheory.Group.MeasurableEquiv
import Mathbin.MeasureTheory.Measure.OpenPos
import Mathbin.MeasureTheory.Group.Action
import Mathbin.MeasureTheory.Constructions.Prod.Basic
import Mathbin.Topology.ContinuousFunction.CocompactMap

/-!
# Measures on Groups

We develop some properties of measures on (topological) groups

* We define properties on measures: measures that are left or right invariant w.r.t. multiplication.
* We define the measure `μ.inv : A ↦ μ(A⁻¹)` and show that it is right invariant iff
  `μ` is left invariant.
* We define a class `is_haar_measure μ`, requiring that the measure `μ` is left-invariant, finite
  on compact sets, and positive on open sets.

We also give analogues of all these notions in the additive world.
-/


noncomputable section

open scoped NNReal ENNReal Pointwise BigOperators Topology

open Inv Set Function MeasureTheory.Measure Filter

variable {𝕜 G H : Type _} [MeasurableSpace G] [MeasurableSpace H]

namespace MeasureTheory

namespace Measure

/-- A measure `μ` on a measurable additive group is left invariant
  if the measure of left translations of a set are equal to the measure of the set itself. -/
class IsAddLeftInvariant [Add G] (μ : Measure G) : Prop where
  map_add_left_eq_self : ∀ g : G, map ((· + ·) g) μ = μ
#align measure_theory.measure.is_add_left_invariant MeasureTheory.Measure.IsAddLeftInvariant

/-- A measure `μ` on a measurable group is left invariant
  if the measure of left translations of a set are equal to the measure of the set itself. -/
@[to_additive]
class IsMulLeftInvariant [Mul G] (μ : Measure G) : Prop where
  map_mul_left_eq_self : ∀ g : G, map ((· * ·) g) μ = μ
#align measure_theory.measure.is_mul_left_invariant MeasureTheory.Measure.IsMulLeftInvariant
#align measure_theory.measure.is_add_left_invariant MeasureTheory.Measure.IsAddLeftInvariant

/-- A measure `μ` on a measurable additive group is right invariant
  if the measure of right translations of a set are equal to the measure of the set itself. -/
class IsAddRightInvariant [Add G] (μ : Measure G) : Prop where
  map_add_right_eq_self : ∀ g : G, map (· + g) μ = μ
#align measure_theory.measure.is_add_right_invariant MeasureTheory.Measure.IsAddRightInvariant

/-- A measure `μ` on a measurable group is right invariant
  if the measure of right translations of a set are equal to the measure of the set itself. -/
@[to_additive]
class IsMulRightInvariant [Mul G] (μ : Measure G) : Prop where
  map_mul_right_eq_self : ∀ g : G, map (· * g) μ = μ
#align measure_theory.measure.is_mul_right_invariant MeasureTheory.Measure.IsMulRightInvariant
#align measure_theory.measure.is_add_right_invariant MeasureTheory.Measure.IsAddRightInvariant

end Measure

open Measure

section Mul

variable [Mul G] {μ : Measure G}

@[to_additive]
theorem map_mul_left_eq_self (μ : Measure G) [IsMulLeftInvariant μ] (g : G) :
    map ((· * ·) g) μ = μ :=
  IsMulLeftInvariant.map_mul_left_eq_self g
#align measure_theory.map_mul_left_eq_self MeasureTheory.map_mul_left_eq_self
#align measure_theory.map_add_left_eq_self MeasureTheory.map_add_left_eq_self

@[to_additive]
theorem map_mul_right_eq_self (μ : Measure G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ :=
  IsMulRightInvariant.map_mul_right_eq_self g
#align measure_theory.map_mul_right_eq_self MeasureTheory.map_mul_right_eq_self
#align measure_theory.map_add_right_eq_self MeasureTheory.map_add_right_eq_self

@[to_additive MeasureTheory.is_add_left_invariant_smul]
instance isMulLeftInvariant_smul [IsMulLeftInvariant μ] (c : ℝ≥0∞) : IsMulLeftInvariant (c • μ) :=
  ⟨fun g => by rw [measure.map_smul, map_mul_left_eq_self]⟩
#align measure_theory.is_mul_left_invariant_smul MeasureTheory.isMulLeftInvariant_smul
#align measure_theory.is_add_left_invariant_smul MeasureTheory.is_add_left_invariant_smul

@[to_additive MeasureTheory.is_add_right_invariant_smul]
instance isMulRightInvariant_smul [IsMulRightInvariant μ] (c : ℝ≥0∞) :
    IsMulRightInvariant (c • μ) :=
  ⟨fun g => by rw [measure.map_smul, map_mul_right_eq_self]⟩
#align measure_theory.is_mul_right_invariant_smul MeasureTheory.isMulRightInvariant_smul
#align measure_theory.is_add_right_invariant_smul MeasureTheory.is_add_right_invariant_smul

@[to_additive MeasureTheory.is_add_left_invariant_smul_nnreal]
instance isMulLeftInvariant_smul_nNReal [IsMulLeftInvariant μ] (c : ℝ≥0) :
    IsMulLeftInvariant (c • μ) :=
  MeasureTheory.isMulLeftInvariant_smul (c : ℝ≥0∞)
#align measure_theory.is_mul_left_invariant_smul_nnreal MeasureTheory.isMulLeftInvariant_smul_nNReal
#align measure_theory.is_add_left_invariant_smul_nnreal MeasureTheory.is_add_left_invariant_smul_nnreal

@[to_additive MeasureTheory.is_add_right_invariant_smul_nnreal]
instance isMulRightInvariant_smul_nNReal [IsMulRightInvariant μ] (c : ℝ≥0) :
    IsMulRightInvariant (c • μ) :=
  MeasureTheory.isMulRightInvariant_smul (c : ℝ≥0∞)
#align measure_theory.is_mul_right_invariant_smul_nnreal MeasureTheory.isMulRightInvariant_smul_nNReal
#align measure_theory.is_add_right_invariant_smul_nnreal MeasureTheory.is_add_right_invariant_smul_nnreal

section MeasurableMul

variable [MeasurableMul G]

@[to_additive]
theorem measurePreserving_mul_left (μ : Measure G) [IsMulLeftInvariant μ] (g : G) :
    MeasurePreserving ((· * ·) g) μ μ :=
  ⟨measurable_const_mul g, map_mul_left_eq_self μ g⟩
#align measure_theory.measure_preserving_mul_left MeasureTheory.measurePreserving_mul_left
#align measure_theory.measure_preserving_add_left MeasureTheory.measurePreserving_add_left

@[to_additive]
theorem MeasurePreserving.mul_left (μ : Measure G) [IsMulLeftInvariant μ] (g : G) {X : Type _}
    [MeasurableSpace X] {μ' : Measure X} {f : X → G} (hf : MeasurePreserving f μ' μ) :
    MeasurePreserving (fun x => g * f x) μ' μ :=
  (measurePreserving_mul_left μ g).comp hf
#align measure_theory.measure_preserving.mul_left MeasureTheory.MeasurePreserving.mul_left
#align measure_theory.measure_preserving.add_left MeasureTheory.MeasurePreserving.add_left

@[to_additive]
theorem measurePreserving_mul_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) :
    MeasurePreserving (· * g) μ μ :=
  ⟨measurable_mul_const g, map_mul_right_eq_self μ g⟩
#align measure_theory.measure_preserving_mul_right MeasureTheory.measurePreserving_mul_right
#align measure_theory.measure_preserving_add_right MeasureTheory.measurePreserving_add_right

@[to_additive]
theorem MeasurePreserving.mul_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) {X : Type _}
    [MeasurableSpace X] {μ' : Measure X} {f : X → G} (hf : MeasurePreserving f μ' μ) :
    MeasurePreserving (fun x => f x * g) μ' μ :=
  (measurePreserving_mul_right μ g).comp hf
#align measure_theory.measure_preserving.mul_right MeasureTheory.MeasurePreserving.mul_right
#align measure_theory.measure_preserving.add_right MeasureTheory.MeasurePreserving.add_right

@[to_additive]
instance IsMulLeftInvariant.smulInvariantMeasure [IsMulLeftInvariant μ] :
    SmulInvariantMeasure G G μ :=
  ⟨fun x s hs => (measurePreserving_mul_left μ x).measure_preimage hs⟩
#align measure_theory.is_mul_left_invariant.smul_invariant_measure MeasureTheory.IsMulLeftInvariant.smulInvariantMeasure
#align measure_theory.is_mul_left_invariant.vadd_invariant_measure MeasureTheory.IsMulLeftInvariant.vadd_invariant_measure

@[to_additive]
instance IsMulRightInvariant.to_smulInvariantMeasure_op [μ.IsMulRightInvariant] :
    SmulInvariantMeasure Gᵐᵒᵖ G μ :=
  ⟨fun x s hs => (measurePreserving_mul_right μ (MulOpposite.unop x)).measure_preimage hs⟩
#align measure_theory.is_mul_right_invariant.to_smul_invariant_measure_op MeasureTheory.IsMulRightInvariant.to_smulInvariantMeasure_op
#align measure_theory.is_mul_right_invariant.to_vadd_invariant_measure_op MeasureTheory.IsMulRightInvariant.to_vadd_invariant_measure_op

@[to_additive]
instance Subgroup.smulInvariantMeasure {G α : Type _} [Group G] [MulAction G α] [MeasurableSpace α]
    {μ : Measure α} [SmulInvariantMeasure G α μ] (H : Subgroup G) : SmulInvariantMeasure H α μ :=
  ⟨fun y s hs => by convert smul_invariant_measure.measure_preimage_smul μ (y : G) hs⟩
#align measure_theory.subgroup.smul_invariant_measure MeasureTheory.Subgroup.smulInvariantMeasure
#align measure_theory.subgroup.vadd_invariant_measure MeasureTheory.Subgroup.vadd_invariant_measure

/-- An alternative way to prove that `μ` is left invariant under multiplication. -/
@[to_additive " An alternative way to prove that `μ` is left invariant under addition. "]
theorem forall_measure_preimage_mul_iff (μ : Measure G) :
    (∀ (g : G) (A : Set G), MeasurableSet A → μ ((fun h => g * h) ⁻¹' A) = μ A) ↔
      IsMulLeftInvariant μ :=
  by
  trans ∀ g, map ((· * ·) g) μ = μ
  · simp_rw [measure.ext_iff]
    refine' forall_congr' fun g => forall_congr' fun A => forall_congr' fun hA => _
    rw [map_apply (measurable_const_mul g) hA]
  exact ⟨fun h => ⟨h⟩, fun h => h.1⟩
#align measure_theory.forall_measure_preimage_mul_iff MeasureTheory.forall_measure_preimage_mul_iff
#align measure_theory.forall_measure_preimage_add_iff MeasureTheory.forall_measure_preimage_add_iff

/-- An alternative way to prove that `μ` is right invariant under multiplication. -/
@[to_additive " An alternative way to prove that `μ` is right invariant under addition. "]
theorem forall_measure_preimage_mul_right_iff (μ : Measure G) :
    (∀ (g : G) (A : Set G), MeasurableSet A → μ ((fun h => h * g) ⁻¹' A) = μ A) ↔
      IsMulRightInvariant μ :=
  by
  trans ∀ g, map (· * g) μ = μ
  · simp_rw [measure.ext_iff]
    refine' forall_congr' fun g => forall_congr' fun A => forall_congr' fun hA => _
    rw [map_apply (measurable_mul_const g) hA]
  exact ⟨fun h => ⟨h⟩, fun h => h.1⟩
#align measure_theory.forall_measure_preimage_mul_right_iff MeasureTheory.forall_measure_preimage_mul_right_iff
#align measure_theory.forall_measure_preimage_add_right_iff MeasureTheory.forall_measure_preimage_add_right_iff

@[to_additive]
instance [IsMulLeftInvariant μ] [SigmaFinite μ] {H : Type _} [Mul H] {mH : MeasurableSpace H}
    {ν : Measure H} [MeasurableMul H] [IsMulLeftInvariant ν] [SigmaFinite ν] :
    IsMulLeftInvariant (μ.Prod ν) := by
  constructor
  rintro ⟨g, h⟩
  change map (Prod.map ((· * ·) g) ((· * ·) h)) (μ.prod ν) = μ.prod ν
  rw [← map_prod_map _ _ (measurable_const_mul g) (measurable_const_mul h),
    map_mul_left_eq_self μ g, map_mul_left_eq_self ν h]
  · rw [map_mul_left_eq_self μ g]; infer_instance
  · rw [map_mul_left_eq_self ν h]; infer_instance

@[to_additive]
instance [IsMulRightInvariant μ] [SigmaFinite μ] {H : Type _} [Mul H] {mH : MeasurableSpace H}
    {ν : Measure H} [MeasurableMul H] [IsMulRightInvariant ν] [SigmaFinite ν] :
    IsMulRightInvariant (μ.Prod ν) := by
  constructor
  rintro ⟨g, h⟩
  change map (Prod.map (· * g) (· * h)) (μ.prod ν) = μ.prod ν
  rw [← map_prod_map _ _ (measurable_mul_const g) (measurable_mul_const h),
    map_mul_right_eq_self μ g, map_mul_right_eq_self ν h]
  · rw [map_mul_right_eq_self μ g]; infer_instance
  · rw [map_mul_right_eq_self ν h]; infer_instance

@[to_additive]
theorem isMulLeftInvariant_map {H : Type _} [MeasurableSpace H] [Mul H] [MeasurableMul H]
    [IsMulLeftInvariant μ] (f : G →ₙ* H) (hf : Measurable f) (h_surj : Surjective f) :
    IsMulLeftInvariant (Measure.map f μ) :=
  by
  refine' ⟨fun h => _⟩
  rw [map_map (measurable_const_mul _) hf]
  obtain ⟨g, rfl⟩ := h_surj h
  conv_rhs => rw [← map_mul_left_eq_self μ g]
  rw [map_map hf (measurable_const_mul _)]
  congr 2
  ext y
  simp only [comp_app, map_mul]
#align measure_theory.is_mul_left_invariant_map MeasureTheory.isMulLeftInvariant_map
#align measure_theory.is_add_left_invariant_map MeasureTheory.is_add_left_invariant_map

end MeasurableMul

end Mul

section DivInvMonoid

variable [DivInvMonoid G]

@[to_additive]
theorem map_div_right_eq_self (μ : Measure G) [IsMulRightInvariant μ] (g : G) : map (· / g) μ = μ :=
  by simp_rw [div_eq_mul_inv, map_mul_right_eq_self μ g⁻¹]
#align measure_theory.map_div_right_eq_self MeasureTheory.map_div_right_eq_self
#align measure_theory.map_sub_right_eq_self MeasureTheory.map_sub_right_eq_self

end DivInvMonoid

section Group

variable [Group G] [MeasurableMul G]

@[to_additive]
theorem measurePreserving_div_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) :
    MeasurePreserving (· / g) μ μ := by simp_rw [div_eq_mul_inv, measure_preserving_mul_right μ g⁻¹]
#align measure_theory.measure_preserving_div_right MeasureTheory.measurePreserving_div_right
#align measure_theory.measure_preserving_sub_right MeasureTheory.measurePreserving_sub_right

/-- We shorten this from `measure_preimage_mul_left`, since left invariant is the preferred option
  for measures in this formalization. -/
@[simp,
  to_additive
      "We shorten this from `measure_preimage_add_left`, since left invariant is the\npreferred option for measures in this formalization."]
theorem measure_preimage_mul (μ : Measure G) [IsMulLeftInvariant μ] (g : G) (A : Set G) :
    μ ((fun h => g * h) ⁻¹' A) = μ A :=
  calc
    μ ((fun h => g * h) ⁻¹' A) = map (fun h => g * h) μ A :=
      ((MeasurableEquiv.mulLeft g).map_apply A).symm
    _ = μ A := by rw [map_mul_left_eq_self μ g]
    
#align measure_theory.measure_preimage_mul MeasureTheory.measure_preimage_mul
#align measure_theory.measure_preimage_add MeasureTheory.measure_preimage_add

@[simp, to_additive]
theorem measure_preimage_mul_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) (A : Set G) :
    μ ((fun h => h * g) ⁻¹' A) = μ A :=
  calc
    μ ((fun h => h * g) ⁻¹' A) = map (fun h => h * g) μ A :=
      ((MeasurableEquiv.mulRight g).map_apply A).symm
    _ = μ A := by rw [map_mul_right_eq_self μ g]
    
#align measure_theory.measure_preimage_mul_right MeasureTheory.measure_preimage_mul_right
#align measure_theory.measure_preimage_add_right MeasureTheory.measure_preimage_add_right

@[to_additive]
theorem map_mul_left_ae (μ : Measure G) [IsMulLeftInvariant μ] (x : G) :
    Filter.map (fun h => x * h) μ.ae = μ.ae :=
  ((MeasurableEquiv.mulLeft x).map_ae μ).trans <| congr_arg ae <| map_mul_left_eq_self μ x
#align measure_theory.map_mul_left_ae MeasureTheory.map_mul_left_ae
#align measure_theory.map_add_left_ae MeasureTheory.map_add_left_ae

@[to_additive]
theorem map_mul_right_ae (μ : Measure G) [IsMulRightInvariant μ] (x : G) :
    Filter.map (fun h => h * x) μ.ae = μ.ae :=
  ((MeasurableEquiv.mulRight x).map_ae μ).trans <| congr_arg ae <| map_mul_right_eq_self μ x
#align measure_theory.map_mul_right_ae MeasureTheory.map_mul_right_ae
#align measure_theory.map_add_right_ae MeasureTheory.map_add_right_ae

@[to_additive]
theorem map_div_right_ae (μ : Measure G) [IsMulRightInvariant μ] (x : G) :
    Filter.map (fun t => t / x) μ.ae = μ.ae :=
  ((MeasurableEquiv.divRight x).map_ae μ).trans <| congr_arg ae <| map_div_right_eq_self μ x
#align measure_theory.map_div_right_ae MeasureTheory.map_div_right_ae
#align measure_theory.map_sub_right_ae MeasureTheory.map_sub_right_ae

@[to_additive]
theorem eventually_mul_left_iff (μ : Measure G) [IsMulLeftInvariant μ] (t : G) {p : G → Prop} :
    (∀ᵐ x ∂μ, p (t * x)) ↔ ∀ᵐ x ∂μ, p x := by
  conv_rhs => rw [Filter.Eventually, ← map_mul_left_ae μ t]; rfl
#align measure_theory.eventually_mul_left_iff MeasureTheory.eventually_mul_left_iff
#align measure_theory.eventually_add_left_iff MeasureTheory.eventually_add_left_iff

@[to_additive]
theorem eventually_mul_right_iff (μ : Measure G) [IsMulRightInvariant μ] (t : G) {p : G → Prop} :
    (∀ᵐ x ∂μ, p (x * t)) ↔ ∀ᵐ x ∂μ, p x := by
  conv_rhs => rw [Filter.Eventually, ← map_mul_right_ae μ t]; rfl
#align measure_theory.eventually_mul_right_iff MeasureTheory.eventually_mul_right_iff
#align measure_theory.eventually_add_right_iff MeasureTheory.eventually_add_right_iff

@[to_additive]
theorem eventually_div_right_iff (μ : Measure G) [IsMulRightInvariant μ] (t : G) {p : G → Prop} :
    (∀ᵐ x ∂μ, p (x / t)) ↔ ∀ᵐ x ∂μ, p x := by
  conv_rhs => rw [Filter.Eventually, ← map_div_right_ae μ t]; rfl
#align measure_theory.eventually_div_right_iff MeasureTheory.eventually_div_right_iff
#align measure_theory.eventually_sub_right_iff MeasureTheory.eventually_sub_right_iff

end Group

namespace Measure

/-- The measure `A ↦ μ (A⁻¹)`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive "The measure `A ↦ μ (- A)`, where `- A` is the pointwise negation of `A`."]
protected def inv [Inv G] (μ : Measure G) : Measure G :=
  Measure.map inv μ
#align measure_theory.measure.inv MeasureTheory.Measure.inv
#align measure_theory.measure.neg MeasureTheory.Measure.neg

/-- A measure is invariant under negation if `- μ = μ`. Equivalently, this means that for all
measurable `A` we have `μ (- A) = μ A`, where `- A` is the pointwise negation of `A`. -/
class IsNegInvariant [Neg G] (μ : Measure G) : Prop where
  neg_eq_self : μ.neg = μ
#align measure_theory.measure.is_neg_invariant MeasureTheory.Measure.IsNegInvariant

/-- A measure is invariant under inversion if `μ⁻¹ = μ`. Equivalently, this means that for all
measurable `A` we have `μ (A⁻¹) = μ A`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive]
class IsInvInvariant [Inv G] (μ : Measure G) : Prop where
  inv_eq_self : μ.inv = μ
#align measure_theory.measure.is_inv_invariant MeasureTheory.Measure.IsInvInvariant
#align measure_theory.measure.is_neg_invariant MeasureTheory.Measure.IsNegInvariant

section Inv

variable [Inv G]

@[simp, to_additive]
theorem inv_eq_self (μ : Measure G) [IsInvInvariant μ] : μ.inv = μ :=
  IsInvInvariant.inv_eq_self
#align measure_theory.measure.inv_eq_self MeasureTheory.Measure.inv_eq_self
#align measure_theory.measure.neg_eq_self MeasureTheory.Measure.neg_eq_self

@[simp, to_additive]
theorem map_inv_eq_self (μ : Measure G) [IsInvInvariant μ] : map Inv.inv μ = μ :=
  IsInvInvariant.inv_eq_self
#align measure_theory.measure.map_inv_eq_self MeasureTheory.Measure.map_inv_eq_self
#align measure_theory.measure.map_neg_eq_self MeasureTheory.Measure.map_neg_eq_self

variable [MeasurableInv G]

@[to_additive]
theorem measurePreserving_inv (μ : Measure G) [IsInvInvariant μ] : MeasurePreserving Inv.inv μ μ :=
  ⟨measurable_inv, map_inv_eq_self μ⟩
#align measure_theory.measure.measure_preserving_inv MeasureTheory.Measure.measurePreserving_inv
#align measure_theory.measure.measure_preserving_neg MeasureTheory.Measure.measurePreserving_neg

end Inv

section InvolutiveInv

variable [InvolutiveInv G] [MeasurableInv G]

@[simp, to_additive]
theorem inv_apply (μ : Measure G) (s : Set G) : μ.inv s = μ s⁻¹ :=
  (MeasurableEquiv.inv G).map_apply s
#align measure_theory.measure.inv_apply MeasureTheory.Measure.inv_apply
#align measure_theory.measure.neg_apply MeasureTheory.Measure.neg_apply

@[simp, to_additive]
protected theorem inv_inv (μ : Measure G) : μ.inv.inv = μ :=
  (MeasurableEquiv.inv G).map_symm_map
#align measure_theory.measure.inv_inv MeasureTheory.Measure.inv_inv
#align measure_theory.measure.neg_neg MeasureTheory.Measure.neg_neg

@[simp, to_additive]
theorem measure_inv (μ : Measure G) [IsInvInvariant μ] (A : Set G) : μ A⁻¹ = μ A := by
  rw [← inv_apply, inv_eq_self]
#align measure_theory.measure.measure_inv MeasureTheory.Measure.measure_inv
#align measure_theory.measure.measure_neg MeasureTheory.Measure.measure_neg

@[to_additive]
theorem measure_preimage_inv (μ : Measure G) [IsInvInvariant μ] (A : Set G) :
    μ (Inv.inv ⁻¹' A) = μ A :=
  μ.measure_inv A
#align measure_theory.measure.measure_preimage_inv MeasureTheory.Measure.measure_preimage_inv
#align measure_theory.measure.measure_preimage_neg MeasureTheory.Measure.measure_preimage_neg

@[to_additive]
instance (μ : Measure G) [SigmaFinite μ] : SigmaFinite μ.inv :=
  (MeasurableEquiv.inv G).sigmaFinite_map ‹_›

end InvolutiveInv

section DivisionMonoid

variable [DivisionMonoid G] [MeasurableMul G] [MeasurableInv G] {μ : Measure G}

@[to_additive]
instance [IsMulLeftInvariant μ] : IsMulRightInvariant μ.inv :=
  by
  constructor
  intro g
  conv_rhs => rw [← map_mul_left_eq_self μ g⁻¹]
  simp_rw [measure.inv, map_map (measurable_mul_const g) measurable_inv,
    map_map measurable_inv (measurable_const_mul g⁻¹), Function.comp, mul_inv_rev, inv_inv]

@[to_additive]
instance [IsMulRightInvariant μ] : IsMulLeftInvariant μ.inv :=
  by
  constructor
  intro g
  conv_rhs => rw [← map_mul_right_eq_self μ g⁻¹]
  simp_rw [measure.inv, map_map (measurable_const_mul g) measurable_inv,
    map_map measurable_inv (measurable_mul_const g⁻¹), Function.comp, mul_inv_rev, inv_inv]

@[to_additive]
theorem measurePreserving_div_left (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (g : G) : MeasurePreserving (fun t => g / t) μ μ :=
  by
  simp_rw [div_eq_mul_inv]
  exact (measure_preserving_mul_left μ g).comp (measure_preserving_inv μ)
#align measure_theory.measure.measure_preserving_div_left MeasureTheory.Measure.measurePreserving_div_left
#align measure_theory.measure.measure_preserving_sub_left MeasureTheory.Measure.measurePreserving_sub_left

@[to_additive]
theorem map_div_left_eq_self (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G) :
    map (fun t => g / t) μ = μ :=
  (measurePreserving_div_left μ g).map_eq
#align measure_theory.measure.map_div_left_eq_self MeasureTheory.Measure.map_div_left_eq_self
#align measure_theory.measure.map_sub_left_eq_self MeasureTheory.Measure.map_sub_left_eq_self

@[to_additive]
theorem measurePreserving_mul_right_inv (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (g : G) : MeasurePreserving (fun t => (g * t)⁻¹) μ μ :=
  (measurePreserving_inv μ).comp <| measurePreserving_mul_left μ g
#align measure_theory.measure.measure_preserving_mul_right_inv MeasureTheory.Measure.measurePreserving_mul_right_inv
#align measure_theory.measure.measure_preserving_add_right_neg MeasureTheory.Measure.measurePreserving_add_right_neg

@[to_additive]
theorem map_mul_right_inv_eq_self (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (g : G) : map (fun t => (g * t)⁻¹) μ = μ :=
  (measurePreserving_mul_right_inv μ g).map_eq
#align measure_theory.measure.map_mul_right_inv_eq_self MeasureTheory.Measure.map_mul_right_inv_eq_self
#align measure_theory.measure.map_add_right_neg_eq_self MeasureTheory.Measure.map_add_right_neg_eq_self

end DivisionMonoid

section Group

variable [Group G] [MeasurableMul G] [MeasurableInv G] {μ : Measure G}

@[to_additive]
theorem map_div_left_ae (μ : Measure G) [IsMulLeftInvariant μ] [IsInvInvariant μ] (x : G) :
    Filter.map (fun t => x / t) μ.ae = μ.ae :=
  ((MeasurableEquiv.divLeft x).map_ae μ).trans <| congr_arg ae <| map_div_left_eq_self μ x
#align measure_theory.measure.map_div_left_ae MeasureTheory.Measure.map_div_left_ae
#align measure_theory.measure.map_sub_left_ae MeasureTheory.Measure.map_sub_left_ae

end Group

end Measure

section TopologicalGroup

variable [TopologicalSpace G] [BorelSpace G] {μ : Measure G} [Group G]

@[to_additive]
instance Measure.Regular.inv [ContinuousInv G] [T2Space G] [Regular μ] : Regular μ.inv :=
  Regular.map (Homeomorph.inv G)
#align measure_theory.measure.regular.inv MeasureTheory.Measure.Regular.inv
#align measure_theory.measure.regular.neg MeasureTheory.Measure.Regular.neg

variable [TopologicalGroup G]

@[to_additive]
theorem regular_inv_iff [T2Space G] : μ.inv.regular ↔ μ.regular :=
  by
  constructor
  · intro h; rw [← μ.inv_inv]; exact measure.regular.inv
  · intro h; exact measure.regular.inv
#align measure_theory.regular_inv_iff MeasureTheory.regular_inv_iff
#align measure_theory.regular_neg_iff MeasureTheory.regular_neg_iff

variable [IsMulLeftInvariant μ]

/-- If a left-invariant measure gives positive mass to a compact set, then it gives positive mass to
any open set. -/
@[to_additive
      "If a left-invariant measure gives positive mass to a compact set, then it gives\npositive mass to any open set."]
theorem openPosMeasure_of_mul_left_invariant_of_compact (K : Set G) (hK : IsCompact K)
    (h : μ K ≠ 0) : OpenPosMeasure μ :=
  by
  refine' ⟨fun U hU hne => _⟩
  contrapose! h
  rw [← nonpos_iff_eq_zero]
  rw [← hU.interior_eq] at hne
  obtain ⟨t, hKt⟩ : ∃ t : Finset G, K ⊆ ⋃ (g : G) (H : g ∈ t), (fun h : G => g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK hne
  calc
    μ K ≤ μ (⋃ (g : G) (H : g ∈ t), (fun h : G => g * h) ⁻¹' U) := measure_mono hKt
    _ ≤ ∑ g in t, μ ((fun h : G => g * h) ⁻¹' U) := (measure_bUnion_finset_le _ _)
    _ = 0 := by simp [measure_preimage_mul, h]
    
#align measure_theory.is_open_pos_measure_of_mul_left_invariant_of_compact MeasureTheory.openPosMeasure_of_mul_left_invariant_of_compact
#align measure_theory.is_open_pos_measure_of_add_left_invariant_of_compact MeasureTheory.openPosMeasure_of_add_left_invariant_of_compact

/-- A nonzero left-invariant regular measure gives positive mass to any open set. -/
@[to_additive "A nonzero left-invariant regular measure gives positive mass to any open set."]
theorem openPosMeasure_of_mul_left_invariant_of_regular [Regular μ] (h₀ : μ ≠ 0) :
    OpenPosMeasure μ :=
  let ⟨K, hK, h2K⟩ := Regular.exists_compact_not_null.mpr h₀
  openPosMeasure_of_mul_left_invariant_of_compact K hK h2K
#align measure_theory.is_open_pos_measure_of_mul_left_invariant_of_regular MeasureTheory.openPosMeasure_of_mul_left_invariant_of_regular
#align measure_theory.is_open_pos_measure_of_add_left_invariant_of_regular MeasureTheory.openPosMeasure_of_add_left_invariant_of_regular

@[to_additive]
theorem null_iff_of_isMulLeftInvariant [Regular μ] {s : Set G} (hs : IsOpen s) :
    μ s = 0 ↔ s = ∅ ∨ μ = 0 := by
  by_cases h3μ : μ = 0; · simp [h3μ]
  · haveI := is_open_pos_measure_of_mul_left_invariant_of_regular h3μ
    simp only [h3μ, or_false_iff, hs.measure_eq_zero_iff μ]
#align measure_theory.null_iff_of_is_mul_left_invariant MeasureTheory.null_iff_of_isMulLeftInvariant
#align measure_theory.null_iff_of_is_add_left_invariant MeasureTheory.null_iff_of_is_add_left_invariant

@[to_additive]
theorem measure_ne_zero_iff_nonempty_of_isMulLeftInvariant [Regular μ] (hμ : μ ≠ 0) {s : Set G}
    (hs : IsOpen s) : μ s ≠ 0 ↔ s.Nonempty := by
  simpa [null_iff_of_is_mul_left_invariant hs, hμ] using nonempty_iff_ne_empty.symm
#align measure_theory.measure_ne_zero_iff_nonempty_of_is_mul_left_invariant MeasureTheory.measure_ne_zero_iff_nonempty_of_isMulLeftInvariant
#align measure_theory.measure_ne_zero_iff_nonempty_of_is_add_left_invariant MeasureTheory.measure_ne_zero_iff_nonempty_of_is_add_left_invariant

@[to_additive]
theorem measure_pos_iff_nonempty_of_isMulLeftInvariant [Regular μ] (h3μ : μ ≠ 0) {s : Set G}
    (hs : IsOpen s) : 0 < μ s ↔ s.Nonempty :=
  pos_iff_ne_zero.trans <| measure_ne_zero_iff_nonempty_of_isMulLeftInvariant h3μ hs
#align measure_theory.measure_pos_iff_nonempty_of_is_mul_left_invariant MeasureTheory.measure_pos_iff_nonempty_of_isMulLeftInvariant
#align measure_theory.measure_pos_iff_nonempty_of_is_add_left_invariant MeasureTheory.measure_pos_iff_nonempty_of_is_add_left_invariant

/-- If a left-invariant measure gives finite mass to a nonempty open set, then it gives finite mass
to any compact set. -/
@[to_additive
      "If a left-invariant measure gives finite mass to a nonempty open set, then it gives\nfinite mass to any compact set."]
theorem measure_lt_top_of_isCompact_of_isMulLeftInvariant (U : Set G) (hU : IsOpen U)
    (h'U : U.Nonempty) (h : μ U ≠ ∞) {K : Set G} (hK : IsCompact K) : μ K < ∞ :=
  by
  rw [← hU.interior_eq] at h'U
  obtain ⟨t, hKt⟩ : ∃ t : Finset G, K ⊆ ⋃ (g : G) (H : g ∈ t), (fun h : G => g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK h'U
  calc
    μ K ≤ μ (⋃ (g : G) (H : g ∈ t), (fun h : G => g * h) ⁻¹' U) := measure_mono hKt
    _ ≤ ∑ g in t, μ ((fun h : G => g * h) ⁻¹' U) := (measure_bUnion_finset_le _ _)
    _ = Finset.card t * μ U := by simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.nat_ne_top _) h
    
#align measure_theory.measure_lt_top_of_is_compact_of_is_mul_left_invariant MeasureTheory.measure_lt_top_of_isCompact_of_isMulLeftInvariant
#align measure_theory.measure_lt_top_of_is_compact_of_is_add_left_invariant MeasureTheory.measure_lt_top_of_isCompact_of_is_add_left_invariant

/-- If a left-invariant measure gives finite mass to a set with nonempty interior, then
it gives finite mass to any compact set. -/
@[to_additive
      "If a left-invariant measure gives finite mass to a set with nonempty interior, then\nit gives finite mass to any compact set."]
theorem measure_lt_top_of_isCompact_of_is_mul_left_invariant' {U : Set G}
    (hU : (interior U).Nonempty) (h : μ U ≠ ∞) {K : Set G} (hK : IsCompact K) : μ K < ∞ :=
  measure_lt_top_of_isCompact_of_isMulLeftInvariant (interior U) isOpen_interior hU
    ((measure_mono interior_subset).trans_lt (lt_top_iff_ne_top.2 h)).Ne hK
#align measure_theory.measure_lt_top_of_is_compact_of_is_mul_left_invariant' MeasureTheory.measure_lt_top_of_isCompact_of_is_mul_left_invariant'
#align measure_theory.measure_lt_top_of_is_compact_of_is_add_left_invariant' MeasureTheory.measure_lt_top_of_isCompact_of_is_add_left_invariant'

/-- In a noncompact locally compact group, a left-invariant measure which is positive
on open sets has infinite mass. -/
@[simp,
  to_additive
      "In a noncompact locally compact additive group, a left-invariant measure which\nis positive on open sets has infinite mass."]
theorem measure_univ_of_isMulLeftInvariant [LocallyCompactSpace G] [NoncompactSpace G]
    (μ : Measure G) [OpenPosMeasure μ] [μ.IsMulLeftInvariant] : μ univ = ∞ :=
  by
  /- Consider a closed compact set `K` with nonempty interior. For any compact set `L`, one may
    find `g = g (L)` such that `L` is disjoint from `g • K`. Iterating this, one finds
    infinitely many translates of `K` which are disjoint from each other. As they all have the
    same positive mass, it follows that the space has infinite measure. -/
  obtain ⟨K, hK, Kclosed, Kint⟩ : ∃ K : Set G, IsCompact K ∧ IsClosed K ∧ (1 : G) ∈ interior K :=
    by
    rcases local_isCompact_isClosed_nhds_of_group (is_open_univ.mem_nhds (mem_univ (1 : G))) with
      ⟨K, hK⟩
    exact ⟨K, hK.1, hK.2.1, hK.2.2.2⟩
  have K_pos : 0 < μ K := measure_pos_of_nonempty_interior _ ⟨_, Kint⟩
  have A : ∀ L : Set G, IsCompact L → ∃ g : G, Disjoint L (g • K) := fun L hL =>
    exists_disjoint_smul_of_isCompact hL hK
  choose! g hg using A
  set L : ℕ → Set G := fun n => ((fun T => T ∪ g T • K)^[n]) K with hL
  have Lcompact : ∀ n, IsCompact (L n) := by
    intro n
    induction' n with n IH
    · exact hK
    · simp_rw [hL, iterate_succ']
      apply IsCompact.union IH (hK.smul (g (L n)))
  have Lclosed : ∀ n, IsClosed (L n) := by
    intro n
    induction' n with n IH
    · exact Kclosed
    · simp_rw [hL, iterate_succ']
      apply IsClosed.union IH (Kclosed.smul (g (L n)))
  have M : ∀ n, μ (L n) = (n + 1 : ℕ) * μ K := by
    intro n
    induction' n with n IH
    · simp only [L, one_mul, algebraMap.coe_one, iterate_zero, id.def]
    ·
      calc
        μ (L (n + 1)) = μ (L n) + μ (g (L n) • K) :=
          by
          simp_rw [hL, iterate_succ']
          exact measure_union' (hg _ (Lcompact _)) (Lclosed _).MeasurableSet
        _ = (n + 1 + 1 : ℕ) * μ K := by
          simp only [IH, measure_smul, add_mul, Nat.cast_add, algebraMap.coe_one, one_mul]
        
  have N : tendsto (fun n => μ (L n)) at_top (𝓝 (∞ * μ K)) :=
    by
    simp_rw [M]
    apply ENNReal.Tendsto.mul_const _ (Or.inl ENNReal.top_ne_zero)
    exact ennreal.tendsto_nat_nhds_top.comp (tendsto_add_at_top_nat _)
  simp only [ENNReal.top_mul', K_pos.ne', if_false] at N
  apply top_le_iff.1
  exact le_of_tendsto' N fun n => measure_mono (subset_univ _)
#align measure_theory.measure_univ_of_is_mul_left_invariant MeasureTheory.measure_univ_of_isMulLeftInvariant
#align measure_theory.measure_univ_of_is_add_left_invariant MeasureTheory.measure_univ_of_is_add_left_invariant

end TopologicalGroup

section CommSemigroup

variable [CommSemigroup G]

/-- In an abelian group every left invariant measure is also right-invariant.
  We don't declare the converse as an instance, since that would loop type-class inference, and
  we use `is_mul_left_invariant` as the default hypothesis in abelian groups. -/
@[to_additive IsAddLeftInvariant.is_add_right_invariant
      "In an abelian additive\ngroup every left invariant measure is also right-invariant. We don't declare the converse as an\ninstance, since that would loop type-class inference, and we use `is_add_left_invariant` as the\ndefault hypothesis in abelian groups."]
instance (priority := 100) IsMulLeftInvariant.isMulRightInvariant {μ : Measure G}
    [IsMulLeftInvariant μ] : IsMulRightInvariant μ :=
  ⟨fun g => by simp_rw [mul_comm, map_mul_left_eq_self]⟩
#align measure_theory.is_mul_left_invariant.is_mul_right_invariant MeasureTheory.IsMulLeftInvariant.isMulRightInvariant
#align is_add_left_invariant.is_add_right_invariant IsAddLeftInvariant.is_add_right_invariant

end CommSemigroup

section Haar

namespace Measure

/-- A measure on an additive group is an additive Haar measure if it is left-invariant, and gives
finite mass to compact sets and positive mass to open sets. -/
class IsAddHaarMeasure {G : Type _} [AddGroup G] [TopologicalSpace G] [MeasurableSpace G]
  (μ : Measure G) extends FiniteMeasureOnCompacts μ, IsAddLeftInvariant μ, OpenPosMeasure μ : Prop
#align measure_theory.measure.is_add_haar_measure MeasureTheory.Measure.IsAddHaarMeasure

/-- A measure on a group is a Haar measure if it is left-invariant, and gives finite mass to compact
sets and positive mass to open sets. -/
@[to_additive]
class IsHaarMeasure {G : Type _} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  (μ : Measure G) extends FiniteMeasureOnCompacts μ, IsMulLeftInvariant μ, OpenPosMeasure μ : Prop
#align measure_theory.measure.is_haar_measure MeasureTheory.Measure.IsHaarMeasure
#align measure_theory.measure.is_add_haar_measure MeasureTheory.Measure.IsAddHaarMeasure

/-- Record that a Haar measure on a locally compact space is locally finite. This is needed as the
fact that a measure which is finite on compacts is locally finite is not registered as an instance,
to avoid an instance loop.

See Note [lower instance priority]. -/
@[to_additive
      "Record that an additive Haar measure on a locally compact space is\nlocally finite. This is needed as the fact that a measure which is finite on compacts is locally\nfinite is not registered as an instance, to avoid an instance loop.\n\nSee Note [lower instance priority]"]
instance (priority := 100) locallyFiniteMeasure_of_isHaarMeasure {G : Type _} [Group G]
    [MeasurableSpace G] [TopologicalSpace G] [LocallyCompactSpace G] (μ : Measure G)
    [IsHaarMeasure μ] : LocallyFiniteMeasure μ :=
  locallyFiniteMeasure_of_finiteMeasureOnCompacts
#align measure_theory.measure.is_locally_finite_measure_of_is_haar_measure MeasureTheory.Measure.locallyFiniteMeasure_of_isHaarMeasure
#align measure_theory.measure.is_locally_finite_measure_of_is_add_haar_measure MeasureTheory.Measure.locallyFiniteMeasure_of_is_add_haar_measure

section

variable [Group G] [TopologicalSpace G] (μ : Measure G) [IsHaarMeasure μ]

@[simp, to_additive]
theorem haar_singleton [TopologicalGroup G] [BorelSpace G] (g : G) : μ {g} = μ {(1 : G)} :=
  by
  convert measure_preimage_mul μ g⁻¹ _
  simp only [mul_one, preimage_mul_left_singleton, inv_inv]
#align measure_theory.measure.haar_singleton MeasureTheory.Measure.haar_singleton
#align measure_theory.measure.add_haar_singleton MeasureTheory.Measure.add_haar_singleton

@[to_additive MeasureTheory.Measure.IsAddHaarMeasure.smul]
theorem IsHaarMeasure.smul {c : ℝ≥0∞} (cpos : c ≠ 0) (ctop : c ≠ ∞) : IsHaarMeasure (c • μ) :=
  { lt_top_of_isCompact := fun K hK => ENNReal.mul_lt_top Ctop hK.measure_lt_top.Ne
    to_openPosMeasure := openPosMeasure_smul μ cpos }
#align measure_theory.measure.is_haar_measure.smul MeasureTheory.Measure.IsHaarMeasure.smul
#align measure_theory.measure.is_add_haar_measure.smul MeasureTheory.Measure.IsAddHaarMeasure.smul

/-- If a left-invariant measure gives positive mass to some compact set with nonempty interior, then
it is a Haar measure. -/
@[to_additive
      "If a left-invariant measure gives positive mass to some compact set with nonempty\ninterior, then it is an additive Haar measure."]
theorem isHaarMeasure_of_isCompact_nonempty_interior [TopologicalGroup G] [BorelSpace G]
    (μ : Measure G) [IsMulLeftInvariant μ] (K : Set G) (hK : IsCompact K)
    (h'K : (interior K).Nonempty) (h : μ K ≠ 0) (h' : μ K ≠ ∞) : IsHaarMeasure μ :=
  { lt_top_of_isCompact := fun L hL =>
      measure_lt_top_of_isCompact_of_is_mul_left_invariant' h'K h' hL
    to_openPosMeasure := openPosMeasure_of_mul_left_invariant_of_compact K hK h }
#align measure_theory.measure.is_haar_measure_of_is_compact_nonempty_interior MeasureTheory.Measure.isHaarMeasure_of_isCompact_nonempty_interior
#align measure_theory.measure.is_add_haar_measure_of_is_compact_nonempty_interior MeasureTheory.Measure.is_add_haar_measure_of_isCompact_nonempty_interior

/-- The image of a Haar measure under a continuous surjective proper group homomorphism is again
a Haar measure. See also `mul_equiv.is_haar_measure_map`. -/
@[to_additive
      "The image of an additive Haar measure under a continuous surjective proper additive\ngroup homomorphism is again an additive Haar measure. See also\n`add_equiv.is_add_haar_measure_map`."]
theorem isHaarMeasure_map [BorelSpace G] [TopologicalGroup G] {H : Type _} [Group H]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [T2Space H] [TopologicalGroup H]
    (f : G →* H) (hf : Continuous f) (h_surj : Surjective f)
    (h_prop : Tendsto f (cocompact G) (cocompact H)) : IsHaarMeasure (Measure.map f μ) :=
  { to_isMulLeftInvariant := isMulLeftInvariant_map f.toMulHom hf.Measurable h_surj
    lt_top_of_isCompact := by
      intro K hK
      rw [map_apply hf.measurable hK.measurable_set]
      exact IsCompact.measure_lt_top ((⟨⟨f, hf⟩, h_prop⟩ : CocompactMap G H).isCompact_preimage hK)
    to_openPosMeasure := hf.openPosMeasure_map h_surj }
#align measure_theory.measure.is_haar_measure_map MeasureTheory.Measure.isHaarMeasure_map
#align measure_theory.measure.is_add_haar_measure_map MeasureTheory.Measure.is_add_haar_measure_map

/-- A convenience wrapper for `measure_theory.measure.is_haar_measure_map`. -/
@[to_additive "A convenience wrapper for `measure_theory.measure.is_add_haar_measure_map`."]
theorem MulEquiv.isHaarMeasure_map [BorelSpace G] [TopologicalGroup G] {H : Type _} [Group H]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [T2Space H] [TopologicalGroup H]
    (e : G ≃* H) (he : Continuous e) (hesymm : Continuous e.symm) :
    IsHaarMeasure (Measure.map e μ) :=
  isHaarMeasure_map μ (e : G →* H) he e.Surjective
    ({ e with } : G ≃ₜ H).toCocompactMap.cocompact_tendsto'
#align mul_equiv.is_haar_measure_map MulEquiv.isHaarMeasure_map
#align add_equiv.is_add_haar_measure_map AddEquiv.is_add_haar_measure_map

/-- A Haar measure on a σ-compact space is σ-finite.

See Note [lower instance priority] -/
@[to_additive
      "A Haar measure on a σ-compact space is σ-finite.\n\nSee Note [lower instance priority]"]
instance (priority := 100) IsHaarMeasure.sigmaFinite [SigmaCompactSpace G] : SigmaFinite μ :=
  ⟨⟨{   Set := compactCovering G
        set_mem := fun n => mem_univ _
        Finite := fun n => IsCompact.measure_lt_top <| isCompact_compactCovering G n
        spanning := iUnion_compactCovering G }⟩⟩
#align measure_theory.measure.is_haar_measure.sigma_finite MeasureTheory.Measure.IsHaarMeasure.sigmaFinite
#align measure_theory.measure.is_add_haar_measure.sigma_finite MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite

@[to_additive]
instance {G : Type _} [Group G] [TopologicalSpace G] {mG : MeasurableSpace G} {H : Type _} [Group H]
    [TopologicalSpace H] {mH : MeasurableSpace H} (μ : Measure G) (ν : Measure H) [IsHaarMeasure μ]
    [IsHaarMeasure ν] [SigmaFinite μ] [SigmaFinite ν] [MeasurableMul G] [MeasurableMul H] :
    IsHaarMeasure (μ.Prod ν) where

/-- If the neutral element of a group is not isolated, then a Haar measure on this group has
no atoms.

The additive version of this instance applies in particular to show that an additive Haar measure on
a nontrivial finite-dimensional real vector space has no atom. -/
@[to_additive
      "If the zero element of an additive group is not isolated, then an\nadditive Haar measure on this group has no atoms.\n\nThis applies in particular to show that an additive Haar measure on a nontrivial finite-dimensional\nreal vector space has no atom."]
instance (priority := 100) IsHaarMeasure.noAtoms [TopologicalGroup G] [BorelSpace G] [T1Space G]
    [LocallyCompactSpace G] [(𝓝[≠] (1 : G)).ne_bot] (μ : Measure G) [μ.IsHaarMeasure] : NoAtoms μ :=
  by
  suffices H : μ {(1 : G)} ≤ 0; · constructor; simp [le_bot_iff.1 H]
  obtain ⟨K, K_compact, K_int⟩ : ∃ K : Set G, IsCompact K ∧ (1 : G) ∈ interior K :=
    by
    rcases exists_compact_subset isOpen_univ (mem_univ (1 : G)) with ⟨K, hK⟩
    exact ⟨K, hK.1, hK.2.1⟩
  have K_inf : Set.Infinite K := infinite_of_mem_nhds (1 : G) (mem_interior_iff_mem_nhds.1 K_int)
  have μKlt : μ K ≠ ∞ := K_compact.measure_lt_top.ne
  have I : ∀ n : ℕ, μ {(1 : G)} ≤ μ K / n := by
    intro n
    obtain ⟨t, tK, tn⟩ : ∃ t : Finset G, ↑t ⊆ K ∧ t.card = n := K_inf.exists_subset_card_eq n
    have A : μ t ≤ μ K := measure_mono tK
    have B : μ t = n * μ {(1 : G)} :=
      by
      rw [← bUnion_of_singleton ↑t]
      change μ (⋃ x ∈ t, {x}) = n * μ {1}
      rw [@measure_bUnion_finset G G _ μ t fun i => {i}]
      · simp only [tn, Finset.sum_const, nsmul_eq_mul, haar_singleton]
      · intro x hx y hy xy
        simp only [on_fun, xy.symm, mem_singleton_iff, not_false_iff, disjoint_singleton_right]
      · intro b hb; exact measurable_set_singleton b
    rw [B] at A
    rwa [ENNReal.le_div_iff_mul_le _ (Or.inr μKlt), mul_comm]
    right
    apply (measure_pos_of_nonempty_interior μ ⟨_, K_int⟩).ne'
  have J : tendsto (fun n : ℕ => μ K / n) at_top (𝓝 (μ K / ∞)) :=
    ENNReal.Tendsto.const_div ENNReal.tendsto_nat_nhds_top (Or.inr μKlt)
  simp only [ENNReal.div_top] at J
  exact ge_of_tendsto' J I
#align measure_theory.measure.is_haar_measure.has_no_atoms MeasureTheory.Measure.IsHaarMeasure.noAtoms
#align measure_theory.measure.is_add_haar_measure.has_no_atoms MeasureTheory.Measure.IsAddHaarMeasure.noAtoms

end

end Measure

end Haar

end MeasureTheory

