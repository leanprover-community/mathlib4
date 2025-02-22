/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.ContinuousMap.CocompactMap
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Measures on Groups

We develop some properties of measures on (topological) groups

* We define properties on measures: measures that are left or right invariant w.r.t. multiplication.
* We define the measure `μ.inv : A ↦ μ(A⁻¹)` and show that it is right invariant iff
  `μ` is left invariant.
* We define a class `IsHaarMeasure μ`, requiring that the measure `μ` is left-invariant, finite
  on compact sets, and positive on open sets.

We also give analogues of all these notions in the additive world.
-/


noncomputable section

open scoped NNReal ENNReal Pointwise Topology

open Inv Set Function MeasureTheory.Measure Filter

variable {G H : Type*} [MeasurableSpace G] [MeasurableSpace H]

namespace MeasureTheory

section Mul

variable [Mul G] {μ : Measure G}

@[to_additive]
theorem map_mul_left_eq_self (μ : Measure G) [IsMulLeftInvariant μ] (g : G) :
    map (g * ·) μ = μ :=
  IsMulLeftInvariant.map_mul_left_eq_self g

@[to_additive]
theorem map_mul_right_eq_self (μ : Measure G) [IsMulRightInvariant μ] (g : G) : map (· * g) μ = μ :=
  IsMulRightInvariant.map_mul_right_eq_self g

@[to_additive MeasureTheory.isAddLeftInvariant_smul]
instance isMulLeftInvariant_smul [IsMulLeftInvariant μ] (c : ℝ≥0∞) : IsMulLeftInvariant (c • μ) :=
  ⟨fun g => by rw [Measure.map_smul, map_mul_left_eq_self]⟩

@[to_additive MeasureTheory.isAddRightInvariant_smul]
instance isMulRightInvariant_smul [IsMulRightInvariant μ] (c : ℝ≥0∞) :
    IsMulRightInvariant (c • μ) :=
  ⟨fun g => by rw [Measure.map_smul, map_mul_right_eq_self]⟩

@[to_additive MeasureTheory.isAddLeftInvariant_smul_nnreal]
instance isMulLeftInvariant_smul_nnreal [IsMulLeftInvariant μ] (c : ℝ≥0) :
    IsMulLeftInvariant (c • μ) :=
  MeasureTheory.isMulLeftInvariant_smul (c : ℝ≥0∞)

@[to_additive MeasureTheory.isAddRightInvariant_smul_nnreal]
instance isMulRightInvariant_smul_nnreal [IsMulRightInvariant μ] (c : ℝ≥0) :
    IsMulRightInvariant (c • μ) :=
  MeasureTheory.isMulRightInvariant_smul (c : ℝ≥0∞)

section MeasurableMul

variable [MeasurableMul G]

@[to_additive]
theorem measurePreserving_mul_left (μ : Measure G) [IsMulLeftInvariant μ] (g : G) :
    MeasurePreserving (g * ·) μ μ :=
  ⟨measurable_const_mul g, map_mul_left_eq_self μ g⟩

@[to_additive]
theorem MeasurePreserving.mul_left (μ : Measure G) [IsMulLeftInvariant μ] (g : G) {X : Type*}
    [MeasurableSpace X] {μ' : Measure X} {f : X → G} (hf : MeasurePreserving f μ' μ) :
    MeasurePreserving (fun x => g * f x) μ' μ :=
  (measurePreserving_mul_left μ g).comp hf

@[to_additive]
theorem measurePreserving_mul_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) :
    MeasurePreserving (· * g) μ μ :=
  ⟨measurable_mul_const g, map_mul_right_eq_self μ g⟩

@[to_additive]
theorem MeasurePreserving.mul_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) {X : Type*}
    [MeasurableSpace X] {μ' : Measure X} {f : X → G} (hf : MeasurePreserving f μ' μ) :
    MeasurePreserving (fun x => f x * g) μ' μ :=
  (measurePreserving_mul_right μ g).comp hf

@[to_additive]
instance Subgroup.smulInvariantMeasure {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
    {μ : Measure α} [SMulInvariantMeasure G α μ] (H : Subgroup G) : SMulInvariantMeasure H α μ :=
  ⟨fun y s hs => by convert SMulInvariantMeasure.measure_preimage_smul (μ := μ) (y : G) hs⟩

/-- An alternative way to prove that `μ` is left invariant under multiplication. -/
@[to_additive " An alternative way to prove that `μ` is left invariant under addition. "]
theorem forall_measure_preimage_mul_iff (μ : Measure G) :
    (∀ (g : G) (A : Set G), MeasurableSet A → μ ((fun h => g * h) ⁻¹' A) = μ A) ↔
      IsMulLeftInvariant μ := by
  trans ∀ g, map (g * ·) μ = μ
  · simp_rw [Measure.ext_iff]
    refine forall_congr' fun g => forall_congr' fun A => forall_congr' fun hA => ?_
    rw [map_apply (measurable_const_mul g) hA]
  exact ⟨fun h => ⟨h⟩, fun h => h.1⟩

/-- An alternative way to prove that `μ` is right invariant under multiplication. -/
@[to_additive " An alternative way to prove that `μ` is right invariant under addition. "]
theorem forall_measure_preimage_mul_right_iff (μ : Measure G) :
    (∀ (g : G) (A : Set G), MeasurableSet A → μ ((fun h => h * g) ⁻¹' A) = μ A) ↔
      IsMulRightInvariant μ := by
  trans ∀ g, map (· * g) μ = μ
  · simp_rw [Measure.ext_iff]
    refine forall_congr' fun g => forall_congr' fun A => forall_congr' fun hA => ?_
    rw [map_apply (measurable_mul_const g) hA]
  exact ⟨fun h => ⟨h⟩, fun h => h.1⟩

@[to_additive]
instance Measure.prod.instIsMulLeftInvariant [IsMulLeftInvariant μ] [SFinite μ] {H : Type*}
    [Mul H] {mH : MeasurableSpace H} {ν : Measure H} [MeasurableMul H] [IsMulLeftInvariant ν]
    [SFinite ν] : IsMulLeftInvariant (μ.prod ν) := by
  constructor
  rintro ⟨g, h⟩
  change map (Prod.map (g * ·) (h * ·)) (μ.prod ν) = μ.prod ν
  rw [← map_prod_map _ _ (measurable_const_mul g) (measurable_const_mul h),
    map_mul_left_eq_self μ g, map_mul_left_eq_self ν h]

@[to_additive]
instance Measure.prod.instIsMulRightInvariant [IsMulRightInvariant μ] [SFinite μ] {H : Type*}
    [Mul H] {mH : MeasurableSpace H} {ν : Measure H} [MeasurableMul H] [IsMulRightInvariant ν]
    [SFinite ν] : IsMulRightInvariant (μ.prod ν) := by
  constructor
  rintro ⟨g, h⟩
  change map (Prod.map (· * g) (· * h)) (μ.prod ν) = μ.prod ν
  rw [← map_prod_map _ _ (measurable_mul_const g) (measurable_mul_const h),
    map_mul_right_eq_self μ g, map_mul_right_eq_self ν h]

@[to_additive]
theorem isMulLeftInvariant_map {H : Type*} [MeasurableSpace H] [Mul H] [MeasurableMul H]
    [IsMulLeftInvariant μ] (f : G →ₙ* H) (hf : Measurable f) (h_surj : Surjective f) :
    IsMulLeftInvariant (Measure.map f μ) := by
  refine ⟨fun h => ?_⟩
  rw [map_map (measurable_const_mul _) hf]
  obtain ⟨g, rfl⟩ := h_surj h
  conv_rhs => rw [← map_mul_left_eq_self μ g]
  rw [map_map hf (measurable_const_mul _)]
  congr 2
  ext y
  simp only [comp_apply, map_mul]

end MeasurableMul

end Mul

section Semigroup

variable [Semigroup G] [MeasurableMul G] {μ : Measure G}

/-- The image of a left invariant measure under a left action is left invariant, assuming that
the action preserves multiplication. -/
@[to_additive "The image of a left invariant measure under a left additive action is left invariant,
assuming that the action preserves addition."]
theorem isMulLeftInvariant_map_smul
    {α} [SMul α G] [SMulCommClass α G G] [MeasurableSpace α] [MeasurableSMul α G]
    [IsMulLeftInvariant μ] (a : α) :
    IsMulLeftInvariant (map (a • · : G → G) μ) :=
  (forall_measure_preimage_mul_iff _).1 fun x _ hs =>
    (smulInvariantMeasure_map_smul μ a).measure_preimage_smul x hs

/-- The image of a right invariant measure under a left action is right invariant, assuming that
the action preserves multiplication. -/
@[to_additive "The image of a right invariant measure under a left additive action is right
 invariant, assuming that the action preserves addition."]
theorem isMulRightInvariant_map_smul
    {α} [SMul α G] [SMulCommClass α Gᵐᵒᵖ G] [MeasurableSpace α] [MeasurableSMul α G]
    [IsMulRightInvariant μ] (a : α) :
    IsMulRightInvariant (map (a • · : G → G) μ) :=
  (forall_measure_preimage_mul_right_iff _).1 fun x _ hs =>
    (smulInvariantMeasure_map_smul μ a).measure_preimage_smul (MulOpposite.op x) hs

/-- The image of a left invariant measure under right multiplication is left invariant. -/
@[to_additive isMulLeftInvariant_map_add_right
"The image of a left invariant measure under right addition is left invariant."]
instance isMulLeftInvariant_map_mul_right [IsMulLeftInvariant μ] (g : G) :
    IsMulLeftInvariant (map (· * g) μ) :=
  isMulLeftInvariant_map_smul (MulOpposite.op g)

/-- The image of a right invariant measure under left multiplication is right invariant. -/
@[to_additive isMulRightInvariant_map_add_left
"The image of a right invariant measure under left addition is right invariant."]
instance isMulRightInvariant_map_mul_left [IsMulRightInvariant μ] (g : G) :
    IsMulRightInvariant (map (g * ·) μ) :=
  isMulRightInvariant_map_smul g

end Semigroup

section DivInvMonoid

variable [DivInvMonoid G]

@[to_additive]
theorem map_div_right_eq_self (μ : Measure G) [IsMulRightInvariant μ] (g : G) :
    map (· / g) μ = μ := by simp_rw [div_eq_mul_inv, map_mul_right_eq_self μ g⁻¹]

end DivInvMonoid

section Group

variable [Group G] [MeasurableMul G]

@[to_additive]
theorem measurePreserving_div_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) :
    MeasurePreserving (· / g) μ μ := by simp_rw [div_eq_mul_inv, measurePreserving_mul_right μ g⁻¹]

/-- We shorten this from `measure_preimage_mul_left`, since left invariant is the preferred option
  for measures in this formalization. -/
@[to_additive (attr := simp)
"We shorten this from `measure_preimage_add_left`, since left invariant is the preferred option for
measures in this formalization."]
theorem measure_preimage_mul (μ : Measure G) [IsMulLeftInvariant μ] (g : G) (A : Set G) :
    μ ((fun h => g * h) ⁻¹' A) = μ A :=
  calc
    μ ((fun h => g * h) ⁻¹' A) = map (fun h => g * h) μ A :=
      ((MeasurableEquiv.mulLeft g).map_apply A).symm
    _ = μ A := by rw [map_mul_left_eq_self μ g]

@[to_additive (attr := simp)]
theorem measure_preimage_mul_right (μ : Measure G) [IsMulRightInvariant μ] (g : G) (A : Set G) :
    μ ((fun h => h * g) ⁻¹' A) = μ A :=
  calc
    μ ((fun h => h * g) ⁻¹' A) = map (fun h => h * g) μ A :=
      ((MeasurableEquiv.mulRight g).map_apply A).symm
    _ = μ A := by rw [map_mul_right_eq_self μ g]

@[to_additive]
theorem map_mul_left_ae (μ : Measure G) [IsMulLeftInvariant μ] (x : G) :
    Filter.map (fun h => x * h) (ae μ) = ae μ :=
  ((MeasurableEquiv.mulLeft x).map_ae μ).trans <| congr_arg ae <| map_mul_left_eq_self μ x

@[to_additive]
theorem map_mul_right_ae (μ : Measure G) [IsMulRightInvariant μ] (x : G) :
    Filter.map (fun h => h * x) (ae μ) = ae μ :=
  ((MeasurableEquiv.mulRight x).map_ae μ).trans <| congr_arg ae <| map_mul_right_eq_self μ x

@[to_additive]
theorem map_div_right_ae (μ : Measure G) [IsMulRightInvariant μ] (x : G) :
    Filter.map (fun t => t / x) (ae μ) = ae μ :=
  ((MeasurableEquiv.divRight x).map_ae μ).trans <| congr_arg ae <| map_div_right_eq_self μ x

@[to_additive]
theorem eventually_mul_left_iff (μ : Measure G) [IsMulLeftInvariant μ] (t : G) {p : G → Prop} :
    (∀ᵐ x ∂μ, p (t * x)) ↔ ∀ᵐ x ∂μ, p x := by
  conv_rhs => rw [Filter.Eventually, ← map_mul_left_ae μ t]
  rfl

@[to_additive]
theorem eventually_mul_right_iff (μ : Measure G) [IsMulRightInvariant μ] (t : G) {p : G → Prop} :
    (∀ᵐ x ∂μ, p (x * t)) ↔ ∀ᵐ x ∂μ, p x := by
  conv_rhs => rw [Filter.Eventually, ← map_mul_right_ae μ t]
  rfl

@[to_additive]
theorem eventually_div_right_iff (μ : Measure G) [IsMulRightInvariant μ] (t : G) {p : G → Prop} :
    (∀ᵐ x ∂μ, p (x / t)) ↔ ∀ᵐ x ∂μ, p x := by
  conv_rhs => rw [Filter.Eventually, ← map_div_right_ae μ t]
  rfl

end Group

namespace Measure

-- TODO: noncomputable has to be specified explicitly. https://github.com/leanprover-community/mathlib4/issues/1074 (item 8)

/-- The measure `A ↦ μ (A⁻¹)`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive "The measure `A ↦ μ (- A)`, where `- A` is the pointwise negation of `A`."]
protected noncomputable def inv [Inv G] (μ : Measure G) : Measure G :=
  Measure.map inv μ

/-- A measure is invariant under negation if `- μ = μ`. Equivalently, this means that for all
measurable `A` we have `μ (- A) = μ A`, where `- A` is the pointwise negation of `A`. -/
class IsNegInvariant [Neg G] (μ : Measure G) : Prop where
  neg_eq_self : μ.neg = μ

/-- A measure is invariant under inversion if `μ⁻¹ = μ`. Equivalently, this means that for all
measurable `A` we have `μ (A⁻¹) = μ A`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[to_additive existing]
class IsInvInvariant [Inv G] (μ : Measure G) : Prop where
  inv_eq_self : μ.inv = μ

section Inv

variable [Inv G]

@[to_additive]
theorem inv_def (μ : Measure G) : μ.inv = Measure.map inv μ := rfl

@[to_additive (attr := simp)]
theorem inv_eq_self (μ : Measure G) [IsInvInvariant μ] : μ.inv = μ :=
  IsInvInvariant.inv_eq_self

@[to_additive (attr := simp)]
theorem map_inv_eq_self (μ : Measure G) [IsInvInvariant μ] : map Inv.inv μ = μ :=
  IsInvInvariant.inv_eq_self

variable [MeasurableInv G]

@[to_additive]
theorem measurePreserving_inv (μ : Measure G) [IsInvInvariant μ] : MeasurePreserving Inv.inv μ μ :=
  ⟨measurable_inv, map_inv_eq_self μ⟩

@[to_additive]
instance inv.instSFinite (μ : Measure G) [SFinite μ] : SFinite μ.inv := by
  rw [Measure.inv]; infer_instance

end Inv

section InvolutiveInv

variable [InvolutiveInv G] [MeasurableInv G]

@[to_additive (attr := simp)]
theorem inv_apply (μ : Measure G) (s : Set G) : μ.inv s = μ s⁻¹ :=
  (MeasurableEquiv.inv G).map_apply s

@[to_additive (attr := simp)]
protected theorem inv_inv (μ : Measure G) : μ.inv.inv = μ :=
  (MeasurableEquiv.inv G).map_symm_map

@[to_additive (attr := simp)]
theorem measure_inv (μ : Measure G) [IsInvInvariant μ] (A : Set G) : μ A⁻¹ = μ A := by
  rw [← inv_apply, inv_eq_self]

@[to_additive]
theorem measure_preimage_inv (μ : Measure G) [IsInvInvariant μ] (A : Set G) :
    μ (Inv.inv ⁻¹' A) = μ A :=
  μ.measure_inv A

@[to_additive]
instance inv.instSigmaFinite (μ : Measure G) [SigmaFinite μ] : SigmaFinite μ.inv :=
  (MeasurableEquiv.inv G).sigmaFinite_map

end InvolutiveInv

section DivisionMonoid

variable [DivisionMonoid G] [MeasurableMul G] [MeasurableInv G] {μ : Measure G}

@[to_additive]
instance inv.instIsMulRightInvariant [IsMulLeftInvariant μ] : IsMulRightInvariant μ.inv := by
  constructor
  intro g
  conv_rhs => rw [← map_mul_left_eq_self μ g⁻¹]
  simp_rw [Measure.inv, map_map (measurable_mul_const g) measurable_inv,
    map_map measurable_inv (measurable_const_mul g⁻¹), Function.comp_def, mul_inv_rev, inv_inv]

@[to_additive]
instance inv.instIsMulLeftInvariant [IsMulRightInvariant μ] : IsMulLeftInvariant μ.inv := by
  constructor
  intro g
  conv_rhs => rw [← map_mul_right_eq_self μ g⁻¹]
  simp_rw [Measure.inv, map_map (measurable_const_mul g) measurable_inv,
    map_map measurable_inv (measurable_mul_const g⁻¹), Function.comp_def, mul_inv_rev, inv_inv]

@[to_additive]
theorem measurePreserving_div_left (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (g : G) : MeasurePreserving (fun t => g / t) μ μ := by
  simp_rw [div_eq_mul_inv]
  exact (measurePreserving_mul_left μ g).comp (measurePreserving_inv μ)

@[to_additive]
theorem map_div_left_eq_self (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ] (g : G) :
    map (fun t => g / t) μ = μ :=
  (measurePreserving_div_left μ g).map_eq

@[to_additive]
theorem measurePreserving_mul_right_inv (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (g : G) : MeasurePreserving (fun t => (g * t)⁻¹) μ μ :=
  (measurePreserving_inv μ).comp <| measurePreserving_mul_left μ g

@[to_additive]
theorem map_mul_right_inv_eq_self (μ : Measure G) [IsInvInvariant μ] [IsMulLeftInvariant μ]
    (g : G) : map (fun t => (g * t)⁻¹) μ = μ :=
  (measurePreserving_mul_right_inv μ g).map_eq

end DivisionMonoid

section Group

variable [Group G] [MeasurableMul G] [MeasurableInv G] {μ : Measure G}

@[to_additive]
theorem map_div_left_ae (μ : Measure G) [IsMulLeftInvariant μ] [IsInvInvariant μ] (x : G) :
    Filter.map (fun t => x / t) (ae μ) = ae μ :=
  ((MeasurableEquiv.divLeft x).map_ae μ).trans <| congr_arg ae <| map_div_left_eq_self μ x

end Group

end Measure

section TopologicalGroup

variable [TopologicalSpace G] [BorelSpace G] {μ : Measure G} [Group G]

@[to_additive]
instance Measure.IsFiniteMeasureOnCompacts.inv [ContinuousInv G] [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts μ.inv :=
  IsFiniteMeasureOnCompacts.map μ (Homeomorph.inv G)

@[to_additive]
instance Measure.IsOpenPosMeasure.inv [ContinuousInv G] [IsOpenPosMeasure μ] :
    IsOpenPosMeasure μ.inv :=
  (Homeomorph.inv G).continuous.isOpenPosMeasure_map (Homeomorph.inv G).surjective

@[to_additive]
instance Measure.Regular.inv [ContinuousInv G] [Regular μ] : Regular μ.inv :=
  Regular.map (Homeomorph.inv G)

@[to_additive]
instance Measure.InnerRegular.inv [ContinuousInv G] [InnerRegular μ] : InnerRegular μ.inv :=
  InnerRegular.map (Homeomorph.inv G)

/-- The image of an inner regular measure under map of a left action is again inner regular. -/
@[to_additive
   "The image of a inner regular measure under map of a left additive action is again
    inner regular"]
instance innerRegular_map_smul {α} [Monoid α] [MulAction α G] [ContinuousConstSMul α G]
    [InnerRegular μ] (a : α) : InnerRegular (Measure.map (a • · : G → G) μ) :=
  InnerRegular.map_of_continuous (continuous_const_smul a)

/-- The image of an inner regular measure under left multiplication is again inner regular. -/
@[to_additive "The image of an inner regular measure under left addition is again inner regular."]
instance innerRegular_map_mul_left [TopologicalGroup G] [InnerRegular μ] (g : G) :
    InnerRegular (Measure.map (g * ·) μ) := InnerRegular.map_of_continuous (continuous_mul_left g)

/-- The image of an inner regular measure under right multiplication is again inner regular. -/
@[to_additive "The image of an inner regular measure under right addition is again inner regular."]
instance innerRegular_map_mul_right [TopologicalGroup G] [InnerRegular μ] (g : G) :
    InnerRegular (Measure.map (· * g) μ) := InnerRegular.map_of_continuous (continuous_mul_right g)

variable [TopologicalGroup G]

@[to_additive]
theorem regular_inv_iff : μ.inv.Regular ↔ μ.Regular :=
  Regular.map_iff (Homeomorph.inv G)

@[to_additive]
theorem innerRegular_inv_iff : μ.inv.InnerRegular ↔ μ.InnerRegular :=
  InnerRegular.map_iff (Homeomorph.inv G)

/-- Continuity of the measure of translates of a compact set: Given a compact set `k` in a
topological group, for `g` close enough to the origin, `μ (g • k \ k)` is arbitrarily small. -/
@[to_additive]
lemma eventually_nhds_one_measure_smul_diff_lt [LocallyCompactSpace G]
    [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ] {k : Set G}
    (hk : IsCompact k) (h'k : IsClosed k) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∀ᶠ g in 𝓝 (1 : G), μ (g • k \ k) < ε := by
  obtain ⟨U, hUk, hU, hμUk⟩ : ∃ (U : Set G), k ⊆ U ∧ IsOpen U ∧ μ U < μ k + ε :=
    hk.exists_isOpen_lt_add hε
  obtain ⟨V, hV1, hVkU⟩ : ∃ V ∈ 𝓝 (1 : G), V * k ⊆ U := compact_open_separated_mul_left hk hU hUk
  filter_upwards [hV1] with g hg
  calc
    μ (g • k \ k) ≤ μ (U \ k) := by
      gcongr
      exact (smul_set_subset_smul hg).trans hVkU
    _ < ε := measure_diff_lt_of_lt_add h'k.nullMeasurableSet hUk hk.measure_lt_top.ne hμUk

/-- Continuity of the measure of translates of a compact set:
Given a closed compact set `k` in a topological group,
the measure of `g • k \ k` tends to zero as `g` tends to `1`. -/
@[to_additive]
lemma tendsto_measure_smul_diff_isCompact_isClosed [LocallyCompactSpace G]
    [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ] {k : Set G}
    (hk : IsCompact k) (h'k : IsClosed k) :
    Tendsto (fun g : G ↦ μ (g • k \ k)) (𝓝 1) (𝓝 0) :=
  ENNReal.nhds_zero_basis.tendsto_right_iff.mpr <| fun _ h ↦
    eventually_nhds_one_measure_smul_diff_lt hk h'k h.ne'

section IsMulLeftInvariant
variable [IsMulLeftInvariant μ]

/-- If a left-invariant measure gives positive mass to a compact set, then it gives positive mass to
any open set. -/
@[to_additive
"If a left-invariant measure gives positive mass to a compact set, then it gives positive mass to
any open set."]
theorem isOpenPosMeasure_of_mulLeftInvariant_of_compact (K : Set G) (hK : IsCompact K)
    (h : μ K ≠ 0) : IsOpenPosMeasure μ := by
  refine ⟨fun U hU hne => ?_⟩
  contrapose! h
  rw [← nonpos_iff_eq_zero]
  rw [← hU.interior_eq] at hne
  obtain ⟨t, hKt⟩ : ∃ t : Finset G, K ⊆ ⋃ (g : G) (_ : g ∈ t), (fun h : G => g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK hne
  calc
    μ K ≤ μ (⋃ (g : G) (_ : g ∈ t), (fun h : G => g * h) ⁻¹' U) := measure_mono hKt
    _ ≤ ∑ g ∈ t, μ ((fun h : G => g * h) ⁻¹' U) := measure_biUnion_finset_le _ _
    _ = 0 := by simp [measure_preimage_mul, h]

/-- A nonzero left-invariant regular measure gives positive mass to any open set. -/
@[to_additive "A nonzero left-invariant regular measure gives positive mass to any open set."]
instance (priority := 80) isOpenPosMeasure_of_mulLeftInvariant_of_regular [Regular μ] [NeZero μ] :
    IsOpenPosMeasure μ :=
  let ⟨K, hK, h2K⟩ := Regular.exists_isCompact_not_null.mpr (NeZero.ne μ)
  isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK h2K

/-- A nonzero left-invariant inner regular measure gives positive mass to any open set. -/
@[to_additive "A nonzero left-invariant inner regular measure gives positive mass to any open set."]
instance (priority := 80) isOpenPosMeasure_of_mulLeftInvariant_of_innerRegular
    [InnerRegular μ] [NeZero μ] :
    IsOpenPosMeasure μ :=
  let ⟨K, hK, h2K⟩ := InnerRegular.exists_isCompact_not_null.mpr (NeZero.ne μ)
  isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK h2K

@[to_additive]
theorem null_iff_of_isMulLeftInvariant [Regular μ] {s : Set G} (hs : IsOpen s) :
    μ s = 0 ↔ s = ∅ ∨ μ = 0 := by
  rcases eq_zero_or_neZero μ with rfl|hμ
  · simp
  · simp only [or_false, hs.measure_eq_zero_iff μ, NeZero.ne μ]

@[to_additive]
theorem measure_ne_zero_iff_nonempty_of_isMulLeftInvariant [Regular μ] (hμ : μ ≠ 0) {s : Set G}
    (hs : IsOpen s) : μ s ≠ 0 ↔ s.Nonempty := by
  simpa [null_iff_of_isMulLeftInvariant (μ := μ) hs, hμ] using nonempty_iff_ne_empty.symm

@[to_additive]
theorem measure_pos_iff_nonempty_of_isMulLeftInvariant [Regular μ] (h3μ : μ ≠ 0) {s : Set G}
    (hs : IsOpen s) : 0 < μ s ↔ s.Nonempty :=
  pos_iff_ne_zero.trans <| measure_ne_zero_iff_nonempty_of_isMulLeftInvariant h3μ hs

/-- If a left-invariant measure gives finite mass to a nonempty open set, then it gives finite mass
to any compact set. -/
@[to_additive
"If a left-invariant measure gives finite mass to a nonempty open set, then it gives finite mass to
any compact set."]
theorem measure_lt_top_of_isCompact_of_isMulLeftInvariant (U : Set G) (hU : IsOpen U)
    (h'U : U.Nonempty) (h : μ U ≠ ∞) {K : Set G} (hK : IsCompact K) : μ K < ∞ := by
  rw [← hU.interior_eq] at h'U
  obtain ⟨t, hKt⟩ : ∃ t : Finset G, K ⊆ ⋃ g ∈ t, (fun h : G => g * h) ⁻¹' U :=
    compact_covered_by_mul_left_translates hK h'U
  exact (measure_mono hKt).trans_lt <| measure_biUnion_lt_top t.finite_toSet <| by simp [h.lt_top]

/-- If a left-invariant measure gives finite mass to a set with nonempty interior, then
it gives finite mass to any compact set. -/
@[to_additive
"If a left-invariant measure gives finite mass to a set with nonempty interior, then it gives finite
mass to any compact set."]
theorem measure_lt_top_of_isCompact_of_isMulLeftInvariant' {U : Set G}
    (hU : (interior U).Nonempty) (h : μ U ≠ ∞) {K : Set G} (hK : IsCompact K) : μ K < ∞ :=
  measure_lt_top_of_isCompact_of_isMulLeftInvariant (interior U) isOpen_interior hU
    ((measure_mono interior_subset).trans_lt (lt_top_iff_ne_top.2 h)).ne hK

/-- In a noncompact locally compact group, a left-invariant measure which is positive
on open sets has infinite mass. -/
@[to_additive (attr := simp)
"In a noncompact locally compact additive group, a left-invariant measure which is positive on open
sets has infinite mass."]
theorem measure_univ_of_isMulLeftInvariant [WeaklyLocallyCompactSpace G] [NoncompactSpace G]
    (μ : Measure G) [IsOpenPosMeasure μ] [μ.IsMulLeftInvariant] : μ univ = ∞ := by
  /- Consider a closed compact set `K` with nonempty interior. For any compact set `L`, one may
    find `g = g (L)` such that `L` is disjoint from `g • K`. Iterating this, one finds
    infinitely many translates of `K` which are disjoint from each other. As they all have the
    same positive mass, it follows that the space has infinite measure. -/
  obtain ⟨K, K1, hK, Kclosed⟩ : ∃ K ∈ 𝓝 (1 : G), IsCompact K ∧ IsClosed K :=
    exists_mem_nhds_isCompact_isClosed 1
  have K_pos : 0 < μ K := measure_pos_of_mem_nhds μ K1
  have A : ∀ L : Set G, IsCompact L → ∃ g : G, Disjoint L (g • K) := fun L hL =>
    exists_disjoint_smul_of_isCompact hL hK
  choose! g hg using A
  set L : ℕ → Set G := fun n => (fun T => T ∪ g T • K)^[n] K
  have Lcompact : ∀ n, IsCompact (L n) := by
    intro n
    induction' n with n IH
    · exact hK
    · simp_rw [L, iterate_succ']
      apply IsCompact.union IH (hK.smul (g (L n)))
  have Lclosed : ∀ n, IsClosed (L n) := by
    intro n
    induction' n with n IH
    · exact Kclosed
    · simp_rw [L, iterate_succ']
      apply IsClosed.union IH (Kclosed.smul (g (L n)))
  have M : ∀ n, μ (L n) = (n + 1 : ℕ) * μ K := by
    intro n
    induction' n with n IH
    · simp only [L, one_mul, Nat.cast_one, iterate_zero, id, Nat.zero_add]
    · calc
        μ (L (n + 1)) = μ (L n) + μ (g (L n) • K) := by
          simp_rw [L, iterate_succ']
          exact measure_union' (hg _ (Lcompact _)) (Lclosed _).measurableSet
        _ = (n + 1 + 1 : ℕ) * μ K := by
          simp only [IH, measure_smul, add_mul, Nat.cast_add, Nat.cast_one, one_mul]
  have N : Tendsto (fun n => μ (L n)) atTop (𝓝 (∞ * μ K)) := by
    simp_rw [M]
    apply ENNReal.Tendsto.mul_const _ (Or.inl ENNReal.top_ne_zero)
    exact ENNReal.tendsto_nat_nhds_top.comp (tendsto_add_atTop_nat _)
  simp only [ENNReal.top_mul', K_pos.ne', if_false] at N
  apply top_le_iff.1
  exact le_of_tendsto' N fun n => measure_mono (subset_univ _)

@[to_additive]
lemma _root_.MeasurableSet.mul_closure_one_eq {s : Set G} (hs : MeasurableSet s) :
    s * (closure {1} : Set G) = s := by
  induction s, hs using MeasurableSet.induction_on_open with
  | isOpen U hU => exact hU.mul_closure_one_eq
  | compl t _ iht => exact compl_mul_closure_one_eq_iff.2 iht
  | iUnion f _ _ ihf => simp_rw [iUnion_mul f, ihf]

@[to_additive (attr := simp)]
lemma measure_mul_closure_one (s : Set G) (μ : Measure G) :
    μ (s * (closure {1} : Set G)) = μ s := by
  apply le_antisymm ?_ (measure_mono (subset_mul_closure_one s))
  conv_rhs => rw [measure_eq_iInf]
  simp only [le_iInf_iff]
  intro t kt t_meas
  apply measure_mono
  rw [← t_meas.mul_closure_one_eq]
  exact smul_subset_smul_right kt

end IsMulLeftInvariant

@[to_additive]
lemma innerRegularWRT_isCompact_isClosed_measure_ne_top_of_group [h : InnerRegularCompactLTTop μ] :
    InnerRegularWRT μ (fun s ↦ IsCompact s ∧ IsClosed s) (fun s ↦ MeasurableSet s ∧ μ s ≠ ∞) := by
  intro s ⟨s_meas, μs⟩ r hr
  rcases h.innerRegular ⟨s_meas, μs⟩ r hr with ⟨K, Ks, K_comp, hK⟩
  refine ⟨closure K, ?_, ⟨K_comp.closure, isClosed_closure⟩, ?_⟩
  · exact IsCompact.closure_subset_measurableSet K_comp s_meas Ks
  · rwa [K_comp.measure_closure]

end TopologicalGroup

section CommSemigroup

variable [CommSemigroup G]

/-- In an abelian group every left invariant measure is also right-invariant.
  We don't declare the converse as an instance, since that would loop type-class inference, and
  we use `IsMulLeftInvariant` as the default hypothesis in abelian groups. -/
@[to_additive IsAddLeftInvariant.isAddRightInvariant
"In an abelian additive group every left invariant measure is also right-invariant. We don't declare
the converse as an instance, since that would loop type-class inference, and we use
`IsAddLeftInvariant` as the default hypothesis in abelian groups."]
instance (priority := 100) IsMulLeftInvariant.isMulRightInvariant {μ : Measure G}
    [IsMulLeftInvariant μ] : IsMulRightInvariant μ :=
  ⟨fun g => by simp_rw [mul_comm, map_mul_left_eq_self]⟩

end CommSemigroup

section Haar

namespace Measure

/-- A measure on an additive group is an additive Haar measure if it is left-invariant, and
gives finite mass to compact sets and positive mass to open sets.

Textbooks generally require an additional regularity assumption to ensure nice behavior on
arbitrary locally compact groups. Use `[IsAddHaarMeasure μ] [Regular μ]` or
`[IsAddHaarMeasure μ] [InnerRegular μ]` in these situations. Note that a Haar measure in our
sense is automatically regular and inner regular on second countable locally compact groups, as
checked just below this definition. -/
class IsAddHaarMeasure {G : Type*} [AddGroup G] [TopologicalSpace G] [MeasurableSpace G]
  (μ : Measure G) extends IsFiniteMeasureOnCompacts μ, IsAddLeftInvariant μ, IsOpenPosMeasure μ :
  Prop

/-- A measure on a group is a Haar measure if it is left-invariant, and gives finite mass to
compact sets and positive mass to open sets.

Textbooks generally require an additional regularity assumption to ensure nice behavior on
arbitrary locally compact groups. Use `[IsHaarMeasure μ] [Regular μ]` or
`[IsHaarMeasure μ] [InnerRegular μ]` in these situations. Note that a Haar measure in our
sense is automatically regular and inner regular on second countable locally compact groups, as
checked just below this definition. -/
@[to_additive existing]
class IsHaarMeasure {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  (μ : Measure G) extends IsFiniteMeasureOnCompacts μ, IsMulLeftInvariant μ, IsOpenPosMeasure μ :
  Prop

variable [Group G] [TopologicalSpace G] (μ : Measure G) [IsHaarMeasure μ]

@[to_additive (attr := simp)]
theorem haar_singleton [ContinuousMul G] [BorelSpace G] (g : G) : μ {g} = μ {(1 : G)} := by
  convert measure_preimage_mul μ g⁻¹ _
  simp only [mul_one, preimage_mul_left_singleton, inv_inv]

@[to_additive IsAddHaarMeasure.smul]
theorem IsHaarMeasure.smul {c : ℝ≥0∞} (cpos : c ≠ 0) (ctop : c ≠ ∞) : IsHaarMeasure (c • μ) :=
  { lt_top_of_isCompact := fun _K hK => ENNReal.mul_lt_top ctop.lt_top hK.measure_lt_top
    toIsOpenPosMeasure := isOpenPosMeasure_smul μ cpos }

/-- If a left-invariant measure gives positive mass to some compact set with nonempty interior, then
it is a Haar measure. -/
@[to_additive
"If a left-invariant measure gives positive mass to some compact set with nonempty interior, then
it is an additive Haar measure."]
theorem isHaarMeasure_of_isCompact_nonempty_interior [TopologicalGroup G] [BorelSpace G]
    (μ : Measure G) [IsMulLeftInvariant μ] (K : Set G) (hK : IsCompact K)
    (h'K : (interior K).Nonempty) (h : μ K ≠ 0) (h' : μ K ≠ ∞) : IsHaarMeasure μ :=
  { lt_top_of_isCompact := fun _L hL =>
      measure_lt_top_of_isCompact_of_isMulLeftInvariant' h'K h' hL
    toIsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_compact K hK h }

/-- The image of a Haar measure under a continuous surjective proper group homomorphism is again
a Haar measure. See also `MulEquiv.isHaarMeasure_map` and `ContinuousMulEquiv.isHaarMeasure_map`. -/
@[to_additive
"The image of an additive Haar measure under a continuous surjective proper additive group
homomorphism is again an additive Haar measure. See also `AddEquiv.isAddHaarMeasure_map`,
`ContinuousAddEquiv.isAddHaarMeasure_map` and `ContinuousLinearEquiv.isAddHaarMeasure_map`."]
theorem isHaarMeasure_map [BorelSpace G] [TopologicalGroup G] {H : Type*} [Group H]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [TopologicalGroup H]
    (f : G →* H) (hf : Continuous f) (h_surj : Surjective f)
    (h_prop : Tendsto f (cocompact G) (cocompact H)) : IsHaarMeasure (Measure.map f μ) :=
  { toIsMulLeftInvariant := isMulLeftInvariant_map f.toMulHom hf.measurable h_surj
    lt_top_of_isCompact := by
      intro K hK
      rw [← hK.measure_closure, map_apply hf.measurable isClosed_closure.measurableSet]
      set g : CocompactMap G H := ⟨⟨f, hf⟩, h_prop⟩
      exact IsCompact.measure_lt_top (g.isCompact_preimage_of_isClosed hK.closure isClosed_closure)
    toIsOpenPosMeasure := hf.isOpenPosMeasure_map h_surj }

/-- The image of a finite Haar measure under a continuous surjective group homomorphism is again
a Haar measure. See also `isHaarMeasure_map`. -/
@[to_additive
"The image of a finite additive Haar measure under a continuous surjective additive group
homomorphism is again an additive Haar measure. See also `isAddHaarMeasure_map`."]
theorem isHaarMeasure_map_of_isFiniteMeasure
    [BorelSpace G] [ContinuousMul G] {H : Type*} [Group H]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [ContinuousMul H] [IsFiniteMeasure μ]
    (f : G →* H) (hf : Continuous f) (h_surj : Surjective f) :
    IsHaarMeasure (Measure.map f μ) where
  toIsMulLeftInvariant := isMulLeftInvariant_map f.toMulHom hf.measurable h_surj
  toIsOpenPosMeasure := hf.isOpenPosMeasure_map h_surj

/-- The image of a Haar measure under map of a left action is again a Haar measure. -/
@[to_additive
   "The image of a Haar measure under map of a left additive action is again a Haar measure"]
instance isHaarMeasure_map_smul {α} [BorelSpace G] [TopologicalGroup G]
    [Group α] [MulAction α G] [SMulCommClass α G G] [MeasurableSpace α] [MeasurableSMul α G]
    [ContinuousConstSMul α G] (a : α) : IsHaarMeasure (Measure.map (a • · : G → G) μ) where
  toIsMulLeftInvariant := isMulLeftInvariant_map_smul _
  lt_top_of_isCompact K hK := by
    let F := (Homeomorph.smul a (α := G)).toMeasurableEquiv
    change map F μ K < ∞
    rw [F.map_apply K]
    exact IsCompact.measure_lt_top <| (Homeomorph.isCompact_preimage (Homeomorph.smul a)).2 hK
  toIsOpenPosMeasure :=
    (continuous_const_smul a).isOpenPosMeasure_map (MulAction.surjective a)

/-- The image of a Haar measure under right multiplication is again a Haar measure. -/
@[to_additive isHaarMeasure_map_add_right
  "The image of a Haar measure under right addition is again a Haar measure."]
instance isHaarMeasure_map_mul_right [BorelSpace G] [TopologicalGroup G] (g : G) :
    IsHaarMeasure (Measure.map (· * g) μ) :=
  isHaarMeasure_map_smul μ (MulOpposite.op g)

/-- A convenience wrapper for `MeasureTheory.Measure.isHaarMeasure_map`. -/
@[to_additive "A convenience wrapper for `MeasureTheory.Measure.isAddHaarMeasure_map`."]
nonrec theorem _root_.MulEquiv.isHaarMeasure_map [BorelSpace G] [TopologicalGroup G] {H : Type*}
    [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalGroup H] (e : G ≃* H) (he : Continuous e) (hesymm : Continuous e.symm) :
    IsHaarMeasure (Measure.map e μ) :=
  let f : G ≃ₜ H := .mk e
  #adaptation_note /-- https://github.com/leanprover/lean4/pull/6024
  we needed to write `e.toMonoidHom` instead of just `e`, to avoid unification issues.
  -/
  isHaarMeasure_map μ e.toMonoidHom he e.surjective f.isClosedEmbedding.tendsto_cocompact

/--
A convenience wrapper for MeasureTheory.Measure.isHaarMeasure_map.
-/
@[to_additive "A convenience wrapper for MeasureTheory.Measure.isAddHaarMeasure_map.
"]
instance _root_.ContinuousMulEquiv.isHaarMeasure_map [BorelSpace G] [TopologicalGroup G] {H : Type*}
    [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [TopologicalGroup H] (e : G ≃ₜ* H) : (μ.map e).IsHaarMeasure :=
  e.toMulEquiv.isHaarMeasure_map μ e.continuous e.symm.continuous

/-- A convenience wrapper for MeasureTheory.Measure.isAddHaarMeasure_map`. -/
instance _root_.ContinuousLinearEquiv.isAddHaarMeasure_map
    {E F R S : Type*} [Semiring R] [Semiring S]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module S F]
    [TopologicalSpace E] [TopologicalAddGroup E] [TopologicalSpace F]
    [TopologicalAddGroup F]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (L : E ≃SL[σ] F) (μ : Measure E) [IsAddHaarMeasure μ] :
    IsAddHaarMeasure (μ.map L) :=
  AddEquiv.isAddHaarMeasure_map _ (L : E ≃+ F) L.continuous L.symm.continuous

/-- A Haar measure on a σ-compact space is σ-finite.

See Note [lower instance priority] -/
@[to_additive
"A Haar measure on a σ-compact space is σ-finite.

See Note [lower instance priority]"]
instance (priority := 100) IsHaarMeasure.sigmaFinite [SigmaCompactSpace G] : SigmaFinite μ :=
  ⟨⟨{   set := compactCovering G
        set_mem := fun _ => mem_univ _
        finite := fun n => IsCompact.measure_lt_top <| isCompact_compactCovering G n
        spanning := iUnion_compactCovering G }⟩⟩

@[to_additive]
instance prod.instIsHaarMeasure {G : Type*} [Group G] [TopologicalSpace G] {_ : MeasurableSpace G}
    {H : Type*} [Group H] [TopologicalSpace H] {_ : MeasurableSpace H} (μ : Measure G)
    (ν : Measure H) [IsHaarMeasure μ] [IsHaarMeasure ν] [SFinite μ] [SFinite ν]
    [MeasurableMul G] [MeasurableMul H] : IsHaarMeasure (μ.prod ν) where

/-- If the neutral element of a group is not isolated, then a Haar measure on this group has
no atoms.

The additive version of this instance applies in particular to show that an additive Haar
measure on a nontrivial finite-dimensional real vector space has no atom. -/
@[to_additive
"If the zero element of an additive group is not isolated, then an additive Haar measure on this
group has no atoms.

This applies in particular to show that an additive Haar measure on a nontrivial
finite-dimensional real vector space has no atom."]
instance (priority := 100) IsHaarMeasure.noAtoms [TopologicalGroup G] [BorelSpace G] [T1Space G]
    [WeaklyLocallyCompactSpace G] [(𝓝[≠] (1 : G)).NeBot] (μ : Measure G) [μ.IsHaarMeasure] :
    NoAtoms μ := by
  cases eq_or_ne (μ 1) 0 with
  | inl h => constructor; simpa
  | inr h =>
    obtain ⟨K, K_compact, K_nhds⟩ : ∃ K : Set G, IsCompact K ∧ K ∈ 𝓝 1 := exists_compact_mem_nhds 1
    have K_inf : Set.Infinite K := infinite_of_mem_nhds (1 : G) K_nhds
    exact absurd (K_inf.meas_eq_top ⟨_, h, fun x _ ↦ (haar_singleton _ _).ge⟩)
      K_compact.measure_lt_top.ne

end Measure

end Haar

end MeasureTheory
