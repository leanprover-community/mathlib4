/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov
-/
import Mathlib.MeasureTheory.Measure.Map

/-!
# Definitions about invariant measures

In this file we define typeclasses for measures invariant under (scalar) multiplication.

- `MeasureTheory.SMulInvariantMeasure M α μ`
  says that the measure `μ` is invariant under scalar multiplication by `c : M`;
- `MeasureTheory.VAddInvariantMeasure M α μ` is the additive version of this typeclass;
- `MeasureTheory.Measure.IsMulLeftInvariant μ`, `MeasureTheory.Measure.IsMulRightInvariant μ`
  say that the measure `μ` is invariant under multiplication on the left and on the right,
  respectively.
- `MeasureTheory.Measure.IsAddLeftInvariant μ`, `MeasureTheory.Measure.IsAddRightInvariant μ`
  are the additive versions of these typeclasses.

For basic facts about the first two typeclasses, see `Mathlib/MeasureTheory/Group/Action`.
For facts about left/right-invariant measures, see `Mathlib/MeasureTheory/Group/Measure`.

## Implementation Notes

The `smul`/`vadd` typeclasses and the left/right multiplication typeclasses
were defined by different people with different tastes,
so the former explicitly use measures of the preimages,
while the latter use `MeasureTheory.Measure.map`.

If the left/right multiplication is measurable
(which is the case in most if not all interesting examples),
these definitions are equivalent.

The definitions that use `MeasureTheory.Measure.map`
imply that the left (resp., right) multiplication is `AEMeasurable`.
-/

assert_not_exists Module.Basis

namespace MeasureTheory

/-- A measure `μ : Measure α` is invariant under an additive action of `M` on `α` if for any
measurable set `s : Set α` and `c : M`, the measure of its preimage under `fun x => c +ᵥ x` is equal
to the measure of `s`. -/
class VAddInvariantMeasure (M α : Type*) [VAdd M α] {_ : MeasurableSpace α} (μ : Measure α) :
  Prop where
  measure_preimage_vadd : ∀ (c : M) ⦃s : Set α⦄, MeasurableSet s → μ ((fun x => c +ᵥ x) ⁻¹' s) = μ s

/-- A measure `μ : Measure α` is invariant under a multiplicative action of `M` on `α` if for any
measurable set `s : Set α` and `c : M`, the measure of its preimage under `fun x => c • x` is equal
to the measure of `s`. -/
@[to_additive, mk_iff smulInvariantMeasure_iff]
class SMulInvariantMeasure (M α : Type*) [SMul M α] {_ : MeasurableSpace α} (μ : Measure α) :
  Prop where
  measure_preimage_smul : ∀ (c : M) ⦃s : Set α⦄, MeasurableSet s → μ ((fun x => c • x) ⁻¹' s) = μ s

attribute [to_additive] smulInvariantMeasure_iff

namespace Measure

variable {G : Type*} [MeasurableSpace G]

/-- A measure `μ` on a measurable additive group is left invariant
  if the measure of left translations of a set are equal to the measure of the set itself. -/
class IsAddLeftInvariant [Add G] (μ : Measure G) : Prop where
  map_add_left_eq_self : ∀ g : G, map (g + ·) μ = μ

/-- A measure `μ` on a measurable group is left invariant
  if the measure of left translations of a set are equal to the measure of the set itself. -/
@[to_additive existing]
class IsMulLeftInvariant [Mul G] (μ : Measure G) : Prop where
  map_mul_left_eq_self : ∀ g : G, map (g * ·) μ = μ

/-- A measure `μ` on a measurable additive group is right invariant
  if the measure of right translations of a set are equal to the measure of the set itself. -/
class IsAddRightInvariant [Add G] (μ : Measure G) : Prop where
  map_add_right_eq_self : ∀ g : G, map (· + g) μ = μ

/-- A measure `μ` on a measurable group is right invariant
  if the measure of right translations of a set are equal to the measure of the set itself. -/
@[to_additive existing]
class IsMulRightInvariant [Mul G] (μ : Measure G) : Prop where
  map_mul_right_eq_self : ∀ g : G, map (· * g) μ = μ

variable {μ : Measure G}

@[to_additive]
instance IsMulLeftInvariant.smulInvariantMeasure [Mul G] [IsMulLeftInvariant μ] :
    SMulInvariantMeasure G G μ :=
  ⟨fun _x _s hs => measure_preimage_of_map_eq_self (map_mul_left_eq_self _) hs.nullMeasurableSet⟩

@[to_additive]
instance [Monoid G] (s : Submonoid G) [IsMulLeftInvariant μ] :
    SMulInvariantMeasure {x // x ∈ s} G μ :=
  ⟨fun ⟨x, _⟩ _ h ↦ IsMulLeftInvariant.smulInvariantMeasure.1 x h⟩

@[to_additive]
instance IsMulRightInvariant.toSMulInvariantMeasure_op [Mul G] [μ.IsMulRightInvariant] :
    SMulInvariantMeasure Gᵐᵒᵖ G μ :=
  ⟨fun _x _s hs => measure_preimage_of_map_eq_self (map_mul_right_eq_self _) hs.nullMeasurableSet⟩

end Measure

end MeasureTheory
