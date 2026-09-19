/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.VectorMeasure.Basic

/-!

# Operations on vector measures

This file defines conversions between ordinary measures and vector measures, together with
pushforwards, maps on the range, restrictions, and restriction to a sub-σ-algebra.

## Main definitions

* `Measure.toSignedMeasure`, `Measure.toENNRealVectorMeasure`, and
  `VectorMeasure.ennrealToMeasure` convert between measures and vector measures.
* `MeasureTheory.VectorMeasure.map` is the pushforward of a vector measure along a function.
* `VectorMeasure.mapRange` composes a vector measure with a continuous additive homomorphism.
* `MeasureTheory.VectorMeasure.restrict` is the restriction of a vector measure on some set.
* `VectorMeasure.trim` restricts a vector measure to a smaller measurable space.
-/

@[expose] public section

noncomputable section

open NNReal ENNReal

namespace MeasureTheory

variable {α β : Type*} {m : MeasurableSpace α}

open Set

namespace Measure

open scoped Classical in
/-- A finite measure coerced into a real function is a signed measure. -/
def toSignedMeasure (μ : Measure α) [hμ : IsFiniteMeasure μ] : SignedMeasure α where
  measureOf' s := if MeasurableSet s then μ.real s else 0
  empty' := by simp
  not_measurable' _ hi := ite_eq_right hi
  m_iUnion' f hf₁ hf₂ := by
    simp only [*, MeasurableSet.iUnion hf₁, ite_true, measure_iUnion hf₂ hf₁, measureReal_def]
    rw [ENNReal.tsum_toReal_eq]
    exacts [(summable_measure_toReal hf₁ hf₂).hasSum, fun _ ↦ measure_ne_top _ _]

open scoped Classical in
@[simp]
theorem toSignedMeasure_apply (μ : Measure α) [hμ : IsFiniteMeasure μ] (i : Set α) :
    μ.toSignedMeasure i = if MeasurableSet i then μ.real i else 0 := rfl

theorem toSignedMeasure_apply_measurable {μ : Measure α} [IsFiniteMeasure μ] {i : Set α}
    (hi : MeasurableSet i) : μ.toSignedMeasure i = μ.real i :=
  ite_eq_left hi

-- Without this lemma, `singularPart_neg` in
-- `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean` is extremely slow
theorem toSignedMeasure_congr {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ = ν) : μ.toSignedMeasure = ν.toSignedMeasure := by
  congr

theorem toSignedMeasure_eq_toSignedMeasure_iff {μ ν : Measure α} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : μ.toSignedMeasure = ν.toSignedMeasure ↔ μ = ν := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · ext1 i hi
    have : μ.toSignedMeasure i = ν.toSignedMeasure i := by rw [h]
    rwa [toSignedMeasure_apply_measurable hi, toSignedMeasure_apply_measurable hi,
        measureReal_eq_measureReal_iff] at this
  · congr

@[simp]
theorem toSignedMeasure_zero : (0 : Measure α).toSignedMeasure = 0 := by
  ext i hi
  simp [hi]

@[simp]
theorem toSignedMeasure_add (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ + ν).toSignedMeasure = μ.toSignedMeasure + ν.toSignedMeasure := by
  ext i hi
  rw [toSignedMeasure_apply_measurable hi, measureReal_add_apply,
    _root_.add_apply, toSignedMeasure_apply_measurable hi,
    toSignedMeasure_apply_measurable hi]

@[simp]
theorem toSignedMeasure_smul (μ : Measure α) [IsFiniteMeasure μ] (r : ℝ≥0) :
    (r • μ).toSignedMeasure = r • μ.toSignedMeasure := by
  ext i hi
  rw [toSignedMeasure_apply_measurable hi, _root_.smul_apply,
    toSignedMeasure_apply_measurable hi, measureReal_nnreal_smul_apply]
  rfl

open scoped Classical in
/-- A measure is a vector measure over `ℝ≥0∞`. -/
def toENNRealVectorMeasure (μ : Measure α) : VectorMeasure α ℝ≥0∞ where
  measureOf' i := if MeasurableSet i then μ i else 0
  empty' := by simp
  not_measurable' _ hi := ite_eq_right hi
  m_iUnion' _ hf₁ hf₂ := by
    rw [Summable.hasSum_iff ENNReal.summable, ite_eq_left (MeasurableSet.iUnion hf₁),
      MeasureTheory.measure_iUnion hf₂ hf₁]
    exact tsum_congr fun n => ite_eq_left (hf₁ n)

open scoped Classical in
@[simp]
theorem toENNRealVectorMeasure_apply (μ : Measure α) (i : Set α) :
    μ.toENNRealVectorMeasure i = if MeasurableSet i then μ i else 0 := rfl

theorem toENNRealVectorMeasure_apply_measurable {μ : Measure α} {i : Set α} (hi : MeasurableSet i) :
    μ.toENNRealVectorMeasure i = μ i :=
  ite_eq_left hi

@[simp]
theorem toENNRealVectorMeasure_zero : (0 : Measure α).toENNRealVectorMeasure = 0 := by
  ext i
  simp

@[simp]
theorem toENNRealVectorMeasure_add (μ ν : Measure α) :
    (μ + ν).toENNRealVectorMeasure = μ.toENNRealVectorMeasure + ν.toENNRealVectorMeasure := by
  refine MeasureTheory.VectorMeasure.ext fun i hi => ?_
  rw [toENNRealVectorMeasure_apply_measurable hi, add_apply, _root_.add_apply,
    toENNRealVectorMeasure_apply_measurable hi, toENNRealVectorMeasure_apply_measurable hi]

theorem toSignedMeasure_sub_apply {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {i : Set α} (hi : MeasurableSet i) :
    (μ.toSignedMeasure - ν.toSignedMeasure) i = μ.real i - ν.real i := by
  rw [_root_.sub_apply, toSignedMeasure_apply_measurable hi,
    Measure.toSignedMeasure_apply_measurable hi]

end Measure

namespace VectorMeasure

open Measure

section

/-- A vector measure over `ℝ≥0∞` is a measure. -/
def ennrealToMeasure {_ : MeasurableSpace α} (v : VectorMeasure α ℝ≥0∞) : Measure α :=
  ofMeasurable (fun s _ => v s) v.empty fun _ hf₁ hf₂ => v.of_disjoint_iUnion hf₁ hf₂

theorem ennrealToMeasure_apply {m : MeasurableSpace α} {v : VectorMeasure α ℝ≥0∞} {s : Set α}
    (hs : MeasurableSet s) : ennrealToMeasure v s = v s := by
  rw [ennrealToMeasure, ofMeasurable_apply _ hs]

@[simp]
theorem ennrealToMeasure_zero : ennrealToMeasure (0 : VectorMeasure α ℝ≥0∞) = 0 := by
  simp [ennrealToMeasure]

@[simp]
theorem _root_.MeasureTheory.Measure.toENNRealVectorMeasure_ennrealToMeasure
    (μ : VectorMeasure α ℝ≥0∞) :
    toENNRealVectorMeasure (ennrealToMeasure μ) = μ := ext fun s hs => by
  rw [toENNRealVectorMeasure_apply_measurable hs, ennrealToMeasure_apply hs]

@[simp]
theorem ennrealToMeasure_toENNRealVectorMeasure (μ : Measure α) :
    ennrealToMeasure (toENNRealVectorMeasure μ) = μ := Measure.ext fun s hs => by
  rw [ennrealToMeasure_apply hs, toENNRealVectorMeasure_apply_measurable hs]

/-- The equiv between `VectorMeasure α ℝ≥0∞` and `Measure α` formed by
`MeasureTheory.VectorMeasure.ennrealToMeasure` and
`MeasureTheory.Measure.toENNRealVectorMeasure`. -/
@[simps]
def equivMeasure [MeasurableSpace α] : VectorMeasure α ℝ≥0∞ ≃ Measure α where
  toFun := ennrealToMeasure
  invFun := toENNRealVectorMeasure
  left_inv := toENNRealVectorMeasure_ennrealToMeasure
  right_inv := ennrealToMeasure_toENNRealVectorMeasure

end

section

variable {mα : MeasurableSpace α} [MeasurableSpace β]
variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable (v : VectorMeasure α M)

open scoped Classical in
/-- The pushforward of a vector measure along a function. -/
def map (v : VectorMeasure α M) (f : α → β) : VectorMeasure β M :=
  if hf : Measurable f then
    { measureOf' := fun s => if MeasurableSet s then v (f ⁻¹' s) else 0
      empty' := by simp
      not_measurable' := fun _ hi => ite_eq_right hi
      m_iUnion' := by
        intro g hg₁ hg₂
        convert! v.m_iUnion (fun i => hf (hg₁ i)) fun i j hij => (hg₂ hij).preimage _
        · rw [ite_eq_left (hg₁ _)]
        · rw [Set.preimage_iUnion, ite_eq_left (MeasurableSet.iUnion hg₁)] }
  else 0

theorem map_not_measurable {f : α → β} (hf : ¬Measurable f) : v.map f = 0 :=
  dite_eq_right hf

theorem map_apply {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    v.map f s = v (f ⁻¹' s) := by
  rw [map, dite_eq_left hf]
  exact ite_eq_left hs

@[simp]
theorem map_id : v.map id = v :=
  ext fun i hi => by rw [map_apply v measurable_id hi, Set.preimage_id]

@[simp]
theorem map_zero (f : α → β) : (0 : VectorMeasure α M).map f = 0 := by
  by_cases hf : Measurable f
  · ext i hi
    rw [map_apply _ hf hi, zero_apply, zero_apply]
  · exact dite_eq_right hf

section

variable {N : Type*} [AddCommMonoid N] [TopologicalSpace N]

/-- Given a vector measure `v` on `M` and a continuous `AddMonoidHom` `f : M → N`, `f ∘ v` is a
vector measure on `N`. -/
def mapRange (v : VectorMeasure α M) (f : M →+ N) (hf : Continuous f) : VectorMeasure α N where
  measureOf' s := f (v s)
  empty' := by rw [empty, AddMonoidHom.map_zero]
  not_measurable' i hi := by rw [not_measurable v hi, AddMonoidHom.map_zero]
  m_iUnion' _ hg₁ hg₂ := HasSum.map (v.m_iUnion hg₁ hg₂) f hf

@[simp]
theorem mapRange_apply {f : M →+ N} (hf : Continuous f) {s : Set α} : v.mapRange f hf s = f (v s) :=
  rfl

@[simp]
theorem mapRange_id : v.mapRange (AddMonoidHom.id M) continuous_id = v := by
  ext
  rfl

@[simp]
theorem mapRange_zero {f : M →+ N} (hf : Continuous f) :
    mapRange (0 : VectorMeasure α M) f hf = 0 := by
  ext
  simp

section ContinuousAdd

variable [ContinuousAdd M] [ContinuousAdd N]

@[simp]
theorem mapRange_add {v w : VectorMeasure α M} {f : M →+ N} (hf : Continuous f) :
    (v + w).mapRange f hf = v.mapRange f hf + w.mapRange f hf := by
  ext
  simp

/-- Given a continuous `AddMonoidHom` `f : M → N`, `mapRangeHom` is the `AddMonoidHom` mapping the
vector measure `v` on `M` to the vector measure `f ∘ v` on `N`. -/
def mapRangeHom {α : Type*} [MeasurableSpace α] (f : M →+ N) (hf : Continuous f) :
    VectorMeasure α M →+ VectorMeasure α N where
  toFun v := v.mapRange f hf
  map_zero' := mapRange_zero hf
  map_add' _ _ := mapRange_add hf

end ContinuousAdd

section Module

variable {R : Type*} [Semiring R] [Module R M] [Module R N]

variable [ContinuousConstSMul R M] [ContinuousConstSMul R N]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem mapRange_smul {v : VectorMeasure α M} {f : M →ₗ[R] N} (hf : Continuous f) {c : R} :
    (c • v).mapRange f.toAddMonoidHom hf = c • (v.mapRange f.toAddMonoidHom hf) := by
  ext; simp

variable [ContinuousAdd M] [ContinuousAdd N]

/-- Given a continuous linear map `f : M → N`, `mapRangeL` is the linear map mapping the
vector measure `v` on `M` to the vector measure `f ∘ v` on `N`. -/
def mapRangeL {α : Type*} [MeasurableSpace α] (f : M →L[R] N) :
    VectorMeasure α M →ₗ[R] VectorMeasure α N where
  toFun v := v.mapRange f.toAddMonoidHom f.continuous
  map_add' _ _ := mapRange_add f.continuous
  map_smul' _ _ := mapRange_smul f.continuous

@[deprecated (since := "2026-08-14")] alias mapRangeₗ := mapRangeL

end Module

end

open scoped Classical in
/-- The restriction of a vector measure on some set. -/
@[no_expose] def restrict (v : VectorMeasure α M) (i : Set α) : VectorMeasure α M :=
  if hi : MeasurableSet i then
    { measureOf' := fun s => if MeasurableSet s then v (s ∩ i) else 0
      empty' := by simp
      not_measurable' := fun _ hi => ite_eq_right hi
      m_iUnion' := by
        intro f hf₁ hf₂
        convert!
          v.m_iUnion (fun n => (hf₁ n).inter hi)
            (hf₂.mono fun i j => Disjoint.mono inf_le_left inf_le_left)
        · rw [ite_eq_left (hf₁ _)]
        · rw [Set.iUnion_inter, ite_eq_left (MeasurableSet.iUnion hf₁)] }
  else 0

theorem restrict_not_measurable {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0 :=
  dite_eq_right hi

theorem restrict_apply {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) :
    v.restrict i j = v (j ∩ i) := by
  rw [restrict, dite_eq_left hi]
  exact ite_eq_left hj

@[simp] theorem restrict_apply_univ {i : Set α} :
    v.restrict i univ = v i := by
  by_cases hi : MeasurableSet i
  · simp [restrict_apply, hi]
  · simp [restrict_not_measurable, hi]

theorem restrict_eq_self {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j)
    (hij : j ⊆ i) : v.restrict i j = v j := by
  rw [restrict_apply v hi hj, Set.inter_eq_left.2 hij]

@[simp]
theorem restrict_empty : v.restrict ∅ = 0 :=
  ext fun i hi => by
    rw [restrict_apply v MeasurableSet.empty hi, Set.inter_empty, v.empty, zero_apply]

@[simp]
theorem restrict_univ : v.restrict Set.univ = v :=
  ext fun i hi => by rw [restrict_apply v MeasurableSet.univ hi, Set.inter_univ]

@[simp]
theorem restrict_zero {i : Set α} : (0 : VectorMeasure α M).restrict i = 0 := by
  by_cases hi : MeasurableSet i
  · ext j hj
    rw [restrict_apply 0 hi hj, zero_apply, zero_apply]
  · exact dite_eq_right hi

theorem restrict_dirac {s : Set α} {x : α} {m : M} (hs : MeasurableSet s) [Decidable (x ∈ s)] :
    (dirac x m).restrict s = if x ∈ s then dirac x m else 0 := by
  classical
  ext t ht
  simp only [hs, ht, restrict_apply]
  split_ifs with has <;> simp [dirac, ht, ht.inter hs, has]

@[simp]
theorem restrict_dirac_of_mem {s : Set α} {x : α} {m : M} (hs : MeasurableSet s) (hx : x ∈ s) :
    (dirac x m).restrict s = dirac x m := by
  classical
  simp [restrict_dirac, hs, hx]

@[simp]
theorem restrict_dirac_of_notMem {s : Set α} {x : α} {m : M} (hx : x ∉ s) :
    (dirac x m).restrict s = 0 := by
  classical
  by_cases hs : MeasurableSet s
  · simp [restrict_dirac, hs, hx]
  · simp [restrict, hs]

@[simp]
theorem restrict_singleton {a : α} : v.restrict {a} = dirac a (v {a}) := by
  by_cases h : MeasurableSet {a}
  · ext s hs
    by_cases ha : a ∈ s <;> simp [*, restrict_apply]
  · simp [restrict, h]

theorem restrict_restrict {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (v.restrict t).restrict s = v.restrict (s ∩ t) := by
  ext u hu
  simp [restrict_apply, hs, hu, ht, Set.inter_assoc]

theorem restrict_map {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    (v.map f).restrict s = (v.restrict (f ⁻¹' s)).map f := by
  ext t ht
  simp [map_apply, hs, hf hs, restrict_apply, ht, hf, hf ht]

theorem restrict_toSignedMeasure {μ : Measure α} [IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s) :
    μ.toSignedMeasure.restrict s = (μ.restrict s).toSignedMeasure := by
  ext t ht
  rw [restrict_apply _ hs ht, Measure.toSignedMeasure_apply_measurable (ht.inter hs),
    Measure.toSignedMeasure_apply_measurable ht, measureReal_restrict_apply ht]

section ContinuousAdd

variable [ContinuousAdd M]

theorem map_add (v w : VectorMeasure α M) (f : α → β) : (v + w).map f = v.map f + w.map f := by
  by_cases hf : Measurable f
  · ext i hi
    simp [map_apply _ hf hi]
  · simp [map, dite_eq_right hf]

/-- `VectorMeasure.map` as an additive monoid homomorphism. -/
@[simps]
def mapGm {α : Type*} [MeasurableSpace α] (f : α → β) : VectorMeasure α M →+ VectorMeasure β M where
  toFun v := v.map f
  map_zero' := map_zero f
  map_add' _ _ := map_add _ _ f

@[simp]
theorem restrict_add (v w : VectorMeasure α M) (i : Set α) :
    (v + w).restrict i = v.restrict i + w.restrict i := by
  by_cases hi : MeasurableSet i
  · ext j hj
    simp [restrict_apply _ hi hj]
  · simp [restrict_not_measurable _ hi]

/-- `VectorMeasure.restrict` as an additive monoid homomorphism. -/
@[simps]
def restrictGm {α : Type*} [MeasurableSpace α] (i : Set α) :
    VectorMeasure α M →+ VectorMeasure α M where
  toFun v := v.restrict i
  map_zero' := restrict_zero
  map_add' _ _ := restrict_add _ _ i

end ContinuousAdd

section Partition

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [T2Space M] [ContinuousAdd M]
variable {v : VectorMeasure α M} {i s t : Set α}

@[simp]
theorem restrict_add_restrict_compl (hi : MeasurableSet i) :
    v.restrict i + v.restrict iᶜ = v := by
  ext A hA
  rw [_root_.add_apply, restrict_apply _ hi hA, restrict_apply _ hi.compl hA,
    ← of_union _ (hA.inter hi) (hA.inter hi.compl)]
  · simp
  · exact disjoint_compl_right.inter_right' A |>.inter_left' A

theorem restrict_inter_add_sdiff (hs : MeasurableSet s) (ht : MeasurableSet t) :
    v.restrict (s ∩ t) + v.restrict (s \ t) = v.restrict s := by
  ext u hu
  simp only [_root_.add_apply, restrict_apply, hs, hu, hs.inter ht, hs.diff ht]
  rw [← of_union (by grind) (hu.inter (hs.inter ht)) (hu.inter (hs.diff ht))]
  congr
  grind

@[deprecated (since := "2026-06-03")] alias restrict_inter_add_diff := restrict_inter_add_sdiff

theorem restrict_union_add_inter (hs : MeasurableSet s) (ht : MeasurableSet t) :
    v.restrict (s ∪ t) + v.restrict (s ∩ t) = v.restrict s + v.restrict t := by
  rw [← v.restrict_inter_add_sdiff (hs.union ht) ht, union_inter_cancel_right, union_sdiff_right,
    ← v.restrict_inter_add_sdiff hs ht, add_comm, ← add_assoc, add_right_comm]

theorem restrict_union (h : Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    v.restrict (s ∪ t) = v.restrict s + v.restrict t := by
  simp [← v.restrict_union_add_inter hs ht, disjoint_iff_inter_eq_empty.mp h]

end Partition

section Sub

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

@[simp]
theorem restrict_neg (v : VectorMeasure α M) (i : Set α) :
    (-v).restrict i = -(v.restrict i) := by
  by_cases hi : MeasurableSet i
  · ext j hj; simp [restrict_apply _ hi hj]
  · simp [restrict_not_measurable _ hi]

@[simp]
theorem restrict_sub (v w : VectorMeasure α M) (i : Set α) :
    (v - w).restrict i = v.restrict i - w.restrict i := by
  simp [sub_eq_add_neg, restrict_add, restrict_neg]

end Sub

end

section

variable [MeasurableSpace β]
variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [DistribMulAction R M] [ContinuousConstSMul R M]

@[simp]
theorem map_smul {v : VectorMeasure α M} {f : α → β} (c : R) : (c • v).map f = c • v.map f := by
  by_cases hf : Measurable f
  · ext i hi
    simp [map_apply _ hf hi]
  · simp only [map, dite_eq_right hf]
    -- `smul_zero` does not work since we do not require `ContinuousAdd`
    ext i
    simp

@[simp]
theorem restrict_smul {v : VectorMeasure α M} {i : Set α} (c : R) :
    (c • v).restrict i = c • v.restrict i := by
  by_cases hi : MeasurableSet i
  · ext j hj
    simp [restrict_apply _ hi hj]
  · simp only [restrict_not_measurable _ hi]
    -- `smul_zero` does not work since we do not require `ContinuousAdd`
    ext j
    simp

end

section

variable [MeasurableSpace β]
variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
variable {R : Type*} [Semiring R] [Module R M] [ContinuousConstSMul R M] [ContinuousAdd M]

/-- `VectorMeasure.map` as a linear map. -/
@[simps]
def mapₗ (f : α → β) : VectorMeasure α M →ₗ[R] VectorMeasure β M where
  toFun v := v.map f
  map_add' _ _ := map_add _ _ f
  map_smul' _ _ := map_smul _

/-- `VectorMeasure.restrict` as an additive monoid homomorphism. -/
@[simps]
def restrictₗ (i : Set α) : VectorMeasure α M →ₗ[R] VectorMeasure α M where
  toFun v := v.restrict i
  map_add' _ _ := restrict_add _ _ i
  map_smul' _ _ := restrict_smul _

end


section Trim

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

open scoped Classical in
/-- Restriction of a vector measure onto a sub-σ-algebra. -/
@[simps]
def trim {m n : MeasurableSpace α} (v : VectorMeasure α M) (hle : m ≤ n) :
    @VectorMeasure α m M _ _ :=
  @VectorMeasure.mk α m M _ _
    (fun i => if MeasurableSet[m] i then v i else 0)
    (by rw [ite_eq_left (@MeasurableSet.empty _ m), v.empty])
    (fun i hi => by rw [ite_eq_right hi])
    (fun f hf₁ hf₂ => by
      have hf₁' : ∀ k, MeasurableSet[n] (f k) := fun k => hle _ (hf₁ k)
      convert! v.m_iUnion hf₁' hf₂ using 1
      · ext n
        rw [ite_eq_left (hf₁ n)]
      · rw [ite_eq_left (@MeasurableSet.iUnion _ _ m _ _ hf₁)])

variable {n : MeasurableSpace α} {v : VectorMeasure α M}

theorem trim_eq_self : v.trim le_rfl = v := by
  ext i hi
  exact ite_eq_left hi

@[simp]
theorem zero_trim (hle : m ≤ n) : (0 : VectorMeasure α M).trim hle = 0 := by
  ext i hi
  exact ite_eq_left hi

theorem trim_measurableSet_eq (hle : m ≤ n) {i : Set α} (hi : MeasurableSet[m] i) :
    v.trim hle i = v i :=
  ite_eq_left hi

theorem restrict_trim (hle : m ≤ n) {i : Set α} (hi : MeasurableSet[m] i) :
    @VectorMeasure.restrict α m M _ _ (v.trim hle) i = (v.restrict i).trim hle := by
  ext j hj
  rw [@restrict_apply _ m, trim_measurableSet_eq hle hj, restrict_apply, trim_measurableSet_eq]
  all_goals measurability

end Trim

end VectorMeasure

end MeasureTheory
