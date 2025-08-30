/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.LinearAlgebra.AffineSpace.Combination

/-!
# Centroid of a Finite Set of Points in Affine Space

This file defines the centroid of a finite set of points in an affine space over a division
ring.

## Main definitions

* `centroidWeights`: A constant weight function assigning to each index in a `Finset` the same
  weight, equal to the reciprocal of the number of elements.

* `centroid`: the centroid of a `Finset` of points, defined as the affine combination using
  `centroidWeights`.

-/

assert_not_exists Affine.Simplex

noncomputable section

open Affine

namespace Finset

variable (k : Type*) {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P] {ι : Type*} (s : Finset ι) {ι₂ : Type*} (s₂ : Finset ι₂)

/-- The weights for the centroid of some points. -/
def centroidWeights : ι → k :=
  Function.const ι (#s : k)⁻¹

/-- `centroidWeights` at any point. -/
@[simp]
theorem centroidWeights_apply (i : ι) : s.centroidWeights k i = (#s : k)⁻¹ :=
  rfl

/-- `centroidWeights` equals a constant function. -/
theorem centroidWeights_eq_const : s.centroidWeights k = Function.const ι (#s : k)⁻¹ :=
  rfl

variable {k} in
/-- The weights in the centroid sum to 1, if the number of points,
converted to `k`, is not zero. -/
theorem sum_centroidWeights_eq_one_of_cast_card_ne_zero (h : (#s : k) ≠ 0) :
    ∑ i ∈ s, s.centroidWeights k i = 1 := by simp [h]

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the number of points is not zero. -/
theorem sum_centroidWeights_eq_one_of_card_ne_zero [CharZero k] (h : #s ≠ 0) :
    ∑ i ∈ s, s.centroidWeights k i = 1 := by
  simp_all

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the set is nonempty. -/
theorem sum_centroidWeights_eq_one_of_nonempty [CharZero k] (h : s.Nonempty) :
    ∑ i ∈ s, s.centroidWeights k i = 1 :=
  s.sum_centroidWeights_eq_one_of_card_ne_zero k (ne_of_gt (card_pos.2 h))

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the number of points is `n + 1`. -/
theorem sum_centroidWeights_eq_one_of_card_eq_add_one [CharZero k] {n : ℕ} (h : #s = n + 1) :
    ∑ i ∈ s, s.centroidWeights k i = 1 :=
  s.sum_centroidWeights_eq_one_of_card_ne_zero k (h.symm ▸ Nat.succ_ne_zero n)

/-- The centroid of some points.  Although defined for any `s`, this
is intended to be used in the case where the number of points,
converted to `k`, is not zero. -/
def centroid (p : ι → P) : P :=
  s.affineCombination k p (s.centroidWeights k)

/-- The definition of the centroid. -/
theorem centroid_def (p : ι → P) : s.centroid k p = s.affineCombination k p (s.centroidWeights k) :=
  rfl

theorem centroid_univ (s : Finset P) : univ.centroid k ((↑) : s → P) = s.centroid k id := by
  rw [centroid, centroid, ← s.attach_affineCombination_coe]
  congr
  ext
  simp

/-- The centroid of a single point. -/
@[simp]
theorem centroid_singleton (p : ι → P) (i : ι) : ({i} : Finset ι).centroid k p = p i := by
  simp [centroid_def, affineCombination_apply]

/-- The centroid of two points, expressed directly as adding a vector
to a point. -/
theorem centroid_pair [DecidableEq ι] [Invertible (2 : k)] (p : ι → P) (i₁ i₂ : ι) :
    ({i₁, i₂} : Finset ι).centroid k p = (2⁻¹ : k) • (p i₂ -ᵥ p i₁) +ᵥ p i₁ := by
  by_cases h : i₁ = i₂
  · simp [h]
  · have hc : (#{i₁, i₂} : k) ≠ 0 := by
      rw [card_insert_of_notMem (notMem_singleton.2 h), card_singleton]
      norm_num
      exact Invertible.ne_zero _
    rw [centroid_def,
      affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _
        (sum_centroidWeights_eq_one_of_cast_card_ne_zero _ hc) (p i₁)]
    simp [h, one_add_one_eq_two]

/-- The centroid of two points indexed by `Fin 2`, expressed directly
as adding a vector to the first point. -/
theorem centroid_pair_fin [Invertible (2 : k)] (p : Fin 2 → P) :
    univ.centroid k p = (2⁻¹ : k) • (p 1 -ᵥ p 0) +ᵥ p 0 := by
  rw [univ_fin2]
  convert centroid_pair k p 0 1

/-- A centroid, over the image of an embedding, equals a centroid with
the same points and weights over the original `Finset`. -/
theorem centroid_map (e : ι₂ ↪ ι) (p : ι → P) :
    (s₂.map e).centroid k p = s₂.centroid k (p ∘ e) := by
  simp [centroid_def, affineCombination_map, centroidWeights]

/-- `centroidWeights` gives the weights for the centroid as a
constant function, which is suitable when summing over the points
whose centroid is being taken.  This function gives the weights in a
form suitable for summing over a larger set of points, as an indicator
function that is zero outside the set whose centroid is being taken.
In the case of a `Fintype`, the sum may be over `univ`. -/
def centroidWeightsIndicator : ι → k :=
  Set.indicator (↑s) (s.centroidWeights k)

/-- The definition of `centroidWeightsIndicator`. -/
theorem centroidWeightsIndicator_def :
    s.centroidWeightsIndicator k = Set.indicator (↑s) (s.centroidWeights k) :=
  rfl

/-- The sum of the weights for the centroid indexed by a `Fintype`. -/
theorem sum_centroidWeightsIndicator [Fintype ι] :
    ∑ i, s.centroidWeightsIndicator k i = ∑ i ∈ s, s.centroidWeights k i :=
  sum_indicator_subset _ (subset_univ _)

/-- In the characteristic zero case, the weights in the centroid
indexed by a `Fintype` sum to 1 if the number of points is not
zero. -/
theorem sum_centroidWeightsIndicator_eq_one_of_card_ne_zero [CharZero k] [Fintype ι]
    (h : #s ≠ 0) : ∑ i, s.centroidWeightsIndicator k i = 1 := by
  rw [sum_centroidWeightsIndicator]
  exact s.sum_centroidWeights_eq_one_of_card_ne_zero k h

/-- In the characteristic zero case, the weights in the centroid
indexed by a `Fintype` sum to 1 if the set is nonempty. -/
theorem sum_centroidWeightsIndicator_eq_one_of_nonempty [CharZero k] [Fintype ι] (h : s.Nonempty) :
    ∑ i, s.centroidWeightsIndicator k i = 1 := by
  rw [sum_centroidWeightsIndicator]
  exact s.sum_centroidWeights_eq_one_of_nonempty k h

/-- In the characteristic zero case, the weights in the centroid
indexed by a `Fintype` sum to 1 if the number of points is `n + 1`. -/
theorem sum_centroidWeightsIndicator_eq_one_of_card_eq_add_one [CharZero k] [Fintype ι] {n : ℕ}
    (h : #s = n + 1) : ∑ i, s.centroidWeightsIndicator k i = 1 := by
  rw [sum_centroidWeightsIndicator]
  exact s.sum_centroidWeights_eq_one_of_card_eq_add_one k h

/-- The centroid as an affine combination over a `Fintype`. -/
theorem centroid_eq_affineCombination_fintype [Fintype ι] (p : ι → P) :
    s.centroid k p = univ.affineCombination k p (s.centroidWeightsIndicator k) :=
  affineCombination_indicator_subset _ _ (subset_univ _)

/-- An indexed family of points that is injective on the given
`Finset` has the same centroid as the image of that `Finset`.  This is
stated in terms of a set equal to the image to provide control of
definitional equality for the index type used for the centroid of the
image. -/
theorem centroid_eq_centroid_image_of_inj_on {p : ι → P}
    (hi : ∀ i ∈ s, ∀ j ∈ s, p i = p j → i = j) {ps : Set P} [Fintype ps]
    (hps : ps = p '' ↑s) : s.centroid k p = (univ : Finset ps).centroid k fun x => (x : P) := by
  let f : p '' ↑s → ι := fun x => x.property.choose
  have hf : ∀ x, f x ∈ s ∧ p (f x) = x := fun x => x.property.choose_spec
  let f' : ps → ι := fun x => f ⟨x, hps ▸ x.property⟩
  have hf' : ∀ x, f' x ∈ s ∧ p (f' x) = x := fun x => hf ⟨x, hps ▸ x.property⟩
  have hf'i : Function.Injective f' := by
    intro x y h
    rw [Subtype.ext_iff, ← (hf' x).2, ← (hf' y).2, h]
  let f'e : ps ↪ ι := ⟨f', hf'i⟩
  have hu : Finset.univ.map f'e = s := by
    ext x
    rw [mem_map]
    constructor
    · rintro ⟨i, _, rfl⟩
      exact (hf' i).1
    · intro hx
      use ⟨p x, hps.symm ▸ Set.mem_image_of_mem _ hx⟩, mem_univ _
      refine hi _ (hf' _).1 _ hx ?_
      rw [(hf' _).2]
  rw [← hu, centroid_map]
  congr with x
  change p (f' x) = ↑x
  rw [(hf' x).2]

/-- Two indexed families of points that are injective on the given
`Finset`s and with the same points in the image of those `Finset`s
have the same centroid. -/
theorem centroid_eq_of_inj_on_of_image_eq {p : ι → P}
    (hi : ∀ i ∈ s, ∀ j ∈ s, p i = p j → i = j) {p₂ : ι₂ → P}
    (hi₂ : ∀ i ∈ s₂, ∀ j ∈ s₂, p₂ i = p₂ j → i = j) (he : p '' ↑s = p₂ '' ↑s₂) :
    s.centroid k p = s₂.centroid k p₂ := by
  classical rw [s.centroid_eq_centroid_image_of_inj_on k hi rfl,
      s₂.centroid_eq_centroid_image_of_inj_on k hi₂ he]

end Finset

section DivisionRing

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P] {ι : Type*}

open Set Finset

/-- The centroid lies in the affine span if the number of points,
converted to `k`, is not zero. -/
theorem centroid_mem_affineSpan_of_cast_card_ne_zero {s : Finset ι} (p : ι → P)
    (h : (#s : k) ≠ 0) : s.centroid k p ∈ affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_cast_card_ne_zero h) p

variable (k)

/-- In the characteristic zero case, the centroid lies in the affine
span if the number of points is not zero. -/
theorem centroid_mem_affineSpan_of_card_ne_zero [CharZero k] {s : Finset ι} (p : ι → P)
    (h : #s ≠ 0) : s.centroid k p ∈ affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_card_ne_zero k h) p

/-- In the characteristic zero case, the centroid lies in the affine
span if the set is nonempty. -/
theorem centroid_mem_affineSpan_of_nonempty [CharZero k] {s : Finset ι} (p : ι → P)
    (h : s.Nonempty) : s.centroid k p ∈ affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_nonempty k h) p

/-- In the characteristic zero case, the centroid lies in the affine
span if the number of points is `n + 1`. -/
theorem centroid_mem_affineSpan_of_card_eq_add_one [CharZero k] {s : Finset ι} (p : ι → P) {n : ℕ}
    (h : #s = n + 1) : s.centroid k p ∈ affineSpan k (range p) :=
  affineCombination_mem_affineSpan (s.sum_centroidWeights_eq_one_of_card_eq_add_one k h) p

end DivisionRing
