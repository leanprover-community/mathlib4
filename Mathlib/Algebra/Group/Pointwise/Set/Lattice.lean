/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn, Yaël Dillies
-/
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Indexed unions and intersections of pointwise operations of sets

This file contains lemmas on taking the union and intersection over pointwise algebraic operations
on sets.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

assert_not_exists MulAction MonoidWithZero

open Function MulOpposite

variable {F α β γ : Type*}

namespace Set

/-! ### Set negation/inversion -/


section Inv

open Pointwise

variable {ι : Sort*} [Inv α]

@[to_additive (attr := simp)]
theorem iInter_inv (s : ι → Set α) : (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹ :=
  preimage_iInter

@[to_additive (attr := simp)]
theorem sInter_inv (S : Set (Set α)) : (⋂₀ S)⁻¹ = ⋂ s ∈ S, s⁻¹ :=
  preimage_sInter

@[to_additive (attr := simp)]
theorem iUnion_inv (s : ι → Set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹ :=
  preimage_iUnion

@[to_additive (attr := simp)]
theorem sUnion_inv (S : Set (Set α)) : (⋃₀ S)⁻¹ = ⋃ s ∈ S, s⁻¹ :=
  preimage_sUnion

end Inv

open Pointwise

/-! ### Set addition/multiplication -/


section Mul

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

@[to_additive]
theorem iUnion_mul_left_image : ⋃ a ∈ s, (a * ·) '' t = s * t :=
  iUnion_image_left _

@[to_additive]
theorem iUnion_mul_right_image : ⋃ a ∈ t, (· * a) '' s = s * t :=
  iUnion_image_right _

@[to_additive]
theorem iUnion_mul (s : ι → Set α) (t : Set α) : (⋃ i, s i) * t = ⋃ i, s i * t :=
  image2_iUnion_left ..

@[to_additive]
theorem mul_iUnion (s : Set α) (t : ι → Set α) : (s * ⋃ i, t i) = ⋃ i, s * t i :=
  image2_iUnion_right ..

@[to_additive]
theorem sUnion_mul (S : Set (Set α)) (t : Set α) : ⋃₀ S * t = ⋃ s ∈ S, s * t :=
  image2_sUnion_left ..

@[to_additive]
theorem mul_sUnion (s : Set α) (T : Set (Set α)) : s * ⋃₀ T = ⋃ t ∈ T, s * t :=
  image2_sUnion_right ..

@[to_additive]
theorem iUnion₂_mul (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) * t = ⋃ (i) (j), s i j * t :=
  image2_iUnion₂_left ..

@[to_additive]
theorem mul_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s * ⋃ (i) (j), t i j) = ⋃ (i) (j), s * t i j :=
  image2_iUnion₂_right ..

@[to_additive]
theorem iInter_mul_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) * t ⊆ ⋂ i, s i * t :=
  Set.image2_iInter_subset_left ..

@[to_additive]
theorem mul_iInter_subset (s : Set α) (t : ι → Set α) : (s * ⋂ i, t i) ⊆ ⋂ i, s * t i :=
  image2_iInter_subset_right ..

@[to_additive]
lemma mul_sInter_subset (s : Set α) (T : Set (Set α)) :
    s * ⋂₀ T ⊆ ⋂ t ∈ T, s * t := image2_sInter_right_subset s T (fun a b => a * b)

@[to_additive]
lemma sInter_mul_subset (S : Set (Set α)) (t : Set α) :
    ⋂₀ S * t ⊆ ⋂ s ∈ S, s * t := image2_sInter_left_subset S t (fun a b => a * b)

@[to_additive]
theorem iInter₂_mul_subset (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) * t ⊆ ⋂ (i) (j), s i j * t :=
  image2_iInter₂_subset_left ..

@[to_additive]
theorem mul_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) :
    (s * ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s * t i j :=
  image2_iInter₂_subset_right ..

end Mul

/-! ### Set subtraction/division -/


section Div

variable {ι : Sort*} {κ : ι → Sort*} [Div α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

@[to_additive]
theorem iUnion_div_left_image : ⋃ a ∈ s, (a / ·) '' t = s / t :=
  iUnion_image_left _

@[to_additive]
theorem iUnion_div_right_image : ⋃ a ∈ t, (· / a) '' s = s / t :=
  iUnion_image_right _

@[to_additive]
theorem iUnion_div (s : ι → Set α) (t : Set α) : (⋃ i, s i) / t = ⋃ i, s i / t :=
  image2_iUnion_left ..

@[to_additive]
theorem div_iUnion (s : Set α) (t : ι → Set α) : (s / ⋃ i, t i) = ⋃ i, s / t i :=
  image2_iUnion_right ..

@[to_additive]
theorem sUnion_div (S : Set (Set α)) (t : Set α) : ⋃₀ S / t = ⋃ s ∈ S, s / t :=
  image2_sUnion_left ..

@[to_additive]
theorem div_sUnion (s : Set α) (T : Set (Set α)) : s / ⋃₀ T = ⋃ t ∈ T, s / t :=
  image2_sUnion_right ..

@[to_additive]
theorem iUnion₂_div (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) / t = ⋃ (i) (j), s i j / t :=
  image2_iUnion₂_left ..

@[to_additive]
theorem div_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s / ⋃ (i) (j), t i j) = ⋃ (i) (j), s / t i j :=
  image2_iUnion₂_right ..

@[to_additive]
theorem iInter_div_subset (s : ι → Set α) (t : Set α) : (⋂ i, s i) / t ⊆ ⋂ i, s i / t :=
  image2_iInter_subset_left ..

@[to_additive]
theorem div_iInter_subset (s : Set α) (t : ι → Set α) : (s / ⋂ i, t i) ⊆ ⋂ i, s / t i :=
  image2_iInter_subset_right ..

@[to_additive]
theorem sInter_div_subset (S : Set (Set α)) (t : Set α) : ⋂₀ S / t ⊆ ⋂ s ∈ S, s / t :=
  image2_sInter_subset_left ..

@[to_additive]
theorem div_sInter_subset (s : Set α) (T : Set (Set α)) : s / ⋂₀ T ⊆ ⋂ t ∈ T, s / t :=
  image2_sInter_subset_right ..

@[to_additive]
theorem iInter₂_div_subset (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) / t ⊆ ⋂ (i) (j), s i j / t :=
  image2_iInter₂_subset_left ..

@[to_additive]
theorem div_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set α) :
    (s / ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s / t i j :=
  image2_iInter₂_subset_right ..

end Div

/-! ### Translation/scaling of sets -/

section SMul

variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

@[to_additive] lemma iUnion_smul_left_image : ⋃ a ∈ s, a • t = s • t := iUnion_image_left _

@[to_additive]
lemma iUnion_smul_right_image : ⋃ a ∈ t, (· • a) '' s = s • t := iUnion_image_right _

@[to_additive]
lemma iUnion_smul (s : ι → Set α) (t : Set β) : (⋃ i, s i) • t = ⋃ i, s i • t :=
  image2_iUnion_left ..

@[to_additive]
lemma smul_iUnion (s : Set α) (t : ι → Set β) : (s • ⋃ i, t i) = ⋃ i, s • t i :=
  image2_iUnion_right ..

@[to_additive]
lemma sUnion_smul (S : Set (Set α)) (t : Set β) : ⋃₀ S • t = ⋃ s ∈ S, s • t :=
  image2_sUnion_left ..

@[to_additive]
lemma smul_sUnion (s : Set α) (T : Set (Set β)) : s • ⋃₀ T = ⋃ t ∈ T, s • t :=
  image2_sUnion_right ..

@[to_additive]
lemma iUnion₂_smul (s : ∀ i, κ i → Set α) (t : Set β) :
    (⋃ i, ⋃ j, s i j) • t = ⋃ i, ⋃ j, s i j • t := image2_iUnion₂_left ..

@[to_additive]
lemma smul_iUnion₂ (s : Set α) (t : ∀ i, κ i → Set β) :
    (s • ⋃ i, ⋃ j, t i j) = ⋃ i, ⋃ j, s • t i j := image2_iUnion₂_right ..

@[to_additive]
lemma iInter_smul_subset (s : ι → Set α) (t : Set β) : (⋂ i, s i) • t ⊆ ⋂ i, s i • t :=
  image2_iInter_subset_left ..

@[to_additive]
lemma smul_iInter_subset (s : Set α) (t : ι → Set β) : (s • ⋂ i, t i) ⊆ ⋂ i, s • t i :=
  image2_iInter_subset_right ..

@[to_additive]
lemma sInter_smul_subset (S : Set (Set α)) (t : Set β) : ⋂₀ S • t ⊆ ⋂ s ∈ S, s • t :=
  image2_sInter_left_subset S t (fun a x => a • x)

@[to_additive]
lemma smul_sInter_subset (s : Set α) (T : Set (Set β)) : s • ⋂₀ T ⊆ ⋂ t ∈ T, s • t :=
  image2_sInter_right_subset s T (fun a x => a • x)

@[to_additive]
lemma iInter₂_smul_subset (s : ∀ i, κ i → Set α) (t : Set β) :
    (⋂ i, ⋂ j, s i j) • t ⊆ ⋂ i, ⋂ j, s i j • t := image2_iInter₂_subset_left ..

@[to_additive]
lemma smul_iInter₂_subset (s : Set α) (t : ∀ i, κ i → Set β) :
    (s • ⋂ i, ⋂ j, t i j) ⊆ ⋂ i, ⋂ j, s • t i j := image2_iInter₂_subset_right ..

@[to_additive (attr := simp)]
lemma iUnion_smul_set (s : Set α) (t : Set β) : ⋃ a ∈ s, a • t = s • t := iUnion_image_left _

end SMul

section SMulSet
variable {ι : Sort*} {κ : ι → Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

@[to_additive]
lemma smul_set_iUnion (a : α) (s : ι → Set β) : a • ⋃ i, s i = ⋃ i, a • s i :=
  image_iUnion

@[to_additive]
lemma smul_set_iUnion₂ (a : α) (s : ∀ i, κ i → Set β) :
    a • ⋃ i, ⋃ j, s i j = ⋃ i, ⋃ j, a • s i j := image_iUnion₂ ..

@[to_additive]
lemma smul_set_sUnion (a : α) (S : Set (Set β)) : a • ⋃₀ S = ⋃ s ∈ S, a • s := by
  rw [sUnion_eq_biUnion, smul_set_iUnion₂]

@[to_additive]
lemma smul_set_iInter_subset (a : α) (t : ι → Set β) : a • ⋂ i, t i ⊆ ⋂ i, a • t i :=
  image_iInter_subset ..

@[to_additive]
lemma smul_set_sInter_subset (a : α) (S : Set (Set β)) :
    a • ⋂₀ S ⊆ ⋂ s ∈ S, a • s := image_sInter_subset ..

@[to_additive]
lemma smul_set_iInter₂_subset (a : α) (t : ∀ i, κ i → Set β) :
    a • ⋂ i, ⋂ j, t i j ⊆ ⋂ i, ⋂ j, a • t i j := image_iInter₂_subset ..

end SMulSet
variable {s : Set α} {t : Set β} {a : α} {b : β}

section VSub
variable {ι : Sort*} {κ : ι → Sort*} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

lemma iUnion_vsub_left_image : ⋃ a ∈ s, (a -ᵥ ·) '' t = s -ᵥ t := iUnion_image_left _
lemma iUnion_vsub_right_image : ⋃ a ∈ t, (· -ᵥ a) '' s = s -ᵥ t := iUnion_image_right _

lemma iUnion_vsub (s : ι → Set β) (t : Set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t :=
  image2_iUnion_left ..

lemma vsub_iUnion (s : Set β) (t : ι → Set β) : (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i :=
  image2_iUnion_right ..

lemma sUnion_vsub (S : Set (Set β)) (t : Set β) : ⋃₀ S -ᵥ t = ⋃ s ∈ S, s -ᵥ t :=
  image2_sUnion_left ..

lemma vsub_sUnion (s : Set β) (T : Set (Set β)) : s -ᵥ ⋃₀ T = ⋃ t ∈ T, s -ᵥ t :=
  image2_sUnion_right ..

lemma iUnion₂_vsub (s : ∀ i, κ i → Set β) (t : Set β) :
    (⋃ i, ⋃ j, s i j) -ᵥ t = ⋃ i, ⋃ j, s i j -ᵥ t := image2_iUnion₂_left ..

lemma vsub_iUnion₂ (s : Set β) (t : ∀ i, κ i → Set β) :
    (s -ᵥ ⋃ i, ⋃ j, t i j) = ⋃ i, ⋃ j, s -ᵥ t i j := image2_iUnion₂_right ..

lemma iInter_vsub_subset (s : ι → Set β) (t : Set β) : (⋂ i, s i) -ᵥ t ⊆ ⋂ i, s i -ᵥ t :=
  image2_iInter_subset_left ..

lemma vsub_iInter_subset (s : Set β) (t : ι → Set β) : (s -ᵥ ⋂ i, t i) ⊆ ⋂ i, s -ᵥ t i :=
  image2_iInter_subset_right ..

lemma sInter_vsub_subset (S : Set (Set β)) (t : Set β) : ⋂₀ S -ᵥ t ⊆ ⋂ s ∈ S, s -ᵥ t :=
  image2_sInter_subset_left ..

lemma vsub_sInter_subset (s : Set β) (T : Set (Set β)) : s -ᵥ ⋂₀ T ⊆ ⋂ t ∈ T, s -ᵥ t :=
  image2_sInter_subset_right ..

lemma iInter₂_vsub_subset (s : ∀ i, κ i → Set β) (t : Set β) :
    (⋂ i, ⋂ j, s i j) -ᵥ t ⊆ ⋂ i, ⋂ j, s i j -ᵥ t := image2_iInter₂_subset_left ..

lemma vsub_iInter₂_subset (s : Set β) (t : ∀ i, κ i → Set β) :
    s -ᵥ ⋂ i, ⋂ j, t i j ⊆ ⋂ i, ⋂ j, s -ᵥ t i j := image2_iInter₂_subset_right ..

end VSub

end Set
