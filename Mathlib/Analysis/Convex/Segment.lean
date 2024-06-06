/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Algebra.Order.Invertible
import Mathlib.Algebra.Order.Module.OrderedSMul
import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.LinearAlgebra.Ray
import Mathlib.Tactic.GCongr

#align_import analysis.convex.segment from "leanprover-community/mathlib"@"c5773405394e073885e2a144c9ca14637e8eb963"

/-!
# Segments in vector spaces

In a 𝕜-vector space, we define the following objects and properties.
* `segment 𝕜 x y`: Closed segment joining `x` and `y`.
* `openSegment 𝕜 x y`: Open segment joining `x` and `y`.

## Notations

We provide the following notation:
* `[x -[𝕜] y] = segment 𝕜 x y` in locale `Convex`

## TODO

Generalize all this file to affine spaces.

Should we rename `segment` and `openSegment` to `convex.Icc` and `convex.Ioo`? Should we also
define `clopenSegment`/`convex.Ico`/`convex.Ioc`?
-/


variable {𝕜 E F G ι : Type*} {π : ι → Type*}

open Function Set

open Pointwise Convex

section OrderedSemiring

variable [OrderedSemiring 𝕜] [AddCommMonoid E]

section SMul

variable (𝕜) [SMul 𝕜 E] {s : Set E} {x y : E}

/-- Segments in a vector space. -/
def segment (x y : E) : Set E :=
  { z : E | ∃ a b : 𝕜, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a • x + b • y = z }
#align segment segment

/-- Open segment in a vector space. Note that `openSegment 𝕜 x x = {x}` instead of being `∅` when
the base semiring has some element between `0` and `1`. -/
def openSegment (x y : E) : Set E :=
  { z : E | ∃ a b : 𝕜, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a • x + b • y = z }
#align open_segment openSegment

@[inherit_doc] scoped[Convex] notation (priority := high) "[" x "-[" 𝕜 "]" y "]" => segment 𝕜 x y

theorem segment_eq_image₂ (x y : E) :
    [x -[𝕜] y] =
      (fun p : 𝕜 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1 } := by
  simp only [segment, image, Prod.exists, mem_setOf_eq, exists_prop, and_assoc]
#align segment_eq_image₂ segment_eq_image₂

theorem openSegment_eq_image₂ (x y : E) :
    openSegment 𝕜 x y =
      (fun p : 𝕜 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 = 1 } := by
  simp only [openSegment, image, Prod.exists, mem_setOf_eq, exists_prop, and_assoc]
#align open_segment_eq_image₂ openSegment_eq_image₂

theorem segment_symm (x y : E) : [x -[𝕜] y] = [y -[𝕜] x] :=
  Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
      fun ⟨a, b, ha, hb, hab, H⟩ =>
      ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩
#align segment_symm segment_symm

theorem openSegment_symm (x y : E) : openSegment 𝕜 x y = openSegment 𝕜 y x :=
  Set.ext fun _ =>
    ⟨fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
      fun ⟨a, b, ha, hb, hab, H⟩ =>
      ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩
#align open_segment_symm openSegment_symm

theorem openSegment_subset_segment (x y : E) : openSegment 𝕜 x y ⊆ [x -[𝕜] y] :=
  fun _ ⟨a, b, ha, hb, hab, hz⟩ => ⟨a, b, ha.le, hb.le, hab, hz⟩
#align open_segment_subset_segment openSegment_subset_segment

theorem segment_subset_iff :
    [x -[𝕜] y] ⊆ s ↔ ∀ a b : 𝕜, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s :=
  ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H _ ⟨a, b, ha, hb, hab, hz⟩ =>
    hz ▸ H a b ha hb hab⟩
#align segment_subset_iff segment_subset_iff

theorem openSegment_subset_iff :
    openSegment 𝕜 x y ⊆ s ↔ ∀ a b : 𝕜, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s :=
  ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H _ ⟨a, b, ha, hb, hab, hz⟩ =>
    hz ▸ H a b ha hb hab⟩
#align open_segment_subset_iff openSegment_subset_iff

end SMul

open Convex

section MulActionWithZero

variable (𝕜)
variable [MulActionWithZero 𝕜 E]


theorem left_mem_segment (x y : E) : x ∈ [x -[𝕜] y] :=
  ⟨1, 0, zero_le_one, le_refl 0, add_zero 1, by rw [zero_smul, one_smul, add_zero]⟩
#align left_mem_segment left_mem_segment

theorem right_mem_segment (x y : E) : y ∈ [x -[𝕜] y] :=
  segment_symm 𝕜 y x ▸ left_mem_segment 𝕜 y x
#align right_mem_segment right_mem_segment

end MulActionWithZero

section Module

variable (𝕜)
variable [Module 𝕜 E] {s : Set E} {x y z : E}

@[simp]
theorem segment_same (x : E) : [x -[𝕜] x] = {x} :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, _, _, hab, hz⟩ => by
      simpa only [(add_smul _ _ _).symm, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
      fun h => mem_singleton_iff.1 h ▸ left_mem_segment 𝕜 z z⟩
#align segment_same segment_same

theorem insert_endpoints_openSegment (x y : E) :
    insert x (insert y (openSegment 𝕜 x y)) = [x -[𝕜] y] := by
  simp only [subset_antisymm_iff, insert_subset_iff, left_mem_segment, right_mem_segment,
    openSegment_subset_segment, true_and_iff]
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  refine hb.eq_or_gt.imp ?_ fun hb' => ha.eq_or_gt.imp ?_ fun ha' => ?_
  · rintro rfl
    rw [← add_zero a, hab, one_smul, zero_smul, add_zero]
  · rintro rfl
    rw [← zero_add b, hab, one_smul, zero_smul, zero_add]
  · exact ⟨a, b, ha', hb', hab, rfl⟩
#align insert_endpoints_open_segment insert_endpoints_openSegment

variable {𝕜}

theorem mem_openSegment_of_ne_left_right (hx : x ≠ z) (hy : y ≠ z) (hz : z ∈ [x -[𝕜] y]) :
    z ∈ openSegment 𝕜 x y := by
  rw [← insert_endpoints_openSegment] at hz
  exact (hz.resolve_left hx.symm).resolve_left hy.symm
#align mem_open_segment_of_ne_left_right mem_openSegment_of_ne_left_right

theorem openSegment_subset_iff_segment_subset (hx : x ∈ s) (hy : y ∈ s) :
    openSegment 𝕜 x y ⊆ s ↔ [x -[𝕜] y] ⊆ s := by
  simp only [← insert_endpoints_openSegment, insert_subset_iff, *, true_and_iff]
#align open_segment_subset_iff_segment_subset openSegment_subset_iff_segment_subset

end Module

end OrderedSemiring

open Convex

section OrderedRing

variable (𝕜) [OrderedRing 𝕜] [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [Module 𝕜 E]
  [Module 𝕜 F]

section DenselyOrdered

variable [Nontrivial 𝕜] [DenselyOrdered 𝕜]

@[simp]
theorem openSegment_same (x : E) : openSegment 𝕜 x x = {x} :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, _, _, hab, hz⟩ => by
      simpa only [← add_smul, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
    fun h : z = x => by
      obtain ⟨a, ha₀, ha₁⟩ := DenselyOrdered.dense (0 : 𝕜) 1 zero_lt_one
      refine ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel _ _, ?_⟩
      rw [← add_smul, add_sub_cancel, one_smul, h]⟩
#align open_segment_same openSegment_same

end DenselyOrdered

theorem segment_eq_image (x y : E) :
    [x -[𝕜] y] = (fun θ : 𝕜 => (1 - θ) • x + θ • y) '' Icc (0 : 𝕜) 1 :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ =>
      ⟨b, ⟨hb, hab ▸ le_add_of_nonneg_left ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel_right]⟩,
      fun ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩ => ⟨1 - θ, θ, sub_nonneg.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩
#align segment_eq_image segment_eq_image

theorem openSegment_eq_image (x y : E) :
    openSegment 𝕜 x y = (fun θ : 𝕜 => (1 - θ) • x + θ • y) '' Ioo (0 : 𝕜) 1 :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ =>
      ⟨b, ⟨hb, hab ▸ lt_add_of_pos_left _ ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel_right]⟩,
      fun ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩ => ⟨1 - θ, θ, sub_pos.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩
#align open_segment_eq_image openSegment_eq_image

theorem segment_eq_image' (x y : E) :
    [x -[𝕜] y] = (fun θ : 𝕜 => x + θ • (y - x)) '' Icc (0 : 𝕜) 1 := by
  convert segment_eq_image 𝕜 x y using 2
  simp only [smul_sub, sub_smul, one_smul]
  abel
#align segment_eq_image' segment_eq_image'

theorem openSegment_eq_image' (x y : E) :
    openSegment 𝕜 x y = (fun θ : 𝕜 => x + θ • (y - x)) '' Ioo (0 : 𝕜) 1 := by
  convert openSegment_eq_image 𝕜 x y using 2
  simp only [smul_sub, sub_smul, one_smul]
  abel
#align open_segment_eq_image' openSegment_eq_image'

theorem segment_eq_image_lineMap (x y : E) : [x -[𝕜] y] =
    AffineMap.lineMap x y '' Icc (0 : 𝕜) 1 := by
  convert segment_eq_image 𝕜 x y using 2
  exact AffineMap.lineMap_apply_module _ _ _
#align segment_eq_image_line_map segment_eq_image_lineMap

theorem openSegment_eq_image_lineMap (x y : E) :
    openSegment 𝕜 x y = AffineMap.lineMap x y '' Ioo (0 : 𝕜) 1 := by
  convert openSegment_eq_image 𝕜 x y using 2
  exact AffineMap.lineMap_apply_module _ _ _
#align open_segment_eq_image_line_map openSegment_eq_image_lineMap

@[simp]
theorem image_segment (f : E →ᵃ[𝕜] F) (a b : E) : f '' [a -[𝕜] b] = [f a -[𝕜] f b] :=
  Set.ext fun x => by
    simp_rw [segment_eq_image_lineMap, mem_image, exists_exists_and_eq_and, AffineMap.apply_lineMap]
#align image_segment image_segment

@[simp]
theorem image_openSegment (f : E →ᵃ[𝕜] F) (a b : E) :
    f '' openSegment 𝕜 a b = openSegment 𝕜 (f a) (f b) :=
  Set.ext fun x => by
    simp_rw [openSegment_eq_image_lineMap, mem_image, exists_exists_and_eq_and,
      AffineMap.apply_lineMap]
#align image_open_segment image_openSegment

@[simp]
theorem vadd_segment [AddTorsor G E] [VAddCommClass G E E] (a : G) (b c : E) :
    a +ᵥ [b -[𝕜] c] = [a +ᵥ b -[𝕜] a +ᵥ c] :=
  image_segment 𝕜 ⟨_, LinearMap.id, fun _ _ => vadd_comm _ _ _⟩ b c
#align vadd_segment vadd_segment

@[simp]
theorem vadd_openSegment [AddTorsor G E] [VAddCommClass G E E] (a : G) (b c : E) :
    a +ᵥ openSegment 𝕜 b c = openSegment 𝕜 (a +ᵥ b) (a +ᵥ c) :=
  image_openSegment 𝕜 ⟨_, LinearMap.id, fun _ _ => vadd_comm _ _ _⟩ b c
#align vadd_open_segment vadd_openSegment

@[simp]
theorem mem_segment_translate (a : E) {x b c} : a + x ∈ [a + b -[𝕜] a + c] ↔ x ∈ [b -[𝕜] c] := by
  simp_rw [← vadd_eq_add, ← vadd_segment, vadd_mem_vadd_set_iff]
#align mem_segment_translate mem_segment_translate

@[simp]
theorem mem_openSegment_translate (a : E) {x b c : E} :
    a + x ∈ openSegment 𝕜 (a + b) (a + c) ↔ x ∈ openSegment 𝕜 b c := by
  simp_rw [← vadd_eq_add, ← vadd_openSegment, vadd_mem_vadd_set_iff]
#align mem_open_segment_translate mem_openSegment_translate

theorem segment_translate_preimage (a b c : E) :
    (fun x => a + x) ⁻¹' [a + b -[𝕜] a + c] = [b -[𝕜] c] :=
  Set.ext fun _ => mem_segment_translate 𝕜 a
#align segment_translate_preimage segment_translate_preimage

theorem openSegment_translate_preimage (a b c : E) :
    (fun x => a + x) ⁻¹' openSegment 𝕜 (a + b) (a + c) = openSegment 𝕜 b c :=
  Set.ext fun _ => mem_openSegment_translate 𝕜 a
#align open_segment_translate_preimage openSegment_translate_preimage

theorem segment_translate_image (a b c : E) : (fun x => a + x) '' [b -[𝕜] c] = [a + b -[𝕜] a + c] :=
  segment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ <| add_left_surjective a
#align segment_translate_image segment_translate_image

theorem openSegment_translate_image (a b c : E) :
    (fun x => a + x) '' openSegment 𝕜 b c = openSegment 𝕜 (a + b) (a + c) :=
  openSegment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ <| add_left_surjective a
#align open_segment_translate_image openSegment_translate_image

lemma segment_inter_eq_endpoint_of_linearIndependent_sub
    {c x y : E} (h : LinearIndependent 𝕜 ![x - c, y - c]) :
    [c -[𝕜] x] ∩ [c -[𝕜] y] = {c} := by
  apply Subset.antisymm; swap
  · simp [singleton_subset_iff, left_mem_segment]
  intro z ⟨hzt, hzs⟩
  rw [segment_eq_image, mem_image] at hzt hzs
  rcases hzt with ⟨p, ⟨p0, p1⟩, rfl⟩
  rcases hzs with ⟨q, ⟨q0, q1⟩, H⟩
  have Hx : x = (x - c) + c := by abel
  have Hy : y = (y - c) + c := by abel
  rw [Hx, Hy, smul_add, smul_add] at H
  have : c + q • (y - c) = c + p • (x - c) := by
    convert H using 1 <;> simp [sub_smul]
  obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := h.eq_zero_of_pair' ((add_right_inj c).1 this).symm
  simp

end OrderedRing

theorem sameRay_of_mem_segment [StrictOrderedCommRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {x y z : E}
    (h : x ∈ [y -[𝕜] z]) : SameRay 𝕜 (x - y) (z - x) := by
  rw [segment_eq_image'] at h
  rcases h with ⟨θ, ⟨hθ₀, hθ₁⟩, rfl⟩
  simpa only [add_sub_cancel_left, ← sub_sub, sub_smul, one_smul] using
    (SameRay.sameRay_nonneg_smul_left (z - y) hθ₀).nonneg_smul_right (sub_nonneg.2 hθ₁)
#align same_ray_of_mem_segment sameRay_of_mem_segment

lemma segment_inter_eq_endpoint_of_linearIndependent_of_ne [OrderedCommRing 𝕜] [NoZeroDivisors 𝕜]
    [AddCommGroup E] [Module 𝕜 E]
    {x y : E} (h : LinearIndependent 𝕜 ![x, y]) {s t : 𝕜} (hs : s ≠ t) (c : E) :
    [c + x -[𝕜] c + t • y] ∩ [c + x -[𝕜] c + s • y] = {c + x} := by
  apply segment_inter_eq_endpoint_of_linearIndependent_sub
  simp only [add_sub_add_left_eq_sub]
  suffices H : LinearIndependent 𝕜 ![(-1 : 𝕜) • x + t • y, (-1 : 𝕜) • x + s • y] by
    convert H using 1; simp only [neg_smul, one_smul]; abel_nf
  apply h.linear_combination_pair_of_det_ne_zero
  contrapose! hs
  apply Eq.symm
  simpa [neg_mul, one_mul, mul_neg, mul_one, sub_neg_eq_add, add_comm _ t,
    ← sub_eq_add_neg, sub_eq_zero] using hs

section LinearOrderedRing

variable [LinearOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {x y : E}

theorem midpoint_mem_segment [Invertible (2 : 𝕜)] (x y : E) : midpoint 𝕜 x y ∈ [x -[𝕜] y] := by
  rw [segment_eq_image_lineMap]
  exact ⟨⅟ 2, ⟨invOf_nonneg.mpr zero_le_two, invOf_le_one one_le_two⟩, rfl⟩
#align midpoint_mem_segment midpoint_mem_segment

theorem mem_segment_sub_add [Invertible (2 : 𝕜)] (x y : E) : x ∈ [x - y -[𝕜] x + y] := by
  convert @midpoint_mem_segment 𝕜 _ _ _ _ _ (x - y) (x + y)
  rw [midpoint_sub_add]
#align mem_segment_sub_add mem_segment_sub_add

theorem mem_segment_add_sub [Invertible (2 : 𝕜)] (x y : E) : x ∈ [x + y -[𝕜] x - y] := by
  convert @midpoint_mem_segment 𝕜 _ _ _ _ _ (x + y) (x - y)
  rw [midpoint_add_sub]
#align mem_segment_add_sub mem_segment_add_sub

@[simp]
theorem left_mem_openSegment_iff [DenselyOrdered 𝕜] [NoZeroSMulDivisors 𝕜 E] :
    x ∈ openSegment 𝕜 x y ↔ x = y := by
  constructor
  · rintro ⟨a, b, _, hb, hab, hx⟩
    refine smul_right_injective _ hb.ne' ((add_right_inj (a • x)).1 ?_)
    rw [hx, ← add_smul, hab, one_smul]
  · rintro rfl
    rw [openSegment_same]
    exact mem_singleton _
#align left_mem_open_segment_iff left_mem_openSegment_iff

@[simp]
theorem right_mem_openSegment_iff [DenselyOrdered 𝕜] [NoZeroSMulDivisors 𝕜 E] :
    y ∈ openSegment 𝕜 x y ↔ x = y := by rw [openSegment_symm, left_mem_openSegment_iff, eq_comm]
#align right_mem_open_segment_iff right_mem_openSegment_iff

end LinearOrderedRing

section LinearOrderedSemifield

variable [LinearOrderedSemifield 𝕜] [AddCommGroup E] [Module 𝕜 E] {x y z : E}

theorem mem_segment_iff_div :
    x ∈ [y -[𝕜] z] ↔
      ∃ a b : 𝕜, 0 ≤ a ∧ 0 ≤ b ∧ 0 < a + b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    use a, b, ha, hb
    simp [*]
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨a / (a + b), b / (a + b), by positivity, by positivity, ?_, rfl⟩
    rw [← add_div, div_self hab.ne']
#align mem_segment_iff_div mem_segment_iff_div

theorem mem_openSegment_iff_div : x ∈ openSegment 𝕜 y z ↔
    ∃ a b : 𝕜, 0 < a ∧ 0 < b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    use a, b, ha, hb
    rw [hab, div_one, div_one]
  · rintro ⟨a, b, ha, hb, rfl⟩
    have hab : 0 < a + b := by positivity
    refine ⟨a / (a + b), b / (a + b), by positivity, by positivity, ?_, rfl⟩
    rw [← add_div, div_self hab.ne']
#align mem_open_segment_iff_div mem_openSegment_iff_div

end LinearOrderedSemifield

section LinearOrderedField

variable [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {x y z : E}

theorem mem_segment_iff_sameRay : x ∈ [y -[𝕜] z] ↔ SameRay 𝕜 (x - y) (z - x) := by
  refine ⟨sameRay_of_mem_segment, fun h => ?_⟩
  rcases h.exists_eq_smul_add with ⟨a, b, ha, hb, hab, hxy, hzx⟩
  rw [add_comm, sub_add_sub_cancel] at hxy hzx
  rw [← mem_segment_translate _ (-x), neg_add_self]
  refine ⟨b, a, hb, ha, add_comm a b ▸ hab, ?_⟩
  rw [← sub_eq_neg_add, ← neg_sub, hxy, ← sub_eq_neg_add, hzx, smul_neg, smul_comm, neg_add_self]
#align mem_segment_iff_same_ray mem_segment_iff_sameRay

open AffineMap

/-- If `z = lineMap x y c` is a point on the line passing through `x` and `y`, then the open
segment `openSegment 𝕜 x y` is included in the union of the open segments `openSegment 𝕜 x z`,
`openSegment 𝕜 z y`, and the point `z`. Informally, `(x, y) ⊆ {z} ∪ (x, z) ∪ (z, y)`. -/
theorem openSegment_subset_union (x y : E) {z : E} (hz : z ∈ range (lineMap x y : 𝕜 → E)) :
    openSegment 𝕜 x y ⊆ insert z (openSegment 𝕜 x z ∪ openSegment 𝕜 z y) := by
  rcases hz with ⟨c, rfl⟩
  simp only [openSegment_eq_image_lineMap, ← mapsTo']
  rintro a ⟨h₀, h₁⟩
  rcases lt_trichotomy a c with (hac | rfl | hca)
  · right
    left
    have hc : 0 < c := h₀.trans hac
    refine ⟨a / c, ⟨div_pos h₀ hc, (div_lt_one hc).2 hac⟩, ?_⟩
    simp only [← homothety_eq_lineMap, ← homothety_mul_apply, div_mul_cancel₀ _ hc.ne']
  · left
    rfl
  · right
    right
    have hc : 0 < 1 - c := sub_pos.2 (hca.trans h₁)
    simp only [← lineMap_apply_one_sub y]
    refine
      ⟨(a - c) / (1 - c), ⟨div_pos (sub_pos.2 hca) hc, (div_lt_one hc).2 <| sub_lt_sub_right h₁ _⟩,
        ?_⟩
    simp only [← homothety_eq_lineMap, ← homothety_mul_apply, sub_mul, one_mul,
      div_mul_cancel₀ _ hc.ne', sub_sub_sub_cancel_right]
#align open_segment_subset_union openSegment_subset_union

end LinearOrderedField

/-!
#### Segments in an ordered space

Relates `segment`, `openSegment` and `Set.Icc`, `Set.Ico`, `Set.Ioc`, `Set.Ioo`
-/


section OrderedSemiring

variable [OrderedSemiring 𝕜]

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid E] [Module 𝕜 E] [OrderedSMul 𝕜 E] {x y : E}

theorem segment_subset_Icc (h : x ≤ y) : [x -[𝕜] y] ⊆ Icc x y := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  constructor
  · calc
      x = a • x + b • x := (Convex.combo_self hab _).symm
      _ ≤ a • x + b • y := by gcongr
  · calc
      a • x + b • y ≤ a • y + b • y := by gcongr
      _ = y := Convex.combo_self hab _
#align segment_subset_Icc segment_subset_Icc

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid E] [Module 𝕜 E] [OrderedSMul 𝕜 E] {x y : E}

theorem openSegment_subset_Ioo (h : x < y) : openSegment 𝕜 x y ⊆ Ioo x y := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  constructor
  · calc
      x = a • x + b • x := (Convex.combo_self hab _).symm
      _ < a • x + b • y := by gcongr
  · calc
      a • x + b • y < a • y + b • y := by gcongr
      _ = y := Convex.combo_self hab _
#align open_segment_subset_Ioo openSegment_subset_Ioo

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid E] [Module 𝕜 E] [OrderedSMul 𝕜 E] {a b : 𝕜}

theorem segment_subset_uIcc (x y : E) : [x -[𝕜] y] ⊆ uIcc x y := by
  rcases le_total x y with h | h
  · rw [uIcc_of_le h]
    exact segment_subset_Icc h
  · rw [uIcc_of_ge h, segment_symm]
    exact segment_subset_Icc h
#align segment_subset_uIcc segment_subset_uIcc

theorem Convex.min_le_combo (x y : E) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    min x y ≤ a • x + b • y :=
  (segment_subset_uIcc x y ⟨_, _, ha, hb, hab, rfl⟩).1
#align convex.min_le_combo Convex.min_le_combo

theorem Convex.combo_le_max (x y : E) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ≤ max x y :=
  (segment_subset_uIcc x y ⟨_, _, ha, hb, hab, rfl⟩).2
#align convex.combo_le_max Convex.combo_le_max

end LinearOrderedAddCommMonoid

end OrderedSemiring

section LinearOrderedField

variable [LinearOrderedField 𝕜] {x y z : 𝕜}

theorem Icc_subset_segment : Icc x y ⊆ [x -[𝕜] y] := by
  rintro z ⟨hxz, hyz⟩
  obtain rfl | h := (hxz.trans hyz).eq_or_lt
  · rw [segment_same]
    exact hyz.antisymm hxz
  rw [← sub_nonneg] at hxz hyz
  rw [← sub_pos] at h
  refine ⟨(y - z) / (y - x), (z - x) / (y - x), div_nonneg hyz h.le, div_nonneg hxz h.le, ?_, ?_⟩
  · rw [← add_div, sub_add_sub_cancel, div_self h.ne']
  · rw [smul_eq_mul, smul_eq_mul, ← mul_div_right_comm, ← mul_div_right_comm, ← add_div,
      div_eq_iff h.ne', add_comm, sub_mul, sub_mul, mul_comm x, sub_add_sub_cancel, mul_sub]
#align Icc_subset_segment Icc_subset_segment

@[simp]
theorem segment_eq_Icc (h : x ≤ y) : [x -[𝕜] y] = Icc x y :=
  (segment_subset_Icc h).antisymm Icc_subset_segment
#align segment_eq_Icc segment_eq_Icc

theorem Ioo_subset_openSegment : Ioo x y ⊆ openSegment 𝕜 x y := fun _ hz =>
  mem_openSegment_of_ne_left_right hz.1.ne hz.2.ne' <| Icc_subset_segment <| Ioo_subset_Icc_self hz
#align Ioo_subset_open_segment Ioo_subset_openSegment

@[simp]
theorem openSegment_eq_Ioo (h : x < y) : openSegment 𝕜 x y = Ioo x y :=
  (openSegment_subset_Ioo h).antisymm Ioo_subset_openSegment
#align open_segment_eq_Ioo openSegment_eq_Ioo

theorem segment_eq_Icc' (x y : 𝕜) : [x -[𝕜] y] = Icc (min x y) (max x y) := by
  rcases le_total x y with h | h
  · rw [segment_eq_Icc h, max_eq_right h, min_eq_left h]
  · rw [segment_symm, segment_eq_Icc h, max_eq_left h, min_eq_right h]
#align segment_eq_Icc' segment_eq_Icc'

theorem openSegment_eq_Ioo' (hxy : x ≠ y) : openSegment 𝕜 x y = Ioo (min x y) (max x y) := by
  cases' hxy.lt_or_lt with h h
  · rw [openSegment_eq_Ioo h, max_eq_right h.le, min_eq_left h.le]
  · rw [openSegment_symm, openSegment_eq_Ioo h, max_eq_left h.le, min_eq_right h.le]
#align open_segment_eq_Ioo' openSegment_eq_Ioo'

theorem segment_eq_uIcc (x y : 𝕜) : [x -[𝕜] y] = uIcc x y :=
  segment_eq_Icc' _ _
#align segment_eq_uIcc segment_eq_uIcc

/-- A point is in an `Icc` iff it can be expressed as a convex combination of the endpoints. -/
theorem Convex.mem_Icc (h : x ≤ y) :
    z ∈ Icc x y ↔ ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * x + b * y = z := by
  rw [← segment_eq_Icc h]
  rfl
#align convex.mem_Icc Convex.mem_Icc

/-- A point is in an `Ioo` iff it can be expressed as a strict convex combination of the endpoints.
-/
theorem Convex.mem_Ioo (h : x < y) :
    z ∈ Ioo x y ↔ ∃ a b, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z := by
  rw [← openSegment_eq_Ioo h]
  rfl
#align convex.mem_Ioo Convex.mem_Ioo

/-- A point is in an `Ioc` iff it can be expressed as a semistrict convex combination of the
endpoints. -/
theorem Convex.mem_Ioc (h : x < y) :
    z ∈ Ioc x y ↔ ∃ a b, 0 ≤ a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z := by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := (Convex.mem_Icc h.le).1 (Ioc_subset_Icc_self hz)
    obtain rfl | hb' := hb.eq_or_lt
    · rw [add_zero] at hab
      rw [hab, one_mul, zero_mul, add_zero] at hz
      exact (hz.1.ne rfl).elim
    · exact ⟨a, b, ha, hb', hab, rfl⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    obtain rfl | ha' := ha.eq_or_lt
    · rw [zero_add] at hab
      rwa [hab, one_mul, zero_mul, zero_add, right_mem_Ioc]
    · exact Ioo_subset_Ioc_self ((Convex.mem_Ioo h).2 ⟨a, b, ha', hb, hab, rfl⟩)
#align convex.mem_Ioc Convex.mem_Ioc

/-- A point is in an `Ico` iff it can be expressed as a semistrict convex combination of the
endpoints. -/
theorem Convex.mem_Ico (h : x < y) :
    z ∈ Ico x y ↔ ∃ a b, 0 < a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * x + b * y = z := by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨a, b, ha, hb, hab, rfl⟩ := (Convex.mem_Icc h.le).1 (Ico_subset_Icc_self hz)
    obtain rfl | ha' := ha.eq_or_lt
    · rw [zero_add] at hab
      rw [hab, one_mul, zero_mul, zero_add] at hz
      exact (hz.2.ne rfl).elim
    · exact ⟨a, b, ha', hb, hab, rfl⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    obtain rfl | hb' := hb.eq_or_lt
    · rw [add_zero] at hab
      rwa [hab, one_mul, zero_mul, add_zero, left_mem_Ico]
    · exact Ioo_subset_Ico_self ((Convex.mem_Ioo h).2 ⟨a, b, ha, hb', hab, rfl⟩)
#align convex.mem_Ico Convex.mem_Ico

end LinearOrderedField

namespace Prod

variable [OrderedSemiring 𝕜] [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F]

theorem segment_subset (x y : E × F) : segment 𝕜 x y ⊆ segment 𝕜 x.1 y.1 ×ˢ segment 𝕜 x.2 y.2 := by
  rintro z ⟨a, b, ha, hb, hab, hz⟩
  exact ⟨⟨a, b, ha, hb, hab, congr_arg Prod.fst hz⟩, a, b, ha, hb, hab, congr_arg Prod.snd hz⟩
#align prod.segment_subset Prod.segment_subset

theorem openSegment_subset (x y : E × F) :
    openSegment 𝕜 x y ⊆ openSegment 𝕜 x.1 y.1 ×ˢ openSegment 𝕜 x.2 y.2 := by
  rintro z ⟨a, b, ha, hb, hab, hz⟩
  exact ⟨⟨a, b, ha, hb, hab, congr_arg Prod.fst hz⟩, a, b, ha, hb, hab, congr_arg Prod.snd hz⟩
#align prod.open_segment_subset Prod.openSegment_subset

theorem image_mk_segment_left (x₁ x₂ : E) (y : F) :
    (fun x => (x, y)) '' [x₁ -[𝕜] x₂] = [(x₁, y) -[𝕜] (x₂, y)] := by
  rw [segment_eq_image₂, segment_eq_image₂, image_image]
  refine EqOn.image_eq fun a ha ↦ ?_
  simp [Convex.combo_self ha.2.2]
#align prod.image_mk_segment_left Prod.image_mk_segment_left

theorem image_mk_segment_right (x : E) (y₁ y₂ : F) :
    (fun y => (x, y)) '' [y₁ -[𝕜] y₂] = [(x, y₁) -[𝕜] (x, y₂)] := by
  rw [segment_eq_image₂, segment_eq_image₂, image_image]
  refine EqOn.image_eq fun a ha ↦ ?_
  simp [Convex.combo_self ha.2.2]
#align prod.image_mk_segment_right Prod.image_mk_segment_right

theorem image_mk_openSegment_left (x₁ x₂ : E) (y : F) :
    (fun x => (x, y)) '' openSegment 𝕜 x₁ x₂ = openSegment 𝕜 (x₁, y) (x₂, y) := by
  rw [openSegment_eq_image₂, openSegment_eq_image₂, image_image]
  refine EqOn.image_eq fun a ha ↦ ?_
  simp [Convex.combo_self ha.2.2]
#align prod.image_mk_open_segment_left Prod.image_mk_openSegment_left

@[simp]
theorem image_mk_openSegment_right (x : E) (y₁ y₂ : F) :
    (fun y => (x, y)) '' openSegment 𝕜 y₁ y₂ = openSegment 𝕜 (x, y₁) (x, y₂) := by
  rw [openSegment_eq_image₂, openSegment_eq_image₂, image_image]
  refine EqOn.image_eq fun a ha ↦ ?_
  simp [Convex.combo_self ha.2.2]
#align prod.image_mk_open_segment_right Prod.image_mk_openSegment_right

end Prod

namespace Pi

variable [OrderedSemiring 𝕜] [∀ i, AddCommMonoid (π i)] [∀ i, Module 𝕜 (π i)] {s : Set ι}

theorem segment_subset (x y : ∀ i, π i) : segment 𝕜 x y ⊆ s.pi fun i => segment 𝕜 (x i) (y i) := by
  rintro z ⟨a, b, ha, hb, hab, hz⟩ i -
  exact ⟨a, b, ha, hb, hab, congr_fun hz i⟩
#align pi.segment_subset Pi.segment_subset

theorem openSegment_subset (x y : ∀ i, π i) :
    openSegment 𝕜 x y ⊆ s.pi fun i => openSegment 𝕜 (x i) (y i) := by
  rintro z ⟨a, b, ha, hb, hab, hz⟩ i -
  exact ⟨a, b, ha, hb, hab, congr_fun hz i⟩
#align pi.open_segment_subset Pi.openSegment_subset

variable [DecidableEq ι]

theorem image_update_segment (i : ι) (x₁ x₂ : π i) (y : ∀ i, π i) :
    update y i '' [x₁ -[𝕜] x₂] = [update y i x₁ -[𝕜] update y i x₂] := by
  rw [segment_eq_image₂, segment_eq_image₂, image_image]
  refine EqOn.image_eq fun a ha ↦ ?_
  simp only [← update_smul, ← update_add, Convex.combo_self ha.2.2]
#align pi.image_update_segment Pi.image_update_segment

theorem image_update_openSegment (i : ι) (x₁ x₂ : π i) (y : ∀ i, π i) :
    update y i '' openSegment 𝕜 x₁ x₂ = openSegment 𝕜 (update y i x₁) (update y i x₂) := by
  rw [openSegment_eq_image₂, openSegment_eq_image₂, image_image]
  refine EqOn.image_eq fun a ha ↦ ?_
  simp only [← update_smul, ← update_add, Convex.combo_self ha.2.2]
#align pi.image_update_open_segment Pi.image_update_openSegment

end Pi
