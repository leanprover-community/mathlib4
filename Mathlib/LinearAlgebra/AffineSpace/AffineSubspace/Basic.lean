/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-!
# Affine spaces

This file gives further properties of affine subspaces (over modules)
and the affine span of a set of points.

## Main definitions

* `AffineSubspace.Parallel`, notation `∥`, gives the property of two affine subspaces being
  parallel (one being a translate of the other).

-/

noncomputable section

open Affine

open Set
open scoped Pointwise

section

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P]

@[simp] lemma vectorSpan_vadd (s : Set P) (v : V) : vectorSpan k (v +ᵥ s) = vectorSpan k s := by
  simp [vectorSpan]

end


namespace AffineSubspace

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

variable {k P}


/-- Given a point in an affine subspace, a result of subtracting that point on the right is in the
direction if and only if the other point is in the subspace. -/
theorem vsub_right_mem_direction_iff_mem {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (p₂ : P) :
    p₂ -ᵥ p ∈ s.direction ↔ p₂ ∈ s := by
  rw [mem_direction_iff_eq_vsub_right hp]
  simp

/-- Given a point in an affine subspace, a result of subtracting that point on the left is in the
direction if and only if the other point is in the subspace. -/
theorem vsub_left_mem_direction_iff_mem {s : AffineSubspace k P} {p : P} (hp : p ∈ s) (p₂ : P) :
    p -ᵥ p₂ ∈ s.direction ↔ p₂ ∈ s := by
  rw [mem_direction_iff_eq_vsub_left hp]
  simp

instance toAddTorsor (s : AffineSubspace k P) [Nonempty s] : AddTorsor s.direction s where
  vadd a b := ⟨(a : V) +ᵥ (b : P), vadd_mem_of_mem_direction a.2 b.2⟩
  zero_vadd := fun a => by
    ext
    exact zero_vadd _ _
  add_vadd a b c := by
    ext
    apply add_vadd
  vsub a b := ⟨(a : P) -ᵥ (b : P), (vsub_left_mem_direction_iff_mem a.2 _).mpr b.2⟩
  vsub_vadd' a b := by
    ext
    apply AddTorsor.vsub_vadd'
  vadd_vsub' a b := by
    ext
    apply AddTorsor.vadd_vsub'

@[simp, norm_cast]
theorem coe_vsub (s : AffineSubspace k P) [Nonempty s] (a b : s) : ↑(a -ᵥ b) = (a : P) -ᵥ (b : P) :=
  rfl

@[simp, norm_cast]
theorem coe_vadd (s : AffineSubspace k P) [Nonempty s] (a : s.direction) (b : s) :
    ↑(a +ᵥ b) = (a : V) +ᵥ (b : P) :=
  rfl

/-- Embedding of an affine subspace to the ambient space, as an affine map. -/
protected def subtype (s : AffineSubspace k P) [Nonempty s] : s →ᵃ[k] P where
  toFun := (↑)
  linear := s.direction.subtype
  map_vadd' _ _ := rfl

@[simp]
theorem subtype_linear (s : AffineSubspace k P) [Nonempty s] :
    s.subtype.linear = s.direction.subtype := rfl

@[simp]
theorem subtype_apply {s : AffineSubspace k P} [Nonempty s] (p : s) : s.subtype p = p :=
  rfl

theorem subtype_injective (s : AffineSubspace k P) [Nonempty s] : Function.Injective s.subtype :=
  Subtype.coe_injective

@[simp]
theorem coe_subtype (s : AffineSubspace k P) [Nonempty s] : (s.subtype : s → P) = ((↑) : s → P) :=
  rfl

@[deprecated (since := "2025-02-18")]
alias coeSubtype := coe_subtype

end AffineSubspace

theorem AffineMap.lineMap_mem {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V]
    [AddTorsor V P] {Q : AffineSubspace k P} {p₀ p₁ : P} (c : k) (h₀ : p₀ ∈ Q) (h₁ : p₁ ∈ Q) :
    AffineMap.lineMap p₀ p₁ c ∈ Q := by
  rw [AffineMap.lineMap_apply]
  exact Q.smul_vsub_vadd_mem c h₁ h₀ h₀

namespace AffineSubspace

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AffineSpace V P]

variable (k V) {p₁ p₂ : P}

/-- The affine span of a single point, coerced to a set, contains just that point. -/
@[simp high] -- This needs to take priority over `coe_affineSpan`
theorem coe_affineSpan_singleton (p : P) : (affineSpan k ({p} : Set P) : Set P) = {p} := by
  ext x
  rw [mem_coe, ← vsub_right_mem_direction_iff_mem (mem_affineSpan k (Set.mem_singleton p)) _,
    direction_affineSpan]
  simp

/-- A point is in the affine span of a single point if and only if they are equal. -/
@[simp]
theorem mem_affineSpan_singleton : p₁ ∈ affineSpan k ({p₂} : Set P) ↔ p₁ = p₂ := by
  simp [← mem_coe]

instance unique_affineSpan_singleton (p : P) : Unique (affineSpan k {p}) where
  default := ⟨p, mem_affineSpan _ (Set.mem_singleton _)⟩
  uniq := fun x ↦ Subtype.ext ((mem_affineSpan_singleton _ _).1 x.property)

@[simp]
theorem preimage_coe_affineSpan_singleton (x : P) :
    ((↑) : affineSpan k ({x} : Set P) → P) ⁻¹' {x} = univ :=
  eq_univ_of_forall fun y => (AffineSubspace.mem_affineSpan_singleton _ _).1 y.2

variable (P)

/-- The top affine subspace is linearly equivalent to the affine space.
This is the affine version of `Submodule.topEquiv`. -/
@[simps! linear apply symm_apply_coe]
def topEquiv : (⊤ : AffineSubspace k P) ≃ᵃ[k] P where
  toEquiv := Equiv.Set.univ P
  linear := .ofEq _ _ (direction_top _ _ _) ≪≫ₗ Submodule.topEquiv
  map_vadd' _ _ := rfl

variable {k V P}

theorem subsingleton_of_subsingleton_span_eq_top {s : Set P} (h₁ : s.Subsingleton)
    (h₂ : affineSpan k s = ⊤) : Subsingleton P := by
  obtain ⟨p, hp⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top k V P h₂
  have : s = {p} := Subset.antisymm (fun q hq => h₁ hq hp) (by simp [hp])
  rw [this, AffineSubspace.ext_iff, AffineSubspace.coe_affineSpan_singleton,
    AffineSubspace.top_coe, eq_comm, ← subsingleton_iff_singleton (mem_univ _)] at h₂
  exact subsingleton_of_univ_subsingleton h₂

theorem eq_univ_of_subsingleton_span_eq_top {s : Set P} (h₁ : s.Subsingleton)
    (h₂ : affineSpan k s = ⊤) : s = (univ : Set P) := by
  obtain ⟨p, hp⟩ := AffineSubspace.nonempty_of_affineSpan_eq_top k V P h₂
  have : s = {p} := Subset.antisymm (fun q hq => h₁ hq hp) (by simp [hp])
  rw [this, eq_comm, ← subsingleton_iff_singleton (mem_univ p), subsingleton_univ_iff]
  exact subsingleton_of_subsingleton_span_eq_top h₁ h₂

/-- If one nonempty affine subspace is less than another, the same applies to their directions -/
theorem direction_lt_of_nonempty {s₁ s₂ : AffineSubspace k P} (h : s₁ < s₂)
    (hn : (s₁ : Set P).Nonempty) : s₁.direction < s₂.direction := by
  obtain ⟨p, hp⟩ := hn
  rw [lt_iff_le_and_exists] at h
  rcases h with ⟨hle, p₂, hp₂, hp₂s₁⟩
  rw [SetLike.lt_iff_le_and_exists]
  use direction_le hle, p₂ -ᵥ p, vsub_mem_direction hp₂ (hle hp)
  intro hm
  rw [vsub_right_mem_direction_iff_mem hp p₂] at hm
  exact hp₂s₁ hm

end AffineSubspace

section AffineSpace'

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

variable {ι : Type*}

open AffineSubspace Set

/-- The `vectorSpan` is the span of the pairwise subtractions with a given point on the left. -/
theorem vectorSpan_eq_span_vsub_set_left {s : Set P} {p : P} (hp : p ∈ s) :
    vectorSpan k s = Submodule.span k ((p -ᵥ ·) '' s) := by
  rw [vectorSpan_def]
  refine le_antisymm ?_ (Submodule.span_mono ?_)
  · rw [Submodule.span_le]
    rintro v ⟨p₁, hp₁, p₂, hp₂, hv⟩
    simp_rw [← vsub_sub_vsub_cancel_left p₁ p₂ p] at hv
    rw [← hv, SetLike.mem_coe, Submodule.mem_span]
    exact fun m hm => Submodule.sub_mem _ (hm ⟨p₂, hp₂, rfl⟩) (hm ⟨p₁, hp₁, rfl⟩)
  · rintro v ⟨p₂, hp₂, hv⟩
    exact ⟨p, hp, p₂, hp₂, hv⟩

/-- The `vectorSpan` is the span of the pairwise subtractions with a given point on the right. -/
theorem vectorSpan_eq_span_vsub_set_right {s : Set P} {p : P} (hp : p ∈ s) :
    vectorSpan k s = Submodule.span k ((· -ᵥ p) '' s) := by
  rw [vectorSpan_def]
  refine le_antisymm ?_ (Submodule.span_mono ?_)
  · rw [Submodule.span_le]
    rintro v ⟨p₁, hp₁, p₂, hp₂, hv⟩
    simp_rw [← vsub_sub_vsub_cancel_right p₁ p₂ p] at hv
    rw [← hv, SetLike.mem_coe, Submodule.mem_span]
    exact fun m hm => Submodule.sub_mem _ (hm ⟨p₁, hp₁, rfl⟩) (hm ⟨p₂, hp₂, rfl⟩)
  · rintro v ⟨p₂, hp₂, hv⟩
    exact ⟨p₂, hp₂, p, hp, hv⟩

/-- The `vectorSpan` is the span of the pairwise subtractions with a given point on the left,
excluding the subtraction of that point from itself. -/
theorem vectorSpan_eq_span_vsub_set_left_ne {s : Set P} {p : P} (hp : p ∈ s) :
    vectorSpan k s = Submodule.span k ((p -ᵥ ·) '' (s \ {p})) := by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_left k hp, ← Set.insert_eq_of_mem hp, ←
      Set.insert_diff_singleton, Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

/-- The `vectorSpan` is the span of the pairwise subtractions with a given point on the right,
excluding the subtraction of that point from itself. -/
theorem vectorSpan_eq_span_vsub_set_right_ne {s : Set P} {p : P} (hp : p ∈ s) :
    vectorSpan k s = Submodule.span k ((· -ᵥ p) '' (s \ {p})) := by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_right k hp, ← Set.insert_eq_of_mem hp, ←
      Set.insert_diff_singleton, Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

/-- The `vectorSpan` is the span of the pairwise subtractions with a given point on the right,
excluding the subtraction of that point from itself. -/
theorem vectorSpan_eq_span_vsub_finset_right_ne [DecidableEq P] [DecidableEq V] {s : Finset P}
    {p : P} (hp : p ∈ s) :
    vectorSpan k (s : Set P) = Submodule.span k ((s.erase p).image (· -ᵥ p)) := by
  simp [vectorSpan_eq_span_vsub_set_right_ne _ (Finset.mem_coe.mpr hp)]

/-- The `vectorSpan` of the image of a function is the span of the pairwise subtractions with a
given point on the left, excluding the subtraction of that point from itself. -/
theorem vectorSpan_image_eq_span_vsub_set_left_ne (p : ι → P) {s : Set ι} {i : ι} (hi : i ∈ s) :
    vectorSpan k (p '' s) = Submodule.span k ((p i -ᵥ ·) '' (p '' (s \ {i}))) := by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_left k (Set.mem_image_of_mem p hi), ← Set.insert_eq_of_mem hi, ←
      Set.insert_diff_singleton, Set.image_insert_eq, Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

/-- The `vectorSpan` of the image of a function is the span of the pairwise subtractions with a
given point on the right, excluding the subtraction of that point from itself. -/
theorem vectorSpan_image_eq_span_vsub_set_right_ne (p : ι → P) {s : Set ι} {i : ι} (hi : i ∈ s) :
    vectorSpan k (p '' s) = Submodule.span k ((· -ᵥ p i) '' (p '' (s \ {i}))) := by
  conv_lhs =>
    rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_image_of_mem p hi), ← Set.insert_eq_of_mem hi,
      ← Set.insert_diff_singleton, Set.image_insert_eq, Set.image_insert_eq]
  simp [Submodule.span_insert_eq_span]

/-- The `vectorSpan` of an indexed family is the span of the pairwise subtractions with a given
point on the left. -/
theorem vectorSpan_range_eq_span_range_vsub_left (p : ι → P) (i0 : ι) :
    vectorSpan k (Set.range p) = Submodule.span k (Set.range fun i : ι => p i0 -ᵥ p i) := by
  rw [vectorSpan_eq_span_vsub_set_left k (Set.mem_range_self i0), ← Set.range_comp]
  congr

/-- The `vectorSpan` of an indexed family is the span of the pairwise subtractions with a given
point on the right. -/
theorem vectorSpan_range_eq_span_range_vsub_right (p : ι → P) (i0 : ι) :
    vectorSpan k (Set.range p) = Submodule.span k (Set.range fun i : ι => p i -ᵥ p i0) := by
  rw [vectorSpan_eq_span_vsub_set_right k (Set.mem_range_self i0), ← Set.range_comp]
  congr

/-- The `vectorSpan` of an indexed family is the span of the pairwise subtractions with a given
point on the left, excluding the subtraction of that point from itself. -/
theorem vectorSpan_range_eq_span_range_vsub_left_ne (p : ι → P) (i₀ : ι) :
    vectorSpan k (Set.range p) =
      Submodule.span k (Set.range fun i : { x // x ≠ i₀ } => p i₀ -ᵥ p i) := by
  rw [← Set.image_univ, vectorSpan_image_eq_span_vsub_set_left_ne k _ (Set.mem_univ i₀)]
  congr with v
  simp only [Set.mem_range, Set.mem_image, Set.mem_diff, Set.mem_singleton_iff, Subtype.exists]
  constructor
  · rintro ⟨x, ⟨i₁, ⟨⟨_, hi₁⟩, rfl⟩⟩, hv⟩
    exact ⟨i₁, hi₁, hv⟩
  · exact fun ⟨i₁, hi₁, hv⟩ => ⟨p i₁, ⟨i₁, ⟨Set.mem_univ _, hi₁⟩, rfl⟩, hv⟩

/-- The `vectorSpan` of an indexed family is the span of the pairwise subtractions with a given
point on the right, excluding the subtraction of that point from itself. -/
theorem vectorSpan_range_eq_span_range_vsub_right_ne (p : ι → P) (i₀ : ι) :
    vectorSpan k (Set.range p) =
      Submodule.span k (Set.range fun i : { x // x ≠ i₀ } => p i -ᵥ p i₀) := by
  rw [← Set.image_univ, vectorSpan_image_eq_span_vsub_set_right_ne k _ (Set.mem_univ i₀)]
  congr with v
  simp only [Set.mem_range, Set.mem_image, Set.mem_diff, Set.mem_singleton_iff, Subtype.exists]
  constructor
  · rintro ⟨x, ⟨i₁, ⟨⟨_, hi₁⟩, rfl⟩⟩, hv⟩
    exact ⟨i₁, hi₁, hv⟩
  · exact fun ⟨i₁, hi₁, hv⟩ => ⟨p i₁, ⟨i₁, ⟨Set.mem_univ _, hi₁⟩, rfl⟩, hv⟩

variable {k}

/-- A set, considered as a subset of its spanned affine subspace, spans the whole subspace. -/
@[simp]
theorem affineSpan_coe_preimage_eq_top (A : Set P) [Nonempty A] :
    affineSpan k (((↑) : affineSpan k A → P) ⁻¹' A) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  refine affineSpan_induction' (fun y hy ↦ ?_) (fun c u hu v hv w hw ↦ ?_) hx
  · exact subset_affineSpan _ _ hy
  · exact AffineSubspace.smul_vsub_vadd_mem _ _

/-- Suppose a set of vectors spans `V`.  Then a point `p`, together with those vectors added to `p`,
spans `P`. -/
theorem affineSpan_singleton_union_vadd_eq_top_of_span_eq_top {s : Set V} (p : P)
    (h : Submodule.span k (Set.range ((↑) : s → V)) = ⊤) :
    affineSpan k ({p} ∪ (fun v => v +ᵥ p) '' s) = ⊤ := by
  convert ext_of_direction_eq _
      ⟨p, mem_affineSpan k (Set.mem_union_left _ (Set.mem_singleton _)), mem_top k V p⟩
  rw [direction_affineSpan, direction_top,
    vectorSpan_eq_span_vsub_set_right k (Set.mem_union_left _ (Set.mem_singleton _) : p ∈ _),
    eq_top_iff, ← h]
  apply Submodule.span_mono
  rintro v ⟨v', rfl⟩
  use (v' : V) +ᵥ p
  simp

variable (k)

/-- The `vectorSpan` of two points is the span of their difference. -/
theorem vectorSpan_pair (p₁ p₂ : P) : vectorSpan k ({p₁, p₂} : Set P) = k ∙ p₁ -ᵥ p₂ := by
  simp_rw [vectorSpan_eq_span_vsub_set_left k (mem_insert p₁ _), image_pair, vsub_self,
    Submodule.span_insert_zero]

/-- The `vectorSpan` of two points is the span of their difference (reversed). -/
theorem vectorSpan_pair_rev (p₁ p₂ : P) : vectorSpan k ({p₁, p₂} : Set P) = k ∙ p₂ -ᵥ p₁ := by
  rw [pair_comm, vectorSpan_pair]

variable {k}

/-- A vector lies in the `vectorSpan` of two points if and only if it is a multiple of their
difference. -/
theorem mem_vectorSpan_pair {p₁ p₂ : P} {v : V} :
    v ∈ vectorSpan k ({p₁, p₂} : Set P) ↔ ∃ r : k, r • (p₁ -ᵥ p₂) = v := by
  rw [vectorSpan_pair, Submodule.mem_span_singleton]

/-- A vector lies in the `vectorSpan` of two points if and only if it is a multiple of their
difference (reversed). -/
theorem mem_vectorSpan_pair_rev {p₁ p₂ : P} {v : V} :
    v ∈ vectorSpan k ({p₁, p₂} : Set P) ↔ ∃ r : k, r • (p₂ -ᵥ p₁) = v := by
  rw [vectorSpan_pair_rev, Submodule.mem_span_singleton]


/-- A combination of two points expressed with `lineMap` lies in their affine span. -/
theorem AffineMap.lineMap_mem_affineSpan_pair (r : k) (p₁ p₂ : P) :
    AffineMap.lineMap p₁ p₂ r ∈ line[k, p₁, p₂] :=
  AffineMap.lineMap_mem _ (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _)

/-- A combination of two points expressed with `lineMap` (with the two points reversed) lies in
their affine span. -/
theorem AffineMap.lineMap_rev_mem_affineSpan_pair (r : k) (p₁ p₂ : P) :
    AffineMap.lineMap p₂ p₁ r ∈ line[k, p₁, p₂] :=
  AffineMap.lineMap_mem _ (right_mem_affineSpan_pair _ _ _) (left_mem_affineSpan_pair _ _ _)

/-- A multiple of the difference of two points added to the first point lies in their affine
span. -/
theorem smul_vsub_vadd_mem_affineSpan_pair (r : k) (p₁ p₂ : P) :
    r • (p₂ -ᵥ p₁) +ᵥ p₁ ∈ line[k, p₁, p₂] :=
  AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- A multiple of the difference of two points added to the second point lies in their affine
span. -/
theorem smul_vsub_rev_vadd_mem_affineSpan_pair (r : k) (p₁ p₂ : P) :
    r • (p₁ -ᵥ p₂) +ᵥ p₂ ∈ line[k, p₁, p₂] :=
  AffineMap.lineMap_rev_mem_affineSpan_pair _ _ _

/-- A vector added to the first point lies in the affine span of two points if and only if it is
a multiple of their difference. -/
theorem vadd_left_mem_affineSpan_pair {p₁ p₂ : P} {v : V} :
    v +ᵥ p₁ ∈ line[k, p₁, p₂] ↔ ∃ r : k, r • (p₂ -ᵥ p₁) = v := by
  rw [vadd_mem_iff_mem_direction _ (left_mem_affineSpan_pair _ _ _), direction_affineSpan,
    mem_vectorSpan_pair_rev]

/-- A vector added to the second point lies in the affine span of two points if and only if it is
a multiple of their difference. -/
theorem vadd_right_mem_affineSpan_pair {p₁ p₂ : P} {v : V} :
    v +ᵥ p₂ ∈ line[k, p₁, p₂] ↔ ∃ r : k, r • (p₁ -ᵥ p₂) = v := by
  rw [vadd_mem_iff_mem_direction _ (right_mem_affineSpan_pair _ _ _), direction_affineSpan,
    mem_vectorSpan_pair]

end AffineSpace'

namespace AffineSubspace

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AffineSpace V P]

/-- The direction of the sup of two nonempty affine subspaces is the sup of the two directions and
of any one difference between points in the two subspaces. -/
theorem direction_sup {s₁ s₂ : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s₁) (hp₂ : p₂ ∈ s₂) :
    (s₁ ⊔ s₂).direction = s₁.direction ⊔ s₂.direction ⊔ k ∙ p₂ -ᵥ p₁ := by
  refine le_antisymm ?_ ?_
  · change (affineSpan k ((s₁ : Set P) ∪ s₂)).direction ≤ _
    rw [← mem_coe] at hp₁
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right k (Set.mem_union_left _ hp₁),
      Submodule.span_le]
    rintro v ⟨p₃, hp₃, rfl⟩
    rcases hp₃ with hp₃ | hp₃
    · rw [sup_assoc, sup_comm, SetLike.mem_coe, Submodule.mem_sup]
      use 0, Submodule.zero_mem _, p₃ -ᵥ p₁, vsub_mem_direction hp₃ hp₁
      rw [zero_add]
    · rw [sup_assoc, SetLike.mem_coe, Submodule.mem_sup]
      use 0, Submodule.zero_mem _, p₃ -ᵥ p₁
      rw [and_comm, zero_add]
      use rfl
      rw [← vsub_add_vsub_cancel p₃ p₂ p₁, Submodule.mem_sup]
      use p₃ -ᵥ p₂, vsub_mem_direction hp₃ hp₂, p₂ -ᵥ p₁, Submodule.mem_span_singleton_self _
  · refine sup_le (sup_direction_le _ _) ?_
    rw [direction_eq_vectorSpan, vectorSpan_def]
    exact
      sInf_le_sInf fun p hp =>
        Set.Subset.trans
          (Set.singleton_subset_iff.2
            (vsub_mem_vsub (mem_affineSpan k (Set.mem_union_right _ hp₂))
              (mem_affineSpan k (Set.mem_union_left _ hp₁))))
          hp

/-- The direction of the sup of two affine subspaces with a common point is the sup of the two
directions. -/
lemma direction_sup_eq_sup_direction {s₁ s₂ : AffineSubspace k P} {p : P} (hp₁ : p ∈ s₁)
    (hp₂ : p ∈ s₂) : (s₁ ⊔ s₂).direction = s₁.direction ⊔ s₂.direction := by
  rw [direction_sup hp₁ hp₂]
  simp

/-- The direction of the span of the result of adding a point to a nonempty affine subspace is the
sup of the direction of that subspace and of any one difference between that point and a point in
the subspace. -/
theorem direction_affineSpan_insert {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s) :
    (affineSpan k (insert p₂ (s : Set P))).direction =
    Submodule.span k {p₂ -ᵥ p₁} ⊔ s.direction := by
  rw [sup_comm, ← Set.union_singleton, ← coe_affineSpan_singleton k V p₂]
  change (s ⊔ affineSpan k {p₂}).direction = _
  rw [direction_sup hp₁ (mem_affineSpan k (Set.mem_singleton _)), direction_affineSpan]
  simp

/-- Given a point `p₁` in an affine subspace `s`, and a point `p₂`, a point `p` is in the span of
`s` with `p₂` added if and only if it is a multiple of `p₂ -ᵥ p₁` added to a point in `s`. -/
theorem mem_affineSpan_insert_iff {s : AffineSubspace k P} {p₁ : P} (hp₁ : p₁ ∈ s) (p₂ p : P) :
    p ∈ affineSpan k (insert p₂ (s : Set P)) ↔
      ∃ r : k, ∃ p0 ∈ s, p = r • (p₂ -ᵥ p₁ : V) +ᵥ p0 := by
  rw [← mem_coe] at hp₁
  rw [← vsub_right_mem_direction_iff_mem (mem_affineSpan k (Set.mem_insert_of_mem _ hp₁)),
    direction_affineSpan_insert hp₁, Submodule.mem_sup]
  constructor
  · rintro ⟨v₁, hv₁, v₂, hv₂, hp⟩
    rw [Submodule.mem_span_singleton] at hv₁
    rcases hv₁ with ⟨r, rfl⟩
    use r, v₂ +ᵥ p₁, vadd_mem_of_mem_direction hv₂ hp₁
    symm at hp
    rw [← sub_eq_zero, ← vsub_vadd_eq_vsub_sub, vsub_eq_zero_iff_eq] at hp
    rw [hp, vadd_vadd]
  · rintro ⟨r, p₃, hp₃, rfl⟩
    use r • (p₂ -ᵥ p₁), Submodule.mem_span_singleton.2 ⟨r, rfl⟩, p₃ -ᵥ p₁,
      vsub_mem_direction hp₃ hp₁
    rw [vadd_vsub_assoc]

variable (k) in
/-- The vector span of a union of sets with a common point is the sup of their vector spans. -/
lemma vectorSpan_union_of_mem_of_mem {s₁ s₂ : Set P} {p : P} (hp₁ : p ∈ s₁) (hp₂ : p ∈ s₂) :
    vectorSpan k (s₁ ∪ s₂) = vectorSpan k s₁ ⊔ vectorSpan k s₂ := by
  simp_rw [← direction_affineSpan, span_union,
    direction_sup_eq_sup_direction (mem_affineSpan k hp₁) (mem_affineSpan k hp₂)]

end AffineSubspace

section MapComap

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]
variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]
variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

section

variable (f : P₁ →ᵃ[k] P₂)

@[simp]
theorem AffineMap.vectorSpan_image_eq_submodule_map {s : Set P₁} :
    Submodule.map f.linear (vectorSpan k s) = vectorSpan k (f '' s) := by
  simp [vectorSpan_def, f.image_vsub_image]

namespace AffineSubspace

/-- The image of an affine subspace under an affine map as an affine subspace. -/
def map (s : AffineSubspace k P₁) : AffineSubspace k P₂ where
  carrier := f '' s
  smul_vsub_vadd_mem := by
    rintro t - - - ⟨p₁, h₁, rfl⟩ ⟨p₂, h₂, rfl⟩ ⟨p₃, h₃, rfl⟩
    use t • (p₁ -ᵥ p₂) +ᵥ p₃
    suffices t • (p₁ -ᵥ p₂) +ᵥ p₃ ∈ s by
    { simp only [SetLike.mem_coe, true_and, this]
      rw [AffineMap.map_vadd, map_smul, AffineMap.linearMap_vsub] }
    exact s.smul_vsub_vadd_mem t h₁ h₂ h₃

@[simp]
theorem coe_map (s : AffineSubspace k P₁) : (s.map f : Set P₂) = f '' s :=
  rfl

@[simp]
theorem mem_map {f : P₁ →ᵃ[k] P₂} {x : P₂} {s : AffineSubspace k P₁} :
    x ∈ s.map f ↔ ∃ y ∈ s, f y = x :=
  Iff.rfl

theorem mem_map_of_mem {x : P₁} {s : AffineSubspace k P₁} (h : x ∈ s) : f x ∈ s.map f :=
  Set.mem_image_of_mem _ h

@[simp 1100]
theorem mem_map_iff_mem_of_injective {f : P₁ →ᵃ[k] P₂} {x : P₁} {s : AffineSubspace k P₁}
    (hf : Function.Injective f) : f x ∈ s.map f ↔ x ∈ s :=
  hf.mem_set_image

@[simp]
theorem map_bot : (⊥ : AffineSubspace k P₁).map f = ⊥ :=
  coe_injective <| image_empty f

@[simp]
theorem map_eq_bot_iff {s : AffineSubspace k P₁} : s.map f = ⊥ ↔ s = ⊥ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rwa [← coe_eq_bot_iff, coe_map, image_eq_empty, coe_eq_bot_iff] at h
  · rw [h, map_bot]

@[simp]
theorem map_id (s : AffineSubspace k P₁) : s.map (AffineMap.id k P₁) = s :=
  coe_injective <| image_id _

theorem map_map (s : AffineSubspace k P₁) (f : P₁ →ᵃ[k] P₂) (g : P₂ →ᵃ[k] P₃) :
    (s.map f).map g = s.map (g.comp f) :=
  coe_injective <| image_image _ _ _

@[simp]
theorem map_direction (s : AffineSubspace k P₁) :
    (s.map f).direction = s.direction.map f.linear := by
  simp [direction_eq_vectorSpan, AffineMap.vectorSpan_image_eq_submodule_map]

theorem map_span (s : Set P₁) : (affineSpan k s).map f = affineSpan k (f '' s) := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p, hp⟩)
  · simp
  apply ext_of_direction_eq
  · simp [direction_affineSpan]
  · exact ⟨f p, mem_image_of_mem f (subset_affineSpan k _ hp),
          subset_affineSpan k _ (mem_image_of_mem f hp)⟩

@[gcongr]
theorem map_mono {s₁ s₂ : AffineSubspace k P₁} (h : s₁ ≤ s₂) : s₁.map f ≤ s₂.map f :=
  Set.image_mono h

section inclusion
variable {S₁ S₂ : AffineSubspace k P₁} [Nonempty S₁]

/-- Affine map from a smaller to a larger subspace of the same space.

This is the affine version of `Submodule.inclusion`. -/
@[simps linear]
def inclusion (h : S₁ ≤ S₂) :
    letI := Nonempty.map (Set.inclusion h) ‹_›
    S₁ →ᵃ[k] S₂ :=
  letI := Nonempty.map (Set.inclusion h) ‹_›
  { toFun := Set.inclusion h
    linear := Submodule.inclusion <| AffineSubspace.direction_le h
    map_vadd' := fun ⟨_,_⟩ ⟨_,_⟩ => rfl }

@[simp]
theorem coe_inclusion_apply (h : S₁ ≤ S₂) (x : S₁) : (inclusion h x : P₁) = x :=
  rfl

@[simp]
theorem inclusion_rfl : inclusion (le_refl S₁) = AffineMap.id k S₁ := rfl

end inclusion

end AffineSubspace

namespace AffineMap

@[simp]
theorem map_top_of_surjective (hf : Function.Surjective f) : AffineSubspace.map f ⊤ = ⊤ := by
  rw [AffineSubspace.ext_iff]
  exact image_univ_of_surjective hf

theorem span_eq_top_of_surjective {s : Set P₁} (hf : Function.Surjective f)
    (h : affineSpan k s = ⊤) : affineSpan k (f '' s) = ⊤ := by
  rw [← AffineSubspace.map_span, h, map_top_of_surjective f hf]

end AffineMap

namespace AffineEquiv

section ofEq
variable (S₁ S₂ : AffineSubspace k P₁) [Nonempty S₁] [Nonempty S₂]

/-- Affine equivalence between two equal affine subspace.

This is the affine version of `LinearEquiv.ofEq`. -/
@[simps linear]
def ofEq (h : S₁ = S₂) : S₁ ≃ᵃ[k] S₂ where
  toEquiv := Equiv.setCongr <| congr_arg _ h
  linear := .ofEq _ _ <| congr_arg _ h
  map_vadd' := fun ⟨_,_⟩ ⟨_,_⟩ => rfl

@[simp]
theorem coe_ofEq_apply (h : S₁ = S₂) (x : S₁) : (ofEq S₁ S₂ h x : P₁) = x :=
  rfl

@[simp]
theorem ofEq_symm (h : S₁ = S₂) : (ofEq S₁ S₂ h).symm = ofEq S₂ S₁ h.symm := by
  ext
  rfl

@[simp]
theorem ofEq_rfl : ofEq S₁ S₁ rfl = AffineEquiv.refl k S₁ := rfl

end ofEq

theorem span_eq_top_iff {s : Set P₁} (e : P₁ ≃ᵃ[k] P₂) :
    affineSpan k s = ⊤ ↔ affineSpan k (e '' s) = ⊤ := by
  refine ⟨(e : P₁ →ᵃ[k] P₂).span_eq_top_of_surjective e.surjective, ?_⟩
  intro h
  have : s = e.symm '' (e '' s) := by rw [← image_comp]; simp
  rw [this]
  exact (e.symm : P₂ →ᵃ[k] P₁).span_eq_top_of_surjective e.symm.surjective h

end AffineEquiv

end

namespace AffineSubspace

/-- The preimage of an affine subspace under an affine map as an affine subspace. -/
def comap (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₂) : AffineSubspace k P₁ where
  carrier := f ⁻¹' s
  smul_vsub_vadd_mem t p₁ p₂ p₃ (hp₁ : f p₁ ∈ s) (hp₂ : f p₂ ∈ s) (hp₃ : f p₃ ∈ s) :=
    show f _ ∈ s by
      rw [AffineMap.map_vadd, LinearMap.map_smul, AffineMap.linearMap_vsub]
      apply s.smul_vsub_vadd_mem _ hp₁ hp₂ hp₃

@[simp]
theorem coe_comap (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₂) : (s.comap f : Set P₁) = f ⁻¹' ↑s :=
  rfl

@[simp]
theorem mem_comap {f : P₁ →ᵃ[k] P₂} {x : P₁} {s : AffineSubspace k P₂} : x ∈ s.comap f ↔ f x ∈ s :=
  Iff.rfl

theorem comap_mono {f : P₁ →ᵃ[k] P₂} {s t : AffineSubspace k P₂} : s ≤ t → s.comap f ≤ t.comap f :=
  preimage_mono

@[simp]
theorem comap_top {f : P₁ →ᵃ[k] P₂} : (⊤ : AffineSubspace k P₂).comap f = ⊤ := by
  rw [AffineSubspace.ext_iff]
  exact preimage_univ (f := f)

@[simp] theorem comap_bot (f : P₁ →ᵃ[k] P₂) : comap f ⊥ = ⊥ := rfl

@[simp]
theorem comap_id (s : AffineSubspace k P₁) : s.comap (AffineMap.id k P₁) = s :=
  rfl

theorem comap_comap (s : AffineSubspace k P₃) (f : P₁ →ᵃ[k] P₂) (g : P₂ →ᵃ[k] P₃) :
    (s.comap g).comap f = s.comap (g.comp f) :=
  rfl

-- lemmas about map and comap derived from the Galois connection
theorem map_le_iff_le_comap {f : P₁ →ᵃ[k] P₂} {s : AffineSubspace k P₁} {t : AffineSubspace k P₂} :
    s.map f ≤ t ↔ s ≤ t.comap f :=
  image_subset_iff

theorem gc_map_comap (f : P₁ →ᵃ[k] P₂) : GaloisConnection (map f) (comap f) := fun _ _ =>
  map_le_iff_le_comap

theorem map_comap_le (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₂) : (s.comap f).map f ≤ s :=
  (gc_map_comap f).l_u_le _

theorem le_comap_map (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₁) : s ≤ (s.map f).comap f :=
  (gc_map_comap f).le_u_l _

theorem map_sup (s t : AffineSubspace k P₁) (f : P₁ →ᵃ[k] P₂) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup

theorem map_iSup {ι : Sort*} (f : P₁ →ᵃ[k] P₂) (s : ι → AffineSubspace k P₁) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

theorem comap_inf (s t : AffineSubspace k P₂) (f : P₁ →ᵃ[k] P₂) :
    (s ⊓ t).comap f = s.comap f ⊓ t.comap f :=
  (gc_map_comap f).u_inf

theorem comap_supr {ι : Sort*} (f : P₁ →ᵃ[k] P₂) (s : ι → AffineSubspace k P₂) :
    (iInf s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_iInf

@[simp]
theorem comap_symm (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁) :
    s.comap (e.symm : P₂ →ᵃ[k] P₁) = s.map e :=
  coe_injective <| e.preimage_symm _

@[simp]
theorem map_symm (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₂) :
    s.map (e.symm : P₂ →ᵃ[k] P₁) = s.comap e :=
  coe_injective <| e.image_symm _

theorem comap_span (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) :
    (affineSpan k s).comap (f : P₁ →ᵃ[k] P₂) = affineSpan k (f ⁻¹' s) := by
  rw [← map_symm, map_span, AffineEquiv.coe_coe, f.image_symm]

end AffineSubspace

end MapComap

namespace AffineSubspace

open AffineEquiv

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P]

/-- Two affine subspaces are parallel if one is related to the other by adding the same vector
to all points. -/
def Parallel (s₁ s₂ : AffineSubspace k P) : Prop :=
  ∃ v : V, s₂ = s₁.map (constVAdd k P v)

@[inherit_doc]
scoped[Affine] infixl:50 " ∥ " => AffineSubspace.Parallel

@[symm]
theorem Parallel.symm {s₁ s₂ : AffineSubspace k P} (h : s₁ ∥ s₂) : s₂ ∥ s₁ := by
  rcases h with ⟨v, rfl⟩
  refine ⟨-v, ?_⟩
  rw [map_map, ← coe_trans_to_affineMap, ← constVAdd_add, neg_add_cancel, constVAdd_zero,
    coe_refl_to_affineMap, map_id]

theorem parallel_comm {s₁ s₂ : AffineSubspace k P} : s₁ ∥ s₂ ↔ s₂ ∥ s₁ :=
  ⟨Parallel.symm, Parallel.symm⟩

@[refl]
theorem Parallel.refl (s : AffineSubspace k P) : s ∥ s :=
  ⟨0, by simp⟩

@[trans]
theorem Parallel.trans {s₁ s₂ s₃ : AffineSubspace k P} (h₁₂ : s₁ ∥ s₂) (h₂₃ : s₂ ∥ s₃) :
    s₁ ∥ s₃ := by
  rcases h₁₂ with ⟨v₁₂, rfl⟩
  rcases h₂₃ with ⟨v₂₃, rfl⟩
  refine ⟨v₂₃ + v₁₂, ?_⟩
  rw [map_map, ← coe_trans_to_affineMap, ← constVAdd_add]

theorem Parallel.direction_eq {s₁ s₂ : AffineSubspace k P} (h : s₁ ∥ s₂) :
    s₁.direction = s₂.direction := by
  rcases h with ⟨v, rfl⟩
  simp

@[simp]
theorem parallel_bot_iff_eq_bot {s : AffineSubspace k P} : s ∥ ⊥ ↔ s = ⊥ := by
  refine ⟨fun h => ?_, fun h => h ▸ Parallel.refl _⟩
  rcases h with ⟨v, h⟩
  rwa [eq_comm, map_eq_bot_iff] at h

@[simp]
theorem bot_parallel_iff_eq_bot {s : AffineSubspace k P} : ⊥ ∥ s ↔ s = ⊥ := by
  rw [parallel_comm, parallel_bot_iff_eq_bot]

theorem parallel_iff_direction_eq_and_eq_bot_iff_eq_bot {s₁ s₂ : AffineSubspace k P} :
    s₁ ∥ s₂ ↔ s₁.direction = s₂.direction ∧ (s₁ = ⊥ ↔ s₂ = ⊥) := by
  refine ⟨fun h => ⟨h.direction_eq, ?_, ?_⟩, fun h => ?_⟩
  · rintro rfl
    exact bot_parallel_iff_eq_bot.1 h
  · rintro rfl
    exact parallel_bot_iff_eq_bot.1 h
  · rcases h with ⟨hd, hb⟩
    by_cases hs₁ : s₁ = ⊥
    · rw [hs₁, bot_parallel_iff_eq_bot]
      exact hb.1 hs₁
    · have hs₂ : s₂ ≠ ⊥ := hb.not.1 hs₁
      rcases (nonempty_iff_ne_bot s₁).2 hs₁ with ⟨p₁, hp₁⟩
      rcases (nonempty_iff_ne_bot s₂).2 hs₂ with ⟨p₂, hp₂⟩
      refine ⟨p₂ -ᵥ p₁, (eq_iff_direction_eq_of_mem hp₂ ?_).2 ?_⟩
      · rw [mem_map]
        refine ⟨p₁, hp₁, ?_⟩
        simp
      · simpa using hd.symm

theorem Parallel.vectorSpan_eq {s₁ s₂ : Set P} (h : affineSpan k s₁ ∥ affineSpan k s₂) :
    vectorSpan k s₁ = vectorSpan k s₂ := by
  simp_rw [← direction_affineSpan]
  exact h.direction_eq

theorem affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty {s₁ s₂ : Set P} :
    affineSpan k s₁ ∥ affineSpan k s₂ ↔ vectorSpan k s₁ = vectorSpan k s₂ ∧ (s₁ = ∅ ↔ s₂ = ∅) := by
  repeat rw [← direction_affineSpan, ← affineSpan_eq_bot k]
  exact parallel_iff_direction_eq_and_eq_bot_iff_eq_bot

theorem affineSpan_pair_parallel_iff_vectorSpan_eq {p₁ p₂ p₃ p₄ : P} :
    line[k, p₁, p₂] ∥ line[k, p₃, p₄] ↔
      vectorSpan k ({p₁, p₂} : Set P) = vectorSpan k ({p₃, p₄} : Set P) := by
  simp [affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty, ←
    not_nonempty_iff_eq_empty]

end AffineSubspace
