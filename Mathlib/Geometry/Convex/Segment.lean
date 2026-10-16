/-
Copyright (c) 2026 Olivia Röhrig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig
-/

module

public import Mathlib.Data.Set.Insert
public import Mathlib.Geometry.Convex.ConvexSpace.Prod

/-!
# Segments in convex spaces

In an R-convex space, we define the following objects:
* `Icc R x y`: Closed segment joining `x` and `y`.
* `Ioo R x y`: Open segment joining `x` and `y`.
* `Ico R x y`: Right-open segment joining `x` and `y`.
-/

namespace Convexity

open Convexity Function

@[expose] public section Semiring

variable (R) {X} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X] {s : Set X}
  {x y z : X}

/-- Segments in a convex space. Denoted as `Icc R x y` within the `Convex` namespace. -/
def Icc (x y : X) : Set X :=
  { z : X | ∃ (a b : R) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
    convexCombPair a b ha hb hab x y = z }

/-- Open segments in a convex space. Denoted as `Ioo R x y` within the `Convex` namespace.
Note that `Ioo R x x = {x}` instead of being `∅` when the base semiring has some element between
`0` and `1`. -/
def Ioo (x y : X) : Set X :=
  { z : X | ∃ (a b : R) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1),
    convexCombPair a b ha.le hb.le hab x y = z }

/-- Left-open segments in a convex space. Denoted as `Ico R x y` within the `Convex` namespace.
Note that `Ico R x x = {x}` instead of being `∅` . -/
def Ico (x y : X) : Set X :=
  { z : X | ∃ (a b : R) (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1),
    convexCombPair a b ha.le hb hab x y = z }

/- [x,y] = [y,x] -/
theorem Icc_symm (x y : X) : Icc R x y = Icc R y x := by
  ext z
  constructor
  all_goals
  · rintro ⟨m, n, hm , hn , hmn , hz⟩
    rw [convexCombPair_symm] at hz
    exact ⟨n, m, hn, hm, add_comm m n ▸ hmn, hz⟩

/- (x,y) = (y,x) -/
theorem Ioo_symm (x y : X) : Ioo R x y = Ioo R y x := by
  ext z
  constructor
  all_goals (intro h; rcases h with ⟨m, n, hm , hn , hmn , hz⟩; use n, m, hn, hm)
  all_goals (rw [convexCombPair_symm] at hz; rw [add_comm] at hmn; use hmn)

theorem Ioo_subset_Ico (x y : X) : Ioo R x y ⊆ Ico R x y :=
  fun _ ⟨a, b, ha, hb, hab, hz⟩ ↦ ⟨a, b, ha, hb.le, hab, hz⟩

theorem Ico_subset_Icc (x y : X) : Ico R x y ⊆ Icc R x y :=
  fun _ ⟨a, b, ha, hb, hab, hz⟩ ↦ ⟨a, b, ha.le, hb, hab, hz⟩

theorem Ioo_subset_Icc (x y : X) : Ioo R x y ⊆ Icc R x y :=
  le_trans (Ioo_subset_Ico R x y) (Ico_subset_Icc R x y)

section

variable {R}

theorem convexCombPair_mem_Icc {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    convexCombPair a b ha hb hab x y ∈ Icc R x y :=
  ⟨a, b, ha, hb, hab, rfl⟩

theorem convexCombPair_mem_Ioo {a b : R} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    convexCombPair a b ha.le hb.le hab x y ∈ Ioo R x y := by
  use a, b, ha, hb, hab

theorem convexCombPair_mem_Ico {a b : R} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    convexCombPair a b ha.le hb hab x y ∈ Ico R x y := by
  use a, b, ha, hb, hab

theorem forall_mem_Icc_iff (p : X → Prop) : (∀ z ∈ Icc R x y, p z) ↔
    ∀ {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
    p (convexCombPair a b ha hb hab x y) := by
  grind [Icc]

theorem forall_mem_Ioo_iff (p : X → Prop) : (∀ z ∈ Ioo R x y, p z) ↔
    ∀ {a b : R} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1),
    p (convexCombPair a b ha.le hb.le hab x y) := by
  grind [Ioo]

theorem forall_mem_Ico_iff (p : X → Prop) : (∀ z ∈ Ico R x y, p z) ↔
    ∀ {a b : R} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1),
    p (convexCombPair a b ha.le hb hab x y) := by
  grind [Ico]

theorem Icc_subset_iff : Icc R x y ⊆ s ↔ ∀ {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
    convexCombPair a b ha hb hab x y ∈ s :=
  forall_mem_Icc_iff ..

theorem Ioo_subset_iff :
    Ioo R x y ⊆ s ↔ ∀ {a b : R} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1),
    convexCombPair a b ha.le hb.le hab x y ∈ s :=
  forall_mem_Ioo_iff ..

theorem Ico_subset_iff :
    Ico R x y ⊆ s ↔ ∀ {a b : R} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1),
    convexCombPair a b ha.le hb hab x y ∈ s :=
  forall_mem_Ico_iff ..

end

@[simp]
theorem left_mem_Icc (x y : X) : x ∈ Icc R x y :=
  ⟨1, 0, zero_le_one, le_refl 0, add_zero 1, by rw [convexCombPair_one]⟩

@[simp]
theorem right_mem_Icc (x y : X) : y ∈ Icc R x y :=
  Icc_symm R y x ▸ left_mem_Icc R y x

@[simp]
theorem left_mem_Ico (x y : X) : x ∈ Ico R x y :=
  ⟨1, 0, zero_lt_one, le_refl 0, add_zero 1, convexCombPair_one⟩

@[simp]
theorem Icc_same (x : X) : Icc R x x = {x} :=
  Set.ext <| fun z ↦ ⟨by simp +contextual [Icc], by simp +contextual⟩

@[simp]
theorem Ioo_same_subset_singleton (x : X) : Ioo R x x ⊆ {x} :=
  fun _ ⟨_, _, _, _, _, h⟩ => h ▸ convexCombPair_same ..

@[simp]
theorem Ico_same (x : X) : Ico R x x = {x} := by
  apply Set.Subset.antisymm
  · rw [← Icc_same R x]; exact Ico_subset_Icc R x x
  · simp [left_mem_Ico]

@[simp]
theorem Ioo_insert_left (x y : X) : insert x (Ioo R x y) = Ico R x y := by
  simp only [subset_antisymm_iff, Set.insert_subset_iff, left_mem_Ico, Ioo_subset_Ico, and_self,
    true_and]
  rintro z ⟨a, b, ha, hb', hab, rfl⟩
  by_cases hb : 0 < b
  · exact Set.mem_insert_of_mem x (convexCombPair_mem_Ioo ha hb hab)
  · rw [← eq_of_le_of_not_lt hb' hb] at hab
    simp [← eq_of_le_of_not_lt hb' hb, add_zero a ▸ hab]

@[simp]
theorem Ioo_insert_right (x y : X) : insert y (Ioo R x y) = Ico R y x := by
  rw [Ioo_symm, Iio_insert_left]

@[simp]
theorem Ico_insert (x y : X) : insert y (Ico R x y) = Icc R x y := by
  simp only [subset_antisymm_iff, Set.insert_subset_iff, right_mem_Icc, Ico_subset_Icc, true_and]
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  refine ha.eq_or_lt.imp ?_ (fun hal ↦ convexCombPair_mem_Ico hal hb hab)
  rintro rfl
  simp [zero_add b ▸ hab]

namespace IsAffineMap

variable {R} {Y} [ConvexSpace R Y] {f : X → Y}

@[simp]
theorem image_Icc (hf : IsAffineMap R f) (a b : X) :
    f '' Icc R a b = Icc R (f a) (f b) :=
  Set.ext fun _ ↦ by simp [Icc, IsAffineMap.map_convexCombPair hf]

theorem mem_Icc_image (hf : IsAffineMap R f) {a b c : X}
    (h : c ∈ Icc R a b) : f c ∈ Icc R (f a) (f b) := by
  rw [← image_Icc hf, Set.mem_image]
  exact ⟨c, ⟨h, rfl⟩⟩

@[simp]
theorem image_Ioo (hf : IsAffineMap R f) (a b : X) :
    f '' Ioo R a b = Ioo R (f a) (f b) :=
  Set.ext fun _ ↦ by simp [Ioo, IsAffineMap.map_convexCombPair hf]

theorem mem_Ioo_image (hf : IsAffineMap R f) {a b c : X}
    (h : c ∈ Ioo R a b) : f c ∈ Ioo R (f a) (f b) := by
  rw [← image_Ioo hf, Set.mem_image]
  exact ⟨c, ⟨h, rfl⟩⟩

@[simp]
theorem image_Ico (hf : IsAffineMap R f) (a b : X) : f '' Ico R a b = Ico R (f a) (f b) :=
  Set.ext fun _ ↦ by simp [Ico, IsAffineMap.map_convexCombPair hf]

theorem mem_Ico_image (hf : IsAffineMap R f) {a b c : X} (h : c ∈ Ico R a b) :
    f c ∈ Ico R (f a) (f b) := by
  rw [← image_Ico hf, Set.mem_image]
  exact ⟨c, ⟨h, rfl⟩⟩

end IsAffineMap

namespace Prod

variable {Y} [ConvexSpace R Y]

theorem Icc_subset (x y : X × Y) : Icc R x y ⊆ Icc R x.1 y.1 ×ˢ Icc R x.2 y.2 := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  simp [convexCombPair_mem_Icc]

theorem Ioo_subset (x y : X × Y) : Ioo R x y ⊆ Ioo R x.1 y.1 ×ˢ Ioo R x.2 y.2 := by
  rintro z ⟨a, b, ha, hb, hab, hz⟩
  exact ⟨⟨a, b, ha, hb, hab, by subst hz; simp⟩, a, b, ha, hb, hab, by subst hz; simp⟩

theorem Ico_subset (x y : X × Y) : Ico R x y ⊆ Ico R x.1 y.1 ×ˢ Ico R x.2 y.2 := by
  rintro z ⟨a, b, ha, hb, hab, hz⟩
  exact ⟨⟨a, b, ha, hb, hab, by subst hz; simp⟩, a, b, ha, hb, hab, by subst hz; simp⟩

theorem image_mk_Icc_left (x₁ x₂ : X) (y : Y) :
    (fun x ↦ (x, y)) '' Icc R x₁ x₂ = Icc R (x₁, y) (x₂, y) :=
  (IsAffineMap.prodMk IsAffineMap.id (IsAffineMap.const y)).image_Icc ..

theorem image_mk_Icc_right (x : X) (y₁ y₂ : Y) :
    (fun y ↦ (x, y)) '' Icc R y₁ y₂ = Icc R (x, y₁) (x, y₂) :=
  (IsAffineMap.prodMk (IsAffineMap.const x) IsAffineMap.id).image_Icc ..

theorem image_mk_Ioo_left (x₁ x₂ : X) (y : Y) :
    (fun x ↦ (x, y)) '' Ioo R x₁ x₂ = Ioo R (x₁, y) (x₂, y) :=
  (IsAffineMap.prodMk IsAffineMap.id (IsAffineMap.const y)).image_Ioo ..

theorem image_mk_Ioo_right (x : X) (y₁ y₂ : Y) :
    (fun y ↦ (x, y)) '' Ioo R y₁ y₂ = Ioo R (x, y₁) (x, y₂) :=
  (IsAffineMap.prodMk (IsAffineMap.const x) IsAffineMap.id).image_Ioo ..

theorem image_mk_Ico_left (x₁ x₂ : X) (y : Y) :
    (fun x ↦ (x, y)) '' Ico R x₁ x₂ = Ico R (x₁, y) (x₂, y) :=
  (IsAffineMap.prodMk IsAffineMap.id (IsAffineMap.const y)).image_Ico ..

theorem image_mk_Ico_right (x : X) (y₁ y₂ : Y) :
    (fun y ↦ (x, y)) '' Ico R y₁ y₂ = Ico R (x, y₁) (x, y₂) :=
  (IsAffineMap.prodMk (IsAffineMap.const x) IsAffineMap.id).image_Ico ..

end Prod

end Semiring

section DenselyOrdered

variable (R) {X} [Ring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]
  [DenselyOrdered R]

@[simp]
theorem Ioo_same (x : X) : Ioo R x x = {x} := by
  ext
    refine ⟨by simp +contextual [Ioo], ?_⟩
    obtain ⟨a, ha₀, ha₁⟩ := exists_between (α := R) zero_lt_one
    refine fun h ↦ ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel .., ?_⟩
    rw [convexCombPair_same, Set.mem_singleton_iff.mp h]

end DenselyOrdered

end Convexity
