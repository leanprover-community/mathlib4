/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Pointwise
import Mathlib.Algebra.Group.Center

/-! # `Set.center`, `Set.centralizer` and the `star` operation -/

variable {R : Type*} [Mul R] [StarMul R] {a : R} {s : Set R}

theorem Set.star_mem_center (ha : a ∈ Set.center R) : star a ∈ Set.center R where
  comm := by simpa only [star_mul, star_star] using fun g =>
    congr_arg star ((mem_center_iff.1 ha).comm <| star g).symm
  left_assoc b c := calc
    star a * (b * c) = star a * (star (star b) * star (star c)) := by rw [star_star, star_star]
    _ = star a * star (star c * star b) := by rw [star_mul]
    _ = star ((star c * star b) * a) := by rw [← star_mul]
    _ = star (star c * (star b * a)) := by rw [ha.right_assoc]
    _ = star (star b * a) * c := by rw [star_mul, star_star]
    _ = (star a * b) * c := by rw [star_mul, star_star]
  right_assoc b c := calc
    b * c * star a = star (a * star (b * c)) := by rw [star_mul, star_star]
    _ = star (a * (star c * star b)) := by rw [star_mul b]
    _ = star ((a * star c) * star b) := by rw [ha.left_assoc]
    _ = b * star (a * star c) := by rw [star_mul, star_star]
    _ = b * (c * star a) := by rw [star_mul, star_star]

theorem Set.star_centralizer : star s.centralizer = (star s).centralizer := by
  simp_rw [centralizer, ← commute_iff_eq]
  conv_lhs => simp only [← star_preimage, preimage_setOf_eq, ← commute_star_comm]
  conv_rhs => simp only [← image_star, forall_mem_image]

theorem Set.union_star_self_comm (hcomm : ∀ x ∈ s, ∀ y ∈ s, y * x = x * y)
    (hcomm_star : ∀ x ∈ s, ∀ y ∈ s, y * star x = star x * y) :
    ∀ x ∈ s ∪ star s, ∀ y ∈ s ∪ star s, y * x = x * y := by
  change s ∪ star s ⊆ (s ∪ star s).centralizer
  simp_rw [centralizer_union, ← star_centralizer, union_subset_iff, subset_inter_iff,
    star_subset_star, star_subset]
  exact ⟨⟨hcomm, hcomm_star⟩, ⟨hcomm_star, hcomm⟩⟩

theorem Set.star_mem_centralizer' (h : ∀ a : R, a ∈ s → star a ∈ s) (ha : a ∈ Set.centralizer s) :
    star a ∈ Set.centralizer s := fun y hy => by simpa using congr_arg star (ha _ (h _ hy)).symm

open scoped Pointwise

theorem Set.star_mem_centralizer (ha : a ∈ Set.centralizer (s ∪ star s)) :
    star a ∈ Set.centralizer (s ∪ star s) :=
  Set.star_mem_centralizer'
    (fun _x hx => hx.elim (fun hx => Or.inr <| Set.star_mem_star.mpr hx) Or.inl) ha
