/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pointwise
public import Mathlib.Algebra.Group.Center

/-! # `Set.center`, `Set.centralizer` and the `star` operation -/

public section

variable {R : Type*} [Mul R] [StarMul R] {a : R} {s : Set R}

theorem Set.star_mem_center (ha : a ∈ Set.center R) : star a ∈ Set.center R where
  comm := by simpa only [star_mul, star_star] using fun g =>
    congr_arg star ((mem_center_iff.1 ha).comm <| star g).symm
  left_assoc b c := by
    rw [← star_star b, ← star_star c, ← star_mul, ← star_mul, ha.right_assoc, star_mul,
      star_mul, star_star, star_star]
  right_assoc b c := by
    rw [← star_star b, ← star_star c, ← star_mul, ← star_mul, ha.left_assoc, star_mul,
      star_mul, star_star, star_star]

theorem Set.star_centralizer : star s.centralizer = (star s).centralizer := by
  simp_rw [centralizer, ← commute_iff_eq]
  conv_lhs => simp [← star_preimage, ← commute_star_comm]
  conv_rhs => simp [← image_star]

theorem Set.union_star_self_comm (hcomm : ∀ x ∈ s, ∀ y ∈ s, y * x = x * y)
    (hcomm_star : ∀ x ∈ s, ∀ y ∈ s, y * star x = star x * y) :
    ∀ x ∈ s ∪ star s, ∀ y ∈ s ∪ star s, y * x = x * y := by
  change s ∪ star s ⊆ (s ∪ star s).centralizer
  simpa [centralizer_union, ← star_centralizer, star_subset]
    using ⟨⟨hcomm, hcomm_star⟩, ⟨hcomm_star, hcomm⟩⟩

theorem Set.star_mem_centralizer' (h : ∀ a : R, a ∈ s → star a ∈ s) (ha : a ∈ Set.centralizer s) :
    star a ∈ Set.centralizer s := fun y hy => by simpa using congr_arg star (ha _ (h _ hy)).symm

open scoped Pointwise

theorem Set.star_mem_centralizer (ha : a ∈ Set.centralizer (s ∪ star s)) :
    star a ∈ Set.centralizer (s ∪ star s) :=
  star_mem_centralizer' (fun _x hx => hx.elim (Or.inr <| Set.star_mem_star.mpr ·) Or.inl) ha
