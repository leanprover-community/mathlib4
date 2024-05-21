/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Pointwise
import Mathlib.Algebra.Group.Centralizer

/-! # `Set.center`, `Set.centralizer` and the `star` operation -/

variable {R : Type*} [Mul R] [StarMul R] {a : R} {s : Set R}

theorem Set.star_mem_center (ha : a ∈ Set.center R) : star a ∈ Set.center R where
  comm := by simpa only [star_mul, star_star] using fun g =>
    congr_arg star (((Set.mem_center_iff R).mp ha).comm <| star g).symm
  left_assoc b c := calc
    star a * (b * c) = star a * (star (star b) * star (star c)) := by rw [star_star, star_star]
    _ = star a * star (star c * star b) := by rw [star_mul]
    _ = star ((star c * star b) * a) := by rw [← star_mul]
    _ = star (star c * (star b * a)) := by rw [ha.right_assoc]
    _ = star (star b * a) * c := by rw [star_mul, star_star]
    _ = (star a * b) * c := by rw [star_mul, star_star]
  mid_assoc b c := calc
    b * star a * c = star (star c * star (b * star a)) := by rw [← star_mul, star_star]
    _ = star (star c * (a * star b)) := by rw [star_mul b, star_star]
    _ = star ((star c * a) * star b) := by rw [ha.mid_assoc]
    _ = b * (star a * c) := by rw [star_mul, star_star, star_mul (star c), star_star]
  right_assoc b c := calc
    b * c * star a = star (a * star (b * c)) := by rw [star_mul, star_star]
    _ = star (a * (star c * star b)) := by rw [star_mul b]
    _ = star ((a * star c) * star b) := by rw [ha.left_assoc]
    _ = b * star (a * star c) := by rw [star_mul, star_star]
    _ = b * (c * star a) := by rw [star_mul, star_star]

theorem Set.star_mem_centralizer' (h : ∀ a : R, a ∈ s → star a ∈ s) (ha : a ∈ Set.centralizer s) :
    star a ∈ Set.centralizer s := fun y hy => by simpa using congr_arg star (ha _ (h _ hy)).symm

open scoped Pointwise

theorem Set.star_mem_centralizer (ha : a ∈ Set.centralizer (s ∪ star s)) :
    star a ∈ Set.centralizer (s ∪ star s) :=
  Set.star_mem_centralizer'
    (fun _x hx => hx.elim (fun hx => Or.inr <| Set.star_mem_star.mpr hx) Or.inl) ha
