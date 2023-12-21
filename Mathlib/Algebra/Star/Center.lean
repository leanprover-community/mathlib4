/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.GroupTheory.Subsemigroup.Center
import Mathlib.GroupTheory.Subsemigroup.Centralizer
import Mathlib.Algebra.Star.Pointwise

/-! # `Set.center`, `Set.centralizer` and the `star` operation -/

variable {R : Type*} [Semigroup R] [StarSemigroup R] {a : R} {s : Set R}

theorem Set.star_mem_center (ha : a ∈ Set.center R) : star a ∈ Set.center R := by
  simpa only [star_mul, star_star] using fun g =>
    congr_arg star ((Set.mem_center_iff R).mp ha <| star g).symm

theorem Set.star_mem_centralizer' (h : ∀ a : R, a ∈ s → star a ∈ s) (ha : a ∈ Set.centralizer s) :
    star a ∈ Set.centralizer s := fun y hy => by simpa using congr_arg star (ha _ (h _ hy)).symm

open scoped Pointwise

theorem Set.star_mem_centralizer (ha : a ∈ Set.centralizer (s ∪ star s)) :
    star a ∈ Set.centralizer (s ∪ star s) :=
  Set.star_mem_centralizer'
    (fun _x hx => hx.elim (fun hx => Or.inr <| Set.star_mem_star.mpr hx) Or.inl) ha
