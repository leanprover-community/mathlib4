/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Algebra.Order.Monoid.OrderDual
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.ConditionallyCompleteLattice.Basic

#align_import algebra.bounds from "leanprover-community/mathlib"@"dd71334db81d0bd444af1ee339a29298bef40734"

/-!
# Upper/lower bounds in ordered monoids and groups

In this file we prove a few facts like “`-s` is bounded above iff `s` is bounded below”
(`bddAbove_neg`).
-/


open Function Set

open Pointwise

section InvNeg

variable {G : Type*} [Group G] [Preorder G] [CovariantClass G G (· * ·) (· ≤ ·)]
  [CovariantClass G G (swap (· * ·)) (· ≤ ·)] {s : Set G} {a : G}

@[to_additive (attr := simp)]
theorem bddAbove_inv : BddAbove s⁻¹ ↔ BddBelow s :=
  (OrderIso.inv G).bddAbove_preimage

@[to_additive (attr := simp)]
theorem bddBelow_inv : BddBelow s⁻¹ ↔ BddAbove s :=
  (OrderIso.inv G).bddBelow_preimage

@[to_additive]
theorem BddAbove.inv (h : BddAbove s) : BddBelow s⁻¹ :=
  bddBelow_inv.2 h

@[to_additive]
theorem BddBelow.inv (h : BddBelow s) : BddAbove s⁻¹ :=
  bddAbove_inv.2 h

@[to_additive (attr := simp)]
theorem isLUB_inv : IsLUB s⁻¹ a ↔ IsGLB s a⁻¹ :=
  (OrderIso.inv G).isLUB_preimage

@[to_additive]
theorem isLUB_inv' : IsLUB s⁻¹ a⁻¹ ↔ IsGLB s a :=
  (OrderIso.inv G).isLUB_preimage'

@[to_additive]
theorem IsGLB.inv (h : IsGLB s a) : IsLUB s⁻¹ a⁻¹ :=
  isLUB_inv'.2 h

@[to_additive (attr := simp)]
theorem isGLB_inv : IsGLB s⁻¹ a ↔ IsLUB s a⁻¹ :=
  (OrderIso.inv G).isGLB_preimage

@[to_additive]
theorem isGLB_inv' : IsGLB s⁻¹ a⁻¹ ↔ IsLUB s a :=
  (OrderIso.inv G).isGLB_preimage'

@[to_additive]
theorem IsLUB.inv (h : IsLUB s a) : IsGLB s⁻¹ a⁻¹ :=
  isGLB_inv'.2 h

end InvNeg

section mul_add

variable {M : Type*} [Mul M] [Preorder M] [CovariantClass M M (· * ·) (· ≤ ·)]
  [CovariantClass M M (swap (· * ·)) (· ≤ ·)]

@[to_additive]
theorem mul_mem_upperBounds_mul {s t : Set M} {a b : M} (ha : a ∈ upperBounds s)
    (hb : b ∈ upperBounds t) : a * b ∈ upperBounds (s * t) :=
  forall_image2_iff.2 fun _ hx _ hy => mul_le_mul' (ha hx) (hb hy)

@[to_additive]
theorem subset_upperBounds_mul (s t : Set M) :
    upperBounds s * upperBounds t ⊆ upperBounds (s * t) :=
  image2_subset_iff.2 fun _ hx _ hy => mul_mem_upperBounds_mul hx hy

@[to_additive]
theorem mul_mem_lowerBounds_mul {s t : Set M} {a b : M} (ha : a ∈ lowerBounds s)
    (hb : b ∈ lowerBounds t) : a * b ∈ lowerBounds (s * t) :=
  @mul_mem_upperBounds_mul Mᵒᵈ _ _ _ _ _ _ _ _ ha hb

@[to_additive]
theorem subset_lowerBounds_mul (s t : Set M) :
    lowerBounds s * lowerBounds t ⊆ lowerBounds (s * t) :=
  @subset_upperBounds_mul Mᵒᵈ _ _ _ _ _ _

@[to_additive]
theorem BddAbove.mul {s t : Set M} (hs : BddAbove s) (ht : BddAbove t) : BddAbove (s * t) :=
  (Nonempty.mul hs ht).mono (subset_upperBounds_mul s t)

@[to_additive]
theorem BddBelow.mul {s t : Set M} (hs : BddBelow s) (ht : BddBelow t) : BddBelow (s * t) :=
  (Nonempty.mul hs ht).mono (subset_lowerBounds_mul s t)

end mul_add

section ConditionallyCompleteLattice

section Right

variable {ι G : Type*} [Group G] [ConditionallyCompleteLattice G]
  [CovariantClass G G (Function.swap (· * ·)) (· ≤ ·)] [Nonempty ι] {f : ι → G}

@[to_additive]
theorem ciSup_mul (hf : BddAbove (Set.range f)) (a : G) : (⨆ i, f i) * a = ⨆ i, f i * a :=
  (OrderIso.mulRight a).map_ciSup hf

@[to_additive]
theorem ciSup_div (hf : BddAbove (Set.range f)) (a : G) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, ciSup_mul hf]

@[to_additive]
theorem ciInf_mul (hf : BddBelow (Set.range f)) (a : G) : (⨅ i, f i) * a = ⨅ i, f i * a :=
  (OrderIso.mulRight a).map_ciInf hf

@[to_additive]
theorem ciInf_div (hf : BddBelow (Set.range f)) (a : G) : (⨅ i, f i) / a = ⨅ i, f i / a := by
  simp only [div_eq_mul_inv, ciInf_mul hf]

end Right

section Left

variable {ι G : Type*} [Group G] [ConditionallyCompleteLattice G]
  [CovariantClass G G (· * ·) (· ≤ ·)] [Nonempty ι] {f : ι → G}

@[to_additive]
theorem mul_ciSup (hf : BddAbove (Set.range f)) (a : G) : (a * ⨆ i, f i) = ⨆ i, a * f i :=
  (OrderIso.mulLeft a).map_ciSup hf

@[to_additive]
theorem mul_ciInf (hf : BddBelow (Set.range f)) (a : G) : (a * ⨅ i, f i) = ⨅ i, a * f i :=
  (OrderIso.mulLeft a).map_ciInf hf

end Left

end ConditionallyCompleteLattice
