/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual

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

@[to_additive]
lemma BddBelow.range_inv {α : Type*} {f : α → G} (hf : BddBelow (range f)) :
    BddAbove (range (fun x => (f x)⁻¹)) :=
  hf.range_comp (OrderIso.inv G).monotone

@[to_additive]
lemma BddAbove.range_inv {α : Type*} {f : α → G} (hf : BddAbove (range f)) :
    BddBelow (range (fun x => (f x)⁻¹)) :=
  BddBelow.range_inv (G := Gᵒᵈ) hf

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
  mul_mem_upperBounds_mul (M := Mᵒᵈ) ha hb

@[to_additive]
theorem subset_lowerBounds_mul (s t : Set M) :
    lowerBounds s * lowerBounds t ⊆ lowerBounds (s * t) :=
  subset_upperBounds_mul (M := Mᵒᵈ) _ _

@[to_additive]
theorem BddAbove.mul {s t : Set M} (hs : BddAbove s) (ht : BddAbove t) : BddAbove (s * t) :=
  (Nonempty.mul hs ht).mono (subset_upperBounds_mul s t)

@[to_additive]
theorem BddBelow.mul {s t : Set M} (hs : BddBelow s) (ht : BddBelow t) : BddBelow (s * t) :=
  (Nonempty.mul hs ht).mono (subset_lowerBounds_mul s t)

@[to_additive]
lemma BddAbove.range_mul {α : Type*} {f g : α → M} (hf : BddAbove (range f))
    (hg : BddAbove (range g)) : BddAbove (range (fun x => f x * g x)) :=
  BddAbove.range_comp (f := fun x => (⟨f x, g x⟩ : M × M))
    (bddAbove_range_prod.mpr ⟨hf, hg⟩) (Monotone.mul' monotone_fst monotone_snd)

@[to_additive]
lemma BddBelow.range_mul {α : Type*} {f g : α → M} (hf : BddBelow (range f))
    (hg : BddBelow (range g)) : BddBelow (range (fun x => f x * g x)) :=
  BddAbove.range_mul (M := Mᵒᵈ) hf hg

end mul_add

section ConditionallyCompleteLattice

section Right

variable {ι G : Type*} [Group G] [ConditionallyCompleteLattice G]
  [CovariantClass G G (Function.swap (· * ·)) (· ≤ ·)] [Nonempty ι] {f : ι → G}

@[to_additive]
theorem ciSup_mul (hf : BddAbove (range f)) (a : G) : (⨆ i, f i) * a = ⨆ i, f i * a :=
  (OrderIso.mulRight a).map_ciSup hf

@[to_additive]
theorem ciSup_div (hf : BddAbove (range f)) (a : G) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, ciSup_mul hf]

@[to_additive]
theorem ciInf_mul (hf : BddBelow (range f)) (a : G) : (⨅ i, f i) * a = ⨅ i, f i * a :=
  (OrderIso.mulRight a).map_ciInf hf

@[to_additive]
theorem ciInf_div (hf : BddBelow (range f)) (a : G) : (⨅ i, f i) / a = ⨅ i, f i / a := by
  simp only [div_eq_mul_inv, ciInf_mul hf]

end Right

section Left

variable {ι : Sort*} {G : Type*} [Group G] [ConditionallyCompleteLattice G]
  [CovariantClass G G (· * ·) (· ≤ ·)] [Nonempty ι] {f : ι → G}

@[to_additive]
theorem mul_ciSup (hf : BddAbove (range f)) (a : G) : (a * ⨆ i, f i) = ⨆ i, a * f i :=
  (OrderIso.mulLeft a).map_ciSup hf

@[to_additive]
theorem mul_ciInf (hf : BddBelow (range f)) (a : G) : (a * ⨅ i, f i) = ⨅ i, a * f i :=
  (OrderIso.mulLeft a).map_ciInf hf

end Left

end ConditionallyCompleteLattice
