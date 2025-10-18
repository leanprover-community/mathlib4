/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Upper/lower bounds in ordered monoids and groups

In this file we prove a few facts like “`-s` is bounded above iff `s` is bounded below”
(`bddAbove_neg`).
-/

open Function Set
open scoped Pointwise

variable {ι G M : Type*}

section Mul
variable [Mul M] [Preorder M] [MulLeftMono M]
  [MulRightMono M] {f g : ι → M} {s t : Set M} {a b : M}

@[to_additive]
lemma mul_mem_upperBounds_mul (ha : a ∈ upperBounds s) (hb : b ∈ upperBounds t) :
    a * b ∈ upperBounds (s * t) := forall_mem_image2.2 fun _ hx _ hy => mul_le_mul' (ha hx) (hb hy)

@[to_additive]
lemma subset_upperBounds_mul (s t : Set M) : upperBounds s * upperBounds t ⊆ upperBounds (s * t) :=
  image2_subset_iff.2 fun _ hx _ hy => mul_mem_upperBounds_mul hx hy

@[to_additive]
lemma mul_mem_lowerBounds_mul (ha : a ∈ lowerBounds s) (hb : b ∈ lowerBounds t) :
    a * b ∈ lowerBounds (s * t) := mul_mem_upperBounds_mul (M := Mᵒᵈ) ha hb

@[to_additive]
lemma subset_lowerBounds_mul (s t : Set M) : lowerBounds s * lowerBounds t ⊆ lowerBounds (s * t) :=
  subset_upperBounds_mul (M := Mᵒᵈ) _ _

@[to_additive]
lemma BddAbove.mul (hs : BddAbove s) (ht : BddAbove t) : BddAbove (s * t) :=
  (Nonempty.mul hs ht).mono (subset_upperBounds_mul s t)

@[to_additive]
lemma BddBelow.mul (hs : BddBelow s) (ht : BddBelow t) : BddBelow (s * t) :=
  (Nonempty.mul hs ht).mono (subset_lowerBounds_mul s t)

@[to_additive] alias Set.BddAbove.mul := BddAbove.mul

@[to_additive]
lemma BddAbove.range_mul (hf : BddAbove (range f)) (hg : BddAbove (range g)) :
    BddAbove (range fun i ↦ f i * g i) :=
  .range_comp (f := fun i ↦ (f i, g i)) (bddAbove_range_prod.2 ⟨hf, hg⟩)
    (monotone_fst.mul' monotone_snd)

@[to_additive]
lemma BddBelow.range_mul (hf : BddBelow (range f)) (hg : BddBelow (range g)) :
    BddBelow (range fun i ↦ f i * g i) := BddAbove.range_mul (M := Mᵒᵈ) hf hg

end Mul

section InvNeg
variable [Group G] [Preorder G] [MulLeftMono G]
  [MulRightMono G] {s : Set G} {a : G}

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
