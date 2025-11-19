/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Sums and products from lists

This file provides basic definitions for `List.prod`, `List.sum`,
which calculate the product and sum of elements of a list
and `List.alternatingProd`, `List.alternatingSum`, their alternating counterparts.
-/

@[expose] public section

variable {ι M N : Type*}

namespace List
section Defs

set_option linter.existingAttributeWarning false in
attribute [to_additive existing] prod prod_nil prod_cons prod_one_cons prod_append prod_concat
  prod_flatten prod_eq_foldl

/-- The alternating sum of a list. -/
def alternatingSum {G : Type*} [Zero G] [Add G] [Neg G] : List G → G
  | [] => 0
  | g :: [] => g
  | g :: h :: t => g + -h + alternatingSum t

/-- The alternating product of a list. -/
@[to_additive existing]
def alternatingProd {G : Type*} [One G] [Mul G] [Inv G] : List G → G
  | [] => 1
  | g :: [] => g
  | g :: h :: t => g * h⁻¹ * alternatingProd t

end Defs

section Mul

variable [Mul M] [One M] {a : M} {l : List M}

@[to_additive]
lemma prod_induction
    (p : M → Prop) (hom : ∀ a b, p a → p b → p (a * b)) (unit : p 1) (base : ∀ x ∈ l, p x) :
    p l.prod := by
  induction l with
  | nil => simpa
  | cons a l ih =>
    rw [List.prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at base
    exact hom _ _ (base.1) (ih base.2)

end Mul

section MulOneClass

variable [MulOneClass M] {l : List M} {a : M}

@[to_additive]
theorem prod_map_one {l : List ι} :
    (l.map fun _ => (1 : M)).prod = 1 := by
  induction l with simp [*]

@[to_additive]
lemma prod_induction_nonempty
    (p : M → Prop) (hom : ∀ a b, p a → p b → p (a * b)) (hl : l ≠ []) (base : ∀ x ∈ l, p x) :
    p l.prod := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    by_cases hl_empty : l = []
    · simp [*]
    rw [List.prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at base
    exact hom _ _ (base.1) (ih hl_empty base.2)

end MulOneClass

section Monoid

variable [Monoid M] [Monoid N]

@[to_additive (attr := simp)]
theorem prod_replicate (n : ℕ) (a : M) : (replicate n a).prod = a ^ n := by
  induction n with
  | zero => rw [pow_zero, replicate_zero, prod_nil]
  | succ n ih => rw [replicate_succ, prod_cons, ih, pow_succ']

@[to_additive sum_eq_card_nsmul]
theorem prod_eq_pow_card (l : List M) (m : M) (h : ∀ x ∈ l, x = m) : l.prod = m ^ l.length := by
  rw [← prod_replicate, ← List.eq_replicate_iff.mpr ⟨rfl, h⟩]

@[to_additive]
theorem prod_hom_rel (l : List ι) {r : M → N → Prop} {f : ι → M} {g : ι → N} (h₁ : r 1 1)
    (h₂ : ∀ ⦃i a b⦄, r a b → r (f i * a) (g i * b)) : r (l.map f).prod (l.map g).prod :=
  List.recOn l h₁ fun a l hl => by simp only [map_cons, prod_cons, h₂ hl]

end Monoid

end List
