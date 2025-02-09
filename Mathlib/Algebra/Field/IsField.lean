/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Common

/-!
# `IsField` predicate

Predicate on a (semi)ring that it is a (semi)field, i.e. that the multiplication is
commutative, that it has more than one element and that all non-zero elements have a
multiplicative inverse. In contrast to `Field`, which contains the data of a function associating
to an element of the field its multiplicative inverse, this predicate only assumes the existence
and can therefore more easily be used to e.g. transfer along ring isomorphisms.
-/

universe u

section IsField

/-- A predicate to express that a (semi)ring is a (semi)field.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms.
Additionally, this is useful when trying to prove that
a particular ring structure extends to a (semi)field. -/
structure IsField (R : Type u) [Semiring R] : Prop where
  /-- For a semiring to be a field, it must have two distinct elements. -/
  exists_pair_ne : ∃ x y : R, x ≠ y
  /-- Fields are commutative. -/
  mul_comm : ∀ x y : R, x * y = y * x
  /-- Nonzero elements have multiplicative inverses. -/
  mul_inv_cancel : ∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1

/-- Transferring from `Semifield` to `IsField`. -/
theorem Semifield.toIsField (R : Type u) [Semifield R] : IsField R where
  __ := ‹Semifield R›
  mul_inv_cancel {a} ha := ⟨a⁻¹, mul_inv_cancel₀ ha⟩

/-- Transferring from `Field` to `IsField`. -/
theorem Field.toIsField (R : Type u) [Field R] : IsField R :=
  Semifield.toIsField _

@[simp]
theorem IsField.nontrivial {R : Type u} [Semiring R] (h : IsField R) : Nontrivial R :=
  ⟨h.exists_pair_ne⟩

@[simp]
theorem not_isField_of_subsingleton (R : Type u) [Semiring R] [Subsingleton R] : ¬IsField R :=
  fun h =>
  let ⟨_, _, h⟩ := h.exists_pair_ne
  h (Subsingleton.elim _ _)

open Classical in
/-- Transferring from `IsField` to `Semifield`. -/
noncomputable def IsField.toSemifield {R : Type u} [Semiring R] (h : IsField R) : Semifield R where
  __ := ‹Semiring R›
  __ := h
  inv a := if ha : a = 0 then 0 else Classical.choose (h.mul_inv_cancel ha)
  inv_zero := dif_pos rfl
  mul_inv_cancel a ha := by convert Classical.choose_spec (h.mul_inv_cancel ha); exact dif_neg ha
  nnqsmul := _
  nnqsmul_def _ _ := rfl

/-- Transferring from `IsField` to `Field`. -/
noncomputable def IsField.toField {R : Type u} [Ring R] (h : IsField R) : Field R where
  __ := (‹Ring R›:) -- this also works without the `( :)`, but it's slow
  __ := h.toSemifield
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `IsField` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
theorem uniq_inv_of_isField (R : Type u) [Ring R] (hf : IsField R) :
    ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1 := by
  intro x hx
  apply existsUnique_of_exists_of_unique
  · exact hf.mul_inv_cancel hx
  · intro y z hxy hxz
    calc
      y = y * (x * z) := by rw [hxz, mul_one]
      _ = x * y * z := by rw [← mul_assoc, hf.mul_comm y x]
      _ = z := by rw [hxy, one_mul]

end IsField
