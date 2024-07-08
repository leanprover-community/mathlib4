/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Order.Atoms
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Ring.Subring.Basic

/-! # Simple rings

A ring `R` is **simple** if it has only two two-sided ideals, namely `0` and `⟨1⟩`.

## Main results

- `IsSimpleRing.nontrivial`: simple rings are non-trivial.
- `IsSimpleRing.of_divisionRing`: division rings are simple.
- `IsSimpleRing.center_isField`: the center of a simple ring is a field.

-/

variable (R : Type*) [NonUnitalNonAssocRing R]

/--
A ring `R` is **simple** if it has only two two-sided ideals, namely `0` and `⟨1⟩`.
-/
class IsSimpleRing : Prop where
  simple : IsSimpleOrder (TwoSidedIdeal R)

namespace IsSimpleRing

variable {R}

instance nontrivial [simple : IsSimpleRing R] : Nontrivial R := by
  refine subsingleton_or_nontrivial R |>.resolve_left fun r ↦ ?_
  obtain ⟨x, y, hxy⟩ := simple.1.1
  exact hxy $ SetLike.ext fun a ↦ (show a = 0 from Subsingleton.elim _ _) ▸ by
    simp [TwoSidedIdeal.zero_mem]

lemma twoSidedIdeal_elim [simple : IsSimpleRing R] (I : TwoSidedIdeal R) : I = ⊥ ∨ I = ⊤ :=
    simple.1.2 I

lemma one_mem_of_ne_bot {A : Type*} [NonAssocRing A] [IsSimpleRing A] (I : TwoSidedIdeal A)
    (hI : I ≠ ⊥) : (1 : A) ∈ I :=
  (twoSidedIdeal_elim I).resolve_left hI ▸ ⟨⟩

lemma one_mem_of_ne_zero_mem {A : Type*} [NonAssocRing A] [IsSimpleRing A] (I : TwoSidedIdeal A)
    {x : A} (hx : x ≠ 0) (hxI : x ∈ I) : (1 : A) ∈ I :=
  one_mem_of_ne_bot I (by rintro rfl; exact hx hxI)

instance of_divisionRing (A : Type*) [DivisionRing A] : IsSimpleRing A where
  simple :=
  { exists_pair_ne := ⟨⊥, ⊤, bot_ne_top⟩
    eq_bot_or_eq_top := fun I ↦ (eq_or_ne I ⊥).elim .inl fun H ↦ .inr $ by
      suffices mem : 1 ∈ I from eq_top_iff.2 $ fun x _ ↦ mul_one x ▸ I.mul_mem_left x _ mem
      rw [← bot_lt_iff_ne_bot, TwoSidedIdeal.lt_iff, Set.ssubset_def,
        Set.not_subset_iff_exists_mem_not_mem] at H
      obtain ⟨-, x, hx1, (hx2 : x ≠ 0)⟩ := H
      simpa [inv_mul_cancel hx2] using I.mul_mem_left x⁻¹ _ hx1 }

open TwoSidedIdeal in
lemma center_isField (A : Type*) [Ring A] [IsSimpleRing A] : IsField (Subring.center A) where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    ext
    simp only [Subring.mem_center_iff] at hx hy
    exact hx y |>.symm
  mul_inv_cancel := by
    rintro ⟨x, hx1⟩ hx2
    rw [Subring.mem_center_iff] at hx1
    replace hx2 : x ≠ 0 := by contrapose! hx2; aesop
    let I := TwoSidedIdeal.mk' (Set.range (x * ·)) ⟨0, by simp⟩
      (by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, mul_add _ _ _⟩)
      (by rintro _ ⟨x, rfl⟩; exact ⟨-x, by simp⟩)
      (by rintro a _ ⟨c, rfl⟩; exact ⟨a * c, by dsimp; rw [← mul_assoc, ← hx1, mul_assoc]⟩)
      (by rintro _ b ⟨a, rfl⟩; exact ⟨a * b, by dsimp; rw [← mul_assoc, ← hx1, mul_assoc]⟩)
    have mem : 1 ∈ I := one_mem_of_ne_zero_mem I hx2 (by simpa [I, mem_mk'] using ⟨1, by simp⟩)
    simp only [TwoSidedIdeal.mem_mk', Set.mem_range, I] at mem
    obtain ⟨y, hy⟩ := mem
    refine ⟨⟨y, Subring.mem_center_iff.2 fun a ↦ ?_⟩, by ext; exact hy⟩
    calc a * y
      _ = (x * y) * a * y := by rw [hy, one_mul]
      _ = (y * x) * a * y := by rw [hx1]
      _ = y * (x * a) * y := by rw [mul_assoc y x a]
      _ = y * (a * x) * y := by rw [hx1]
      _ = y * ((a * x) * y) := by rw [mul_assoc]
      _ = y * (a * (x * y)) := by rw [mul_assoc a x y]
      _ = y * a := by rw [hy, mul_one]

lemma iff_isField_of_commutative (A : Type*) [CommRing A]  :
    IsField A ↔ IsSimpleRing A :=
  ⟨fun h ↦ letI := IsField.toField h; inferInstance, fun _ ↦ by
    have h := center_isField A
    refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha ↦ ?_⟩
    obtain ⟨⟨b, _⟩, hb⟩ := h.mul_inv_cancel
      (a := ⟨a, Subring.mem_center_iff.2 fun b ↦ mul_comm _ _⟩)
      (by contrapose! ha; simpa [Subtype.ext_iff] using ha)
    exact ⟨b, Subtype.ext_iff |>.1 hb⟩⟩

end IsSimpleRing
