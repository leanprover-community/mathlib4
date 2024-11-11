/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.SimpleRing.Defs
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.Ring.Subring.Basic

/-! # Basic Properties of Simple rings

A ring `R` is **simple** if it has only two two-sided ideals, namely `⊥` and `⊤`.

## Main results

- `IsSimpleRing.nontrivial`: simple rings are non-trivial.
- `DivisionRing.IsSimpleRing`: division rings are simple.
- `IsSimpleRing.center_isField`: the center of a simple ring is a field.
- `IsSimpleRing.injective_ringHom`: every ring homomorphism from a simple ring to a nontrivial ring
  is injective.
- `IsSimpleRing.iff_injective_ringHom`: a ring is simple iff every ring homomorphism to a nontrivial
  ring is injective.

-/

variable (R : Type*) [NonUnitalNonAssocRing R]

namespace IsSimpleRing

variable {R}

instance [IsSimpleRing R] : IsSimpleOrder (TwoSidedIdeal R) := IsSimpleRing.simple

instance [simple : IsSimpleRing R] : Nontrivial R := by
  obtain ⟨x, hx⟩ := SetLike.exists_of_lt (bot_lt_top : (⊥ : TwoSidedIdeal R) < ⊤)
  have h (hx : x = 0) : False := by simp_all [TwoSidedIdeal.zero_mem]
  use x, 0, h

lemma one_mem_of_ne_bot {A : Type*} [NonAssocRing A] [IsSimpleRing A] (I : TwoSidedIdeal A)
    (hI : I ≠ ⊥) : (1 : A) ∈ I :=
  (eq_bot_or_eq_top I).resolve_left hI ▸ ⟨⟩

lemma one_mem_of_ne_zero_mem {A : Type*} [NonAssocRing A] [IsSimpleRing A] (I : TwoSidedIdeal A)
    {x : A} (hx : x ≠ 0) (hxI : x ∈ I) : (1 : A) ∈ I :=
  one_mem_of_ne_bot I (by rintro rfl; exact hx hxI)

lemma of_eq_bot_or_eq_top [Nontrivial R] (h : ∀ I : TwoSidedIdeal R, I = ⊥ ∨ I = ⊤) :
    IsSimpleRing R where
  simple := { eq_bot_or_eq_top := h }

instance _root_.DivisionRing.isSimpleRing (A : Type*) [DivisionRing A] : IsSimpleRing A :=
  .of_eq_bot_or_eq_top <| fun I ↦ by
    rw [or_iff_not_imp_left, ← I.one_mem_iff]
    intro H
    obtain ⟨x, hx1, hx2 : x ≠ 0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr H : ⊥ < I)
    simpa [inv_mul_cancel₀ hx2] using I.mul_mem_left x⁻¹ _ hx1

open TwoSidedIdeal in
lemma isField_center (A : Type*) [Ring A] [IsSimpleRing A] : IsField (Subring.center A) where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel := by
    rintro ⟨x, hx1⟩ hx2
    rw [Subring.mem_center_iff] at hx1
    replace hx2 : x ≠ 0 := by simpa [Subtype.ext_iff] using hx2
    -- Todo: golf the following `let` once `TwoSidedIdeal.span` is defined
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

lemma injective_ringHom_or_subsingleton_codomain
    {R S : Type*} [NonAssocRing R] [IsSimpleRing R] [NonAssocRing S]
    (f : R →+* S) : Function.Injective f ∨ Subsingleton S :=
  simple.eq_bot_or_eq_top (TwoSidedIdeal.ker f) |>.imp (TwoSidedIdeal.ker_eq_bot _ |>.1)
    (fun h => subsingleton_iff_zero_eq_one.1 <| by
      have mem : 1 ∈ TwoSidedIdeal.ker f := h.symm ▸ TwoSidedIdeal.mem_top _
      rwa [TwoSidedIdeal.mem_ker, map_one, eq_comm] at mem)

-- Implementation note: the following lemma **cannot** replace `RingHom.Injective` even though all
-- division rings are simple. For `RingHom.injective` works when the target is a semiring.
lemma injective_ringHom
    {R S : Type*} [NonAssocRing R] [IsSimpleRing R] [NonAssocRing S] [Nontrivial S]
    (f : R →+* S) : Function.Injective f :=
  injective_ringHom_or_subsingleton_codomain f |>.resolve_right fun r => not_subsingleton _ r

universe u in
lemma iff_injective_ringHom_or_subsingleton_codomain (R : Type u) [NonAssocRing R] [Nontrivial R] :
    IsSimpleRing R ↔
    ∀ {S : Type u} [NonAssocRing S] (f : R →+* S), Function.Injective f ∨ Subsingleton S where
  mp _ _ _ := injective_ringHom_or_subsingleton_codomain
  mpr H := of_eq_bot_or_eq_top fun I => H I.ringCon.mk' |>.imp
    (fun h => le_antisymm
      (fun _ hx => TwoSidedIdeal.ker_eq_bot _ |>.2 h ▸ I.ker_ringCon_mk'.symm ▸ hx) bot_le)
    (fun h => le_antisymm le_top fun x _ => I.mem_iff _ |>.2 (Quotient.eq'.1 (h.elim x 0)))

universe u in
lemma iff_injective_ringHom (R : Type u) [NonAssocRing R] [Nontrivial R] :
    IsSimpleRing R ↔
    ∀ {S : Type u} [NonAssocRing S] [Nontrivial S] (f : R →+* S), Function.Injective f :=
  iff_injective_ringHom_or_subsingleton_codomain R |>.trans <|
    ⟨fun H _ _ _ f => H f |>.resolve_right (by simpa [not_subsingleton_iff_nontrivial]),
      fun H S _ f => subsingleton_or_nontrivial S |>.recOn Or.inr fun _ => Or.inl <| H f⟩

end IsSimpleRing

lemma isSimpleRing_iff_isField (A : Type*) [CommRing A] : IsSimpleRing A ↔ IsField A :=
  ⟨fun _ ↦ Subring.topEquiv.symm.toMulEquiv.isField _ <| by
    rw [← Subring.center_eq_top A]; exact IsSimpleRing.isField_center A,
    fun h ↦ letI := h.toField; inferInstance⟩
