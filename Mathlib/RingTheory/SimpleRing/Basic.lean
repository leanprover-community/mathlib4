/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.RingTheory.SimpleRing.Defs
import Mathlib.Algebra.Ring.Opposite
import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-! # Basic Properties of Simple rings

A ring `R` is **simple** if it has only two two-sided ideals, namely `⊥` and `⊤`.

## Main results

- `IsSimpleRing.nontrivial`: simple rings are non-trivial.
- `DivisionRing.isSimpleRing`: division rings are simple.
- `RingHom.injective`: every ring homomorphism from a simple ring to a nontrivial ring is injective.
- `IsSimpleRing.iff_injective_ringHom`: a ring is simple iff every ring homomorphism to a nontrivial
  ring is injective.

-/

assert_not_exists Finset

variable (R : Type*) [NonUnitalNonAssocRing R]

namespace IsSimpleRing

variable {R}

instance [IsSimpleRing R] : Nontrivial R := by
  obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt (bot_lt_top : (⊥ : TwoSidedIdeal R) < ⊤)
  use x, 0, hx

lemma one_mem_of_ne_bot {A : Type*} [NonAssocRing A] [IsSimpleRing A] (I : TwoSidedIdeal A)
    (hI : I ≠ ⊥) : (1 : A) ∈ I :=
  (eq_bot_or_eq_top I).resolve_left hI ▸ ⟨⟩

lemma one_mem_of_ne_zero_mem {A : Type*} [NonAssocRing A] [IsSimpleRing A] (I : TwoSidedIdeal A)
    {x : A} (hx : x ≠ 0) (hxI : x ∈ I) : (1 : A) ∈ I :=
  one_mem_of_ne_bot I (by rintro rfl; exact hx hxI)

lemma of_eq_bot_or_eq_top [Nontrivial R] (h : ∀ I : TwoSidedIdeal R, I = ⊥ ∨ I = ⊤) :
    IsSimpleRing R where
  simple.eq_bot_or_eq_top := h

instance _root_.DivisionRing.isSimpleRing (A : Type*) [DivisionRing A] : IsSimpleRing A :=
  .of_eq_bot_or_eq_top <| fun I ↦ by
    rw [or_iff_not_imp_left, ← I.one_mem_iff]
    intro H
    obtain ⟨x, hx1, hx2 : x ≠ 0⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr H : ⊥ < I)
    simpa [inv_mul_cancel₀ hx2] using I.mul_mem_left x⁻¹ _ hx1

lemma injective_ringHom_or_subsingleton_codomain
    {R S : Type*} [NonAssocRing R] [IsSimpleRing R] [NonAssocSemiring S]
    (f : R →+* S) : Function.Injective f ∨ Subsingleton S :=
  simple.eq_bot_or_eq_top (TwoSidedIdeal.ker f) |>.imp (TwoSidedIdeal.ker_eq_bot _ |>.1)
    (fun h => subsingleton_iff_zero_eq_one.1 <| by
      have mem : 1 ∈ TwoSidedIdeal.ker f := h.symm ▸ TwoSidedIdeal.mem_top _
      rwa [TwoSidedIdeal.mem_ker, map_one, eq_comm] at mem)

protected theorem _root_.RingHom.injective
    {R S : Type*} [NonAssocRing R] [IsSimpleRing R] [NonAssocSemiring S] [Nontrivial S]
    (f : R →+* S) : Function.Injective f :=
  injective_ringHom_or_subsingleton_codomain f |>.resolve_right fun r => not_subsingleton _ r

universe u in
lemma iff_injective_ringHom_or_subsingleton_codomain (R : Type u) [NonAssocRing R] [Nontrivial R] :
    IsSimpleRing R ↔
    ∀ {S : Type u} [NonAssocSemiring S] (f : R →+* S), Function.Injective f ∨ Subsingleton S where
  mp _ _ _ := injective_ringHom_or_subsingleton_codomain
  mpr H := of_eq_bot_or_eq_top fun I => H I.ringCon.mk' |>.imp
    (fun h => le_antisymm
      (fun _ hx => TwoSidedIdeal.ker_eq_bot _ |>.2 h ▸ I.ker_ringCon_mk'.symm ▸ hx) bot_le)
    (fun h => le_antisymm le_top fun x _ => I.mem_iff _ |>.2 (Quotient.eq'.1 (h.elim x 0)))

universe u in
lemma iff_injective_ringHom (R : Type u) [NonAssocRing R] [Nontrivial R] :
    IsSimpleRing R ↔
    ∀ {S : Type u} [NonAssocSemiring S] [Nontrivial S] (f : R →+* S), Function.Injective f :=
  iff_injective_ringHom_or_subsingleton_codomain R |>.trans <|
    ⟨fun H _ _ _ f => H f |>.resolve_right (by simpa [not_subsingleton_iff_nontrivial]),
      fun H S _ f => subsingleton_or_nontrivial S |>.recOn Or.inr fun _ => Or.inl <| H f⟩

instance [IsSimpleRing R] : IsSimpleRing Rᵐᵒᵖ := ⟨TwoSidedIdeal.opOrderIso.symm.isSimpleOrder⟩

end IsSimpleRing
