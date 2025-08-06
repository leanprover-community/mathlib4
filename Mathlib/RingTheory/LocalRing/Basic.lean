/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.Ideal.Nonunits

/-!

# Local rings

We prove basic properties of local rings.

-/

variable {R S : Type*}

namespace IsLocalRing

section Semiring

variable [Semiring R]

theorem of_isUnit_or_isUnit_of_isUnit_add [Nontrivial R]
    (h : ∀ a b : R, IsUnit (a + b) → IsUnit a ∨ IsUnit b) : IsLocalRing R :=
  ⟨fun {a b} hab => h a b <| hab.symm ▸ isUnit_one⟩

/-- A semiring is local if it is nontrivial and the set of nonunits is closed under the addition. -/
theorem of_nonunits_add [Nontrivial R]
    (h : ∀ a b : R, a ∈ nonunits R → b ∈ nonunits R → a + b ∈ nonunits R) : IsLocalRing R where
  isUnit_or_isUnit_of_add_one {a b} hab :=
    or_iff_not_and_not.2 fun H => h a b H.1 H.2 <| hab.symm ▸ isUnit_one

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- A semiring is local if it has a unique maximal ideal. -/
theorem of_unique_max_ideal (h : ∃! I : Ideal R, I.IsMaximal) : IsLocalRing R :=
  @of_nonunits_add _ _
    (nontrivial_of_ne (0 : R) 1 <|
      let ⟨I, Imax, _⟩ := h
      fun H : 0 = 1 => Imax.1.1 <| I.eq_top_iff_one.2 <| H ▸ I.zero_mem)
    fun x y hx hy H =>
    let ⟨I, Imax, Iuniq⟩ := h
    let ⟨Ix, Ixmax, Hx⟩ := exists_max_ideal_of_mem_nonunits hx
    let ⟨Iy, Iymax, Hy⟩ := exists_max_ideal_of_mem_nonunits hy
    have xmemI : x ∈ I := Iuniq Ix Ixmax ▸ Hx
    have ymemI : y ∈ I := Iuniq Iy Iymax ▸ Hy
    Imax.1.1 <| I.eq_top_of_isUnit_mem (I.add_mem xmemI ymemI) H

theorem of_unique_nonzero_prime (h : ∃! P : Ideal R, P ≠ ⊥ ∧ Ideal.IsPrime P) : IsLocalRing R :=
  of_unique_max_ideal
    (by
      rcases h with ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩
      refine ⟨P, ⟨⟨hPnot_top, ?_⟩⟩, fun M hM => hPunique _ ⟨?_, Ideal.IsMaximal.isPrime hM⟩⟩
      · refine Ideal.maximal_of_no_maximal fun M hPM hM => ne_of_lt hPM ?_
        exact (hPunique _ ⟨ne_bot_of_gt hPM, Ideal.IsMaximal.isPrime hM⟩).symm
      · rintro rfl
        exact hPnot_top (hM.1.2 P (bot_lt_iff_ne_bot.2 hPnonzero)))

variable [IsLocalRing R]

theorem isUnit_or_isUnit_of_isUnit_add {a b : R} (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b := by
  rcases h with ⟨u, hu⟩
  rw [← Units.inv_mul_eq_one, mul_add] at hu
  apply Or.imp _ _ (isUnit_or_isUnit_of_add_one hu) <;> exact isUnit_of_mul_isUnit_right

theorem nonunits_add {a b : R} (ha : a ∈ nonunits R) (hb : b ∈ nonunits R) : a + b ∈ nonunits R :=
  fun H => not_or_intro ha hb (isUnit_or_isUnit_of_isUnit_add H)

end CommSemiring

section Ring

variable [Ring R]

theorem of_isUnit_or_isUnit_one_sub_self [Nontrivial R] (h : ∀ a : R, IsUnit a ∨ IsUnit (1 - a)) :
    IsLocalRing R :=
  ⟨fun {a b} hab => add_sub_cancel_left a b ▸ hab.symm ▸ h a⟩

end Ring

section CommRing

variable [CommRing R] [IsLocalRing R]

theorem isUnit_or_isUnit_one_sub_self (a : R) : IsUnit a ∨ IsUnit (1 - a) :=
  isUnit_or_isUnit_of_isUnit_add <| (add_sub_cancel a 1).symm ▸ isUnit_one

theorem isUnit_of_mem_nonunits_one_sub_self (a : R) (h : 1 - a ∈ nonunits R) : IsUnit a :=
  or_iff_not_imp_right.1 (isUnit_or_isUnit_one_sub_self a) h

theorem isUnit_one_sub_self_of_mem_nonunits (a : R) (h : a ∈ nonunits R) : IsUnit (1 - a) :=
  or_iff_not_imp_left.1 (isUnit_or_isUnit_one_sub_self a) h

theorem of_surjective' [Ring S] [Nontrivial S] (f : R →+* S) (hf : Function.Surjective f) :
    IsLocalRing S :=
  of_isUnit_or_isUnit_one_sub_self (by
    intro b
    obtain ⟨a, rfl⟩ := hf b
    apply (isUnit_or_isUnit_one_sub_self a).imp <| RingHom.isUnit_map _
    rw [← f.map_one, ← f.map_sub]
    apply f.isUnit_map)

end CommRing

end IsLocalRing

namespace Field

variable (K : Type*) [Field K]

-- see Note [lower instance priority]
instance (priority := 100) : IsLocalRing K := by
  classical exact IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    if h : a = 0 then Or.inr (by rw [h, sub_zero]; exact isUnit_one)
    else Or.inl <| IsUnit.mk0 a h

end Field
