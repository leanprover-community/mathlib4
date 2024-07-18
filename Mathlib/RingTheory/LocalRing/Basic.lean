/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.JacobsonIdeal

#align_import ring_theory.ideal.local_ring from "leanprover-community/mathlib"@"ec1c7d810034d4202b0dd239112d1792be9f6fdc"

/-!

# Local rings

## Main definitions

* `LocalRing.ResidueField`: The quotient of a local ring by its maximal ideal.

-/


universe u v w u'

variable {R : Type u} {S : Type v} {T : Type w} {K : Type u'}

section CommSemiring

variable [CommSemiring R]

namespace LocalRing

theorem of_isUnit_or_isUnit_of_isUnit_add [Nontrivial R]
    (h : ∀ a b : R, IsUnit (a + b) → IsUnit a ∨ IsUnit b) : LocalRing R :=
  ⟨fun {a b} hab => h a b <| hab.symm ▸ isUnit_one⟩
#align local_ring.of_is_unit_or_is_unit_of_is_unit_add LocalRing.of_isUnit_or_isUnit_of_isUnit_add

/-- A semiring is local if it is nontrivial and the set of nonunits is closed under the addition. -/
theorem of_nonunits_add [Nontrivial R]
    (h : ∀ a b : R, a ∈ nonunits R → b ∈ nonunits R → a + b ∈ nonunits R) : LocalRing R :=
  ⟨fun {a b} hab => or_iff_not_and_not.2 fun H => h a b H.1 H.2 <| hab.symm ▸ isUnit_one⟩
#align local_ring.of_nonunits_add LocalRing.of_nonunits_add

/-- A semiring is local if it has a unique maximal ideal. -/
theorem of_unique_max_ideal (h : ∃! I : Ideal R, I.IsMaximal) : LocalRing R :=
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
#align local_ring.of_unique_max_ideal LocalRing.of_unique_max_ideal

theorem of_unique_nonzero_prime (h : ∃! P : Ideal R, P ≠ ⊥ ∧ Ideal.IsPrime P) : LocalRing R :=
  of_unique_max_ideal
    (by
      rcases h with ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩
      refine ⟨P, ⟨⟨hPnot_top, ?_⟩⟩, fun M hM => hPunique _ ⟨?_, Ideal.IsMaximal.isPrime hM⟩⟩
      · refine Ideal.maximal_of_no_maximal fun M hPM hM => ne_of_lt hPM ?_
        exact (hPunique _ ⟨ne_bot_of_gt hPM, Ideal.IsMaximal.isPrime hM⟩).symm
      · rintro rfl
        exact hPnot_top (hM.1.2 P (bot_lt_iff_ne_bot.2 hPnonzero)))
#align local_ring.of_unique_nonzero_prime LocalRing.of_unique_nonzero_prime

variable [LocalRing R]

variable (R)

instance maximalIdeal.isMaximal : (maximalIdeal R).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · intro h
    apply h
    exact isUnit_one
  · intro I x _ hx H
    erw [Classical.not_not] at hx
    rcases hx with ⟨u, rfl⟩
    simpa using I.mul_mem_left (↑u⁻¹) H
#align local_ring.maximal_ideal.is_maximal LocalRing.maximalIdeal.isMaximal

theorem maximal_ideal_unique : ∃! I : Ideal R, I.IsMaximal :=
  ⟨maximalIdeal R, maximalIdeal.isMaximal R, fun I hI =>
    hI.eq_of_le (maximalIdeal.isMaximal R).1.1 fun _ hx => hI.1.1 ∘ I.eq_top_of_isUnit_mem hx⟩
#align local_ring.maximal_ideal_unique LocalRing.maximal_ideal_unique

variable {R}

theorem eq_maximalIdeal {I : Ideal R} (hI : I.IsMaximal) : I = maximalIdeal R :=
  ExistsUnique.unique (maximal_ideal_unique R) hI <| maximalIdeal.isMaximal R
#align local_ring.eq_maximal_ideal LocalRing.eq_maximalIdeal

theorem le_maximalIdeal {J : Ideal R} (hJ : J ≠ ⊤) : J ≤ maximalIdeal R := by
  rcases Ideal.exists_le_maximal J hJ with ⟨M, hM1, hM2⟩
  rwa [← eq_maximalIdeal hM1]
#align local_ring.le_maximal_ideal LocalRing.le_maximalIdeal

@[simp]
theorem mem_maximalIdeal (x) : x ∈ maximalIdeal R ↔ x ∈ nonunits R :=
  Iff.rfl
#align local_ring.mem_maximal_ideal LocalRing.mem_maximalIdeal

theorem isField_iff_maximalIdeal_eq : IsField R ↔ maximalIdeal R = ⊥ :=
  not_iff_not.mp
    ⟨Ring.ne_bot_of_isMaximal_of_not_isField inferInstance, fun h =>
      Ring.not_isField_iff_exists_prime.mpr ⟨_, h, Ideal.IsMaximal.isPrime' _⟩⟩
#align local_ring.is_field_iff_maximal_ideal_eq LocalRing.isField_iff_maximalIdeal_eq

end LocalRing

end CommSemiring

section CommRing

variable [CommRing R]

namespace LocalRing

theorem of_isUnit_or_isUnit_one_sub_self [Nontrivial R] (h : ∀ a : R, IsUnit a ∨ IsUnit (1 - a)) :
    LocalRing R :=
  ⟨fun {a b} hab => add_sub_cancel_left a b ▸ hab.symm ▸ h a⟩
#align local_ring.of_is_unit_or_is_unit_one_sub_self LocalRing.of_isUnit_or_isUnit_one_sub_self

variable [LocalRing R]

theorem isUnit_or_isUnit_one_sub_self (a : R) : IsUnit a ∨ IsUnit (1 - a) :=
  isUnit_or_isUnit_of_isUnit_add <| (add_sub_cancel a 1).symm ▸ isUnit_one
#align local_ring.is_unit_or_is_unit_one_sub_self LocalRing.isUnit_or_isUnit_one_sub_self

theorem isUnit_of_mem_nonunits_one_sub_self (a : R) (h : 1 - a ∈ nonunits R) : IsUnit a :=
  or_iff_not_imp_right.1 (isUnit_or_isUnit_one_sub_self a) h
#align local_ring.is_unit_of_mem_nonunits_one_sub_self LocalRing.isUnit_of_mem_nonunits_one_sub_self

theorem isUnit_one_sub_self_of_mem_nonunits (a : R) (h : a ∈ nonunits R) : IsUnit (1 - a) :=
  or_iff_not_imp_left.1 (isUnit_or_isUnit_one_sub_self a) h
#align local_ring.is_unit_one_sub_self_of_mem_nonunits LocalRing.isUnit_one_sub_self_of_mem_nonunits

theorem of_surjective' [CommRing S] [Nontrivial S] (f : R →+* S) (hf : Function.Surjective f) :
    LocalRing S :=
  of_isUnit_or_isUnit_one_sub_self (by
    intro b
    obtain ⟨a, rfl⟩ := hf b
    apply (isUnit_or_isUnit_one_sub_self a).imp <| RingHom.isUnit_map _
    rw [← f.map_one, ← f.map_sub]
    apply f.isUnit_map)
#align local_ring.of_surjective' LocalRing.of_surjective'

theorem maximalIdeal_le_jacobson (I : Ideal R) :
    LocalRing.maximalIdeal R ≤ I.jacobson :=
  le_sInf fun _ ⟨_, h⟩ => le_of_eq (LocalRing.eq_maximalIdeal h).symm

theorem jacobson_eq_maximalIdeal (I : Ideal R) (h : I ≠ ⊤) :
    I.jacobson = LocalRing.maximalIdeal R :=
  le_antisymm (sInf_le ⟨le_maximalIdeal h, maximalIdeal.isMaximal R⟩)
              (maximalIdeal_le_jacobson I)
#align local_ring.jacobson_eq_maximal_ideal LocalRing.jacobson_eq_maximalIdeal

end LocalRing

end CommRing

namespace LocalRing

section

variable [CommRing R] [LocalRing R] [CommRing S] [LocalRing S] [CommRing T] [LocalRing T]

theorem ker_eq_maximalIdeal [Field K] (φ : R →+* K) (hφ : Function.Surjective φ) :
    RingHom.ker φ = maximalIdeal R :=
  LocalRing.eq_maximalIdeal <| (RingHom.ker_isMaximal_of_surjective φ) hφ
#align local_ring.ker_eq_maximal_ideal LocalRing.ker_eq_maximalIdeal

end

end LocalRing

namespace Field

variable (K) [Field K]

open scoped Classical

-- see Note [lower instance priority]
instance (priority := 100) : LocalRing K :=
  LocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    if h : a = 0 then Or.inr (by rw [h, sub_zero]; exact isUnit_one)
    else Or.inl <| IsUnit.mk0 a h

end Field

theorem LocalRing.maximalIdeal_eq_bot {R : Type*} [Field R] : LocalRing.maximalIdeal R = ⊥ :=
  LocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField R)
#align local_ring.maximal_ideal_eq_bot LocalRing.maximalIdeal_eq_bot
