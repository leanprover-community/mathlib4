/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

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

variable [LocalRing R]

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

theorem LocalRing.maximalIdeal_eq_bot {R : Type*} [Field R] : LocalRing.maximalIdeal R = ⊥ :=
  LocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField R)
#align local_ring.maximal_ideal_eq_bot LocalRing.maximalIdeal_eq_bot
