/-
Copyright (c) 2024 Jujian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Jujian Zhang
-/

import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice

/-!
# Kernel of a ring homomorphism as a two-sided ideal

In this file we define the kernel of a ring homomorphism `f : R → S` as a two-sided ideal of `R`.

We put this in a separate file so that we could import it in `SimpleRing/Basic.lean` without
importing any finiteness result.
-/

assert_not_exists Finset

namespace TwoSidedIdeal

section ker

variable {R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocSemiring S]
variable {F : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S]
variable (f : F)

/--
The kernel of a ring homomorphism, as a two-sided ideal.
-/
def ker : TwoSidedIdeal R :=
  .mk
  { r := fun x y ↦ f x = f y
    iseqv := by constructor <;> aesop
    mul' := by intro; simp_all
    add' := by intro; simp_all }

@[simp]
lemma ker_ringCon {x y : R} : (ker f).ringCon x y ↔ f x = f y := Iff.rfl

lemma mem_ker {x : R} : x ∈ ker f ↔ f x = 0 := by
  rw [mem_iff, ker_ringCon, map_zero]

lemma ker_eq_bot : ker f = ⊥ ↔ Function.Injective f := by
  fconstructor
  · intro h x y hxy
    simpa [h, rel_iff, mem_bot, sub_eq_zero] using show (ker f).ringCon x y from hxy
  · exact fun h ↦ eq_bot_iff.2 fun x hx => h hx

section NonAssocRing

variable {R : Type*} [NonAssocRing R]

/--
The kernel of the ring homomorphism `R → R⧸I` is `I`.
-/
@[simp]
lemma ker_ringCon_mk' (I : TwoSidedIdeal R) : ker I.ringCon.mk' = I :=
  le_antisymm
    (fun _ h => by simpa using I.rel_iff _ _ |>.1 (Quotient.eq'.1 h))
    (fun _ h => Quotient.sound' <| I.rel_iff _ _ |>.2 (by simpa using h))

end NonAssocRing

end ker

end TwoSidedIdeal
