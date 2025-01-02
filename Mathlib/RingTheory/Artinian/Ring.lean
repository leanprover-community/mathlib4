/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu, Jujian Zhang
-/
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Nakayama

/-!
# Artinian rings

A ring is said to be left (or right) Artinian if it is Artinian as a left (or right) module over
itself, or simply Artinian if it is both left and right Artinian.

## Main definitions

* `IsArtinianRing R` is the proposition that `R` is a left Artinian ring.

## Main results

* `IsArtinianRing.localization_surjective`: the canonical homomorphism from a commutative artinian
  ring to any localization of itself is surjective.

* `IsArtinianRing.isNilpotent_jacobson_bot`: the Jacobson radical of a commutative artinian ring
  is a nilpotent ideal. (TODO: generalize to noncommutative rings.)

## Implementation Details

The predicate `IsArtinianRing` is defined in `Mathlib.RingTheory.Artinian.Ring` instead, so that we
can apply basic API on artinian modules to division rings without a heavy import.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel]

## Tags

Artinian, artinian, Artinian ring, artinian ring

-/

open Set Submodule IsArtinian

namespace IsArtinianRing

variable {R : Type*} [CommRing R] [IsArtinianRing R]

@[stacks 00J8]
theorem isNilpotent_jacobson_bot : IsNilpotent (Ideal.jacobson (⊥ : Ideal R)) := by
  let Jac := Ideal.jacobson (⊥ : Ideal R)
  let f : ℕ →o (Ideal R)ᵒᵈ := ⟨fun n => Jac ^ n, fun _ _ h => Ideal.pow_le_pow_right h⟩
  obtain ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → Jac ^ n = Jac ^ m := IsArtinian.monotone_stabilizes f
  refine ⟨n, ?_⟩
  let J : Ideal R := annihilator (Jac ^ n)
  suffices J = ⊤ by
    have hJ : J • Jac ^ n = ⊥ := annihilator_smul (Jac ^ n)
    simpa only [this, top_smul, Ideal.zero_eq_bot] using hJ
  by_contra hJ
  change J ≠ ⊤ at hJ
  rcases IsArtinian.set_has_minimal { J' : Ideal R | J < J' } ⟨⊤, hJ.lt_top⟩ with
    ⟨J', hJJ' : J < J', hJ' : ∀ I, J < I → ¬I < J'⟩
  rcases SetLike.exists_of_lt hJJ' with ⟨x, hxJ', hxJ⟩
  obtain rfl : J ⊔ Ideal.span {x} = J' := by
    apply eq_of_le_of_not_lt _ (hJ' (J ⊔ Ideal.span {x}) _)
    · exact sup_le hJJ'.le (span_le.2 (singleton_subset_iff.2 hxJ'))
    · rw [SetLike.lt_iff_le_and_exists]
      exact ⟨le_sup_left, ⟨x, mem_sup_right (mem_span_singleton_self x), hxJ⟩⟩
  have : J ⊔ Jac • Ideal.span {x} ≤ J ⊔ Ideal.span {x} :=
    sup_le_sup_left (smul_le.2 fun _ _ _ => Submodule.smul_mem _ _) _
  have : Jac * Ideal.span {x} ≤ J := by -- Need version 4 of Nakayama's lemma on Stacks
    by_contra H
    refine H (Ideal.mul_le_left.trans (le_of_le_smul_of_le_jacobson_bot (fg_span_singleton _) le_rfl
      (le_sup_right.trans_eq (this.eq_of_not_lt (hJ' _ ?_)).symm)))
    exact lt_of_le_of_ne le_sup_left fun h => H <| h.symm ▸ le_sup_right
  have : Ideal.span {x} * Jac ^ (n + 1) ≤ ⊥ := calc
    Ideal.span {x} * Jac ^ (n + 1) = Ideal.span {x} * Jac * Jac ^ n := by
      rw [pow_succ', ← mul_assoc]
    _ ≤ J * Jac ^ n := mul_le_mul (by rwa [mul_comm]) le_rfl
    _ = ⊥ := by simp [J]
  refine hxJ (mem_annihilator.2 fun y hy => (mem_bot R).1 ?_)
  refine this (mul_mem_mul (mem_span_singleton_self x) ?_)
  rwa [← hn (n + 1) (Nat.le_succ _)]

section Localization

variable (S : Submonoid R) (L : Type*) [CommRing L] [Algebra R L] [IsLocalization S L]
include S

/-- Localizing an artinian ring can only reduce the amount of elements. -/
theorem localization_surjective : Function.Surjective (algebraMap R L) := by
  intro r'
  obtain ⟨r₁, s, rfl⟩ := IsLocalization.mk'_surjective S r'
  -- TODO: can `rsuffices` be used to move the `exact` below before the proof of this `obtain`?
  obtain ⟨r₂, h⟩ : ∃ r : R, IsLocalization.mk' L 1 s = algebraMap R L r := by
    obtain ⟨n, r, hr⟩ := IsArtinian.exists_pow_succ_smul_dvd (s : R) (1 : R)
    use r
    rw [smul_eq_mul, smul_eq_mul, pow_succ, mul_assoc] at hr
    apply_fun algebraMap R L at hr
    simp only [map_mul] at hr
    rw [← IsLocalization.mk'_one (M := S) L, IsLocalization.mk'_eq_iff_eq, mul_one,
      Submonoid.coe_one, ← (IsLocalization.map_units L (s ^ n)).mul_left_cancel hr, map_mul]
  exact ⟨r₁ * r₂, by rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, h]⟩

theorem localization_artinian : IsArtinianRing L :=
  (localization_surjective S L).isArtinianRing

/-- `IsArtinianRing.localization_artinian` can't be made an instance, as it would make `S` + `R`
into metavariables. However, this is safe. -/
instance : IsArtinianRing (Localization S) :=
  localization_artinian S _

end Localization

end IsArtinianRing
