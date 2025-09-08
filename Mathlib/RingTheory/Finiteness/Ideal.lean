/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Ideal.Maps

/-!
# Finitely generated ideals

Lemmas about finiteness of ideal operations.
-/

open Function (Surjective)
open Finsupp

namespace Ideal

variable {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The image of a finitely generated ideal is finitely generated.

This is the `Ideal` version of `Submodule.FG.map`. -/
theorem FG.map {R S : Type*} [Semiring R] [Semiring S] {I : Ideal R} (h : I.FG) (f : R →+* S) :
    (I.map f).FG := by
  classical
    obtain ⟨s, hs⟩ := h
    refine ⟨s.image f, ?_⟩
    rw [Finset.coe_image, ← Ideal.map_span, hs]

theorem fg_ker_comp {R S A : Type*} [CommRing R] [CommRing S] [CommRing A] (f : R →+* S)
    (g : S →+* A) (hf : (RingHom.ker f).FG) (hg : (RingHom.ker g).FG)
    (hsur : Function.Surjective f) :
    (RingHom.ker (g.comp f)).FG := by
  letI : Algebra R S := RingHom.toAlgebra f
  letI : Algebra R A := RingHom.toAlgebra (g.comp f)
  letI : Algebra S A := RingHom.toAlgebra g
  letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f₁ := Algebra.linearMap R S
  let g₁ := (IsScalarTower.toAlgHom R S A).toLinearMap
  exact Submodule.fg_ker_comp f₁ g₁ hf (Submodule.fg_restrictScalars (RingHom.ker g) hg hsur) hsur

theorem exists_radical_pow_le_of_fg {R : Type*} [CommSemiring R] (I : Ideal R) (h : I.radical.FG) :
    ∃ n : ℕ, I.radical ^ n ≤ I := by
  have := le_refl I.radical; revert this
  refine Submodule.fg_induction _ _ (fun J => J ≤ I.radical → ∃ n : ℕ, J ^ n ≤ I) ?_ ?_ _ h
  · intro x hx
    obtain ⟨n, hn⟩ := hx (subset_span (Set.mem_singleton x))
    exact ⟨n, by rwa [← Ideal.span, span_singleton_pow, span_le, Set.singleton_subset_iff]⟩
  · intro J K hJ hK hJK
    obtain ⟨n, hn⟩ := hJ fun x hx => hJK <| Ideal.mem_sup_left hx
    obtain ⟨m, hm⟩ := hK fun x hx => hJK <| Ideal.mem_sup_right hx
    use n + m
    rw [← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup, Finset.sup_le_iff]
    refine fun i _ => Ideal.mul_le_right.trans ?_
    obtain h | h := le_or_gt n i
    · apply Ideal.mul_le_right.trans ((Ideal.pow_le_pow_right h).trans hn)
    · apply Ideal.mul_le_left.trans
      refine (Ideal.pow_le_pow_right ?_).trans hm
      rw [add_comm, Nat.add_sub_assoc h.le]
      apply Nat.le_add_right

theorem exists_pow_le_of_le_radical_of_fg_radical {R : Type*} [CommSemiring R] {I J : Ideal R}
    (hIJ : I ≤ J.radical) (hJ : J.radical.FG) :
    ∃ k : ℕ, I ^ k ≤ J := by
  obtain ⟨k, hk⟩ := J.exists_radical_pow_le_of_fg hJ
  use k
  calc
    I ^ k ≤ J.radical ^ k := Ideal.pow_right_mono hIJ _
    _ ≤ J := hk

lemma exists_pow_le_of_le_radical_of_fg {R : Type*} [CommSemiring R] {I J : Ideal R}
    (h' : I ≤ J.radical) (h : I.FG) :
    ∃ n : ℕ, I ^ n ≤ J := by
  revert h'
  apply Submodule.fg_induction _ _ _ _ _ I h
  · intro x hJ
    simp only [Ideal.submodule_span_eq, Ideal.span_le,
      Set.singleton_subset_iff, SetLike.mem_coe] at hJ
    obtain ⟨n, hn⟩ := hJ
    refine ⟨n, by simpa [Ideal.span_singleton_pow, Ideal.span_le]⟩
  · intro I₁ I₂ h₁ h₂ hJ
    obtain ⟨n₁, hn₁⟩ := h₁ (le_sup_left.trans hJ)
    obtain ⟨n₂, hn₂⟩ := h₂ (le_sup_right.trans hJ)
    use n₁ + n₂
    exact Ideal.sup_pow_add_le_pow_sup_pow.trans (sup_le hn₁ hn₂)

end Ideal
