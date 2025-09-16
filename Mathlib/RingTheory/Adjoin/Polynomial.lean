/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomials and adjoining roots

## Main results

* `Polynomial.instCommSemiringAdjoinSingleton, instCommRingAdjoinSingleton`:
  adjoining an element to a commutative (semi)ring gives a commutative (semi)ring
-/

noncomputable section

open Finset

open Polynomial

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

section aeval

open Algebra

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]
variable [Algebra R A] [Algebra R B]
variable {p q : R[X]} (x : A)

@[simp]
theorem adjoin_X : adjoin R ({X} : Set R[X]) = ⊤ := by
  refine top_unique fun p _hp => ?_
  set S := adjoin R ({X} : Set R[X])
  rw [← sum_monomial_eq p]; simp only [← smul_X_eq_monomial]
  exact S.sum_mem fun n _hn => S.smul_mem (S.pow_mem (subset_adjoin rfl) _) _

variable (R)
theorem _root_.Algebra.adjoin_singleton_eq_range_aeval (x : A) :
    adjoin R {x} = (aeval x).range := by
  rw [← Algebra.map_top, ← adjoin_X, AlgHom.map_adjoin, Set.image_singleton, aeval_X]

@[simp]
theorem aeval_mem_adjoin_singleton : aeval x p ∈ adjoin R {x} := by
  simp [adjoin_singleton_eq_range_aeval]

theorem _root_.Algebra.adjoin_mem_exists_aeval {a : A} (h : a ∈ Algebra.adjoin R {x}) :
    ∃ p : R[X], aeval x p = a := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h
  simp_all

theorem _root_.Algebra.adjoin_eq_exists_aeval (a : Algebra.adjoin R {x}) :
    ∃ p : R[X], aeval x p = a := by
  have : (a : A) ∈ Algebra.adjoin R {x} := by simp
  set y := (a : A) with h
  rw [Algebra.adjoin_singleton_eq_range_aeval] at this
  simp_all

@[elab_as_elim]
theorem _root_.Algebra.adjoin_singleton_induction {M : (adjoin R {x}) → Prop}
    (a : adjoin R {x}) (f : ∀ (p : Polynomial R),
    M (⟨aeval x p, aeval_mem_adjoin_singleton R x⟩ : adjoin R {x})) :
    M a := by
  obtain ⟨p, hp⟩ := Algebra.adjoin_eq_exists_aeval _ x a
  aesop

instance instCommSemiringAdjoinSingleton :
    CommSemiring <| adjoin R {x} :=
  { mul_comm := fun ⟨p, hp⟩ ⟨q, hq⟩ ↦ by
      obtain ⟨p', rfl⟩ := Algebra.adjoin_singleton_eq_range_aeval R x ▸ hp
      obtain ⟨q', rfl⟩ := Algebra.adjoin_singleton_eq_range_aeval R x ▸ hq
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MulMemClass.mk_mul_mk, ← map_mul,
        mul_comm p' q'] }

instance instCommRingAdjoinSingleton {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (x : A) :
    CommRing <| Algebra.adjoin R {x} :=
  { mul_comm := mul_comm }

end aeval

end Polynomial
