/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Algebraic properties of dual numbers

## Main results

* `DualNumber.instLocalRing`
The dual numbers over a field `K` form a local ring.
* `DualNumber.instPrincipalIdealRing`
The dual numbers over a field `K` form a principal ideal ring.

-/

namespace TrivSqZeroExt

variable {R M : Type*}

lemma isNilpotent_inr [Semiring R] [AddCommMonoid M]
    [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (x : M) :
    IsNilpotent (.inr x : TrivSqZeroExt R M) := by
  refine ⟨2, by simp [pow_two]⟩

lemma isNilpotent_fst_iff [CommSemiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] {x : TrivSqZeroExt R M} :
    IsNilpotent x.fst ↔ IsNilpotent x := by
  constructor <;> rintro ⟨n, hn⟩
  · refine ⟨2 * n, ?_⟩
    rw [pow_mul, ← inl_fst_add_inr_snd_eq x]
    simp only [pow_two, mul_add, add_mul, inr_mul_inr, add_zero, mul_comm, add_assoc, ← two_mul]
    ring_nf
    rw [add_pow]
    refine Finset.sum_eq_zero ?_
    simp only [Finset.mem_range, inl_pow]
    rintro (_|_|k) hk
    · simp [← pow_mul _ 2, mul_comm 2, pow_mul _ n, hn]
    · simp only [zero_add, lt_add_iff_pos_left] at hk
      simp only [zero_add, pow_one, Nat.choose_one_right]
      ring_nf
      rw [mul_right_comm (inl _), ← inl_mul, ← pow_succ', mul_two (n - 1), add_assoc,
          Nat.sub_add_cancel hk, add_comm, pow_add]
      simp [hn]
    · rw [add_assoc, ← two_mul, mul_one, add_comm, pow_add, mul_pow, mul_pow]
      simp [pow_two]
  · refine ⟨n, ?_⟩
    simp [← fst_pow, hn]

lemma isUnit_or_isNilpotent_of_isMaximal_isNilpotent [CommSemiring R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    (h : ∀ I : Ideal R, I.IsMaximal → IsNilpotent I)
    (a : TrivSqZeroExt R M) :
    IsUnit a ∨ IsNilpotent a := by
  rw [isUnit_iff_isUnit_fst, ← isNilpotent_fst_iff]
  refine (em _).imp_right fun ha ↦ ?_
  obtain ⟨I, hI, haI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr ha)
  refine (h _ hI).imp fun n hn ↦ ?_
  exact hn.le (Ideal.pow_mem_pow haI _)

lemma isUnit_or_isNilpotent [Field R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    (a : TrivSqZeroExt R M) :
    IsUnit a ∨ IsNilpotent a := by
  refine isUnit_or_isNilpotent_of_isMaximal_isNilpotent ?_ _
  simp only [isNilpotent_iff_eq_zero, Submodule.zero_eq_bot]
  intros
  exact Ideal.eq_bot_of_prime _

end TrivSqZeroExt

namespace DualNumber

lemma isNilpotent_eps {R : Type*} [Semiring R] :
    IsNilpotent (ε : R[ε]) :=
  TrivSqZeroExt.isNilpotent_inr 1

section Field

open TrivSqZeroExt

variable {K : Type*} [Field K]

instance : LocalRing K[ε] :=
  .of_isUnit_or_isUnit_one_sub_self fun _ ↦
    (isUnit_or_isNilpotent _).imp_right IsNilpotent.isUnit_one_sub

lemma isMaximal_span_singleton_eps :
    (Ideal.span {ε} : Ideal K[ε]).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  simp only [Ideal.mem_span_singleton', TrivSqZeroExt.ext_iff, fst_mul, fst_eps, mul_zero, fst_one,
    zero_ne_one, TrivSqZeroExt.snd_mul, snd_eps, smul_eq_mul, mul_one, MulOpposite.op_zero,
    zero_smul, add_zero, snd_one, false_and, exists_const, not_false_eq_true,
    Ideal.span_singleton_le_iff_mem, exists_and_left, not_and, not_exists, true_and]
  intro I x _ IH hx
  rw [← Ideal.eq_top_iff_one]
  rcases isUnit_or_isNilpotent x with hx'|hx'
  · exact Ideal.eq_top_of_isUnit_mem _ hx hx'
  · simp only [← isNilpotent_fst_iff, isNilpotent_iff_eq_zero] at hx'
    exact absurd rfl (IH hx'.symm (.inl (snd x)))

lemma maximalIdeal_eq_span_singleton_eps :
    LocalRing.maximalIdeal K[ε] = Ideal.span {ε} :=
  (LocalRing.eq_maximalIdeal isMaximal_span_singleton_eps).symm

lemma isMaximal_iff_span_singleton_eps {I : Ideal K[ε]} :
    I.IsMaximal ↔ I = .span {ε} := by
  rw [← maximalIdeal_eq_span_singleton_eps]
  constructor
  · exact LocalRing.eq_maximalIdeal
  · rintro rfl
    infer_instance

instance : IsPrincipalIdealRing K[ε] where
  principal I := by
    rcases eq_or_ne I ⊥ with rfl|hb
    · exact bot_isPrincipal
    rcases eq_or_ne I ⊤ with rfl|ht
    · exact top_isPrincipal
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    refine ⟨x, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem I).mpr hxI)⟩
    rcases isUnit_or_isNilpotent x with hx|hx
    · simp [Ideal.eq_top_of_isUnit_mem _ hxI hx] at ht
    simp only [← isNilpotent_fst_iff, isNilpotent_iff_eq_zero] at hx
    rw [← inl_fst_add_inr_snd_eq x, hx, inl_zero, zero_add, inr_eq_smul_eps,
      Ideal.submodule_span_eq, ← inl_mul_eq_smul, Ideal.span_singleton_mul_left_unit,
      ← maximalIdeal_eq_span_singleton_eps]
    · exact LocalRing.le_maximalIdeal ht
    · contrapose! hx0
      simp only [isUnit_inl_iff, isUnit_iff_ne_zero, ne_eq, not_not] at hx0
      ext <;> simp [hx, hx0]

end Field

end DualNumber
