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

lemma isNilpotent_fst_iff [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] {x : TrivSqZeroExt R M} :
    IsNilpotent x.fst ↔ IsNilpotent x := by
  constructor <;> rintro ⟨n, hn⟩
  · refine ⟨n * 2, ?_⟩
    rw [pow_mul]
    ext
    · rw [fst_pow, fst_pow, hn, zero_pow two_ne_zero, fst_zero]
    · rw [pow_two, snd_mul, fst_pow, hn, MulOpposite.op_zero, zero_smul, zero_smul, zero_add,
        snd_zero]
  · refine ⟨n, ?_⟩
    rw [← fst_pow, hn, fst_zero]

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

lemma isNilpotent_iff_eps_dvd {x : K[ε]} :
    IsNilpotent x ↔ ε ∣ x := by
  simp only [← isNilpotent_fst_iff, isNilpotent_iff_eq_zero, dvd_def, TrivSqZeroExt.ext_iff,
    fst_mul, fst_eps, zero_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, snd_eps,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, one_mul, zero_add, exists_and_left,
    iff_self_and]
  intro
  exact ⟨inl (snd _), rfl⟩

lemma isMaximal_span_singleton_eps :
    (Ideal.span {ε} : Ideal K[ε]).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  simp only [Ideal.mem_span_singleton, ← isNilpotent_iff_eps_dvd, ← isNilpotent_fst_iff, fst_one,
    isNilpotent_iff_eq_zero, one_ne_zero, not_false_eq_true, true_and]
  intro I x _ IH hx
  rw [← Ideal.eq_top_iff_one]
  rcases isUnit_or_isNilpotent x with hx'|hx'
  · exact Ideal.eq_top_of_isUnit_mem _ hx hx'
  · simp only [← isNilpotent_fst_iff, isNilpotent_iff_eq_zero] at hx'
    exact absurd hx' IH

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

lemma exists_mul_left_or_mul_right (a b : K[ε]) :
    ∃ c, a * c = b ∨ b * c = a := by
  rcases isUnit_or_isNilpotent a with ha|ha
  · lift a to K[ε]ˣ using ha
    exact ⟨a⁻¹ * b, by simp⟩
  rcases isUnit_or_isNilpotent b with hb|hb
  · lift b to K[ε]ˣ using hb
    exact ⟨b⁻¹ * a, by simp⟩
  rw [isNilpotent_iff_eps_dvd] at ha hb
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [← inl_fst_add_inr_snd_eq x, ← inl_fst_add_inr_snd_eq y]
  simp only [inr_eq_smul_eps, mul_add, Algebra.mul_smul_comm, eps_mul_eps, smul_zero, add_zero,
    mul_assoc]
  rcases eq_or_ne (fst x) 0 with hx|hx
  · refine ⟨ε, Or.inr ?_⟩
    simp [hx, mul_comm, ← mul_assoc]
  refine ⟨inl ((fst x)⁻¹ * fst y), Or.inl (congr_arg (ε * ·) ?_)⟩
  simp [← inl_mul, ← mul_assoc, mul_inv_cancel₀ hx]

end Field

end DualNumber
