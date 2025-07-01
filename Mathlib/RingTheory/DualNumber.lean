/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Algebraic properties of dual numbers

## Main results

* `DualNumber.instLocalRing`: The dual numbers over a field `K` form a local ring.
* `DualNumber.instPrincipalIdealRing`: The dual numbers over a field `K` form a principal ideal
  ring.

-/

namespace TrivSqZeroExt

variable {R M : Type*}

section Semiring
variable [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

lemma isNilpotent_iff_isNilpotent_fst {x : TrivSqZeroExt R M} :
    IsNilpotent x ↔ IsNilpotent x.fst := by
  constructor <;> rintro ⟨n, hn⟩
  · refine ⟨n, ?_⟩
    rw [← fst_pow, hn, fst_zero]
  · refine ⟨n * 2, ?_⟩
    rw [pow_mul]
    ext
    · rw [fst_pow, fst_pow, hn, zero_pow two_ne_zero, fst_zero]
    · rw [pow_two, snd_mul, fst_pow, hn, MulOpposite.op_zero, zero_smul, zero_smul, zero_add,
        snd_zero]

@[simp]
lemma isNilpotent_inl_iff (r : R) : IsNilpotent (.inl r : TrivSqZeroExt R M) ↔ IsNilpotent r := by
  rw [isNilpotent_iff_isNilpotent_fst, fst_inl]

@[simp]
lemma isNilpotent_inr (x : M) : IsNilpotent (.inr x : TrivSqZeroExt R M) := by
  refine ⟨2, by simp [pow_two]⟩

end Semiring

lemma isUnit_or_isNilpotent_of_isMaximal_isNilpotent [CommSemiring R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    (h : ∀ I : Ideal R, I.IsMaximal → IsNilpotent I)
    (a : TrivSqZeroExt R M) :
    IsUnit a ∨ IsNilpotent a := by
  rw [isUnit_iff_isUnit_fst, isNilpotent_iff_isNilpotent_fst]
  refine (em _).imp_right fun ha ↦ ?_
  obtain ⟨I, hI, haI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr ha)
  refine (h _ hI).imp fun n hn ↦ ?_
  exact hn.le (Ideal.pow_mem_pow haI _)

lemma isUnit_or_isNilpotent [DivisionSemiring R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
    (a : TrivSqZeroExt R M) :
    IsUnit a ∨ IsNilpotent a := by
  simp [isUnit_iff_isUnit_fst, isNilpotent_iff_isNilpotent_fst, em']

end TrivSqZeroExt

namespace DualNumber
variable {R : Type*}

lemma fst_eq_zero_iff_eps_dvd [Semiring R] {x : R[ε]} :
    x.fst = 0 ↔ ε ∣ x := by
  simp_rw [dvd_def, TrivSqZeroExt.ext_iff, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul,
    fst_eps, snd_eps, zero_mul, zero_smul, zero_add, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, one_mul, exists_and_left, iff_self_and]
  intro
  exact ⟨.inl x.snd, rfl⟩

lemma isNilpotent_eps [Semiring R] :
    IsNilpotent (ε : R[ε]) :=
  TrivSqZeroExt.isNilpotent_inr 1

open TrivSqZeroExt

lemma isNilpotent_iff_eps_dvd [DivisionSemiring R] {x : R[ε]} :
    IsNilpotent x ↔ ε ∣ x := by
  simp only [isNilpotent_iff_isNilpotent_fst, isNilpotent_iff_eq_zero, fst_eq_zero_iff_eps_dvd]

section Field

variable {K : Type*}

instance [DivisionRing K] : IsLocalRing K[ε] where
  isUnit_or_isUnit_of_add_one {a b} h := by
    rw [add_comm, ← eq_sub_iff_add_eq] at h
    rcases eq_or_ne (fst a) 0 with ha|ha <;>
    simp [isUnit_iff_isUnit_fst, h, ha]

lemma ideal_trichotomy [DivisionRing K] (I : Ideal K[ε]) :
    I = ⊥ ∨ I = .span {ε} ∨ I = ⊤ := by
  refine (eq_or_ne I ⊥).imp_right fun hb ↦ ?_
  refine (eq_or_ne I ⊤).symm.imp_left fun ht ↦ ?_
  have hd : ∀ x ∈ I, ε ∣ x := by
    intro x hxI
    rcases isUnit_or_isNilpotent x with hx|hx
    · exact absurd (Ideal.eq_top_of_isUnit_mem _ hxI hx) ht
    · rwa [← isNilpotent_iff_eps_dvd]
  have hd' : ∀ x ∈ I, x ≠ 0 → ∃ r, ε = r * x := by
    intro x hxI hx0
    obtain ⟨r, rfl⟩ := hd _ hxI
    have : ε * r = (fst r) • ε := by ext <;> simp
    rw [this] at hxI hx0 ⊢
    have hr : fst r ≠ 0 := by
      contrapose! hx0
      simp [hx0]
    refine ⟨r⁻¹, ?_⟩
    simp [TrivSqZeroExt.ext_iff, inv_mul_cancel₀ hr]
  refine le_antisymm ?_ ?_ <;> intro x <;>
    simp_rw [Ideal.mem_span_singleton', (commute_eps_right _).eq, eq_comm, ← dvd_def]
  · intro hx
    simp_rw [hd _ hx]
  · intro hx
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨r, hr⟩ := hd' _ hyI hy0
    rw [(commute_eps_left _).eq, hr, ← mul_assoc]
    exact Ideal.mul_mem_left _ _ hyI

lemma isMaximal_span_singleton_eps [DivisionRing K] :
    (Ideal.span {ε} : Ideal K[ε]).IsMaximal := by
  refine ⟨?_, fun I hI ↦ ?_⟩
  · simp [ne_eq, Ideal.eq_top_iff_one, Ideal.mem_span_singleton', TrivSqZeroExt.ext_iff]
  · rcases ideal_trichotomy I with rfl|rfl|rfl <;>
    first | simp at hI | simp

lemma maximalIdeal_eq_span_singleton_eps [Field K] :
    IsLocalRing.maximalIdeal K[ε] = Ideal.span {ε} :=
  (IsLocalRing.eq_maximalIdeal isMaximal_span_singleton_eps).symm

instance [DivisionRing K] : IsPrincipalIdealRing K[ε] where
  principal I := by
    rcases ideal_trichotomy I with rfl|rfl|rfl
    · exact bot_isPrincipal
    · exact ⟨_, rfl⟩
    · exact top_isPrincipal

lemma exists_mul_left_or_mul_right [DivisionRing K] (a b : K[ε]) :
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
  suffices ∃ c, fst x * fst c = fst y ∨ fst y * fst c = fst x by
    simpa [TrivSqZeroExt.ext_iff] using this
  rcases eq_or_ne (fst x) 0 with hx|hx
  · refine ⟨ε, Or.inr ?_⟩
    simp [hx]
  refine ⟨inl ((fst x)⁻¹ * fst y), ?_⟩
  simp [← inl_mul, ← mul_assoc, mul_inv_cancel₀ hx]

end Field

end DualNumber
