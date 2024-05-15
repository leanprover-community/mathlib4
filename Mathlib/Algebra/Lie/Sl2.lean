/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!

# The Lie algebra `sl₂` and its representations

The Lie algebra `sl₂` is the unique simple Lie algebra of minimal rank, 1, and as such occupies a
distinguished position in the general theory. This file provides some basic definitions and results
about `sl₂`.

## Main definitions:
 * `Sl2Triple`: a structure representing a triple of elements in a Lie algebra which satisfy the
   standard relations for `sl₂`.
 * `Sl2Triple.HasPrimitiveVectorWith`: a structure representing a primitive vector in a
   representation of a Lie algebra relative to a distinguished `sl₂` triple.
 * `Sl2Triple.HasPrimitiveVectorWith.exists_nat`: the eigenvalue of a primitive vector must be a
   natural number if the representation is finite-dimensional.

-/

-- TODO Find home for this, maybe generalise and put in `Mathlib.Order.SuccPred.Basic`?
lemma Nat.exists_not_and_succ_of_exists_and_not_zero {p : ℕ → Prop} (H : ∃ n, p n) (H' : ¬ p 0) :
    ∃ n, ¬ p n ∧ p (n + 1) := by
  classical
  let k := Nat.find H
  have hk : p k := Nat.find_spec H
  suffices 0 < k from
    ⟨k - 1, Nat.find_min H <| Nat.pred_lt this.ne', by rwa [Nat.sub_add_cancel this]⟩
  by_contra! contra
  rw [nonpos_iff_eq_zero.mp contra] at hk
  exact H' hk

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

open LieModule

/-- An `sl₂` triple within a Lie ring `L` is a triple of elements `h`, `e`, `f` obeying relations
which ensure that the Lie subalgebra they generate is either equivalent to `sl₂` or trivial.

Note that since `h = ⁅e, f⁆`, we do not include it as part of the data. -/
@[ext] structure Sl2Triple where
  /-- The "positive" nilpotent element of an `sl₂` triple. -/
  e : L
  /-- The "negative" nilpotent element of an `sl₂` triple. -/
  f : L
  lie_lie_nsmul_e : ⁅⁅e, f⁆, e⁆ = 2 • e
  lie_lie_nsmul_f : ⁅⁅e, f⁆, f⁆ = - (2 • f)

namespace Sl2Triple

variable {R L M}
variable (t : Sl2Triple L)

lemma lie_lie_smul_e : ⁅⁅t.e, t.f⁆, t.e⁆ = (2 : R) • t.e := by simp [t.lie_lie_nsmul_e, two_smul]

lemma lie_lie_smul_f : ⁅⁅t.e, t.f⁆, t.f⁆ = -((2 : R) • t.f) := by simp [t.lie_lie_nsmul_f, two_smul]

/-- The semisimple element of an `sl₂` triple. -/
def h := ⁅t.e, t.f⁆

lemma lie_e_f : ⁅t.e, t.f⁆ = t.h := rfl

lemma lie_h_e : ⁅t.h, t.e⁆ = (2 : R) • t.e := by rw [← lie_e_f]; exact lie_lie_smul_e t

lemma lie_h_f : ⁅t.h, t.f⁆ = - ((2 : R) • t.f) := by rw [← lie_e_f]; exact lie_lie_smul_f t

/-- Swapping the roles of `e` and `f` yields a natural involution on `sl₂` triples. -/
@[simps] def symm : Sl2Triple L where
  e := t.f
  f := t.e
  lie_lie_nsmul_e := by rw [← lie_skew t.f _, neg_lie, neg_eq_iff_eq_neg, lie_lie_nsmul_f]
  lie_lie_nsmul_f := by rw [← lie_skew t.f _, neg_lie, neg_eq_iff_eq_neg, neg_neg, lie_lie_nsmul_e]

@[simp] lemma symm_symm : t.symm.symm = t := rfl

instance instZero : Zero (Sl2Triple L) where zero := ⟨0, 0, by simp, by simp⟩

protected lemma zero_eq : (0 : Sl2Triple L) = ⟨0, 0, by simp, by simp⟩ := rfl

protected lemma eq_zero_iff : t = 0 ↔ t.e = 0 ∧ t.f = 0 := by cases t; simp [Sl2Triple.zero_eq]

section NoZeroSMulDivisors

variable [NoZeroSMulDivisors ℤ L]

@[simp] lemma e_eq_zero_iff : t.e = 0 ↔ t = 0 := by
  cases' t with e f lie_lie_nsmul_e lie_lie_nsmul_f
  simp only [Sl2Triple.zero_eq, mk.injEq]
  exact ⟨fun hyp ↦ ⟨hyp, by aesop⟩, fun hyp ↦ hyp.1⟩

@[simp] lemma f_eq_zero_iff : t.f = 0 ↔ t = 0 := by
  cases' t with e f lie_lie_nsmul_e lie_lie_nsmul_f
  simp only [Sl2Triple.zero_eq, mk.injEq]
  rw [eq_comm] at lie_lie_nsmul_e
  exact ⟨fun hyp ↦ ⟨by aesop, hyp⟩, fun hyp ↦ hyp.2⟩

@[simp] lemma h_eq_zero_iff : t.h = 0 ↔ t = 0 := by
  refine ⟨fun hyp ↦ ?_, fun hyp ↦ ?_⟩
  · simpa [t.lie_e_f, hyp, eq_comm (a := (0 : L))] using t.lie_lie_nsmul_e
  · rw [← t.lie_e_f, t.e_eq_zero_iff.mpr hyp, zero_lie]

end NoZeroSMulDivisors

/-- Given a representation of a Lie algebra with distinguished `sl₂` triple, a vector is said to be
primitive if it is a simultaneous eigenvector for the action of both `h`, `e`, and the eigenvalue
for `e` is zero. -/
structure HasPrimitiveVectorWith (m : M) (μ : R) : Prop where
  ne_zero : m ≠ 0
  lie_h : ⁅t.h, m⁆ = μ • m
  lie_e : ⁅t.e, m⁆ = 0

/-- Given a representation of a Lie algebra with distinguished `sl₂` triple, a simultaneous
eigenvector for the action of both `h` and `e` necessarily has eigenvalue zero for `e`. -/
lemma HasPrimitiveVectorWith.mk' [NoZeroSMulDivisors ℤ M] (m : M) (μ ρ : R)
    (hm : m ≠ 0) (hm' : ⁅t.h, m⁆ = μ • m) (he : ⁅t.e, m⁆ = ρ • m) :
    t.HasPrimitiveVectorWith m μ where
  ne_zero := hm
  lie_h := hm'
  lie_e := by
    suffices 2 • ⁅t.e, m⁆ = 0 by simpa using this
    rw [← nsmul_lie, ← t.lie_lie_nsmul_e, lie_lie, t.lie_e_f, hm', lie_smul, he, lie_smul, hm',
      smul_smul, smul_smul, mul_comm ρ μ, sub_self]

namespace HasPrimitiveVectorWith

variable {m : M} {μ : R} (P : t.HasPrimitiveVectorWith m μ)

local notation "ψ" n => ((toEndomorphism R L M t.f) ^ n) m

lemma lie_h_pow_toEndomorphism_f (n : ℕ) :
    ⁅t.h, ψ n⁆ = (μ - 2 * n) • ψ n := by
  induction' n with n ih
  · simpa using P.lie_h
  · rw [pow_succ', LinearMap.mul_apply, toEndomorphism_apply_apply, Nat.cast_add, Nat.cast_one,
      leibniz_lie t.h, t.lie_h_f (R := R), ← neg_smul, ih, lie_smul, smul_lie, ← add_smul]
    congr
    ring

lemma lie_f_pow_toEndomorphism_f (n : ℕ) :
    ⁅t.f, ψ n⁆ = ψ (n + 1) := by
  simp [pow_succ']

lemma lie_e_pow_succ_toEndomorphism_f (n : ℕ) :
    ⁅t.e, ψ (n + 1)⁆ = ((n + 1) * (μ - n)) • ψ n := by
  induction' n with n ih
  · simp only [zero_add, pow_one, toEndomorphism_apply_apply, Nat.cast_zero, sub_zero, one_mul,
      pow_zero, LinearMap.one_apply, leibniz_lie t.e, t.lie_e_f, P.lie_e, P.lie_h, lie_zero,
      add_zero]
  · rw [pow_succ', LinearMap.mul_apply, toEndomorphism_apply_apply, leibniz_lie t.e, t.lie_e_f,
      lie_h_pow_toEndomorphism_f t P, ih, lie_smul, lie_f_pow_toEndomorphism_f, ← add_smul,
      Nat.cast_add, Nat.cast_one]
    congr
    ring

open Module.End in
/-- The eigenvalue of a primitive vector must be a natural number if the representation is
finite-dimensional. -/
lemma exists_nat [IsNoetherian R M] [NoZeroSMulDivisors R M] [IsDomain R] [CharZero R] :
    ∃ z : ℕ, μ = z := by
  suffices ∃ n : ℕ, (ψ n) = 0 by
    obtain ⟨n, hn₁, hn₂⟩ := Nat.exists_not_and_succ_of_exists_and_not_zero this P.ne_zero
    refine ⟨n, ?_⟩
    have := lie_e_pow_succ_toEndomorphism_f t P n
    rw [hn₂, lie_zero, eq_comm, smul_eq_zero_iff_left hn₁, mul_eq_zero, sub_eq_zero] at this
    exact_mod_cast this.resolve_left <| Nat.cast_add_one_ne_zero n
  have hs : (Set.range <| fun (n : ℕ) ↦ μ - 2 * n).Infinite := by
    rw [← Set.image_univ, Set.infinite_image_iff (Function.Injective.injOn (fun n m ↦ by simp) _)]
    exact Set.infinite_univ
  by_contra! contra
  exact hs ((toEndomorphism R L M t.h).eigenvectors_linearIndependent
    {μ - 2 * n | n : ℕ}
    (fun ⟨s, hs⟩ ↦ ψ Classical.choose hs)
    (fun ⟨s, hs⟩ ↦ by simp [lie_h_pow_toEndomorphism_f t P, Classical.choose_spec hs, contra,
      HasEigenvector, mem_eigenspace_iff])).finite

end HasPrimitiveVectorWith

end Sl2Triple
