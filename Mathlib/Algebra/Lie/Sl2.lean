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
 * `IsSl2Triple`: a structure representing a triple of elements in a Lie algebra which satisfy the
   standard relations for `sl₂`.
 * `IsSl2Triple.HasPrimitiveVectorWith`: a structure representing a primitive vector in a
   representation of a Lie algebra relative to a distinguished `sl₂` triple.
 * `IsSl2Triple.HasPrimitiveVectorWith.exists_nat`: the eigenvalue of a primitive vector must be a
   natural number if the representation is finite-dimensional.

-/

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

open LieModule Set

variable {L} in
/-- An `sl₂` triple within a Lie ring `L` is a triple of elements `h`, `e`, `f` obeying relations
which ensure that the Lie subalgebra they generate is equivalent to `sl₂`. -/
structure IsSl2Triple (h e f : L) : Prop where
  h_ne_zero : h ≠ 0
  lie_e_f : ⁅e, f⁆ = h
  lie_h_e_nsmul : ⁅h, e⁆ = 2 • e
  lie_h_f_nsmul : ⁅h, f⁆ = - (2 • f)

namespace IsSl2Triple

variable {L M}
variable {h e f : L}

lemma symm (ht : IsSl2Triple h e f) : IsSl2Triple (-h) f e where
  h_ne_zero := by simpa using ht.h_ne_zero
  lie_e_f := by rw [← neg_eq_iff_eq_neg, lie_skew, ht.lie_e_f]
  lie_h_e_nsmul := by rw [neg_lie, neg_eq_iff_eq_neg, ht.lie_h_f_nsmul]
  lie_h_f_nsmul := by rw [neg_lie, neg_inj, ht.lie_h_e_nsmul]

@[simp] lemma symm_iff : IsSl2Triple (-h) f e ↔ IsSl2Triple h e f :=
  ⟨fun t ↦ neg_neg h ▸ t.symm, symm⟩

lemma lie_h_e_smul (t : IsSl2Triple h e f) : ⁅h, e⁆ = (2 : R) • e := by
  simp [t.lie_h_e_nsmul, two_smul]

lemma lie_lie_smul_f (t : IsSl2Triple h e f) : ⁅h, f⁆ = -((2 : R) • f) := by
  simp [t.lie_h_f_nsmul, two_smul]

lemma e_ne_zero (t : IsSl2Triple h e f) : e ≠ 0 := by
  have := t.h_ne_zero
  contrapose! this
  simpa [this] using t.lie_e_f.symm

lemma f_ne_zero (t : IsSl2Triple h e f) : f ≠ 0 := by
  have := t.h_ne_zero
  contrapose! this
  simpa [this] using t.lie_e_f.symm

variable {R}

/-- Given a representation of a Lie algebra with distinguished `sl₂` triple, a vector is said to be
primitive if it is a simultaneous eigenvector for the action of both `h`, `e`, and the eigenvalue
for `e` is zero. -/
structure HasPrimitiveVectorWith (t : IsSl2Triple h e f) (m : M) (μ : R) : Prop where
  ne_zero : m ≠ 0
  lie_h : ⁅h, m⁆ = μ • m
  lie_e : ⁅e, m⁆ = 0

/-- Given a representation of a Lie algebra with distinguished `sl₂` triple, a simultaneous
eigenvector for the action of both `h` and `e` necessarily has eigenvalue zero for `e`. -/
lemma HasPrimitiveVectorWith.mk' [NoZeroSMulDivisors ℤ M] (t : IsSl2Triple h e f) (m : M) (μ ρ : R)
    (hm : m ≠ 0) (hm' : ⁅h, m⁆ = μ • m) (he : ⁅e, m⁆ = ρ • m) :
    HasPrimitiveVectorWith t m μ  where
  ne_zero := hm
  lie_h := hm'
  lie_e := by
    suffices 2 • ⁅e, m⁆ = 0 by simpa using this
    rw [← nsmul_lie, ← t.lie_h_e_nsmul, lie_lie, hm', lie_smul, he, lie_smul, hm',
      smul_smul, smul_smul, mul_comm ρ μ, sub_self]

namespace HasPrimitiveVectorWith

variable {m : M} {μ : R} {t : IsSl2Triple h e f} (P : HasPrimitiveVectorWith t m μ)

local notation "ψ" n => ((toEnd R L M f) ^ n) m

lemma lie_h_pow_toEnd_f (n : ℕ) :
    ⁅h, ψ n⁆ = (μ - 2 * n) • ψ n := by
  induction' n with n ih
  · simpa using P.lie_h
  · rw [pow_succ', LinearMap.mul_apply, toEnd_apply_apply, Nat.cast_add, Nat.cast_one,
      leibniz_lie h, t.lie_lie_smul_f R, ← neg_smul, ih, lie_smul, smul_lie, ← add_smul]
    congr
    ring

-- Although this is true by definition, we include this lemma (and the assumption) to mirror the API
-- for `lie_h_pow_toEnd_f` and `lie_e_pow_succ_toEnd_f`.
set_option linter.unusedVariables false in
@[nolint unusedArguments]
lemma lie_f_pow_toEnd_f (P : HasPrimitiveVectorWith t m μ) (n : ℕ) :
    ⁅f, ψ n⁆ = ψ (n + 1) := by
  simp [pow_succ']

lemma lie_e_pow_succ_toEnd_f (n : ℕ) :
    ⁅e, ψ (n + 1)⁆ = ((n + 1) * (μ - n)) • ψ n := by
  induction' n with n ih
  · simp only [zero_add, pow_one, toEnd_apply_apply, Nat.cast_zero, sub_zero, one_mul,
      pow_zero, LinearMap.one_apply, leibniz_lie e, t.lie_e_f, P.lie_e, P.lie_h, lie_zero,
      add_zero]
  · rw [pow_succ', LinearMap.mul_apply, toEnd_apply_apply, leibniz_lie e, t.lie_e_f,
      lie_h_pow_toEnd_f P, ih, lie_smul, lie_f_pow_toEnd_f P, ← add_smul,
      Nat.cast_add, Nat.cast_one]
    congr
    ring

/-- The eigenvalue of a primitive vector must be a natural number if the representation is
finite-dimensional. -/
lemma exists_nat [IsNoetherian R M] [NoZeroSMulDivisors R M] [IsDomain R] [CharZero R] :
    ∃ n : ℕ, μ = n := by
  suffices ∃ n : ℕ, (ψ n) = 0 by
    obtain ⟨n, hn₁, hn₂⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists P.ne_zero this
    refine ⟨n, ?_⟩
    have := lie_e_pow_succ_toEnd_f P n
    rw [hn₂, lie_zero, eq_comm, smul_eq_zero_iff_left hn₁, mul_eq_zero, sub_eq_zero] at this
    exact this.resolve_left <| Nat.cast_add_one_ne_zero n
  have hs : (range <| fun (n : ℕ) ↦ μ - 2 * n).Infinite := by
    rw [infinite_range_iff (fun n m ↦ by simp)]; infer_instance
  by_contra! contra
  exact hs ((toEnd R L M h).eigenvectors_linearIndependent
    {μ - 2 * n | n : ℕ}
    (fun ⟨s, hs⟩ ↦ ψ Classical.choose hs)
    (fun ⟨r, hr⟩ ↦ by simp [lie_h_pow_toEnd_f P, Classical.choose_spec hr, contra,
      Module.End.HasEigenvector, Module.End.mem_eigenspace_iff])).finite

lemma pow_toEnd_f_ne_zero_of_eq_nat
    [CharZero R] [NoZeroSMulDivisors R M]
    {n : ℕ} (hn : μ = n) {i} (hi : i ≤ n) : (ψ i) ≠ 0 := by
  intro H
  induction i
  · exact P.ne_zero (by simpa using H)
  · next i IH =>
    have : ((i + 1) * (n - i) : ℤ) • (toEnd R L M f ^ i) m = 0 := by
      have := congr_arg (⁅e, ·⁆) H
      simpa [zsmul_eq_smul_cast R, P.lie_e_pow_succ_toEnd_f, hn] using this
    rw [zsmul_eq_smul_cast R, smul_eq_zero, Int.cast_eq_zero, mul_eq_zero, sub_eq_zero,
      Nat.cast_inj, ← @Nat.cast_one ℤ, ← Nat.cast_add, Nat.cast_eq_zero] at this
    simp only [add_eq_zero, one_ne_zero, and_false, false_or] at this
    exact (hi.trans_eq (this.resolve_right (IH (i.le_succ.trans hi)))).not_lt i.lt_succ_self

lemma pow_toEnd_f_eq_zero_of_eq_nat
    [IsNoetherian R M] [NoZeroSMulDivisors R M] [IsDomain R] [CharZero R]
    {n : ℕ} (hn : μ = n) : (ψ (n + 1)) = 0 := by
  by_contra h
  have : t.HasPrimitiveVectorWith (ψ (n + 1)) (n - 2 * (n + 1) : R) :=
    { ne_zero := h
      lie_h := (P.lie_h_pow_toEnd_f _).trans (by simp [hn])
      lie_e := (P.lie_e_pow_succ_toEnd_f _).trans (by simp [hn]) }
  obtain ⟨m, hm⟩ := this.exists_nat
  have : (n : ℤ) < m + 2 * (n + 1) := by linarith
  exact this.ne (Int.cast_injective (α := R) <| by simpa [sub_eq_iff_eq_add] using hm)

end HasPrimitiveVectorWith

end IsSl2Triple
