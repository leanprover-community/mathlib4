/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-!
# Geck's construction of a Lie algebra associated to a root system

This file contains an implementation of Geck's construction of a semisimple Lie algebra from a
reduced crystallographic root system. It follows [Geck](Geck2017) quite closely.

## Main definitions:
* `RootPairing.GeckConstruction.lieAlgebra`: the Geck construction of the Lie algebra associated to
  a root system with distinguished base.
* `RootPairing.GeckConstruction.cartanSubalgebra`: a distinguished subalgebra corresponding to a
  Cartan subalgebra of the Geck construction.
* `RootPairing.GeckConstruction.cartanSubalgebra_le_lieAlgebra`: the distinguished subalgebra is
  contained in the Geck construction.

## Alternative approaches

The are at least three ways to construct a Lie algebra from a root system:
1. As a quotient of a free Lie algebra, using the Serre relations
2. Directly defining the Lie bracket on $H ⊕ K^∣Φ|$
3. The Geck construction

We comment on these as follows:
1. This construction takes just a matrix as input. It yields a semisimple Lie algebra iff the
   matrix is a Cartan matrix but it is quite a lot of work to prove this. On the other hand, it also
   allows construction of Kac-Moody Lie algebras. It has been implemented as `Matrix.ToLieAlgebra`
   but as of May 2025, almost nothing has been proved about it in Mathlib.
2. This construction takes a root system with base as input, together with sufficient additional
   data to determine a collection of extraspecial pairs of roots. The additional data for the
   extraspecial pairs is required to pin down certain signs when defining the Lie bracket. (These
   signs can be interpreted as a set-theoretic splitting of Tits's extension of the Weyl group by
   an elementary 2-group of order $2^l$ where $l$ is the rank.)
3. This construction takes a root system with base as input and is implemented here.

There seems to be no known construction of a Lie algebra from a root system without first choosing
a base: https://mathoverflow.net/questions/495434/

## TODO
* Lemma stating `LinearIndependent R h` (easy using `RootPairing.Base.cartanMatrix_nondegenerate`).
* Instance stating `LieModule.IsIrreducible R (lieAlgebra b) (b.support ⊕ ι → R)`
  (Lemma 4.2 from [Geck](Geck2017)). This will immediately yield that the Geck construction is
  semisimple via `LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful`.
* Instance stating `((cartanSubalgebra b).comap (lieAlgebra b).incl).IsCartanSubalgebra`
  (included in Lemma 4.6 from [Geck](Geck2017)).

-/

noncomputable section

open Set

namespace RootPairing.GeckConstruction

variable {ι R M N : Type*} [Finite ι] [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] {b : P.Base}

/-- Part of an `sl₂` triple used in Geck's construction of a Lie algebra from a root system. -/
def e (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j ↦ if i' = i ∧ j = - i then 1 else 0)
    (.of fun i' j ↦ if i' = i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j ↦ if P.root i' = P.root i + P.root j then P.chainBotCoeff i j + 1 else 0)

/-- Part of an `sl₂` triple used in Geck's construction of a Lie algebra from a root system. -/
def f (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 0
    (.of fun i' j ↦ if i' = i ∧ j = i then 1 else 0)
    (.of fun i' j ↦ if i' = - i then ↑|b.cartanMatrix i j| else 0)
    (.of fun i' j ↦ if P.root i' = P.root j - P.root i then P.chainTopCoeff i j + 1 else 0)

/-- Part of an `sl₂` triple used in Geck's construction of a Lie algebra from a root system. -/
def h (i : b.support) :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  .fromBlocks 0 0 0 (.diagonal (P.pairingIn ℤ · i))

omit [Finite ι] [IsDomain R] [CharZero R] in
lemma h_def [DecidableEq ι] (i : b.support) :
    h i = .fromBlocks 0 0 0 (.diagonal (P.pairingIn ℤ · i)) := by
  ext (j | j) (k | k) <;> simp [h, Matrix.diagonal_apply]

omit [Finite ι] [IsDomain R] [CharZero R] in
lemma h_eq_diagonal [DecidableEq ι] (i : b.support) :
    h i = .diagonal (Sum.elim 0 (P.pairingIn ℤ · i)) := by
  ext (j | j) (k | k) <;> simp [h, Matrix.diagonal_apply]

omit [Finite ι] [IsDomain R] [CharZero R] in
lemma lie_h_h [Fintype ι] (i j : b.support) :
    ⁅h i, h j⁆ = 0 := by
  classical
  simpa only [h_eq_diagonal, ← commute_iff_lie_eq] using Matrix.commute_diagonal _ _

variable (b)

/-- An involutive matrix which can transfer results between `RootPairing.GeckConstruction.e` and
`RootPairing.GeckConstruction.f`. -/
def ω :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
  open scoped Classical in
  letI := P.indexNeg
  .fromBlocks 1 0 0 <| .of fun i j ↦ if i = -j then 1 else 0

/-- Geck's construction of the Lie algebra associated to a root system with distinguished base.

Note that it is convenient to include `range h` in the Lie span, to make it elementary that it
contains `RootPairing.GeckConstruction.cartanSubalgebra`, and not depend on
`RootPairing.GeckConstruction.lie_e_f_same`. -/
def lieAlgebra [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :=
  LieSubalgebra.lieSpan R _ (range h ∪ range e ∪ range f)

/-- A distinguished subalgebra corresponding to a Cartan subalgebra of the Geck construction. -/
def cartanSubalgebra [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) where
  __ := Submodule.span R (range h)
  lie_mem' {x y} hx hy := by
    have aux : (∀ u ∈ range (h (b := b)), ∀ v ∈ range (h (b := b)), ⁅u, v⁆ = 0) := by
      rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩; exact lie_h_h i j
    simp only [Submodule.carrier_eq_coe, SetLike.mem_coe, LieSubalgebra.mem_toSubmodule,
      ← LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero (R := R) aux] at hx hy ⊢
    exact LieSubalgebra.lie_mem _ hx hy

variable {b}

attribute [local simp] Ring.lie_def Matrix.mul_apply Matrix.one_apply Matrix.diagonal_apply

omit [Finite ι] [IsDomain R] [CharZero R] [P.IsCrystallographic] in
@[simp] lemma ω_mul_ω [DecidableEq ι] [Fintype ι] :
    ω b * ω b = 1 := by
  ext (k | k) (l | l) <;>
  simp [ω, -indexNeg_neg]

omit [Finite ι] [IsDomain R] in
lemma ω_mul_h [Fintype ι] (i : b.support) :
    ω b * h i = - h i * ω b := by
  classical
  ext (k | k) (l | l)
  · simp [ω, h]
  · simp [ω, h]
  · simp [ω, h]
  · simp only [ω, h, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₂]
    aesop

lemma ω_mul_e [Fintype ι] (i : b.support) :
    ω b * e i = f i * ω b := by
  letI := P.indexNeg
  classical
  ext (k | k) (l | l)
  · simp [ω, e, f]
  · simp only [ω, e, f, mul_ite, mul_zero, Fintype.sum_sum_type, Matrix.mul_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Finset.sum_ite_eq']
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (by aesop)]
    simp [← ite_and, and_comm, - indexNeg_neg, neg_eq_iff_eq_neg]
  · simp [ω, e, f]
  · simp only [ω, e, f, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.of_apply, mul_ite, ← neg_eq_iff_eq_neg (a := k)]
    rw [Finset.sum_eq_single_of_mem (-k) (Finset.mem_univ _) (by aesop)]
    simp [neg_eq_iff_eq_neg, sub_eq_add_neg]

lemma ω_mul_f [Fintype ι] (i : b.support) :
    ω b * f i = e i * ω b := by
  classical
  have := congr_arg (· * ω b) (congr_arg (ω b * ·) (ω_mul_e i))
  simp only [← mul_assoc, ω_mul_ω] at this
  simpa [mul_assoc, ω_mul_ω] using this.symm

lemma lie_e_f_mul_ω [Fintype ι] (i j : b.support) :
    ⁅e i, f j⁆ * ω b = - ω b * ⁅e j, f i⁆ := by
  classical
  calc ⁅e i, f j⁆ * ω b = e i * f j * ω b - f j * e i * ω b := by rw [Ring.lie_def, sub_mul]
                      _ = e i * (f j * ω b) - f j * (e i * ω b) := by rw [mul_assoc, mul_assoc]
                      _ = e i * (ω b * e j) - f j * (ω b * f i) := by rw [← ω_mul_e, ← ω_mul_f]
                      _ = (e i * ω b) * e j - (f j * ω b) * f i := by rw [← mul_assoc, ← mul_assoc]
                      _ = (ω b * f i) * e j - (ω b * e j) * f i := by rw [← ω_mul_e, ← ω_mul_f]
                      _ = ω b * (f i * e j) - ω b * (e j * f i) := by rw [mul_assoc, mul_assoc]
                      _ = -ω b * ⁅e j, f i⁆ := ?_
  rw [Ring.lie_def, mul_sub, neg_mul, neg_mul, sub_neg_eq_add]
  abel

variable [Fintype ι] (i j : b.support)

lemma cartanSubalgebra_le_lieAlgebra [DecidableEq ι] :
    cartanSubalgebra b ≤ lieAlgebra b := by
  rw [cartanSubalgebra, lieAlgebra, ← LieSubalgebra.toSubmodule_le_toSubmodule, Submodule.span_le]
  rintro - ⟨i, rfl⟩
  exact LieSubalgebra.subset_lieSpan <| Or.inl <| Or.inl <| mem_range_self i

end RootPairing.GeckConstruction
