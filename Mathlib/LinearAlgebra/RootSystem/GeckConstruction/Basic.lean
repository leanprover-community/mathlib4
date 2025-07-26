/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Algebra.Lie.Semisimple.Lemmas
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Weights.Linear
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Lemmas

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
* `RootPairing.GeckConstruction.isSl2Triple`: a distinguished family of `sl₂` triples contained in
  the Geck construction.

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
* Instance stating `(cartanSubalgebra' b).IsCartanSubalgebra`
  (included in Lemma 4.6 from [Geck](Geck2017)).

-/

lemma Submodule.exists_forall_notMem_of_forall_ne_top
    {ι K M : Type*} [Finite ι] [Field K] [Infinite K] [AddCommGroup M] [Module K M]
    (p : ι → Submodule K M) (h : ∀ i, p i ≠ ⊤) :
    ∃ x, ∀ i, x ∉ p i := by
  -- Following https://mathoverflow.net/a/14241/6801
  suffices ∀ s : Finset ι, ⋃ i ∈ s, (p i : Set M) ≠ ⊤ by
    let _i : Fintype ι := Fintype.ofFinite ι
    simpa [Set.iUnion_eq_univ_iff] using this Finset.univ
  intro s
  classical
  induction s using Finset.induction_on with
  | empty => simp [eq_comm (a := (∅ : Set M))]
  | insert j s hj hj' =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa [← SetLike.coe_ne_coe] using h j
    contrapose! hj'
    suffices (p j : Set M) ⊆ ⋃ i ∈ s, (p i : Set M) by
      simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left, Set.top_eq_univ] at hj'
      rwa [Set.union_eq_right.mpr this] at hj'
    intro x (hx : x ∈ p j)
    rcases eq_or_ne x 0 with rfl | hx₀
    · simpa using hs
    obtain ⟨y, hy⟩ : ∃ y, y ∉ p j := by specialize h j; contrapose! h; ext; simp [h]
    have key : {x + t • y | t : K}.Infinite := by
      let f (t : K) := x + t • y
      have hf : Function.Injective f := by
        intro t₁ t₂ ht
        have hy : y ≠ 0 := by contrapose! hy; simp [hy]
        exact smul_left_injective K hy <| by simpa [f] using ht
      exact (Set.infinite_range_iff hf).mpr inferInstance
    obtain ⟨k, hk, t₁, t₂, ht, ht₁, ht₂⟩ : ∃ᵉ (k ∈ s) (t₁ : K) (t₂ : K),
        t₁ ≠ t₂ ∧ x + t₁ • y ∈ p k ∧ x + t₂ • y ∈ p k := by
      -- PHP
      sorry
    replace ht : y ∈ p k := by
      have : (t₁ - t₂) • y ∈ p k := by convert sub_mem ht₁ ht₂ using 1; module
      refine ((p k).smul_mem_iff ?_).mp this
      rwa [sub_ne_zero]
    replace ht : x ∈ p k := by convert sub_mem ht₁ ((p k).smul_mem t₁ ht); simp
    simpa using ⟨k, hk, ht⟩

lemma exists_foo' {ι K M : Type*} [Finite ι] [Field K] [Infinite K] [AddCommGroup M] [Module K M]
    (f : ι → Module.Dual K M) (h : ∀ i, ∃ x, f i x ≠ 0) :
    ∃ x, ∀ i, f i x ≠ 0 := by
  let p i := LinearMap.ker (f i)
  replace h i : p i ≠ ⊤ := by
    intro contra
    simp only [LinearMap.ker_eq_top, p] at contra
    obtain ⟨x, hx⟩ := h i
    exact hx <| LinearMap.congr_fun contra x
  obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p h
  exact ⟨x, by simpa [p] using hx⟩

open Module Submodule in
lemma exists_foo {ι K M : Type*} [Finite ι] [Field K] [Infinite K] [AddCommGroup M] [Module K M]
    (p : Submodule K M) (f : ι → Dual K M) (h : ∀ i, ∃ x ∈ p, f i x ≠ 0) :
    ∃ x ∈ p, ∀ i, f i x ≠ 0 := by
  let f' (i : ι) : Dual K p := (f i).domRestrict p
  replace h (i : ι) : ∃ x : p, f' i x ≠ 0 := by obtain ⟨x, hxp, hx₀⟩ := h i; exact ⟨⟨x, hxp⟩, hx₀⟩
  obtain ⟨⟨x, hxp⟩, hx₀⟩ := exists_foo' f' h
  exact ⟨x, hxp, hx₀⟩

/-- Evaluation as a linear map.

Surely this already exists!? -/
@[simps] def Pi.evalLinear {ι : Type*} (R : Type*) [Semiring R] (i : ι) : (ι → R) →ₗ[R] R where
  toFun f := f i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable section

open Function Module.End
open Set hiding diagonal
open scoped Matrix

namespace RootPairing.GeckConstruction

section IsDomain

variable {ι R M N : Type*} [Finite ι] [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootSystem ι R M N} [P.IsCrystallographic] {b : P.Base}

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

/-- Geck's construction of the Lie algebra associated to a root system with distinguished base. -/
def lieAlgebra [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) :=
  LieSubalgebra.lieSpan R _ (range e ∪ range f)

/-- A distinguished subalgebra corresponding to a Cartan subalgebra of the Geck construction.

See also `RootPairing.GeckConstruction.cartanSubalgebra'`. -/
def cartanSubalgebra [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (Matrix (b.support ⊕ ι) (b.support ⊕ ι) R) where
  __ := Submodule.span R (range h)
  lie_mem' {x y} hx hy := by
    have aux : (∀ u ∈ range (h (b := b)), ∀ v ∈ range (h (b := b)), ⁅u, v⁆ = 0) := by
      rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩; exact lie_h_h i j
    simp only [Submodule.carrier_eq_coe, SetLike.mem_coe, LieSubalgebra.mem_toSubmodule,
      ← LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_eq_zero (R := R) aux] at hx hy ⊢
    exact LieSubalgebra.lie_mem _ hx hy

/-- A distinguished Cartan subalgebra of the Geck construction. -/
def cartanSubalgebra' [Fintype ι] [DecidableEq ι] :
    LieSubalgebra R (lieAlgebra b) :=
  (cartanSubalgebra b).comap (lieAlgebra b).incl

variable {b}

omit [Finite ι] [IsDomain R] [CharZero R] in
@[simp] lemma h_mem_cartanSubalgebra [Fintype ι] [DecidableEq ι] (i : b.support) :
    h i ∈ cartanSubalgebra b :=
  Submodule.subset_span <| mem_range_self i

@[simp] lemma h_mem_cartanSubalgebra' [Fintype ι] [DecidableEq ι] (i : b.support) (hi) :
    ⟨h i, hi⟩ ∈ cartanSubalgebra' b := by
  simp [cartanSubalgebra']

attribute [local simp] Ring.lie_def Matrix.mul_apply Matrix.one_apply Matrix.diagonal_apply

lemma e_mem_lieAlgebra [Fintype ι] [DecidableEq ι] (i : b.support) :
    e i ∈ lieAlgebra b :=
  LieSubalgebra.subset_lieSpan <| by simp

lemma f_mem_lieAlgebra [Fintype ι] [DecidableEq ι] (i : b.support) :
    f i ∈ lieAlgebra b :=
  LieSubalgebra.subset_lieSpan <| by simp

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

variable (b) in
/-- The conjugation `x ↦ ωxω` as an equivalence of Lie algebras. -/
@[simps] def ωConj [DecidableEq ι] :
    Matrix (b.support ⊕ ι) (b.support ⊕ ι) R ≃ₗ⁅R⁆ Matrix (b.support ⊕ ι) (b.support ⊕ ι) R where
  toFun x := ω b * x * ω b
  map_add' x y := by noncomm_ring
  map_smul' t x := by simp
  map_lie' {x y} := by
    simp only [Ring.lie_def]
    nth_rw 1 [← mul_one x]
    nth_rw 2 [← one_mul x]
    simp only [← ω_mul_ω (b := b)]
    noncomm_ring
  invFun x := ω b * x * ω b
  left_inv x := by
    simp only [← mul_assoc, ω_mul_ω, one_mul]
    simp [mul_assoc]
  right_inv x := by
    simp only [← mul_assoc, ω_mul_ω, one_mul]
    simp [mul_assoc]

lemma ωConj_mem_of_mem [DecidableEq ι]
    {x : Matrix (b.support ⊕ ι) (b.support ⊕ ι) R} (hx : x ∈ lieAlgebra b) :
    ωConj b x ∈ lieAlgebra b := by
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem u hu =>
    apply LieSubalgebra.subset_lieSpan
    obtain (⟨i, rfl⟩ | ⟨i, rfl⟩) : (∃ y, e y = u) ∨ ∃ y, f y = u := by
      simpa only [mem_union, mem_range] using hu
    · exact Or.inr ⟨i, by simp [ω_mul_e, mul_assoc]⟩
    · exact Or.inl ⟨i, by simp [ω_mul_f, mul_assoc]⟩
  | zero => simp
  | add u v _ _ hu hv => simpa [mul_add, add_mul] using add_mem hu hv
  | smul t u _ hu => simpa using SMulMemClass.smul_mem _ hu
  | lie u v _ _ hu hv =>
    rw [LieEquiv.map_lie]
    exact (lieAlgebra b).lie_mem hu hv

lemma e_u [DecidableEq ι] (i j : b.support) :
    letI uj : b.support ⊕ ι → R := Pi.single (Sum.inl j) 1
    letI vi : b.support ⊕ ι → R := Pi.single (Sum.inr i) 1
    ⁅e i, uj⁆ = |b.cartanMatrix i j| • vi := by
  ext (k | k) <;> simp [e, Pi.single_apply]

-- TODO Maybe drop since now need `e_u` above
lemma e_u_same [DecidableEq ι] (i : b.support) :
    letI ui : b.support ⊕ ι → R := Pi.single (Sum.inl i) 1
    letI vi : b.support ⊕ ι → R := Pi.single (Sum.inr i) 1
    ⁅e i, ui⁆ = (2 : R) • vi := by
  ext (j | j) <;> simp [e, Pi.single_apply]

lemma e_v_ne [DecidableEq ι] {i j : ι} {k : b.support} (h : P.root j = P.root k + P.root i) :
    letI vi : b.support ⊕ ι → R := Pi.single (Sum.inr i) 1
    letI vj : b.support ⊕ ι → R := Pi.single (Sum.inr j) 1
    ⁅e k, vi⁆ = (P.chainBotCoeff k i + 1 : R) • vj := by
  letI := P.indexNeg
  ext (l | l)
  · replace h : i ≠ -k := by rintro rfl; exact P.ne_zero j <| by simpa using h
    simp [e, h, -indexNeg_neg]
  · simp [e, ← h, Pi.single_apply]

lemma f_v_same [DecidableEq ι] (i : b.support) :
    letI ui : b.support ⊕ ι → R := Pi.single (Sum.inl i) 1
    letI vi : b.support ⊕ ι → R := Pi.single (Sum.inr i) 1
    ⁅f i, vi⁆ = ui := by
  ext (j | j)
  · simp [f, Pi.single_apply]
  · simp [f, P.ne_zero j]

lemma f_v_ne [DecidableEq ι] {i j : ι} {k : b.support} (h : P.root i = P.root j + P.root k) :
    letI vi : b.support ⊕ ι → R := Pi.single (Sum.inr i) 1
    letI vj : b.support ⊕ ι → R := Pi.single (Sum.inr j) 1
    ⁅f k, vi⁆ = (P.chainTopCoeff k i + 1 : R) • vj := by
  ext (l | l)
  · replace h : i ≠ k := by rintro rfl; exact P.ne_zero j <| by simpa using h
    simp [f, h]
  · simp [f, h, Pi.single_apply]

lemma lie_e_lie_f_apply [DecidableEq ι] :
    letI u (i : b.support) : b.support ⊕ ι → R := Pi.single (Sum.inl i) 1
    ⁅e i, ⁅f i, u j⁆⁆ = |b.cartanMatrix i j| • u i := by
  ext (k | k)
  · rcases eq_or_ne k i with rfl | h
    · simp [e, f, Matrix.mulVec, dotProduct]
    · simp [e, f, Matrix.mulVec, dotProduct, h]
  · simp [e, f, Matrix.mulVec, dotProduct, P.ne_zero]

instance [Fintype ι] [DecidableEq ι] : IsLieAbelian (cartanSubalgebra b) := by
  have aux : cartanSubalgebra b = LieSubalgebra.lieSpan R _ (range h) := by
    refine le_antisymm LieSubalgebra.submodule_span_le_lieSpan ?_
    rw [LieSubalgebra.lieSpan_le, cartanSubalgebra]
    exact Submodule.subset_span
  rw [aux, LieSubalgebra.isLieAbelian_lieSpan_iff]
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  exact lie_h_h i j

instance [Fintype ι] [DecidableEq ι] : IsLieAbelian (cartanSubalgebra' b) := by
  refine ⟨fun ⟨⟨x, hx⟩, hx'⟩ ⟨⟨y, hy⟩, hy'⟩ ↦ ?_⟩
  let x' : cartanSubalgebra b := ⟨x, hx'⟩
  let y' : cartanSubalgebra b := ⟨y, hy'⟩
  suffices ⁅x', y'⁆ = 0 by simpa [x', y', Subtype.ext_iff, -trivial_lie_zero] using this
  simp

open Submodule in
instance [Fintype ι] [DecidableEq ι] :
    LieModule.IsTriangularizable R (cartanSubalgebra' b) (b.support ⊕ ι → R) := by
  refine ⟨fun ⟨⟨x, hx'⟩, hx⟩ ↦ ?_⟩
  simp only [LieSubalgebra.toEnd_mk, LieModule.toEnd_matrix, LieEquiv.coe_coe,
    lieEquivMatrix'_symm_apply]
  suffices ∃ d : b.support ⊕ ι → R, x = Matrix.diagonal d by
    obtain ⟨d, rfl⟩ := this
    exact Matrix.iSup_maxGenEigenspace_diagonal_eq_top
  replace hx : x ∈ span R (range h) := by simpa [cartanSubalgebra', cartanSubalgebra] using hx
  clear hx'
  -- Probably worth breaking out the below as a lemma.
  induction hx using span_induction with
  | mem x h =>
    obtain ⟨i, rfl⟩ := h
    exact ⟨Sum.elim 0 (P.pairingIn ℤ · i), h_eq_diagonal i⟩
  | zero => exact ⟨0, Matrix.diagonal_zero.symm⟩
  | add u v _ _ hu hv =>
    obtain ⟨du, rfl⟩ := hu
    obtain ⟨dv, rfl⟩ := hv
    exact ⟨du + dv, by simp⟩
  | smul t u _ hu =>
    obtain ⟨d, rfl⟩ := hu
    exact ⟨t • d, by simp⟩

/-- Lemma 3.3 (a) from [Geck](Geck2017). -/
lemma lie_h_e :
    ⁅h j, e i⁆ = b.cartanMatrix i j • e i := by
  classical
  ext (k | k) (l | l)
  · simp [h, e]
  · simp only [h, e, Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, add_zero, Finset.sum_const_zero]
    rw [Finset.sum_eq_ite l (by aesop)]
    aesop
  · simp only [h, e]
    aesop
  · simp only [h, e, indexNeg_neg, Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, Matrix.fromBlocks_apply₁₂,
      Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_self, Finset.sum_const_zero,
      Matrix.fromBlocks_apply₂₂, zero_add, ite_mul, zero_mul, Matrix.smul_apply, smul_ite, smul_add,
      zsmul_eq_mul, smul_zero]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_subset (Finset.subset_univ {k, l}) (by aesop)]
    rcases eq_or_ne k l with rfl | hkl; · simp [P.ne_zero i]
    simp only [Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_sub_distrib,
      Finset.mem_singleton, Finset.sum_singleton, Finset.sum_insert, hkl, not_false_eq_true,
      reduceIte, right_eq_add, ite_self, add_zero, zero_add, ite_sub_ite, sub_self,
      Base.cartanMatrix, Base.cartanMatrixIn_def]
    refine ite_congr rfl (fun hkil ↦ ?_) (fun _ ↦ rfl)
    simp only [pairingIn_eq_add_of_root_eq_add hkil, Int.cast_add]
    ring

/-- Lemma 3.3 (b) from [Geck](Geck2017). -/
lemma lie_h_f :
    ⁅h j, f i⁆ = -b.cartanMatrix i j • f i := by
  classical
  suffices ω b * ⁅h j, f i⁆ = ω b * (-b.cartanMatrix i j • f i) by
    replace this := congr_arg (ω b * ·) this
    simpa [← mul_assoc, ω_mul_ω] using this
  calc ω b * ⁅h j, f i⁆ = ω b * (h j * f i - f i * h j) := by rw [Ring.lie_def]
                      _ = - (h j * e i - e i * h j) * ω b := ?_
                      _ = - ⁅h j, e i⁆ * ω b := by rw [Ring.lie_def]
                      _ = - (b.cartanMatrix i j • e i) * ω b := by rw [lie_h_e]
                      _ = ω b * (-b.cartanMatrix i j • f i) := ?_
  · rw [mul_sub, ← mul_assoc, ← mul_assoc, ω_mul_h, ω_mul_f, mul_assoc, mul_assoc, ω_mul_f, ω_mul_h,
      neg_sub, neg_mul, neg_mul, mul_neg, sub_mul, mul_assoc, mul_assoc]
    abel
  · rw [Matrix.mul_smul, ω_mul_f]
    simp [mul_assoc]

variable [P.IsReduced]

/-- An auxiliary lemma en route to `RootPairing.Base.lie_e_f_same`. -/
private lemma lie_e_f_same_aux (k : ι) (hki : k ≠ i) (hki' : k ≠ P.reflectionPerm i i) :
    ⁅e i, f i⁆ (Sum.inr k) (Sum.inr k) = h i (Sum.inr k) (Sum.inr k) := by
  classical
  have h_lin_ind : LinearIndependent R ![P.root i, P.root k] := by
    rw [LinearIndependent.pair_symm_iff, IsReduced.linearIndependent_iff]; aesop
  suffices  (∑ x, if P.root k = P.root i + P.root x then
              (P.chainBotCoeff i x + 1 : R) * (P.chainTopCoeff i k + 1) else 0) -
            (∑ x, if P.root k = P.root x - P.root i then
              (P.chainTopCoeff i x + 1 : R) * (P.chainBotCoeff i k + 1) else 0) =
      P.chainBotCoeff i k - P.chainTopCoeff i k by
    have aux (x : ι) : P.root x = P.root k - P.root i ↔ P.root k = P.root i + P.root x := by
      rw [eq_sub_iff_add_eq', eq_comm]
    have aux' (x : ι) : P.root x = P.root i + P.root k ↔ P.root k = P.root x - P.root i := by
      rw [eq_sub_iff_add_eq', eq_comm]
    simpa [e, f, h, hki, hki', aux, aux', ← ite_and, ← P.chainBotCoeff_sub_chainTopCoeff h_lin_ind]
  rcases exists_or_forall_not (fun x ↦ P.root k = P.root i + P.root x) with ⟨x, hx⟩ | h₁ <;>
  rcases exists_or_forall_not (fun x ↦ P.root k = P.root x - P.root i) with ⟨y, hy⟩ | h₂
  · have h_lin_ind_x : LinearIndependent R ![P.root i, P.root x] := by simpa [hx] using h_lin_ind
    have h_lin_ind_y : LinearIndependent R ![P.root i, P.root y] := by
      rw [← add_eq_of_eq_sub hy, add_comm]; simpa
    have hx' : P.chainBotCoeff i k = P.chainBotCoeff i x + 1 :=
      chainBotCoeff_of_add h_lin_ind_x (add_comm (P.root i) _ ▸ hx)
    have hy' : P.chainTopCoeff i k = P.chainTopCoeff i y + 1 := chainTopCoeff_of_sub h_lin_ind_y hy
    rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _) (by aesop),
      Finset.sum_eq_single_of_mem y (Finset.mem_univ _) (by aesop)]
    simp only [hx, hy.symm, hx', hy', reduceIte, Nat.cast_add]
    ring
  · simp_rw [if_neg (h₂ _), Finset.sum_const_zero, sub_zero]
    replace h₂ : P.chainTopCoeff i k = 0 :=
      P.chainTopCoeff_eq_zero_iff.mpr <| Or.inr fun ⟨x, hx⟩ ↦ h₂ x <| by simp [hx]
    have h_lin_ind_x : LinearIndependent R ![P.root i, P.root x] := by simpa [hx] using h_lin_ind
    have hx' : P.chainBotCoeff i k = P.chainBotCoeff i x + 1 :=
      chainBotCoeff_of_add h_lin_ind_x (add_comm (P.root i) _ ▸ hx)
    simp [hx, hx', h₂]
  · simp_rw [if_neg (h₁ _), Finset.sum_const_zero, zero_sub]
    replace h₁ : P.chainBotCoeff i k = 0 :=
      P.chainBotCoeff_eq_zero_iff.mpr <| Or.inr fun ⟨x, hx⟩ ↦ h₁ x <| by simp [hx]
    have h_lin_ind_y : LinearIndependent R ![P.root i, P.root y] := by
      rw [← add_eq_of_eq_sub hy, add_comm]; simpa
    have hy' : P.chainTopCoeff i k = P.chainTopCoeff i y + 1 := chainTopCoeff_of_sub h_lin_ind_y hy
    simp [hy, hy', h₁]
  · suffices P.chainBotCoeff i k = 0 ∧ P.chainTopCoeff i k = 0 by simp [h₁, h₂, this]
    exact ⟨P.chainBotCoeff_eq_zero_iff.mpr <| Or.inr fun ⟨x, hx⟩ ↦ h₁ x <| by simp [hx],
           P.chainTopCoeff_eq_zero_iff.mpr <| Or.inr fun ⟨x, hx⟩ ↦ h₂ x <| by simp [hx]⟩

/-- Lemma 3.4 from [Geck](Geck2017). -/
lemma lie_e_f_same :
    ⁅e i, f i⁆ = h i := by
  letI _i := P.indexNeg
  have _i : NoZeroSMulDivisors ℤ M := have := P.reflexive_left; .int_of_charZero R M
  classical
  ext (k | k) (l | l)
  · simp [e, f, h]
  · have h₁ (x : ι) : ¬ (P.root x = P.root l - P.root i ∧ k = i ∧ x = -i) := by
      simp only [not_and]
      rintro contra rfl rfl
      simp [P.ne_zero, sub_eq_add_neg] at contra
    have h₂ (x : ι) : ¬ (P.root x = P.root i + P.root l ∧ k = i ∧ x = i) := by
      simp only [not_and]
      rintro contra rfl rfl
      simp [P.ne_zero] at contra
    simp [e, f, h, h₁, h₂, - indexNeg_neg, ← ite_and]
  · simp [e, f, h]
  · rcases eq_or_ne k i with rfl | hki
    · have hx (x : ι) : ¬ (P.root x = P.root i + P.root l ∧ P.root i = P.root x - P.root i) := by
        rintro ⟨-, contra⟩
        refine P.nsmul_notMem_range_root (n := 2) (i := i) ⟨x, ?_⟩
        rwa [eq_sub_iff_add_eq, ← two_smul ℕ, eq_comm] at contra
      simp only [e, f, h, P.ne_zero, P.ne_neg, Ring.lie_def, Fintype.sum_sum_type, Matrix.sub_apply,
        Matrix.mul_apply, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Matrix.fromBlocks_apply₂₂,
        left_eq_add, zero_mul, mul_zero, ite_mul, mul_ite, ← ite_and]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (by aesop)]
      simp [hx, eq_comm]
    rcases eq_or_ne k (-i) with rfl | hki'
    · have hx (x : ι) : ¬ (P.root x = P.root l - P.root i ∧ P.root (-i) = P.root i + P.root x) := by
        rintro ⟨-, contra⟩
        refine P.nsmul_notMem_range_root (n := 2) (i := -i) ⟨x, ?_⟩
        replace contra : P.root x = -(P.root i + P.root i) := by
          simpa [neg_eq_iff_add_eq_zero, ← add_assoc, add_eq_zero_iff_eq_neg'] using contra
        simp [contra, two_smul]
      have aux (x : ι) : ¬ P.root (-i) = P.root x - P.root i := by
        simp [P.ne_zero x, eq_comm]
      simp only [e, f, h, Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.fromBlocks_apply₂₁, Matrix.of_apply, hki, reduceIte, zero_mul, Finset.sum_const_zero,
        Matrix.fromBlocks_apply₂₂, mul_ite, ite_mul, mul_zero, ← ite_and, if_neg (hx _), add_zero,
        aux, zero_sub, Matrix.diagonal_apply]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (by aesop)]
      simp [eq_comm, apply_ite ((- ·) : R → R)]
    rcases eq_or_ne k l with rfl | hkl
    · exact lie_e_f_same_aux i k hki hki'
    · simp_all [h, e, f]

lemma isSl2Triple [DecidableEq ι] :
    IsSl2Triple (h i) (e i) (f i) where
  h_ne_zero := fun contra ↦ by simpa [h] using congr_fun₂ contra (.inr i) (.inr i)
  lie_e_f := by rw [lie_e_f_same]
  lie_h_e_nsmul := by rw [lie_h_e]; simp
  lie_h_f_nsmul := by rw [lie_h_f]; simp

lemma cartanSubalgebra_le_lieAlgebra [DecidableEq ι] :
    cartanSubalgebra b ≤ lieAlgebra b := by
  rw [cartanSubalgebra, lieAlgebra, ← LieSubalgebra.toSubmodule_le_toSubmodule, Submodule.span_le]
  rintro - ⟨i, rfl⟩
  rw [← lie_e_f_same]
  apply LieSubalgebra.lie_mem <;>
  exact LieSubalgebra.subset_lieSpan <| by simp

lemma h_mem_lieAlgebra [DecidableEq ι] (i : b.support) :
    h i ∈ lieAlgebra b := by
  rw [← lie_e_f_same]
  exact LieSubalgebra.lie_mem _ (e_mem_lieAlgebra i) (f_mem_lieAlgebra i)

/-- The element `h i`, as a term of the Cartan subalgebra `cartanSubalgebra' b`. -/
def h' [DecidableEq ι] (i : b.support) : cartanSubalgebra' b :=
  ⟨⟨h i, h_mem_lieAlgebra i⟩, h_mem_cartanSubalgebra' i (h_mem_lieAlgebra i)⟩

open Submodule in
variable (b) in
@[simp]
lemma span_range_h'_eq_top [Nonempty ι] [DecidableEq ι] :
    span R (range h') = (⊤ : Submodule R (cartanSubalgebra' b)) := by
  suffices (span R (range h')).map (cartanSubalgebra' b).subtype = cartanSubalgebra' b by
    conv_rhs at this => rw [← map_subtype_top (cartanSubalgebra' b).toSubmodule]
    exact map_injective_of_injective (injective_subtype _) this
  have h₁ : (cartanSubalgebra' b).subtype '' (range h') = (lieAlgebra b).subtype ⁻¹' (range h) := by
    ext ⟨x, hx⟩
    simp only [cartanSubalgebra', cartanSubalgebra, subtype_apply, mem_image, mem_range,
      Subtype.exists, LieSubalgebra.mem_toSubmodule, LieSubalgebra.mem_comap,
      LieSubalgebra.coe_incl, exists_and_right, exists_eq_right, coe_subtype, mem_preimage]
    refine ⟨fun ⟨hx', i, hi, hi'⟩ ↦ ⟨i, hi, by simpa [h'] using hi'⟩, ?_⟩
    rintro ⟨i, hi, rfl⟩
    exact ⟨subset_span <| mem_range_self _, i, hi, by simp [h']⟩
  have h₂ : range (h (b := b)) ⊆ LinearMap.range (lieAlgebra b).subtype := by
    rintro - ⟨i, rfl⟩; simpa using h_mem_lieAlgebra i
  rw [map_span]
  change span R ((cartanSubalgebra' b).subtype '' _) = _
  obtain ⟨i : b.support⟩ := inferInstanceAs (Nonempty b.support)
  rw [h₁, span_preimage_eq ⟨h i, mem_range_self _⟩ h₂]
  rfl

section lie_e_f_ne

open scoped Matrix

variable {i j}
variable (hij : i ≠ j)
omit [P.IsReduced]

/-- An auxiliary lemma en route to `RootPairing.Base.lie_e_f_ne`. -/
private lemma lie_e_f_ne_aux₀ (k : b.support) (l : ι) :
    ⁅e i, f j⁆ (Sum.inl k) (Sum.inr l) = 0 := by
  classical
  letI := P.indexNeg
  have aux₁ : ∀ x ∈ Finset.univ, ¬ (P.root x = P.root i + P.root l ∧ k = j ∧ x = j) := by
    rintro  x - ⟨hl, -, rfl⟩
    exact b.sub_notMem_range_root i.property j.property ⟨-l, by simp [hl]⟩
  have aux₂ : ∀ x ∈ Finset.univ, ¬ (P.root x = P.root l - P.root j ∧ k = i ∧ x = -i) := by
    rintro  x - ⟨hl, -, rfl⟩
    replace hl : P.root i = P.root j - P.root l := by simpa [neg_eq_iff_eq_neg] using hl
    exact b.sub_notMem_range_root i.property j.property ⟨-l, by simp [hl]⟩
  simp [e, f, -indexNeg_neg, ← ite_and, Finset.sum_ite_of_false aux₁, Finset.sum_ite_of_false aux₂]

include hij

/-- An auxiliary lemma en route to `RootPairing.Base.lie_e_f_ne`. -/
private lemma lie_e_f_ne_aux₁ :
    ⁅e i, f j⁆ᵀ (Sum.inr j) = 0 := by
  letI := P.indexNeg
  classical
  ext (k | k)
  · rw [Matrix.transpose_apply, lie_e_f_ne_aux₀, Pi.zero_apply]
  · suffices ((if k = i then ↑|b.cartanMatrix i j| else (0 : R)) -
        ∑ x, if P.root x = P.root i + P.root j ∧ P.root k = P.root x - P.root j then
          (P.chainTopCoeff j x : R) + 1 else 0) = 0 by
      have hij : (j : ι) ≠ -i := by simpa using b.root_ne_neg_of_ne j.property i.property (by aesop)
      have aux : ∀ x ∈ Finset.univ,
        x ≠ j → (if x = j ∧ k = i then ↑|b.cartanMatrix i x| else 0) = (0 : R) := by aesop
      simpa [e, f, P.ne_zero, hij, -indexNeg_neg, -Finset.univ_eq_attach, ← ite_and,
        Finset.sum_eq_single_of_mem j (Finset.mem_univ _) aux]
    rcases eq_or_ne k i with rfl | hk; swap
    · rw [if_neg (by tauto), Finset.sum_ite_of_false (by aesop)]; simp
    by_cases hij_mem : P.root i + P.root j ∈ range P.root
    · obtain ⟨m, hm⟩ := hij_mem
      rw [Finset.sum_eq_single_of_mem m (Finset.mem_univ _) (by rintro x - hx; simp [← hm, hx]),
        b.abs_cartanMatrix_apply, Base.cartanMatrix, Base.cartanMatrixIn_def]
      have aux₁ := b.chainTopCoeff_eq_of_ne hij.symm
      have aux₂ := chainTopCoeff_of_add (b.linearIndependent_pair_of_ne hij.symm) hm
      norm_cast
      aesop
    · have aux : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root i + P.root j ∧ P.root i = P.root x - P.root j) := by
        rintro x - ⟨hx, -⟩; exact hij_mem ⟨x, hx⟩
      simp [Finset.sum_ite_of_false aux, b.cartanMatrix_apply_eq_zero_iff hij, hij_mem]

/-- An auxiliary lemma en route to `RootPairing.Base.lie_e_f_ne`. -/
private lemma lie_e_f_ne_aux₂ :
    letI := P.indexNeg
    ⁅e i, f j⁆ᵀ (Sum.inr (-i)) = 0 := by
  letI := P.indexNeg
  classical
  ext (k | k)
  · rw [Matrix.transpose_apply, lie_e_f_ne_aux₀, Pi.zero_apply]
  · have aux : ⁅e i, f j⁆ (.inr k) (.inr (-i)) = (⁅e i, f j⁆ * ω b) (.inr k) (.inr i) := by simp [ω]
    rw [Matrix.transpose_apply, aux, lie_e_f_mul_ω, ← (-ω b * ⁅e j, f i⁆).transpose_apply,
      Matrix.transpose_mul, Matrix.mul_apply', lie_e_f_ne_aux₁ hij.symm]
    simp

/-- Lemma 3.5 from [Geck](Geck2017).

Note that the assumption `[P.IsNotG2]` is redundant and can be dropped by addressing:
https://github.com/leanprover-community/mathlib4/blob/6a0a7c723bd4fdc5ca679048efb76eb2bf725b3e/Mathlib/LinearAlgebra/RootSystem/Chain.lean#L551
-/
lemma lie_e_f_ne [P.IsNotG2] :
    ⁅e i, f j⁆ = 0 := by
  letI := P.indexNeg
  classical
  ext (k | k) (l | l)
  · aesop (erase simp indexNeg_neg) (add simp [e, f, Matrix.mul_apply, mul_ite, ite_mul])
  · exact lie_e_f_ne_aux₀ k l
  · have aux₁ : P.root k ≠ P.root i - P.root j :=
      fun contra ↦ b.sub_notMem_range_root i.property j.property ⟨k, contra⟩
    simp [e, f, ← sub_eq_add_neg, if_neg aux₁]
  · /- Geck Case 1 (covered by the auxiliary lemmas above). -/
    rcases eq_or_ne l j with rfl | h₃
    · rw [← ⁅e i, f j⁆.transpose_apply, lie_e_f_ne_aux₁ hij, Pi.zero_apply, Matrix.zero_apply]
    rcases eq_or_ne l (-i) with rfl | h₄
    · rw [← ⁅e i, f j⁆.transpose_apply, lie_e_f_ne_aux₂ hij, Pi.zero_apply, Matrix.zero_apply]
    /- Geck Case 2.
    It's all just definition unfolding and case analysis: the only real content is the external
    lemma `chainBotCoeff_mul_chainTopCoeff`. -/
    suffices
      (∑ x, if P.root x = P.root l - P.root j ∧ P.root k = P.root i + P.root x then
          ((P.chainBotCoeff i x : R) + 1) * (P.chainTopCoeff j l + 1) else 0) =
      (∑ x, if P.root x = P.root i + P.root l ∧ P.root k = P.root x - P.root j then
          ((P.chainTopCoeff j x : R) + 1) * (P.chainBotCoeff i l + 1) else 0) by
      have h₁ : ∀ x ∈ Finset.univ, ¬ ((x = i ∧ l = -i) ∧ k = -j) := by
        rintro - - ⟨⟨-, contra⟩, -⟩; contradiction
      have h₂ : ∀ x ∈ Finset.univ, ¬ ((x = j ∧ l = j) ∧ k = i) := by
        rintro - - ⟨⟨-, contra⟩, -⟩; contradiction
      rw [← sub_eq_zero] at this
      simpa [e, f, ← ite_and, Finset.sum_ite_of_false h₁, Finset.sum_ite_of_false h₂, -indexNeg_neg,
        -Finset.univ_eq_attach]
    by_cases h₅ : P.root l + P.root i - P.root j ∈ range P.root; swap
    · have aux₃ : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root i + P.root l ∧ P.root k = P.root x - P.root j) := by
        rintro x - ⟨hx, hx'⟩; exact h₅ ⟨k, by rw [hx', hx]; abel⟩
      have aux₄ : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root l - P.root j ∧ P.root k = P.root i + P.root x) := by
        rintro x - ⟨hx, hx'⟩; exact h₅ ⟨k, by rw [hx', hx]; abel⟩
      simp [Finset.sum_ite_of_false aux₃, Finset.sum_ite_of_false aux₄]
    by_cases h₆ : P.root l + P.root i ∈ range P.root; swap
    · have h₇ : P.root l - P.root j ∉ range P.root := by
        rwa [b.root_sub_mem_iff_root_add_mem i j l (by aesop) i.property j.property
          (by aesop) (by aesop) h₅]
      have aux₃ : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root i + P.root l ∧ P.root k = P.root x - P.root j) := by
        rintro x - ⟨hx, -⟩; exact h₆ ⟨x, by rw [hx]; abel⟩
      have aux₄ : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root l - P.root j ∧ P.root k = P.root i + P.root x) := by
        rintro x - ⟨hx, hx'⟩; exact h₇ ⟨x, hx⟩
      simp [Finset.sum_ite_of_false aux₃, Finset.sum_ite_of_false aux₄]
    obtain ⟨m, hm : P.root m = P.root l - P.root j⟩ :=
      b.root_sub_root_mem_of_mem_of_mem i j l (by aesop) i.property j.property h₅ h₃ h₆
    obtain ⟨l', hl'⟩ := h₆
    by_cases hk : P.root k = P.root l + P.root i - P.root j; swap
    · have aux₃ : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root l - P.root j ∧ P.root k = P.root i + P.root x) := by
        rintro x - ⟨hx, hx'⟩; exact hk <| by rw [hx', hx]; abel
      have aux₄ : ∀ x ∈ Finset.univ,
          ¬ (P.root x = P.root i + P.root l ∧ P.root k = P.root x - P.root j) := by
        rintro x - ⟨hx, hx'⟩; exact hk <| by rw [hx', hx]; abel
      simp [Finset.sum_ite_of_false aux₃, Finset.sum_ite_of_false aux₄]
    have aux₃ (x) (hx : x ≠ m) :
        ¬ (P.root x = P.root l - P.root j ∧ P.root k = P.root i + P.root x) := by
      contrapose! hx
      rw [← hx.1, EmbeddingLike.apply_eq_iff_eq] at hm
      exact hm.symm
    have aux₄ (x) (hx : x ≠ l') :
        ¬ (P.root x = P.root i + P.root l ∧ P.root k = P.root x - P.root j) := by
      contrapose! hx
      rw [add_comm, ← hx.1, EmbeddingLike.apply_eq_iff_eq] at hl'
      exact hl'.symm
    rw [Finset.sum_eq_single_of_mem m (Finset.mem_univ _) (by rintro x - h; rw [if_neg (aux₃ _ h)]),
      Finset.sum_eq_single_of_mem l' (Finset.mem_univ _) (by rintro x - h; rw [if_neg (aux₄ _ h)]),
      if_pos (⟨hm, by rw [hm, hk]; abel⟩), if_pos ⟨by rw [hl', add_comm], by rw [hl', hk]⟩]
    have := chainBotCoeff_mul_chainTopCoeff i.property j.property (by aesop) hl'.symm hm.symm h₅
    norm_cast

end lie_e_f_ne

section ωConjLieSubmodule

variable [DecidableEq ι] (N : LieSubmodule R (lieAlgebra b) (b.support ⊕ ι → R))
omit [P.IsReduced]

/-- The equivalence `x ↦ ωxω` as an operation on Lie submodules of the Geck construction. -/
private def ωConjLieSubmodule :
    LieSubmodule R (lieAlgebra b) (b.support ⊕ ι → R) where
  __ := N.toSubmodule.comap (ω b).toLin'
  lie_mem A {x} hx := by
    let A' : lieAlgebra b := ⟨ωConj b _, ωConj_mem_of_mem A.property⟩
    suffices ⁅A', ω b *ᵥ x⁆ ∈ N by simpa [A', mul_assoc] using this
    exact LieSubmodule.lie_mem _ hx

@[simp] private lemma mem_ωConjLieSubmodule_iff {x : b.support ⊕ ι → R} :
    x ∈ ωConjLieSubmodule N ↔ (ω b) *ᵥ x ∈ N :=
  Iff.rfl

@[simp] private lemma ωConjLieSubmodule_eq_top_iff : ωConjLieSubmodule N = ⊤ ↔ N = ⊤ := by
  rw [← LieSubmodule.toSubmodule_eq_top]
  let e : Submodule R (b.support ⊕ ι → R) ≃o Submodule R (b.support ⊕ ι → R) :=
    Submodule.orderIsoMapComapOfBijective (ω b).toLin' (Involutive.bijective fun x ↦ by simp)
  change e.symm N = ⊤ ↔ _
  simp

end ωConjLieSubmodule

omit [Finite ι] [IsDomain R] [CharZero R] [Fintype ι] [P.IsReduced] in
open Matrix Submodule in
@[simp] lemma diagonal_elim_mem_span_h_iff [DecidableEq ι] [Fintype ι] {d : ι → R} :
    diagonal (Sum.elim 0 d) ∈ span R (range <| h (b := b)) ↔
      d ∈ span R (range <| fun (i : b.support) j ↦ (P.pairingIn ℤ j i : R)) := by
  let f : Matrix ι ι R →ₗ[R] Matrix (b.support ⊕ ι) (b.support ⊕ ι) R :=
    { toFun := .fromBlocks 0 0 0
      map_add' x y := by ext (i | i) (j | j) <;> simp
      map_smul' t x := by ext (i | i) (j | j) <;> simp }
  have h₀ : Injective (f ∘ diagonalLinearMap ι R R) := fun _ _ hd ↦ funext <| by simpa [f] using hd
  have h₁ {d : ι → R} : diagonal (Sum.elim 0 d) = f (diagonalLinearMap ι R R d) := by
    ext (i | i) (j | j) <;> simp [f]
  have h₂ : range h = f '' (diagonalLinearMap ι R R ''
    (range <| fun (i : b.support) j ↦ (P.pairingIn ℤ j i : R))) := by ext; simp [f, h_def]
  simp_rw [h₁, h₂, span_image, ← Submodule.map_comp, ← Function.comp_apply (f := f), mem_map,
    LinearMap.coe_comp, h₀.eq_iff, exists_eq_right]

end IsDomain

section Field

variable {ι K M N : Type*}
  [DecidableEq ι] [Fintype ι]
  [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootSystem ι K M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base}

omit [P.IsReduced] in
variable (b) in
lemma injective_pairingIn_of_mem_support :
    Injective (fun i (k : b.support) ↦ P.pairingIn ℤ i k) := by
  intro i j hij
  replace hij : ∀ k ∈ b.support, P.pairingIn ℤ i k = P.pairingIn ℤ j k :=
    fun k hk ↦ congr_fun hij ⟨k, hk⟩
  obtain ⟨f, hf₁, -, hf₂⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, hg₁, -, hg₂⟩ := b.exists_root_eq_sum_int j
  let f' : b.support → ℤ := f ∘ (↑)
  let g' : b.support → ℤ := g ∘ (↑)
  suffices f' = g' by
    rw [← P.root.apply_eq_iff_eq, hf₂, hg₂]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    replace this : f k = g k := congr_fun this ⟨k, hk⟩
    rw [this]
  replace hf₂ (k : ι) : P.pairingIn ℤ i k = ∑ l ∈ b.support, f l * P.pairingIn ℤ l k := by
    apply FaithfulSMul.algebraMap_injective ℤ K
    simp only [algebraMap_pairingIn, map_sum, map_mul, ← P.root_coroot'_eq_pairing, hf₂]
    simp
  replace hf₂ : (fun k : b.support ↦ P.pairingIn ℤ i k) = f' ᵥ* b.cartanMatrix := by
    ext ⟨k, hk⟩
    simp only [f', hf₂, Base.cartanMatrix, Base.cartanMatrixIn, Matrix.vecMul_eq_sum, comp_apply,
      zsmul_eq_mul, Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply, Int.cast_eq, Matrix.of_apply,
      b.support.sum_subtype (fun x ↦ Iff.rfl)]
  replace hg₂ (k : ι) : P.pairingIn ℤ j k = ∑ l ∈ b.support, g l * P.pairingIn ℤ l k := by
    apply FaithfulSMul.algebraMap_injective ℤ K
    simp only [algebraMap_pairingIn, map_sum, map_mul, ← P.root_coroot'_eq_pairing, hg₂]
    simp
  replace hg₂ : (fun k : b.support ↦ P.pairingIn ℤ j k) = g' ᵥ* b.cartanMatrix := by
    ext ⟨k, hk⟩
    simp only [g', hg₂, Base.cartanMatrix, Base.cartanMatrixIn, Matrix.vecMul_eq_sum, comp_apply,
      zsmul_eq_mul, Finset.sum_apply, Pi.mul_apply, Pi.intCast_apply, Int.cast_eq, Matrix.of_apply,
      b.support.sum_subtype (fun x ↦ Iff.rfl)]
  replace hij :
      (fun k : b.support ↦ P.pairingIn ℤ i k) = (fun k : b.support ↦ P.pairingIn ℤ j k) := by
    ext ⟨k, hk⟩
    simpa using hij k hk
  rw [hij, hg₂] at hf₂
  have key : LinearIndependent ℤ b.cartanMatrix.row := by
    apply Matrix.linearIndependent_rows_of_det_ne_zero
    rw [← Matrix.nondegenerate_iff_det_ne_zero]
    exact b.cartanMatrix_nondegenerate
  rw [← Matrix.vecMul_injective_iff] at key
  exact (key hf₂).symm

omit [P.IsReduced] in
open Module Submodule in
lemma exists_distinct_blah :
    ∃ d : ι → K, (∀ i, d i ≠ 0) ∧ Pairwise ((· ≠ ·) on d) ∧
      d ∈ span K (range fun (i : b.support) j ↦ (P.pairingIn ℤ j i : K)) := by
  rcases isEmpty_or_nonempty ι; · simpa using ⟨0, Submodule.zero_mem _⟩
  set p := span K (range fun (i : b.support) j ↦ (P.pairingIn ℤ j i : K))
  let f : ι ⊕ {(i, j) : ι × ι | i ≠ j} → Dual K (ι → K) :=
    Sum.elim (Pi.evalLinear K) (fun ij ↦ Pi.evalLinear K ij.1.1 - Pi.evalLinear K ij.1.2)
  suffices ∃ d ∈ p, ∀ i, f i d ≠ 0 by
    obtain ⟨d, hp, hf⟩ := this
    refine ⟨d, fun i ↦ hf (Sum.inl i), fun i j h ↦ ?_, hp⟩
    simpa [f, sub_eq_zero] using hf (Sum.inr ⟨⟨i, j⟩, h⟩)
  apply exists_foo p f
  rintro (i | ⟨⟨i, j⟩, h : i ≠ j⟩)
  · obtain ⟨j, hj, hj₀⟩ := b.exists_mem_support_pos_pairingIn_ne_zero i
    refine ⟨fun i ↦ P.pairingIn ℤ i j, subset_span ⟨⟨j, hj⟩, rfl⟩, ?_⟩
    rw [ne_eq, P.pairingIn_eq_zero_iff] at hj₀
    simpa [f, ne_eq, Int.cast_eq_zero]
  · obtain ⟨k, hk, hk'⟩ : ∃ k ∈ b.support, P.pairingIn ℤ i k ≠ P.pairingIn ℤ j k := by
      contrapose! h
      apply injective_pairingIn_of_mem_support b
      ext ⟨k, hk⟩
      exact h k hk
    simpa [f, p, sub_eq_zero] using
      ⟨fun i ↦ P.pairingIn ℤ i k, subset_span ⟨⟨k, hk⟩, rfl⟩, by simpa⟩

open LieModule Matrix Submodule in
lemma bar {χ : cartanSubalgebra' b → K} (hχ : χ ≠ 0) {w : b.support ⊕ ι → K} (hw₀ : w ≠ 0)
    (hw : w ∈ genWeightSpace (b.support ⊕ ι → K) χ) :
    ∃ (i : ι) (t : K), t • w = Pi.single (Sum.inr i) 1 := by
  cases isEmpty_or_nonempty ι; · (suffices w = 0 by contradiction); apply Subsingleton.elim
  have aux (d : b.support ⊕ ι → K) (μ : K) :
      (diagonal d).toLin' - μ • 1 = (diagonal (d - μ • 1)).toLin' := by
    aesop (add simp Pi.single_apply)
  replace aux (d : b.support ⊕ ι → K) (x : cartanSubalgebra' b) (hdx : x = diagonal d) :
      w ∈ genWeightSpaceOf (b.support ⊕ ι → K) (χ x) x ↔
        ∃ k, diagonal ((d - χ x • 1) ^ k) *ᵥ w = 0 := by
    set μ := χ x
    obtain ⟨⟨x, hx⟩, hx'⟩ := x
    replace hdx : x = diagonal d := by simpa using hdx
    simp [mem_genWeightSpaceOf, hdx, aux, ← toLin'_pow, diagonal_pow]
  obtain ⟨i, hi⟩ : ∃ i, w (Sum.inr i) ≠ 0 := by
    obtain ⟨l, hl⟩ : ∃ l, χ (h' l) ≠ 0 := by
      replace hw₀ : genWeightSpace (b.support ⊕ ι → K) χ ≠ ⊥ := by
        contrapose! hw₀; rw [LieSubmodule.eq_bot_iff] at hw₀; exact hw₀ _ hw
      let χ' : cartanSubalgebra' b →ₗ[K] K := (Weight.mk χ hw₀).toLinear
      replace hχ : χ' ≠ 0 := by contrapose! hχ; ext x; simpa using LinearMap.congr_fun hχ x
      contrapose! hχ
      apply LinearMap.ext_on (span_range_h'_eq_top b)
      rintro - ⟨l, rfl⟩
      simp [χ', hχ l]
    contrapose! hw₀
    suffices ∀ i : b.support, w (Sum.inl i) = 0 by aesop
    intro i
    replace hw := genWeightSpace_le_genWeightSpaceOf (b.support ⊕ ι → K) (h' l) χ hw
    rw [aux (Sum.elim 0 (P.pairingIn ℤ · l)) (h' l) (h_eq_diagonal l)] at hw
    obtain ⟨k, hk⟩ := hw
    replace hk := congr_fun hk (Sum.inl i)
    simpa [Matrix.mulVec_eq_sum, Matrix.diagonal_apply, hl] using hk
  refine ⟨i, (w (Sum.inr i))⁻¹, ?_⟩
  suffices ∃ d : ι → K, (∀ i, d i ≠ 0) ∧ Pairwise ((· ≠ ·) on d) ∧
      diagonal (Sum.elim 0 d) ∈ cartanSubalgebra b by
    obtain ⟨d, hd₀, hd₁, hd₂⟩ := this
    let x : cartanSubalgebra' b :=
      ⟨⟨diagonal (Sum.elim 0 d), cartanSubalgebra_le_lieAlgebra hd₂⟩, hd₂⟩
    replace hw := genWeightSpace_le_genWeightSpaceOf (b.support ⊕ ι → K) x χ hw
    rw [aux (Sum.elim 0 d) x rfl] at hw
    obtain ⟨k, hk⟩ := hw
    obtain ⟨hχx, hk₀⟩ : d i = χ x ∧ k ≠ 0 := by
      simpa [hi, Matrix.mulVec_eq_sum, Matrix.diagonal_apply, sub_eq_zero] using
        congr_fun hk (Sum.inr i)
    ext (j | j)
    · have : χ x ≠ 0 := hχx ▸ hd₀ i
      simpa [hi, Matrix.mulVec_eq_sum, Matrix.diagonal_apply, hk₀, this] using
        congr_fun hk (Sum.inl j)
    · rcases eq_or_ne i j with rfl | hij
      · simp [hi]
      · suffices w (Sum.inr j) = 0 by simpa [hij, hi]
        suffices d j ≠ χ x by
          simpa [Matrix.mulVec_eq_sum, Matrix.diagonal_apply, sub_eq_zero, this] using
            congr_fun hk (Sum.inr j)
        rw [← hχx]
        exact hd₁ <| by simp [hij.symm]
  simp_rw [cartanSubalgebra, LieSubalgebra.mem_mk_iff', diagonal_elim_mem_span_h_iff]
  exact exists_distinct_blah

open LieModule Submodule in
lemma baz :
    letI u (i : b.support) : b.support ⊕ ι → K := Pi.single (Sum.inl i) 1
    genWeightSpace (b.support ⊕ ι → K) (0 : cartanSubalgebra' b → K) = span K (range u) := by
  let u (i : b.support) : b.support ⊕ ι → K := Pi.single (Sum.inl i) 1
  apply le_antisymm
  · intro w hw
    replace hw : ∀ (x) (hx : x ∈ lieAlgebra b), ⟨x, hx⟩ ∈ cartanSubalgebra' b →
        ∃ k, (x.toLin' ^ k) w = 0 := by simpa [mem_genWeightSpace] using hw
    rw [Pi.mem_span_range_single_inl_iff]
    intro i
    obtain ⟨j, hj⟩ : ∃ j : b.support, P.pairingIn ℤ i j ≠ 0 := by
      obtain ⟨j, hj, hj₀⟩ := b.exists_mem_support_pos_pairingIn_ne_zero i
      rw [ne_eq, P.pairingIn_eq_zero_iff] at hj₀
      exact ⟨⟨j, hj⟩, hj₀⟩
    obtain ⟨k, hk⟩ := hw (h j) (h_mem_lieAlgebra j) (h_mem_cartanSubalgebra' j _)
    simpa [h_eq_diagonal, ← Matrix.toLin'_pow, Matrix.fromBlocks_pow, Matrix.diagonal_pow,
      Matrix.mulVec_eq_sum, Matrix.diagonal_apply, hj] using congr_fun hk (Sum.inr i)
  · rw [span_le]
    rintro - ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LieSubmodule.mem_toSubmodule, LieModule.mem_genWeightSpace]
    intro ⟨⟨x, hx'⟩, hx⟩
    use 1
    ext j
    suffices x j (Sum.inl i) = 0 by simpa
    replace hx : x ∈ span K (range h) := by simpa [cartanSubalgebra] using hx
    clear hx'
    induction hx using span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; cases j <;> simp [h]
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul t u _ hu => simp [hu]

/-- An auxiliary lemma en route to `RootPairing.GeckConstruction.instIsIrreducible` (where the same
conclusion is proved with the hypothesis `hi` weakened to just `U ≠ ⊥`). -/
private lemma instIsIrreducible_aux₀ [P.IsIrreducible]
    {U : LieSubmodule K (lieAlgebra b) (b.support ⊕ ι → K)} {i : ι}
    (hi : Pi.single (Sum.inr i) 1 ∈ U) :
    U = ⊤ := by
  letI _i := P.indexNeg
  let u (i : b.support) : b.support ⊕ ι → K := Pi.single (Sum.inl i) 1
  let v (i : ι) : b.support ⊕ ι → K := Pi.single (Sum.inr i) 1
  have hωu (i : b.support) : ω b *ᵥ (u i) = u i := by
    ext (j | j) <;> simp [ω, u, Pi.single_apply, Matrix.one_apply]
  have hωv (i : ι) : ω b *ᵥ (v i) = v (-i) := by ext (j | j) <;> simp [ω, v, Pi.single_apply]
  change v i ∈ U at hi
  obtain ⟨j, hj⟩ : ∃ j : b.support, u j ∈ U := by
    revert U
    apply b.induction_add i
    · intro i h U hi
      replace hi : v i ∈ ωConjLieSubmodule U := by simpa [hωv]
      obtain ⟨j, hj⟩ := h hi
      exact ⟨j, by simpa [hωu] using hj⟩
    · intro j hj U hj'
      let f' : lieAlgebra b := ⟨f ⟨j, hj⟩, f_mem_lieAlgebra _⟩
      have : ⁅f', v j⁆ = u ⟨j, hj⟩ := f_v_same ⟨j, hj⟩
      replace this : u ⟨j, hj⟩ ∈ U := by
        rw [← this]
        exact U.lie_mem (x := f') hj'
      exact ⟨⟨j, hj⟩, this⟩
    · intro j k l h₁ h₂ hk U hl
      have : ⁅f ⟨k, hk⟩, v l⁆ = (P.chainTopCoeff k l + 1 : K) • v j := f_v_ne h₁
      replace this : (P.chainTopCoeff k l + 1 : K) • v j ∈ U := by
        rw [← this]
        let f' : lieAlgebra b := ⟨f ⟨k, hk⟩, f_mem_lieAlgebra _⟩
        change ⁅f', v l⁆ ∈ U
        exact U.lie_mem hl
      exact h₂ <| (U.smul_mem_iff (by norm_cast)).mp this
  have aux (k : b.support) : u k ∈ U := by
    refine b.induction_on_cartanMatrix (fun k : b.support ↦ u k ∈ U) hj (fun l l' hl₁ hl₂ ↦ ?_)
    suffices (↑|b.cartanMatrix l' l| : K) • u l' ∈ U from (U.smul_mem_iff (by simpa)).mp this
    rw [Int.cast_smul_eq_zsmul, ← lie_e_lie_f_apply l' l]
    let e' : lieAlgebra b := ⟨e l', e_mem_lieAlgebra l'⟩
    let f' : lieAlgebra b := ⟨f l', f_mem_lieAlgebra l'⟩
    change ⁅e', ⁅f', u l⁆⁆ ∈ U
    exact U.lie_mem <| U.lie_mem hl₁
  clear! j i
  suffices ∀ j, v j ∈ U by
    simp_rw [← LieSubmodule.toSubmodule_eq_top, eq_top_iff,
      ← (Pi.basisFun K (b.support ⊕ ι)).span_eq, Submodule.span_le, range_subset_iff,
      Pi.basisFun_apply]
    aesop
  intro j
  revert U
  apply b.induction_add j
  · intro j h U hU
    suffices v j ∈ ωConjLieSubmodule U by simpa [hωv] using this
    exact h fun k ↦ by simp [hωu, hU]
  · intro k hk U aux
    have : ⁅e ⟨k, hk⟩, u ⟨k, hk⟩⁆ = (2 : K) • v k := e_u_same ⟨k, hk⟩
    let e' : lieAlgebra b := ⟨e ⟨k, hk⟩, e_mem_lieAlgebra ⟨k, hk⟩⟩
    change ⁅e', u ⟨k, hk⟩⁆ = _ at this
    replace aux := U.lie_mem (x := e') <| aux ⟨k, hk⟩
    rw [this] at aux
    exact (U.smul_mem_iff two_ne_zero).mp aux
  · intro k l m hm hk hl U aux
    rw [add_comm] at hm
    let e' : lieAlgebra b := ⟨e ⟨l, hl⟩, e_mem_lieAlgebra _⟩
    have : ⁅e', v k⁆ = (P.chainBotCoeff l k + 1 : K) • v m := e_v_ne hm
    replace this : (P.chainBotCoeff l k + 1 : K) • v m ∈ U := by
      rw [← this]
      exact U.lie_mem (hk aux)
    exact (U.smul_mem_iff (by norm_cast)).mp this

set_option maxHeartbeats 500000 in -- Temporary
open LieModule Submodule in
lemma bar' (U : LieSubmodule K (cartanSubalgebra' b) (b.support ⊕ ι → K))
    (hU : ¬ U ≤ genWeightSpace (b.support ⊕ ι → K) 0) :
    ∃ i, Pi.single (Sum.inr i) 1 ∈ U := by
  let v (i : ι) : b.support ⊕ ι → K := Pi.single (Sum.inr i) 1
  let H := cartanSubalgebra' b
  have key (χ : H → K) (hχ : χ ≠ 0) (hχ' : LieModule.genWeightSpace U χ ≠ ⊥) :
      ∃ i, v i ∈ (LieModule.genWeightSpace U χ).map U.incl := by
    obtain ⟨w, hw, hw₀⟩ : ∃ w ∈ LieModule.genWeightSpace U χ, w ≠ 0 := by
      simpa only [ne_eq, LieSubmodule.eq_bot_iff, not_forall, exists_prop] using hχ'
    replace hw : U.incl w ∈ LieModule.genWeightSpace (b.support ⊕ ι → K) χ :=
      LieModule.map_genWeightSpace_le (f := U.incl) <| by simpa
    obtain ⟨i, t, hi : t • w = v i⟩ := bar hχ (by simpa) hw
    use i
    rw [LieModule.map_genWeightSpace_eq_of_injective U.injective_incl, LieSubmodule.range_incl,
      ← hi, LieSubmodule.mem_inf]
    exact ⟨SMulMemClass.smul_mem _ hw, SMulMemClass.smul_mem _ w.property⟩
  obtain ⟨x, hx⟩ : ∃ x : U, x ∉ LieModule.genWeightSpace U (0 : H → K) := by
    contrapose! hU
    refine le_trans ?_ <| LieModule.map_genWeightSpace_le (f := U.incl)
    exact fun x hx ↦ by simpa [hx] using hU ⟨x, hx⟩
  suffices ∃ᵉ (χ : H → K) (i : ι), v i ∈ (LieModule.genWeightSpace U χ).map U.incl by
    obtain ⟨χ, i, hi⟩ := this
    exact ⟨i, LieSubmodule.map_incl_le hi⟩
  suffices ∃ χ : H → K, χ ≠ 0 ∧ LieModule.genWeightSpace U χ ≠ ⊥ by
    obtain ⟨χ, hχ₀, hχ⟩ := this
    exact ⟨χ, key χ hχ₀ hχ⟩
  contrapose! hx
  -- TODO Pretty gross from here: does the broader API need some love or is this PEBKAC?
  have aux := iSup_split (LieModule.genWeightSpace U) fun χ : H → K ↦ χ = 0
  rw [biSup_congr hx] at aux
  change _ = _ ⊔ (⨆ χ ∈ {χ : H → K | χ ≠ 0}, ⊥) at aux
  rw [biSup_const ⟨1, by simp⟩, sup_bot_eq] at aux
  change _ = ⨆ χ ∈ {χ : H → K | χ = 0}, _ at aux
  simp_rw [setOf_eq_eq_singleton, iSup_singleton] at aux
  rw [← aux, LieModule.iSup_genWeightSpace_eq_top K H U]
  simp

open LieModule Submodule in
lemma foo (hCM : (4 - b.cartanMatrix).det ≠ 0)
    [Nonempty ι]
    (U : LieSubmodule K (lieAlgebra b) (b.support ⊕ ι → K)) (hU : U ≠ ⊥) :
    ∃ i, Pi.single (Sum.inr i) 1 ∈ U := by
  let u (i : b.support) : b.support ⊕ ι → K := Pi.single (Sum.inl i) 1
  let v (i : ι) : b.support ⊕ ι → K := Pi.single (Sum.inr i) 1
  let H := cartanSubalgebra' b
  let U' : LieSubmodule K H (b.support ⊕ ι → K) := {U with lie_mem := U.lie_mem}
  have hU' : U'.toSubmodule = U.toSubmodule := rfl
  apply bar' U'
  contrapose! hU
  replace hU : U ≤ span K (range u) := by
    rwa [← baz, ← hU', LieSubmodule.toSubmodule_le_toSubmodule]
  refine (LieSubmodule.eq_bot_iff _).mpr fun x hx ↦ ?_
  obtain ⟨c, hc⟩ : ∃ c : b.support → K, ∑ i, c i • u i = x :=
    (mem_span_range_iff_exists_fun K).mp <| hU hx
  suffices c = 0 by simp [this, ← hc]
  contrapose! hCM
  suffices ((Int.castRingHom K).mapMatrix (4 - b.cartanMatrix)).det = 0 by
    simpa only [← RingHom.map_det, eq_intCast, Int.cast_eq_zero] using this
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨c, hCM, ?_⟩
  simp only [RingHom.mapMatrix_apply]
  suffices (b.cartanMatrix.map abs).map (↑) *ᵥ c = 0 by simpa using this
  ext j
  simp only [Matrix.mulVec_eq_sum, op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply,
    Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul, Pi.zero_apply]
  have key : ⁅e j, x⁆ ∈ U := U.lie_mem (x := ⟨e j, e_mem_lieAlgebra j⟩) hx
  have aux (k : b.support) : ⁅e j, u k⁆ = |b.cartanMatrix j k| • v j := e_u j k
  simp_rw [← hc, lie_sum, lie_smul, aux, smul_comm (M := K), ← smul_assoc, ← Finset.sum_smul,
    zsmul_eq_mul, mul_comm] at key
  suffices v j ∉ U by
    by_contra contra
    rw [← LieSubmodule.mem_toSubmodule, U.smul_mem_iff contra] at key
    contradiction
  intro contra
  suffices ∀ {x : b.support ⊕ ι → K} (hx : x ∈ span K (range u)), x (Sum.inr j) = 0 by
    simpa [v] using this (hU contra)
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; simp [u]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]

/-- Lemma 4.2 from [Geck](Geck2017).

TODO Drop the redundant assumption about the Cartan matrix not having eigenvalue 4 by proving
elsewhere that this is always true. -/
instance instIsIrreducible [P.IsIrreducible] [Nonempty ι] (hCM : (4 - b.cartanMatrix).det ≠ 0) :
    LieModule.IsIrreducible K (lieAlgebra b) (b.support ⊕ ι → K) := by
  refine LieModule.IsIrreducible.mk fun U hU ↦ ?_
  let v (i : ι) : b.support ⊕ ι → K := Pi.single (Sum.inr i) 1
  set H := cartanSubalgebra' b
  suffices ∃ i, v i ∈ U by obtain ⟨i, hi⟩ := this; exact instIsIrreducible_aux₀ hi
  exact foo hCM U hU

end Field

end RootPairing.GeckConstruction
