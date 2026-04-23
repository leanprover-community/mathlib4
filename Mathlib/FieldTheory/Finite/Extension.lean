/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Kevin Buzzard
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Init
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Extensions of finite fields

In this file we develop the theory of extensions of finite fields.

If `k` is a finite field (of cardinality `q = p ^ m`), then there is a unique (up to in general
non-unique isomorphism) extension `l` of `k` of any given degree `n > 0`.

This extension is Galois with cyclic Galois group of degree `n`, and the (arithmetic) Frobenius map
`x ↦ x ^ q` is a generator.


## Main definition

* `FiniteField.Extension k p n` is a non-canonically chosen extension of `k` of degree `n`
  (for `n > 0`).

## Main Results

* `FiniteField.algEquivExtension`: any other field extension `l/k` of degree `n` is (non-uniquely)
  isomorphic to our chosen `FiniteField.Extension k p n`.

-/

@[expose] public section

noncomputable section

variable (k : Type*) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable (n : ℕ) [NeZero n]

open Polynomial

namespace FiniteField

/-- Given a finite field `k` of characteristic `p`, we have a non-canonically chosen extension
of any given degree `n > 0`. -/
def Extension : Type :=
  letI := ZMod.algebra k p
  GaloisField p (Module.finrank (ZMod p) k * n)
  deriving Field, Finite, Algebra (ZMod p), FiniteDimensional (ZMod p)

theorem finrank_zmod_extension [Algebra (ZMod p) k] :
    Module.finrank (ZMod p) (Extension k p n) = Module.finrank (ZMod p) k * n := by
  letI := ZMod.algebra k p
  unfold Extension
  convert GaloisField.finrank p (n := Module.finrank (ZMod p) k * n) <|
    mul_ne_zero Module.finrank_pos.ne' <| NeZero.ne n
  subsingleton

theorem nonempty_algHom_extension [Algebra (ZMod p) k] :
    Nonempty (k →ₐ[ZMod p] Extension k p n) :=
  nonempty_algHom_of_finrank_dvd (finrank_zmod_extension k p n ▸ dvd_mul_right _ _)

noncomputable instance : Algebra k (Extension k p n) :=
  letI := ZMod.algebra k p
  (nonempty_algHom_extension k p n).some.toAlgebra

instance : Module.Finite k (Extension k p n) :=
  .of_finite

instance [Algebra (ZMod p) k] : IsScalarTower (ZMod p) k (Extension k p n) :=
  -- there is at most one map from `𝔽_p` to any ring
  .of_algebraMap_eq' <| Subsingleton.elim _ _

theorem natCard_extension : Nat.card (Extension k p n) = Nat.card k ^ n := by
  letI := ZMod.algebra k p
  rw [← pow_finrank_eq_natCard p, ← pow_finrank_eq_natCard p, finrank_zmod_extension, pow_mul]

theorem finrank_extension : Module.finrank k (Extension k p n) = n := by
  refine Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card k) ?_
  simp only [← Module.natCard_eq_pow_finrank, natCard_extension]

instance : IsSplittingField k (Extension k p n) (X ^ Nat.card k ^ n - X) := by
  have := Fintype.ofFinite (Extension k p n)
  convert FiniteField.isSplittingField_sub (Extension k p n) k
  · rw [Fintype.card_eq_nat_card, natCard_extension]

example : IsGalois k (Extension k p n) :=
  inferInstance

example : IsCyclic Gal(Extension k p n / k) :=
  inferInstance

theorem natCard_algEquiv_extension : Nat.card Gal(Extension k p n / k) = n :=
  (IsGalois.card_aut_eq_finrank _ _).trans <| finrank_extension k p n

theorem card_algEquiv_extension : Fintype.card Gal(Extension k p n / k) = n :=
  Fintype.card_eq_nat_card.trans <| natCard_algEquiv_extension k p n

/-- The Frobenius automorphism `x ↦ x ^ Nat.card k` that fixes `k`. -/
noncomputable def Extension.frob :
    Gal(Extension k p n / k) :=
  haveI := Fintype.ofFinite k
  FiniteField.frobeniusAlgEquivOfAlgebraic _ _

@[simp] lemma Extension.frob_apply {x : Extension k p n} :
    frob k p n x = x ^ Nat.card k := by
  simp [frob, ← Nat.card_eq_fintype_card]

@[simp]
theorem Extension.frob_iterate_apply (i : ℕ) {x : Extension k p n} :
    (frob k p n ^ i) x = x ^ (Nat.card k ^ i) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
      rw [pow_add, pow_one, AlgEquiv.mul_apply, ih, frob_apply, ← pow_mul, ← Nat.pow_add_one']

theorem Extension.exists_frob_pow_eq (g : Gal(Extension k p n/k)) :
    ∃ i < n, Extension.frob k p n ^ i = g := by
  let := Fintype.ofFinite k
  obtain ⟨⟨i, hi⟩, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k
    (Extension k p n)).2 g
  refine ⟨i, ?_, by ext; simp [frob]⟩
  rwa [finrank_extension] at hi

/-- Given any field extension of finite fields `l/k` of degree `n`, we have a non-unique
isomorphism between `l` and our chosen `Extension k p n`. -/
noncomputable def algEquivExtension (l : Type*) [Field l] [Algebra k l]
    (h : Module.finrank k l = n) : l ≃ₐ[k] Extension k p n := by
  refine Nonempty.some ?_
  have : Module.Finite k l := Module.finite_of_finrank_pos <| h ▸ NeZero.pos n
  have : Finite l := Module.finite_of_finite k
  have : Fintype l := .ofFinite _
  have : IsSplittingField k l (X ^ Nat.card k ^ n - X) := by
    rw [← h, ← Module.natCard_eq_pow_finrank, ← Fintype.card_eq_nat_card]
    exact FiniteField.isSplittingField_sub l k
  refine ⟨(IsSplittingField.algEquiv _ (X ^ (Nat.card k ^ n) - X)).trans ?_⟩
  exact (IsSplittingField.algEquiv _ (X ^ (Nat.card k ^ n) - X)).symm

include p in
theorem exists_forall_apply_eq_pow (l : Type*) [Field l] [Algebra k l] [Finite l] (g : Gal(l/k)) :
    ∃ i, ∀ x, g x = x ^ (Nat.card k ^ i) := by
  let n := Module.finrank k l
  have : NeZero n := NeZero.of_pos Module.finrank_pos
  obtain ⟨i, _, hi⟩ := Extension.exists_frob_pow_eq k p n <|
    (algEquivExtension k p n l rfl).symm.trans (g.trans (algEquivExtension k p n l rfl))
  refine ⟨i, fun x ↦ ?_⟩
  simpa using (AlgEquiv.congr_arg (f := (algEquivExtension k p n l rfl).symm) <|
    AlgEquiv.congr_fun hi (algEquivExtension k p n l rfl x)).symm

end FiniteField

section Polynomial

open FiniteField Polynomial

variable {K : Type*} [Field K]

theorem Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X {n : ℕ} {f : K[X]}
    (hi : Irreducible f) (h : f ∣ X ^ (Nat.card K) ^ n - X) : f.natDegree ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  cases finite_or_infinite K; swap
  · rw [Nat.card_eq_zero_of_infinite, zero_pow hn, pow_zero, ← dvd_neg, neg_sub] at h
    rw [((Splits.X_sub_C 1).of_dvd (X_sub_C_ne_zero 1) h).natDegree_eq_one_of_irreducible hi]
    exact one_dvd n
  let ⟨p, hp⟩ := CharP.exists K
  have : Fact (Nat.Prime p) := ⟨CharP.char_is_prime K p⟩
  have : NeZero n := ⟨hn⟩
  rw [← finrank_extension K p n]
  apply Irreducible.natDegree_dvd_finrank hi
  refine Splits.of_dvd ?_ ?_ (map_dvd (algebraMap K (Extension K p n)) h)
  · apply IsSplittingField.splits
  · exact map_ne_zero (X_pow_card_pow_sub_X_ne_zero K hn Finite.one_lt_card)

end Polynomial
