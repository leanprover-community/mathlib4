/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Kevin Buzzard
-/
import Mathlib.FieldTheory.Finite.GaloisField

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

variable (k : Type*) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k]
variable (n : ℕ) [NeZero n]

open Polynomial

namespace FiniteField

/-- Given a finite field `k` of characteristic `p`, we have a non-canoncailly chosen extension
of any given degree `n > 0`. -/
noncomputable def Extension : Type :=
  GaloisField p (Module.finrank (ZMod p) k * n)
  deriving Field, Finite, Algebra (ZMod p), FiniteDimensional (ZMod p)

noncomputable instance : Field (Extension k p n) :=
  inferInstanceAs (Field (GaloisField _ _))

noncomputable instance : Finite (Extension k p n) :=
  inferInstanceAs (Finite (GaloisField _ _))

noncomputable instance : Algebra (ZMod p) (Extension k p n) :=
  inferInstanceAs (Algebra (ZMod p) (GaloisField _ _))

noncomputable instance : Module.Finite (ZMod p) (Extension k p n) :=
  .of_finite

theorem finrank_zmod_extension :
    Module.finrank (ZMod p) (Extension k p n) = Module.finrank (ZMod p) k * n :=
  GaloisField.finrank _ <| mul_ne_zero Module.finrank_pos.ne' <| NeZero.ne n

theorem nonempty_algHom_extension :
    Nonempty (k →ₐ[ZMod p] Extension k p n) :=
  nonempty_algHom_of_finrank_dvd (finrank_zmod_extension k p n ▸ dvd_mul_right _ _)

noncomputable instance : Algebra k (Extension k p n) :=
  (nonempty_algHom_extension k p n).some.toAlgebra

instance : Module.Finite k (Extension k p n) :=
  .of_finite

instance : IsScalarTower (ZMod p) k (Extension k p n) :=
  -- there is only at most one map from `𝔽_p` to any ring
  .of_algebraMap_eq' <| Subsingleton.elim _ _

theorem natCard_extension : Nat.card (Extension k p n) = Nat.card k ^ n := by
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

theorem natCard_gal_extension : Nat.card Gal(Extension k p n / k) = n :=
  (IsGalois.card_aut_eq_finrank _ _).trans <| finrank_extension k p n

theorem card_gal_extension : Fintype.card Gal(Extension k p n / k) = n :=
  Fintype.card_eq_nat_card.trans <| natCard_gal_extension k p n

/-- The Frobenius automorphism `x ↦ x ^ Nat.card k` that fixes `k`. -/
noncomputable def Extension.frob :
    Extension k p n ≃ₐ[k] Extension k p n :=
  haveI := Fintype.ofFinite k
  FiniteField.frobeniusAlgEquivOfAlgebraic _ _

@[simp] lemma Extension.frob_apply {x : Extension k p n} :
    frob k p n x = x ^ Nat.card k := by
  simp [frob, ← Nat.card_eq_fintype_card]

theorem Extension.frob_pow_surjective (g : Gal(Extension k p n/k)) :
    ∃ i < n, Extension.frob k p n ^ i = g := by
  let := Fintype.ofFinite k
  obtain ⟨⟨i, hi⟩, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k
    (Extension k p n)).2 g
  refine ⟨i, ?_, by ext; simp [frob]⟩
  rwa [finrank_extension] at hi

/-- Given any field extension `l/k` of degree `n`, we have a non-unique isomorphism between `l`
and our chosen `Extension k p n`. -/
noncomputable def algEquivExtension (l : Type*) [Field l] [Algebra k l]
    (h : Module.finrank k l = n) : l ≃ₐ[k] Extension k p n := by
  refine Nonempty.some ?_
  have : Module.Finite k l := Module.finite_of_finrank_pos <| h ▸ NeZero.pos n
  have : Finite l := Module.finite_of_finite k
  have : Fintype l := .ofFinite _
  have : IsSplittingField k l (X ^ Nat.card k ^ n - X) := by
    convert FiniteField.isSplittingField_sub l k
    rw [← h, ← Module.natCard_eq_pow_finrank, Fintype.card_eq_nat_card]
  refine ⟨(IsSplittingField.algEquiv _ (X ^ (Nat.card k ^ n) - X)).trans ?_⟩
  exact (IsSplittingField.algEquiv _ (X ^ (Nat.card k ^ n) - X)).symm

end FiniteField
