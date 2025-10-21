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

* `FiniteField.Extension k p n` is a non-canonically chosen extension of `k` of degree `n` (for `n > 0`).

## Main Results

* `FiniteField.algEquivExtension`: any other field extension `l/k` of degree `n` is (non-uniquely)
isomorphic to our chosen `FiniteField.Extension k p n`.

## TODO

One could complete classify the category of finite fields of characteristic `p`, where
`#(l₁ →ₐ[k] l₂) = [l₁:k]` if `[l₁:k] ∣ [l₂:k]` and `0` otherwise.

-/

-- MOVE:
theorem dvd_pow_sub_one_of_dvd {R : Type*} [Ring R] {r : R} {a b : ℕ} (h : a ∣ b) :
    r ^ a - 1 ∣ r ^ b - 1 := by
  obtain ⟨n, rfl⟩ := h
  exact pow_one_sub_dvd_pow_mul_sub_one r a n -- we have a worse version and it's misnamed

theorem dvd_pow_pow_sub_self_of_dvd {R : Type*} [Ring R] {r : R} {p a b : ℕ} (h : a ∣ b) :
    r ^ p ^ a - r ∣ r ^ p ^ b - r := by
  by_cases hp₀ : p = 0
  · by_cases hb₀ : b = 0
    · rw [hp₀, hb₀, pow_zero, pow_one, sub_self]
      exact dvd_zero _
    have ha₀ : a ≠ 0 := by rintro rfl; rw [zero_dvd_iff] at h; tauto
    rw [hp₀, zero_pow ha₀, zero_pow hb₀]
  have hp (c) : 1 ≤ p ^ c := one_le_pow₀ <| pos_of_ne_zero hp₀
  rw [← Nat.sub_add_cancel (hp a), ← Nat.sub_add_cancel (hp b), pow_succ', pow_succ',
    ← mul_sub_one, ← mul_sub_one]
  refine mul_dvd_mul_left _ (dvd_pow_sub_one_of_dvd ?_)
  zify
  rw [Nat.cast_sub (hp a), Nat.cast_sub (hp b), Nat.cast_pow, Nat.cast_pow]
  exact dvd_pow_sub_one_of_dvd h

open Polynomial FiniteField

theorem FiniteField.pow_finrank_eq_natCard (p : ℕ) [Fact p.Prime]
    (k : Type*) [AddCommGroup k] [Finite k] [Module (ZMod p) k] :
    p ^ Module.finrank (ZMod p) k = Nat.card k := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]

theorem FiniteField.pow_finrank_eq_card (p : ℕ) [Fact p.Prime]
    (k : Type*) [AddCommGroup k] [Fintype k] [Module (ZMod p) k] :
    p ^ Module.finrank (ZMod p) k = Fintype.card k := by
  rw [pow_finrank_eq_natCard, Fintype.card_eq_nat_card]

theorem FiniteField.nonempty_algHom_of_finrank_dvd {p : ℕ} [Fact p.Prime]
    {k : Type*} [Field k] [Finite k] [Algebra (ZMod p) k]
    {l : Type*} [Field l] [Finite l] [Algebra (ZMod p) l]
    (h : Module.finrank (ZMod p) k ∣ Module.finrank (ZMod p) l) :
    Nonempty (k →ₐ[ZMod p] l) := by
  have := Fintype.ofFinite k
  have := Fintype.ofFinite l
  refine ⟨Polynomial.IsSplittingField.lift _ (X ^ Fintype.card k - X) ?_⟩
  refine Polynomial.splits_of_splits_of_dvd _ ?_
    (FiniteField.isSplittingField_sub l (ZMod p)).splits ?_
  · rw [← pow_finrank_eq_card p l]
    exact FiniteField.X_pow_card_pow_sub_X_ne_zero _ Module.finrank_pos.ne'
      (Fact.out (p := p.Prime)).one_lt
  · rw [← pow_finrank_eq_card p k, ← pow_finrank_eq_card p l]
    exact dvd_pow_pow_sub_self_of_dvd h

theorem FiniteField.card_gal_of_finite (K L : Type*) [Finite L] [Field K] [Field L] [Algebra K L] :
    Fintype.card Gal(L/K) = Module.finrank K L :=
  have := Finite.of_injective _ (algebraMap K L).injective
  have := Fintype.ofFinite K
  (Fintype.card_of_bijective (bijective_frobeniusAlgEquivOfAlgebraic_pow K L)).symm.trans <|
    Fintype.card_fin _

theorem FiniteField.natCard_gal_of_finite (K L : Type*) [Finite L] [Field K] [Field L] [Algebra K L] :
    Nat.card Gal(L/K) = Module.finrank K L := by
  rw [← card_gal_of_finite, Fintype.card_eq_nat_card]
-- END MOVE

variable (k : Type*) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) k]
variable (n : ℕ) [NeZero n]

open Polynomial

namespace FiniteField

/-- Given a finite field `k` of characteristic `p`, we have a non-canoncailly chosen extension
of any given degree `n > 0`. -/
noncomputable def Extension : Type :=
  GaloisField p (Module.finrank (ZMod p) k * n)

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

instance : IsGalois k (Extension k p n) :=
  GaloisField.instIsGaloisOfFinite

example : IsCyclic Gal(Extension k p n / k) :=
  inferInstance

theorem card_gal_extension : Fintype.card Gal(Extension k p n / k) = n :=
  (card_gal_of_finite _ _).trans <| finrank_extension _ _ _

theorem natCard_gal_extension : Nat.card Gal(Extension k p n / k) = n :=
  (natCard_gal_of_finite _ _).trans <| finrank_extension _ _ _

/-- The Frobenius automorphism `x ↦ x ^ Nat.card k` that fixes `k`. -/
noncomputable def Extension.frob :
    Extension k p n ≃ₐ[k] Extension k p n :=
  haveI := Fintype.ofFinite k
  FiniteField.frobeniusAlgEquivOfAlgebraic _ _

@[simp] lemma Extension.frob_apply {x : Extension k p n} :
    frob k p n x = x ^ Nat.card k := by
  have := Fintype.ofFinite k
  rw [← Fintype.card_eq_nat_card]
  rfl

theorem Extension.frob_pow_surjective (g : Gal(Extension k p n/k)) :
    ∃ i < n, Extension.frob k p n ^ i = g := by
  have := Fintype.ofFinite k
  obtain ⟨⟨i, hi⟩, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k
    (Extension k p n)).2 g
  refine ⟨i, ?_, by ext; simp [frob]; congr; subsingleton⟩
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
