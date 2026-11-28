/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Trace.Basic

/-!
# Galois theory of quadratic extensions

Let `K/F` be a separable quadratic extension, given by `Algebra.IsQuadraticExtension F K` and
`Algebra.IsSeparable F K`. Then `K/F` is Galois with Galois group of order `2`, see
`Algebra.IsQuadraticExtension.isGalois` and `Algebra.IsQuadraticExtension.isCyclic`.

## Main definitions and results

* `Algebra.IsQuadraticExtension.conj`: the conjugation of `K/F`, that is the nontrivial
  automorphism of `K/F`.
* `Algebra.IsQuadraticExtension.eq_one_or_eq_conj`: an automorphism of `K/F` is either `1` or
  the conjugation.
* `Algebra.IsQuadraticExtension.mul_conj`, `Algebra.IsQuadraticExtension.add_conj`: the product
  and the sum of an element and its conjugate are its norm and its trace.
* `Algebra.IsQuadraticExtension.card_algHom_eq_two`: if `K` embeds into a field `A`, there are
  exactly two embeddings of `K` into `A`.
* `Algebra.IsQuadraticExtension.eq_or_eq_comp_conj`: these embeddings are `φ` and
  `φ ∘ conj F K`.
-/

public section

open Module

namespace Algebra.IsQuadraticExtension

variable (F K : Type*) [Field F] [Field K] [Algebra F K] [IsQuadraticExtension F K]
  [Algebra.IsSeparable F K]

/-- The Galois group of a separable quadratic extension has order `2`. -/
theorem card_aut_eq_two : Nat.card Gal(K/F) = 2 := by
  rw [IsGalois.card_aut_eq_finrank, IsQuadraticExtension.finrank_eq_two]

/-- The conjugation of a Galois quadratic extension `K/F`. -/
noncomputable def conj : Gal(K/F) :=
  (Nat.card_eq_two_iff' 1 |>.mp (card_aut_eq_two F K)).exists.choose

theorem conj_ne_one : conj F K ≠ 1 :=
  (Nat.card_eq_two_iff' 1 |>.mp (card_aut_eq_two F K)).exists.choose_spec

variable {F K}

/-- The conjugation is the only nontrivial automorphism of `K/F`. -/
theorem eq_conj_of_ne_one {σ : Gal(K/F)} (hσ : σ ≠ 1) : σ = conj F K :=
  (Nat.card_eq_two_iff' 1 |>.mp (card_aut_eq_two F K)).unique hσ (conj_ne_one F K)

/-- An automorphism of `K/F` is either the identity or the conjugation. -/
theorem eq_one_or_eq_conj (σ : Gal(K/F)) : σ = 1 ∨ σ = conj F K :=
  or_iff_not_imp_left.mpr fun h ↦ eq_conj_of_ne_one h

@[simp]
theorem conj_conj (x : K) : conj F K (conj F K x) = x := by
  rw [← AlgEquiv.mul_apply, ← pow_two, ← card_aut_eq_two F K, pow_card_eq_one', AlgEquiv.one_apply]

@[simp]
theorem conj_symm : (conj F K).symm = conj F K := by
  ext
  rw [AlgEquiv.symm_apply_eq, conj_conj]

variable (F) in
/-- The product of an element and its conjugate is its norm. -/
theorem mul_conj (x : K) : x * conj F K x = algebraMap F K (Algebra.norm F x) := by
  rw [Algebra.norm_eq_prod_automorphisms, Fintype.prod_eq_mul 1 (conj F K), AlgEquiv.one_apply]
  · exact (conj_ne_one F K).symm
  · exact fun σ h ↦ ((not_or.mpr h) (eq_one_or_eq_conj σ)).elim

variable (F) in
/-- The sum of an element and its conjugate is its trace. -/
theorem add_conj (x : K) : x + conj F K x = algebraMap F K (Algebra.trace F K x) := by
  rw [trace_eq_sum_automorphisms, Fintype.sum_eq_add 1 (conj F K), AlgEquiv.one_apply]
  · exact (conj_ne_one F K).symm
  · exact fun σ h ↦ ((not_or.mpr h) (eq_one_or_eq_conj σ)).elim

variable {A : Type*} [Field A] [Algebra F A]

/-- Composing an embedding with the conjugation gives a different embedding. -/
theorem comp_conj_ne (φ : K →ₐ[F] A) : φ.comp (conj F K : K →ₐ[F] K) ≠ φ :=
  fun h ↦ conj_ne_one F K <| AlgEquiv.ext fun x ↦ φ.toRingHom.injective.eq_iff.mp <|
    AlgHom.congr_fun h x

/-- If there is an embedding of `K` into `A`, there are exactly two of them. -/
theorem card_algHom_eq_two (φ : K →ₐ[F] A) : Nat.card (K →ₐ[F] A) = 2 :=
  IsQuadraticExtension.finrank_eq_two F K ▸ IsGalois.card_algHom_eq_finrank φ

/-- The embeddings of `K` into `A` are `φ` and `φ ∘ conj F K`. -/
theorem eq_or_eq_comp_conj (φ ψ : K →ₐ[F] A) : ψ = φ ∨ ψ = φ.comp (conj F K : K →ₐ[F] K) :=
  or_iff_not_imp_left.mpr fun h ↦
    (Nat.card_eq_two_iff' φ |>.mp (card_algHom_eq_two φ)).unique h (comp_conj_ne φ)

end Algebra.IsQuadraticExtension
