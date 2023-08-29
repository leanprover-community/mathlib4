/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang, Johan Commelin
-/
import Mathlib.Data.MvPolynomial.Rename
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Algebra.Algebra.Subalgebra.Basic

#align_import ring_theory.mv_polynomial.symmetric from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

/-!
# Symmetric Polynomials and Elementary Symmetric Polynomials

This file defines symmetric `MvPolynomial`s and elementary symmetric `MvPolynomial`s.
We also prove some basic facts about them.

## Main declarations

* `MvPolynomial.IsSymmetric`

* `MvPolynomial.symmetricSubalgebra`

* `MvPolynomial.esymm`

* `MvPolynomial.psum`

## Notation

+ `esymm σ R n` is the `n`th elementary symmetric polynomial in `MvPolynomial σ R`.

+ `psum σ R n` is the degree-`n` power sum in `MvPolynomial σ R`, i.e. the sum of monomials
  `(X i)^n` over `i ∈ σ`.

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R S : Type*` `[CommSemiring R]` `[CommSemiring S]` (the coefficients)

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `φ ψ : MvPolynomial σ R`

-/


open Equiv (Perm)

open BigOperators

noncomputable section

namespace Multiset

variable {R : Type*} [CommSemiring R]

/-- The `n`th elementary symmetric function evaluated at the elements of `s` -/
def esymm (s : Multiset R) (n : ℕ) : R :=
  ((s.powersetLen n).map Multiset.prod).sum
#align multiset.esymm Multiset.esymm

theorem _root_.Finset.esymm_map_val {σ} (f : σ → R) (s : Finset σ) (n : ℕ) :
    (s.val.map f).esymm n = (s.powersetLen n).sum fun t => t.prod f := by
  simp only [esymm, powersetLen_map, ← Finset.map_val_val_powersetLen, map_map]
  -- ⊢ sum (map ((fun x => prod x) ∘ (fun x => map f x) ∘ Finset.val) (Finset.power …
  rfl
  -- 🎉 no goals
#align finset.esymm_map_val Finset.esymm_map_val

end Multiset

namespace MvPolynomial

variable {σ : Type*} {R : Type*}

variable {τ : Type*} {S : Type*}

/-- A `MvPolynomial φ` is symmetric if it is invariant under
permutations of its variables by the `rename` operation -/
def IsSymmetric [CommSemiring R] (φ : MvPolynomial σ R) : Prop :=
  ∀ e : Perm σ, rename e φ = φ
#align mv_polynomial.is_symmetric MvPolynomial.IsSymmetric

variable (σ R)

/-- The subalgebra of symmetric `MvPolynomial`s. -/
def symmetricSubalgebra [CommSemiring R] : Subalgebra R (MvPolynomial σ R) where
  carrier := setOf IsSymmetric
  algebraMap_mem' r e := rename_C e r
  mul_mem' ha hb e := by rw [AlgHom.map_mul, ha, hb]
                         -- 🎉 no goals
  add_mem' ha hb e := by rw [AlgHom.map_add, ha, hb]
                         -- 🎉 no goals
#align mv_polynomial.symmetric_subalgebra MvPolynomial.symmetricSubalgebra

variable {σ R}

@[simp]
theorem mem_symmetricSubalgebra [CommSemiring R] (p : MvPolynomial σ R) :
    p ∈ symmetricSubalgebra σ R ↔ p.IsSymmetric :=
  Iff.rfl
#align mv_polynomial.mem_symmetric_subalgebra MvPolynomial.mem_symmetricSubalgebra

namespace IsSymmetric

section CommSemiring

variable [CommSemiring R] [CommSemiring S] {φ ψ : MvPolynomial σ R}

@[simp]
theorem C (r : R) : IsSymmetric (C r : MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).algebraMap_mem r
set_option linter.uppercaseLean3 false in
#align mv_polynomial.is_symmetric.C MvPolynomial.IsSymmetric.C

@[simp]
theorem zero : IsSymmetric (0 : MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).zero_mem
#align mv_polynomial.is_symmetric.zero MvPolynomial.IsSymmetric.zero

@[simp]
theorem one : IsSymmetric (1 : MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).one_mem
#align mv_polynomial.is_symmetric.one MvPolynomial.IsSymmetric.one

theorem add (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ + ψ) :=
  (symmetricSubalgebra σ R).add_mem hφ hψ
#align mv_polynomial.is_symmetric.add MvPolynomial.IsSymmetric.add

theorem mul (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ * ψ) :=
  (symmetricSubalgebra σ R).mul_mem hφ hψ
#align mv_polynomial.is_symmetric.mul MvPolynomial.IsSymmetric.mul

theorem smul (r : R) (hφ : IsSymmetric φ) : IsSymmetric (r • φ) :=
  (symmetricSubalgebra σ R).smul_mem hφ r
#align mv_polynomial.is_symmetric.smul MvPolynomial.IsSymmetric.smul

@[simp]
theorem map (hφ : IsSymmetric φ) (f : R →+* S) : IsSymmetric (map f φ) := fun e => by
  rw [← map_rename, hφ]
  -- 🎉 no goals
#align mv_polynomial.is_symmetric.map MvPolynomial.IsSymmetric.map

end CommSemiring

section CommRing

variable [CommRing R] {φ ψ : MvPolynomial σ R}

theorem neg (hφ : IsSymmetric φ) : IsSymmetric (-φ) :=
  (symmetricSubalgebra σ R).neg_mem hφ
#align mv_polynomial.is_symmetric.neg MvPolynomial.IsSymmetric.neg

theorem sub (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ - ψ) :=
  (symmetricSubalgebra σ R).sub_mem hφ hψ
#align mv_polynomial.is_symmetric.sub MvPolynomial.IsSymmetric.sub

end CommRing

end IsSymmetric

section ElementarySymmetric

open Finset

variable (σ R) [CommSemiring R] [CommSemiring S] [Fintype σ] [Fintype τ]

/-- The `n`th elementary symmetric `MvPolynomial σ R`. -/
def esymm (n : ℕ) : MvPolynomial σ R :=
  ∑ t in powersetLen n univ, ∏ i in t, X i
#align mv_polynomial.esymm MvPolynomial.esymm

/-- The `n`th elementary symmetric `MvPolynomial σ R` is obtained by evaluating the
`n`th elementary symmetric at the `Multiset` of the monomials -/
theorem esymm_eq_multiset_esymm : esymm σ R = (Finset.univ.val.map X).esymm := by
  refine' funext fun n => (Finset.esymm_map_val X _ n).symm
  -- 🎉 no goals
#align mv_polynomial.esymm_eq_multiset_esymm MvPolynomial.esymm_eq_multiset_esymm

theorem aeval_esymm_eq_multiset_esymm [Algebra R S] (f : σ → S) (n : ℕ) :
    aeval f (esymm σ R n) = (Finset.univ.val.map f).esymm n := by
  simp_rw [esymm, aeval_sum, aeval_prod, aeval_X, Finset.esymm_map_val]
  -- 🎉 no goals
#align mv_polynomial.aeval_esymm_eq_multiset_esymm MvPolynomial.aeval_esymm_eq_multiset_esymm

/-- We can define `esymm σ R n` by summing over a subtype instead of over `powerset_len`. -/
theorem esymm_eq_sum_subtype (n : ℕ) :
    esymm σ R n = ∑ t : { s : Finset σ // s.card = n }, ∏ i in (t : Finset σ), X i :=
  sum_subtype _ (fun _ => mem_powerset_len_univ_iff) _
#align mv_polynomial.esymm_eq_sum_subtype MvPolynomial.esymm_eq_sum_subtype

/-- We can define `esymm σ R n` as a sum over explicit monomials -/
theorem esymm_eq_sum_monomial (n : ℕ) :
    esymm σ R n = ∑ t in powersetLen n univ, monomial (∑ i in t, Finsupp.single i 1) 1 := by
  simp_rw [monomial_sum_one]
  -- ⊢ esymm σ R n = ∑ x in powersetLen n univ, ∏ x in x, ↑(monomial (Finsupp.singl …
  rfl
  -- 🎉 no goals
#align mv_polynomial.esymm_eq_sum_monomial MvPolynomial.esymm_eq_sum_monomial

@[simp]
theorem esymm_zero : esymm σ R 0 = 1 := by
  simp only [esymm, powersetLen_zero, sum_singleton, prod_empty]
  -- 🎉 no goals
#align mv_polynomial.esymm_zero MvPolynomial.esymm_zero

theorem map_esymm (n : ℕ) (f : R →+* S) : map f (esymm σ R n) = esymm σ S n := by
  simp_rw [esymm, map_sum, map_prod, map_X]
  -- 🎉 no goals
#align mv_polynomial.map_esymm MvPolynomial.map_esymm

theorem rename_esymm (n : ℕ) (e : σ ≃ τ) : rename e (esymm σ R n) = esymm τ R n :=
  calc
    rename e (esymm σ R n) = ∑ x in powersetLen n univ, ∏ i in x, X (e i) := by
      simp_rw [esymm, map_sum, map_prod, rename_X]
      -- 🎉 no goals
    _ = ∑ t in powersetLen n (univ.map e.toEmbedding), ∏ i in t, X i := by
      simp [Finset.powersetLen_map, -Finset.map_univ_equiv]
      -- ⊢ ∑ x in powersetLen n univ, ∏ x in x, X (↑e x) = ∑ x in powersetLen n univ, ∏ …
      --Porting note: Why did `mapEmbedding_apply` not work?
      dsimp [mapEmbedding, OrderEmbedding.ofMapLEIff]
      -- ⊢ ∑ x in powersetLen n univ, ∏ x in x, X (↑e x) = ∑ x in powersetLen n univ, ∏ …
      simp
      -- 🎉 no goals
    _ = ∑ t in powersetLen n univ, ∏ i in t, X i := by rw [Finset.map_univ_equiv]
                                                       -- 🎉 no goals
#align mv_polynomial.rename_esymm MvPolynomial.rename_esymm

theorem esymm_isSymmetric (n : ℕ) : IsSymmetric (esymm σ R n) := by
  intro
  -- ⊢ ↑(rename ↑e✝) (esymm σ R n) = esymm σ R n
  rw [rename_esymm]
  -- 🎉 no goals
#align mv_polynomial.esymm_is_symmetric MvPolynomial.esymm_isSymmetric

theorem support_esymm'' (n : ℕ) [DecidableEq σ] [Nontrivial R] :
    (esymm σ R n).support =
      (powersetLen n (univ : Finset σ)).biUnion fun t =>
        (Finsupp.single (∑ i : σ in t, Finsupp.single i 1) (1 : R)).support := by
  rw [esymm_eq_sum_monomial]
  -- ⊢ support (∑ t in powersetLen n univ, ↑(monomial (∑ i in t, Finsupp.single i 1 …
  simp only [← single_eq_monomial]
  -- ⊢ support (∑ x in powersetLen n univ, Finsupp.single (∑ i in x, Finsupp.single …
  refine' Finsupp.support_sum_eq_biUnion (powersetLen n (univ : Finset σ)) _
  -- ⊢ ∀ (i₁ i₂ : Finset σ), i₁ ≠ i₂ → Disjoint (Finsupp.single (∑ i in i₁, Finsupp …
  intro s t hst
  -- ⊢ Disjoint (Finsupp.single (∑ i in s, Finsupp.single i 1) 1).support (Finsupp. …
  rw [Finset.disjoint_left, Finsupp.support_single_ne_zero _ one_ne_zero]
  -- ⊢ ∀ ⦃a : σ →₀ ℕ⦄, a ∈ {∑ i in s, Finsupp.single i 1} → ¬a ∈ (Finsupp.single (∑ …
  rw [Finsupp.support_single_ne_zero _ one_ne_zero]
  -- ⊢ ∀ ⦃a : σ →₀ ℕ⦄, a ∈ {∑ i in s, Finsupp.single i 1} → ¬a ∈ {∑ i in t, Finsupp …
  simp only [one_ne_zero, mem_singleton, Finsupp.mem_support_iff]
  -- ⊢ ∀ ⦃a : σ →₀ ℕ⦄, a = ∑ i in s, Finsupp.single i 1 → ¬a = ∑ i in t, Finsupp.si …
  rintro a h rfl
  -- ⊢ False
  have := congr_arg Finsupp.support h
  -- ⊢ False
  rw [Finsupp.support_sum_eq_biUnion, Finsupp.support_sum_eq_biUnion] at this
  have hsingle : ∀ s : Finset σ, ∀ x : σ, x ∈ s → (Finsupp.single x 1).support = {x} := by
    intros _ x _
    rw [Finsupp.support_single_ne_zero x one_ne_zero]
  have hs := biUnion_congr (of_eq_true (eq_self s)) (hsingle s)
  have ht := biUnion_congr (of_eq_true (eq_self t)) (hsingle t)
  rw [hs, ht] at this
  · simp only [biUnion_singleton_eq_self] at this
    -- ⊢ False
    exact absurd this hst.symm
    -- 🎉 no goals
  all_goals intro x y; simp [Finsupp.support_single_disjoint]
  -- 🎉 no goals
#align mv_polynomial.support_esymm'' MvPolynomial.support_esymm''

theorem support_esymm' (n : ℕ) [DecidableEq σ] [Nontrivial R] :
    (esymm σ R n).support =
      (powersetLen n (univ : Finset σ)).biUnion fun t => {∑ i : σ in t, Finsupp.single i 1} := by
  rw [support_esymm'']
  -- ⊢ (Finset.biUnion (powersetLen n univ) fun t => (Finsupp.single (∑ i in t, Fin …
  congr
  -- ⊢ (fun t => (Finsupp.single (∑ i in t, Finsupp.single i 1) 1).support) = fun t …
  funext
  -- ⊢ (Finsupp.single (∑ i in x✝, Finsupp.single i 1) 1).support = {∑ i in x✝, Fin …
  exact Finsupp.support_single_ne_zero _ one_ne_zero
  -- 🎉 no goals
#align mv_polynomial.support_esymm' MvPolynomial.support_esymm'

theorem support_esymm (n : ℕ) [DecidableEq σ] [Nontrivial R] :
    (esymm σ R n).support =
      (powersetLen n (univ : Finset σ)).image fun t => ∑ i : σ in t, Finsupp.single i 1 := by
  rw [support_esymm']
  -- ⊢ (Finset.biUnion (powersetLen n univ) fun t => {∑ i in t, Finsupp.single i 1} …
  exact biUnion_singleton
  -- 🎉 no goals
#align mv_polynomial.support_esymm MvPolynomial.support_esymm

theorem degrees_esymm [Nontrivial R] (n : ℕ) (hpos : 0 < n) (hn : n ≤ Fintype.card σ) :
    (esymm σ R n).degrees = (univ : Finset σ).val := by
  classical
    have :
      (Finsupp.toMultiset ∘ fun t : Finset σ => ∑ i : σ in t, Finsupp.single i 1) = Finset.val := by
      funext
      simp [Finsupp.toMultiset_sum_single]
    rw [degrees_def, support_esymm, sup_image, this]
    have : ((powersetLen n univ).sup (fun (x : Finset σ) => x)).val
        = sup (powersetLen n univ) val := by
      refine' comp_sup_eq_sup_comp _ _ _
      · intros
        simp only [union_val, sup_eq_union]
        congr
      · rfl
    rw [← this]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    simpa using powersetLen_sup _ _ (Nat.lt_of_succ_le hn)
#align mv_polynomial.degrees_esymm MvPolynomial.degrees_esymm

end ElementarySymmetric

section PowerSum

open Finset

variable (σ R) [CommSemiring R] [Fintype σ] [Fintype τ]

/-- The degree-`n` power sum -/
def psum (n : ℕ) : MvPolynomial σ R := ∑ i, X i ^ n

lemma psum_def (n : ℕ) : psum σ R n = ∑ i, X i ^ n := rfl

@[simp]
theorem psum_zero : psum σ R 0 = Fintype.card σ := by
  simp only [psum, _root_.pow_zero, ← cast_card]
  -- ⊢ ↑(card univ) = ↑(Fintype.card σ)
  exact rfl
  -- 🎉 no goals

@[simp]
theorem psum_one : psum σ R 1 = ∑ i, X i := by
  simp only [psum, _root_.pow_one]
  -- 🎉 no goals

@[simp]
theorem rename_psum (n : ℕ) (e : σ ≃ τ) : rename e (psum σ R n) = psum τ R n := by
  simp_rw [psum, map_sum, map_pow, rename_X, e.sum_comp (X · ^ n)]
  -- 🎉 no goals

theorem psum_isSymmetric (n : ℕ) : IsSymmetric (psum σ R n) := rename_psum _ _ n

end PowerSum

end MvPolynomial
