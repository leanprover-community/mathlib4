/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang, Johan Commelin
-/
import Mathlib.Data.MvPolynomial.Rename
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Combinatorics.Composition
import Mathlib.Combinatorics.Partition
import Mathlib.Data.Set.Card

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
  ((s.powersetCard n).map Multiset.prod).sum
#align multiset.esymm Multiset.esymm

theorem _root_.Finset.esymm_map_val {σ} (f : σ → R) (s : Finset σ) (n : ℕ) :
    (s.val.map f).esymm n = (s.powersetCard n).sum fun t => t.prod f := by
  simp only [esymm, powersetCard_map, ← Finset.map_val_val_powersetCard, map_map]
  rfl
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
  add_mem' ha hb e := by rw [AlgHom.map_add, ha, hb]
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
  ∑ t in powersetCard n univ, ∏ i in t, X i
#align mv_polynomial.esymm MvPolynomial.esymm

/-- The `n`th elementary symmetric `MvPolynomial σ R` is obtained by evaluating the
`n`th elementary symmetric at the `Multiset` of the monomials -/
theorem esymm_eq_multiset_esymm : esymm σ R = (Finset.univ.val.map X).esymm := by
  exact funext fun n => (Finset.esymm_map_val X _ n).symm
#align mv_polynomial.esymm_eq_multiset_esymm MvPolynomial.esymm_eq_multiset_esymm

theorem aeval_esymm_eq_multiset_esymm [Algebra R S] (f : σ → S) (n : ℕ) :
    aeval f (esymm σ R n) = (Finset.univ.val.map f).esymm n := by
  simp_rw [esymm, aeval_sum, aeval_prod, aeval_X, Finset.esymm_map_val]
#align mv_polynomial.aeval_esymm_eq_multiset_esymm MvPolynomial.aeval_esymm_eq_multiset_esymm

/-- We can define `esymm σ R n` by summing over a subtype instead of over `powerset_len`. -/
theorem esymm_eq_sum_subtype (n : ℕ) :
    esymm σ R n = ∑ t : { s : Finset σ // s.card = n }, ∏ i in (t : Finset σ), X i :=
  sum_subtype _ (fun _ => mem_powersetCard_univ) _
#align mv_polynomial.esymm_eq_sum_subtype MvPolynomial.esymm_eq_sum_subtype

/-- We can define `esymm σ R n` as a sum over explicit monomials -/
theorem esymm_eq_sum_monomial (n : ℕ) :
    esymm σ R n = ∑ t in powersetCard n univ, monomial (∑ i in t, Finsupp.single i 1) 1 := by
  simp_rw [monomial_sum_one]
  rfl
#align mv_polynomial.esymm_eq_sum_monomial MvPolynomial.esymm_eq_sum_monomial

@[simp]
theorem esymm_zero : esymm σ R 0 = 1 := by
  simp only [esymm, powersetCard_zero, sum_singleton, prod_empty]
#align mv_polynomial.esymm_zero MvPolynomial.esymm_zero

theorem map_esymm (n : ℕ) (f : R →+* S) : map f (esymm σ R n) = esymm σ S n := by
  simp_rw [esymm, map_sum, map_prod, map_X]
#align mv_polynomial.map_esymm MvPolynomial.map_esymm

theorem rename_esymm (n : ℕ) (e : σ ≃ τ) : rename e (esymm σ R n) = esymm τ R n :=
  calc
    rename e (esymm σ R n) = ∑ x in powersetCard n univ, ∏ i in x, X (e i) := by
      simp_rw [esymm, map_sum, map_prod, rename_X]
    _ = ∑ t in powersetCard n (univ.map e.toEmbedding), ∏ i in t, X i := by
      simp [Finset.powersetCard_map, -Finset.map_univ_equiv]
      --Porting note: Why did `mapEmbedding_apply` not work?
      dsimp [mapEmbedding, OrderEmbedding.ofMapLEIff]
      simp
    _ = ∑ t in powersetCard n univ, ∏ i in t, X i := by rw [Finset.map_univ_equiv]
#align mv_polynomial.rename_esymm MvPolynomial.rename_esymm

theorem esymm_isSymmetric (n : ℕ) : IsSymmetric (esymm σ R n) := by
  intro
  rw [rename_esymm]
#align mv_polynomial.esymm_is_symmetric MvPolynomial.esymm_isSymmetric

theorem support_esymm'' (n : ℕ) [DecidableEq σ] [Nontrivial R] :
    (esymm σ R n).support =
      (powersetCard n (univ : Finset σ)).biUnion fun t =>
        (Finsupp.single (∑ i : σ in t, Finsupp.single i 1) (1 : R)).support := by
  rw [esymm_eq_sum_monomial]
  simp only [← single_eq_monomial]
  refine' Finsupp.support_sum_eq_biUnion (powersetCard n (univ : Finset σ)) _
  intro s t hst
  rw [Finset.disjoint_left, Finsupp.support_single_ne_zero _ one_ne_zero]
  rw [Finsupp.support_single_ne_zero _ one_ne_zero]
  simp only [one_ne_zero, mem_singleton, Finsupp.mem_support_iff]
  rintro a h rfl
  have := congr_arg Finsupp.support h
  rw [Finsupp.support_sum_eq_biUnion, Finsupp.support_sum_eq_biUnion] at this
  have hsingle : ∀ s : Finset σ, ∀ x : σ, x ∈ s → (Finsupp.single x 1).support = {x} := by
    intros _ x _
    rw [Finsupp.support_single_ne_zero x one_ne_zero]
  have hs := biUnion_congr (of_eq_true (eq_self s)) (hsingle s)
  have ht := biUnion_congr (of_eq_true (eq_self t)) (hsingle t)
  rw [hs, ht] at this
  · simp only [biUnion_singleton_eq_self] at this
    exact absurd this hst.symm
  all_goals intro x y; simp [Finsupp.support_single_disjoint]
#align mv_polynomial.support_esymm'' MvPolynomial.support_esymm''

theorem support_esymm' (n : ℕ) [DecidableEq σ] [Nontrivial R] :
    (esymm σ R n).support =
      (powersetCard n (univ : Finset σ)).biUnion fun t => {∑ i : σ in t, Finsupp.single i 1} := by
  rw [support_esymm'']
  congr
  funext
  exact Finsupp.support_single_ne_zero _ one_ne_zero
#align mv_polynomial.support_esymm' MvPolynomial.support_esymm'

theorem support_esymm (n : ℕ) [DecidableEq σ] [Nontrivial R] :
    (esymm σ R n).support =
      (powersetCard n (univ : Finset σ)).image fun t => ∑ i : σ in t, Finsupp.single i 1 := by
  rw [support_esymm']
  exact biUnion_singleton
#align mv_polynomial.support_esymm MvPolynomial.support_esymm

theorem degrees_esymm [Nontrivial R] (n : ℕ) (hpos : 0 < n) (hn : n ≤ Fintype.card σ) :
    (esymm σ R n).degrees = (univ : Finset σ).val := by
  classical
    have :
      (Finsupp.toMultiset ∘ fun t : Finset σ => ∑ i : σ in t, Finsupp.single i 1) = Finset.val := by
      funext
      simp [Finsupp.toMultiset_sum_single]
    rw [degrees_def, support_esymm, sup_image, this]
    have : ((powersetCard n univ).sup (fun (x : Finset σ) => x)).val
        = sup (powersetCard n univ) val := by
      refine' comp_sup_eq_sup_comp _ _ _
      · intros
        simp only [union_val, sup_eq_union]
        congr
      · rfl
    rw [← this]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    simpa using powersetCard_sup _ _ (Nat.lt_of_succ_le hn)
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
  exact rfl

@[simp]
theorem psum_one : psum σ R 1 = ∑ i, X i := by
  simp only [psum, _root_.pow_one]

@[simp]
theorem rename_psum (n : ℕ) (e : σ ≃ τ) : rename e (psum σ R n) = psum τ R n := by
  simp_rw [psum, map_sum, map_pow, rename_X, e.sum_comp (X · ^ n)]

theorem psum_isSymmetric (n : ℕ) : IsSymmetric (psum σ R n) := rename_psum _ _ n

end PowerSum

section Exponent

open Classical
open Composition
open Finset

variable (σ R) [CommSemiring R] [CommSemiring S] [Fintype σ] [Fintype τ]

@[ext]
structure Exponent (n : ℕ) :=
  (exp : σ → ℕ)
  (sum_eq : ∑ i, exp i = n)

lemma Exponent.single_le_sum {n : ℕ} (s : Exponent σ n) (i : σ) : s.exp i ≤ n := by
  have h : ∑ i, s.exp i = n := s.sum_eq
  simp_rw [←h]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (s.exp i)) (mem_univ i)
  done

lemma Exponent.zero_of_sum_eq_zero (s : Exponent σ 0) : ∀ i, s.exp i = 0 := by
  intro i
  have := Finset.single_le_sum (fun i _ => Nat.zero_le (s.exp i)) (mem_univ i)
  rw [s.sum_eq] at this
  exact Nat.eq_zero_of_le_zero this
  done

def Exponent.zero : Exponent σ 0 := ⟨fun _ => 0, by norm_num⟩

def Exponent.one (i : σ) : Exponent σ 1 := ⟨fun j => if i = j then 1 else 0, by norm_num⟩

instance exponentFinite (n : ℕ) : Finite (Exponent σ n) := by
  let f : Exponent σ n → (σ → Fin (n+1)) := fun s => fun i => ⟨s.exp i, Nat.lt_succ_of_le (Exponent.single_le_sum σ s i)⟩
  have hf : Function.Injective f := by
    intros s t h
    rw [Exponent.ext_iff]
    ext i
    have := congr_arg (fun s => s i) h
    simp only [Function.Injective.eq_iff] at this
    exact Fin.mk_eq_mk.mp this
  exact Finite.of_injective f hf
  done

instance exponentFintype (n : ℕ) : Fintype (Exponent σ n) := Fintype.ofFinite (Exponent σ n)

def exponentLiftEquiv (e : σ ≃ τ) (n : ℕ): Exponent σ n ≃ Exponent τ n := {
          toFun := fun s => ⟨fun i => s.exp (e.invFun i), by simp_rw [← s.sum_eq]; exact Equiv.sum_comp e.symm s.exp⟩,
          invFun := fun s => ⟨fun i => s.exp (e.toFun i), by simp_rw [← s.sum_eq]; exact Equiv.sum_comp e s.exp⟩,
          left_inv := fun s => by simp,
          right_inv := fun s => by simp
          }

lemma exponentLiftEquiv_toFun (e : σ ≃ τ) (n : ℕ) (s : Exponent σ n) (i : τ) : ((exponentLiftEquiv _ e _).toFun s).exp i = s.exp (e.invFun i) := by
  simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe]
  rfl
  done

lemma Exponent.exponentCard_zero : Fintype.card (Exponent σ 0) = 1 := by
  apply Fintype.card_eq_one_iff.mpr
  use Exponent.zero σ
  intro x
  ext i
  simp only [Exponent.sum_eq, Exponent.zero_of_sum_eq_zero]
  done

lemma Exponent.one_sum_singleton (s : Exponent σ 1) : ∃! (i : σ) , Exponent.one σ i = s:= by
  have h : ∑ i, s.exp i = 1 := s.sum_eq
  have (i : σ): exp s i = 0 ∨ exp s i = 1 := by
    have := Exponent.single_le_sum σ s i
    apply Nat.le_one_iff_eq_zero_or_eq_one.mp
    exact this
  by_cases exists_i : ∃ (i : σ), s.exp i = 1
  · obtain ⟨i, hi⟩ := exists_i
    use i
    constructor
    simp only [Exponent]
    ext j
    by_cases hji : j = i
    · rw [hji, Exponent.one]
      simp only [ite_true, hi]
    · have : exp s j = 0 := by
        obtain (h0 | h1) := (this j)
        · assumption
        · exfalso
          have : 2 <= ∑ i, s.exp i := by
            let f : Finset σ := {i, j}
            have : f ⊆ univ := subset_univ f
            have that : ∑ k in f, s.exp k = 2 := by
              simp only [Finset.sum_insert]
              have : ∀ k ∈ f, s.exp k = 1 := by
                intro k hk
                have : k = i ∨ k = j := by
                  simp only [Finset.mem_insert] at hk
                  obtain (ki | kj) := hk
                  · left
                    exact ki
                  · right
                    exact mem_singleton.mp kj
                obtain (ki | kj) := this
                · rw [ki]
                  exact hi
                · rw [kj]
                  exact h1
              have f2 : f.card = 2 := by
                simp only [Finset.card_insert_of_not_mem, Finset.card_singleton, hji]
                rw [Finset.card_eq_two]
                use i, j
                constructor
                symm
                simp only [ne_eq, hji]
                trivial
                rfl
              have : ∑ k in f, s.exp k = ∑ k in f, 1 := by
                apply Finset.sum_congr
                rfl
                exact this
              rw [this]
              simp only [sum_const, f2, smul_eq_mul, mul_one]
            rw [←that]
            exact Finset.sum_le_sum_of_subset this
          linarith
      rw [this]
      simp only [Exponent.one]
      split
      tauto
      rfl
    intro j
    by_cases hji : j = i
    rw [hji]
    simp only [implies_true]
    intro h0
    exfalso
    rw [←h0] at hi
    have : exp (one σ j) i = 0 := by simp only [Exponent.one]; split; tauto; rfl
    linarith
  · exfalso
    have : ∀ i : σ, s.exp i = 0 := by
      intro i
      obtain (h0 | h1) := (this i)
      · assumption
      · exfalso
        exact exists_i ⟨i, h1⟩
    have : ∑ i, s.exp i = 0 := by
      simp only [this, Finset.sum_const_zero]
    linarith
  done

def Exponent.fintype_toExponent : (σ → Exponent σ 1) := (fun i => ⟨fun j => if i = j then 1 else 0, by simp only [sum_ite_eq, mem_univ, ite_true]⟩)

lemma Exponent.fintype_toExponent_bijective : Function.Bijective (Exponent.fintype_toExponent σ) := by
  rw [Function.bijective_iff_existsUnique]
  exact Exponent.one_sum_singleton σ

lemma Exponent.fintype_toExponent_equiv : σ ≃ Exponent σ 1 := by
  exact Equiv.ofBijective _ (Exponent.fintype_toExponent_bijective σ)
  done

lemma Exponent.exponentCard_one : Fintype.card (Exponent σ 1) = Fintype.card σ := by
  apply Fintype.card_congr
  symm
  exact Exponent.fintype_toExponent_equiv _
  done

end Exponent

section CompleteHomogeneousSymmetric

open Classical

variable (σ R) [CommSemiring R] [CommSemiring S] [Fintype σ] [Fintype τ]

/-- The `n`th complete homogeneous symmetric `MvPolynomial σ R`. -/
def hsymm (n : ℕ) : MvPolynomial σ R := ∑ μ : Exponent σ n, ∏ i : σ, X i ^ (μ.exp i)

lemma hsum_def (n : ℕ) : hsymm σ R n = ∑ μ : Exponent σ n, ∏ i : σ, X i ^ (μ.exp i) := rfl

@[simp]
theorem hsymm_zero : hsymm σ R 0 = 1 := by
  simp only [hsymm, pow_zero]
  simp_rw [Exponent.zero_of_sum_eq_zero]
  have (p : MvPolynomial σ R) : p ^ 0 = 1 := by simp
  simp_rw [this]
  have : ∏ i : σ, (1 : MvPolynomial σ R) = 1 := by simp
  simp_rw [this]
  have : ∑ x : Exponent σ 0, (1 : MvPolynomial σ R) = (Fintype.card (Exponent σ 0) : MvPolynomial σ R) := by simp only [Finset.sum_const,
    nsmul_eq_mul, mul_one, Fintype.card_eq_sum_ones, smul_eq_mul]
  rw [this, Exponent.exponentCard_zero]
  exact Nat.cast_one
  done

@[simp]
theorem hsymm_one : hsymm σ R 1 = ∑ i, X i := by
  have (i : σ) (s : Exponent σ 1) : Exponent.exp s i = if (Equiv.ofBijective (Exponent.fintype_toExponent σ) ((Exponent.fintype_toExponent_bijective σ) : Function.Bijective (Exponent.fintype_toExponent σ))).symm s = i then 1 else 0 := by
    have : ∃ (i : σ), Exponent.one σ i = s := ExistsUnique.exists (Exponent.one_sum_singleton σ s)
    obtain ⟨j, h⟩ := this
    have is_inv (j : σ) : (Equiv.ofBijective (Exponent.fintype_toExponent σ) ((Exponent.fintype_toExponent_bijective σ) : Function.Bijective (Exponent.fintype_toExponent σ))).symm (Exponent.one σ j) = j := by
      have : (Equiv.ofBijective (Exponent.fintype_toExponent σ) ((Exponent.fintype_toExponent_bijective σ) : Function.Bijective (Exponent.fintype_toExponent σ))) j = Exponent.one σ j := by
        simp [Exponent.fintype_toExponent, Exponent.one]
      rw [←this]
      simp only [Equiv.ofBijective_apply, Equiv.ofBijective_symm_apply_apply]
    simp_rw [←h, is_inv j, Exponent.one]
  have pow_eq (i x : σ) : (X x ^ if i = x then 1 else 0) = if i = x then ((X : σ → MvPolynomial σ R) i) else 1 := by
    by_cases h : i = x
    · simp_rw [if_pos h]
      simp only [pow_one, h]
    · simp_rw [if_neg h]
      simp only [pow_zero]
  calc
    hsymm σ R 1 = ∑ μ : Exponent σ 1, ∏ i : σ, X i ^ Exponent.exp μ i := by simp only [hsymm, pow_one]
    _ = ∑ i : σ, ∏ j : σ, X j ^ (Exponent.fintype_toExponent σ i).exp j := by apply Fintype.sum_equiv; swap; symm; exact Equiv.ofBijective _ (Exponent.fintype_toExponent_bijective σ); intro s; congr; simp only [Exponent.fintype_toExponent]; funext i; congr; simp only [this]
    _ = ∑ i : σ, X i := by congr; funext i; simp only [Exponent.fintype_toExponent, Equiv.toFun_as_coe]; simp_rw [pow_eq _ _]; simp only [Finset.prod_ite_eq,
      Finset.mem_univ, ite_true]

theorem map_hsymm (n : ℕ) (f : R →+* S) : map f (hsymm σ R n) = hsymm σ S n := by
  simp_rw [hsymm, map_sum, map_prod, map_pow, map_X]

theorem rename_hsymm (n : ℕ) (e : σ ≃ τ) : rename e (hsymm σ R n) = hsymm τ R n :=
  calc
    rename e (hsymm σ R n) = ∑ μ : Exponent σ n, ∏ i : σ, X (e i) ^ (μ.exp i) := by
      simp_rw [hsymm, map_sum, map_prod, map_pow, rename_X]
    _ = ∑ μ : Exponent σ n, ∏ j : τ, X j ^ (((exponentLiftEquiv _ e _) μ).exp j) := by
      congr
      funext s
      apply Fintype.prod_equiv
      intro i
      swap
      exact e
      congr
      simp only [Equiv.invFun_as_coe, Equiv.symm_apply_apply]
    _ = hsymm τ R n := by
      simp_rw [hsymm]
      apply Fintype.sum_equiv
      intro i
      swap
      exact (exponentLiftEquiv _ e _)
      congr

theorem hsymm_isSymmetric (n : ℕ) : IsSymmetric (hsymm σ R n) := rename_hsymm _ _ n

end CompleteHomogeneousSymmetric

end MvPolynomial
