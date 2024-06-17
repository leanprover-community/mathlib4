/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang, Johan Commelin
-/

import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Combinatorics.Enumerative.Partition

#align_import ring_theory.mv_polynomial.symmetric from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

/-!
# Symmetric Polynomials and Elementary Symmetric Polynomials

This file defines symmetric `MvPolynomial`s and the bases of elementary, complete homogeneous,
power sum, and monomial symmetric `MvPolynomial`s. We also prove some basic facts about them.

## Main declarations

* `MvPolynomial.IsSymmetric`

* `MvPolynomial.symmetricSubalgebra`

* `MvPolynomial.esymm`

* `MvPolynomial.hsymm`

* `MvPolynomial.psum`

* `MvPolynomial.msymm`

## Notation

+ `esymm σ R n` is the `n`th elementary symmetric polynomial in `MvPolynomial σ R`.

+ `hsymm σ R n` is the `n`th complete homogeneous symmetric polynomial in `MvPolynomial σ R`.

+ `psum σ R n` is the degree-`n` power sum in `MvPolynomial σ R`, i.e. the sum of monomials
  `(X i)^n` over `i ∈ σ`.

+ `msymm σ R μ` is the monomial symmetric polynomial whose exponents set are the parts
  of `μ ⊢ n` in `MvPolynomial σ R`.

As in other polynomial files, we typically use the notation:

+ `σ τ : Type*` (indexing the variables)

+ `R S : Type*` `[CommSemiring R]` `[CommSemiring S]` (the coefficients)

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `φ ψ : MvPolynomial σ R`

-/


open Equiv (Perm)

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

variable (n : ℕ) {σ τ : Type*} {R S : Type*}

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

protected theorem rename (hφ : φ.IsSymmetric) (e : σ ≃ τ) : (rename e φ).IsSymmetric := fun _ => by
  apply rename_injective _ e.symm.injective
  simp_rw [rename_rename, ← Equiv.coe_trans, Equiv.self_trans_symm, Equiv.coe_refl, rename_id]
  rw [hφ]

@[simp]
theorem _root_.MvPolynomial.isSymmetric_rename {e : σ ≃ τ} :
    (MvPolynomial.rename e φ).IsSymmetric ↔ φ.IsSymmetric :=
  ⟨fun h => by simpa using (IsSymmetric.rename (R := R) h e.symm), (IsSymmetric.rename · e)⟩

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

/-- `MvPolynomial.rename` induces an isomorphism between the symmetric subalgebras. -/
@[simps!]
def renameSymmetricSubalgebra [CommSemiring R] (e : σ ≃ τ) :
    symmetricSubalgebra σ R ≃ₐ[R] symmetricSubalgebra τ R :=
  AlgEquiv.ofAlgHom
    (((rename e).comp (symmetricSubalgebra σ R).val).codRestrict _ <| fun x => x.2.rename e)
    (((rename e.symm).comp <| Subalgebra.val _).codRestrict _ <| fun x => x.2.rename e.symm)
    (AlgHom.ext <| fun p => Subtype.ext <| by simp)
    (AlgHom.ext <| fun p => Subtype.ext <| by simp)

variable (σ R : Type*) [CommSemiring R] [CommSemiring S] [Fintype σ] [Fintype τ]

section Partitions

/-! ### Multiplicativity on partitions -/

variable (f : ℕ → MvPolynomial σ R)

/-- Given a sequence of `MvPolynomial` functions `f` and a partition `μ` of size `n`,
`muProduct` computes the product of applying each function in `f` to the parts of `μ`. -/
def muProduct {n : ℕ} (μ : n.Partition) : MvPolynomial σ R :=
  (μ.parts.map f).prod

lemma muProduct_def (μ : n.Partition) :
    muProduct σ R f μ = (μ.parts.map f).prod := rfl

@[simp]
theorem muProduct_indiscrete_zero :
    muProduct σ R f (.indiscrete 0) = 1 := by simp [muProduct]

@[simp]
theorem muProduct_indiscrete_of_pos (npos : n > 0) :
    muProduct σ R f (Nat.Partition.indiscrete n) = f n := by
  rw [muProduct, Nat.Partition.indiscrete_parts, Multiset.map_singleton, Multiset.prod_singleton]
  linarith

end Partitions

section ElementarySymmetric

open Finset

variable (n : ℕ)

/-- The `n`th elementary symmetric `MvPolynomial σ R`. -/
def esymm (n : ℕ) : MvPolynomial σ R :=
  ∑ t ∈ powersetCard n univ, ∏ i ∈ t, X i
#align mv_polynomial.esymm MvPolynomial.esymm

lemma esymm_def : esymm σ R n = ∑ t in powersetCard n univ, ∏ i in t, X i := rfl

/--
`esymmMu` is the product of the symmetric polynomials `esymm μᵢ`,
where `μ = (μ₁, μ₂, ...)` is a partition.
-/
def esymmMu {n : ℕ} (μ : n.Partition) : MvPolynomial σ R :=
  muProduct σ R (esymm σ R) μ

/-- The `n`th elementary symmetric `MvPolynomial σ R` is obtained by evaluating the
`n`th elementary symmetric at the `Multiset` of the monomials -/
theorem esymm_eq_multiset_esymm : esymm σ R = (univ.val.map X).esymm := by
  exact funext fun n => (esymm_map_val X _ n).symm
#align mv_polynomial.esymm_eq_multiset_esymm MvPolynomial.esymm_eq_multiset_esymm

theorem aeval_esymm_eq_multiset_esymm [Algebra R S] (f : σ → S) :
    aeval f (esymm σ R n) = (univ.val.map f).esymm n := by
  simp_rw [esymm, aeval_sum, aeval_prod, aeval_X, esymm_map_val]
#align mv_polynomial.aeval_esymm_eq_multiset_esymm MvPolynomial.aeval_esymm_eq_multiset_esymm

/-- We can define `esymm σ R n` by summing over a subtype instead of over `powerset_len`. -/
theorem esymm_eq_sum_subtype (n : ℕ) :
    esymm σ R n = ∑ t : { s : Finset σ // s.card = n }, ∏ i ∈ (t : Finset σ), X i :=
  sum_subtype _ (fun _ => mem_powersetCard_univ) _
#align mv_polynomial.esymm_eq_sum_subtype MvPolynomial.esymm_eq_sum_subtype

/-- We can define `esymm σ R n` as a sum over explicit monomials -/
theorem esymm_eq_sum_monomial (n : ℕ) :
    esymm σ R n = ∑ t ∈ powersetCard n univ, monomial (∑ i ∈ t, Finsupp.single i 1) 1 := by
  simp_rw [monomial_sum_one]
  rfl
#align mv_polynomial.esymm_eq_sum_monomial MvPolynomial.esymm_eq_sum_monomial

@[simp]
theorem esymm_zero : esymm σ R 0 = 1 := by simp [esymm]
#align mv_polynomial.esymm_zero MvPolynomial.esymm_zero

@[simp]
theorem esymm_one : esymm σ R 1 = ∑ i, X i := by simp [esymm, powersetCard_one]

theorem esymmMu_zero : esymmMu σ R (Nat.Partition.indiscrete 0) = 1 := by simp [esymmMu]

@[simp]
theorem esymmMu_onePart : esymmMu σ R (Nat.Partition.indiscrete n) = esymm σ R n := by
  cases n <;> simp [esymmMu]

theorem map_esymm (f : R →+* S) : map f (esymm σ R n) = esymm σ S n := by
  simp_rw [esymm, map_sum, map_prod, map_X]
#align mv_polynomial.map_esymm MvPolynomial.map_esymm

theorem rename_esymm (e : σ ≃ τ) : rename e (esymm σ R n) = esymm τ R n :=
  calc
    rename e (esymm σ R n) = ∑ x ∈ powersetCard n univ, ∏ i ∈ x, X (e i) := by
      simp_rw [esymm, map_sum, map_prod, rename_X]
    _ = ∑ t ∈ powersetCard n (univ.map e.toEmbedding), ∏ i ∈ t, X i := by
      simp [powersetCard_map, -map_univ_equiv]
      -- Porting note: Why did `mapEmbedding_apply` not work?
      dsimp [mapEmbedding, OrderEmbedding.ofMapLEIff]
      simp
    _ = ∑ t ∈ powersetCard n univ, ∏ i ∈ t, X i := by rw [map_univ_equiv]
#align mv_polynomial.rename_esymm MvPolynomial.rename_esymm

theorem esymm_isSymmetric : IsSymmetric (esymm σ R n) := rename_esymm _ _ n
#align mv_polynomial.esymm_is_symmetric MvPolynomial.esymm_isSymmetric

theorem support_esymm'' [DecidableEq σ] [Nontrivial R] :
    (esymm σ R n).support =
      (powersetCard n (univ : Finset σ)).biUnion fun t =>
        (Finsupp.single (∑ i ∈ t, Finsupp.single i 1) (1 : R)).support := by
  rw [esymm_eq_sum_monomial]
  simp only [← single_eq_monomial]
  refine Finsupp.support_sum_eq_biUnion (powersetCard n (univ : Finset σ)) ?_
  intro s t hst
  rw [disjoint_left, Finsupp.support_single_ne_zero _ one_ne_zero]
  rw [Finsupp.support_single_ne_zero _ one_ne_zero]
  simp only [one_ne_zero, mem_singleton, Finsupp.mem_support_iff]
  rintro a h rfl
  have := congr_arg Finsupp.support h
  rw [Finsupp.support_sum_eq_biUnion, Finsupp.support_sum_eq_biUnion] at this
  · have hsingle : ∀ s : Finset σ, ∀ x : σ, x ∈ s → (Finsupp.single x 1).support = {x} := by
      intros _ x _
      rw [Finsupp.support_single_ne_zero x one_ne_zero]
    have hs := biUnion_congr (of_eq_true (eq_self s)) (hsingle s)
    have ht := biUnion_congr (of_eq_true (eq_self t)) (hsingle t)
    rw [hs, ht] at this
    · simp only [biUnion_singleton_eq_self] at this
      exact absurd this hst.symm
  all_goals intro x y; simp [Finsupp.support_single_disjoint]
#align mv_polynomial.support_esymm'' MvPolynomial.support_esymm''

theorem support_esymm' [DecidableEq σ] [Nontrivial R] :
    (esymm σ R n).support =
      (powersetCard n (univ : Finset σ)).biUnion fun t => {∑ i ∈ t, Finsupp.single i 1} := by
  rw [support_esymm'']
  congr
  funext
  exact Finsupp.support_single_ne_zero _ one_ne_zero
#align mv_polynomial.support_esymm' MvPolynomial.support_esymm'

theorem support_esymm [DecidableEq σ] [Nontrivial R] :
    (esymm σ R n).support =
      (powersetCard n (univ : Finset σ)).image fun t => ∑ i ∈ t, Finsupp.single i 1 := by
  rw [support_esymm']
  exact biUnion_singleton
#align mv_polynomial.support_esymm MvPolynomial.support_esymm

theorem degrees_esymm [Nontrivial R] (hpos : 0 < n) (hn : n ≤ Fintype.card σ) :
    (esymm σ R n).degrees = (univ : Finset σ).val := by
  classical
    have :
      (Finsupp.toMultiset ∘ fun t : Finset σ => ∑ i ∈ t, Finsupp.single i 1) = val := by
      funext
      simp [Finsupp.toMultiset_sum_single]
    rw [degrees_def, support_esymm, sup_image, this]
    have : ((powersetCard n univ).sup (fun (x : Finset σ) => x)).val
        = sup (powersetCard n univ) val := by
      refine comp_sup_eq_sup_comp _ ?_ ?_
      · intros
        simp only [union_val, sup_eq_union]
        congr
      · rfl
    rw [← this]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    simpa using powersetCard_sup _ _ (Nat.lt_of_succ_le hn)
#align mv_polynomial.degrees_esymm MvPolynomial.degrees_esymm

end ElementarySymmetric

section CompleteHomogeneousSymmetric

open Finset Multiset Sym

variable [DecidableEq σ] [DecidableEq τ] (n : ℕ)

/-- The `n`th complete homogeneous symmetric `MvPolynomial σ R`. -/
def hsymm : MvPolynomial σ R := ∑ s : Sym σ n, (s.1.map X).prod

lemma hsymm_def : hsymm σ R n = ∑ s : Sym σ n, (s.1.map X).prod := rfl

/-- `hsymmMu` is the product of the symmetric polynomials `hsymm μᵢ`,
where `μ = (μ₁, μ₂, ...)` is a partition. -/
def hsymmMu {n : ℕ} (μ : n.Partition) : MvPolynomial σ R := muProduct σ R (hsymm σ R) μ

lemma hsymmMu_def {n : ℕ} (μ : n.Partition) : hsymmMu σ R μ = (μ.parts.map (hsymm σ R)).prod := rfl

@[simp]
theorem hsymm_zero : hsymm σ R 0 = 1 := by simp [hsymm, eq_nil_of_card_zero]

@[simp]
theorem hsymm_one : hsymm σ R 1 = ∑ i, X i := by
  symm
  apply Fintype.sum_equiv oneEquiv
  simp only [oneEquiv_apply, Multiset.map_singleton, Multiset.prod_singleton, implies_true]

theorem hsymmMu_zero : hsymmMu σ R (Nat.Partition.indiscrete 0) = 1 := by simp [hsymmMu]

@[simp]
theorem hsymmMu_onePart : hsymmMu σ R (Nat.Partition.indiscrete n) = hsymm σ R n := by
  cases n <;> simp [hsymmMu]

theorem map_hsymm (f : R →+* S) : map f (hsymm σ R n) = hsymm σ S n := by
  simp [hsymm, ← Multiset.prod_hom']

theorem rename_hsymm (e : σ ≃ τ) : rename e (hsymm σ R n) = hsymm τ R n := by
  simp_rw [hsymm, map_sum, ← prod_hom', rename_X]
  apply Fintype.sum_equiv (equivCongr e)
  simp

theorem hsymm_isSymmetric : IsSymmetric (hsymm σ R n) := rename_hsymm _ _ n

end CompleteHomogeneousSymmetric

section PowerSum

open Finset

variable (n : ℕ)

/-- The degree-`n` power sum -/
def psum : MvPolynomial σ R := ∑ i, X i ^ n

lemma psum_def : psum σ R n = ∑ i, X i ^ n := rfl

/-- `psumMu` is the product of the symmetric polynomials `psum μᵢ`,
where `μ = (μ₁, μ₂, ...)` is a partition. -/
def psumMu {n : ℕ} (μ : n.Partition) : MvPolynomial σ R :=
  muProduct σ R (psum σ R) μ

lemma psumMu_def {n : ℕ} (μ : n.Partition) : psumMu σ R μ =
    (μ.parts.map (psum σ R)).prod := rfl

@[simp]
theorem psum_zero : psum σ R 0 = Fintype.card σ := by simp [psum]

@[simp]
theorem psum_one : psum σ R 1 = ∑ i, X i := by simp [psum]

@[simp]
theorem psumMu_zero : psumMu σ R (Nat.Partition.indiscrete 0) = 1 := by
  rw [psumMu, muProduct_indiscrete_zero]

@[simp]
theorem psumMu_indiscrete {n : ℕ} (npos : n > 0) :
    psumMu σ R (Nat.Partition.indiscrete n) = psum σ R n := by simp [psumMu, npos]

@[simp]
theorem rename_psum (e : σ ≃ τ) : rename e (psum σ R n) = psum τ R n := by
  simp_rw [psum, map_sum, map_pow, rename_X, e.sum_comp (X · ^ n)]

theorem psum_isSymmetric : IsSymmetric (psum σ R n) := rename_psum _ _ n

end PowerSum

section MonomialSymmetric

open Nat.Partition

variable [DecidableEq σ] [DecidableEq τ] {n : ℕ} (μ : n.Partition)

/-- The monomial symmetric `MvPolynomial σ R` with exponent set μ. -/
def msymm : MvPolynomial σ R :=
  ∑ s : {a : Sym σ n // ofSym a = μ},  (s.1.1.map X).prod

lemma msymm_def : msymm σ R μ =
    ∑ s : {a : Sym σ n // ofSym a = μ}, (s.1.1.map X).prod := rfl

@[simp]
theorem msymm_zero : msymm σ R (indiscrete 0) = 1 := by
  rw [msymm, Fintype.sum_subsingleton _ ⟨(Sym.nil : Sym σ 0), by rfl⟩]
  simp

@[simp]
theorem msymm_one : msymm σ R (indiscrete 1) = ∑ i, X i := by
  symm
  apply Fintype.sum_equiv (ofSym_equiv_onePart σ)
  simp

@[simp]
theorem rename_msymm (e : σ ≃ τ) :
    rename e (msymm σ R μ) = msymm τ R μ := by
  rw [msymm, map_sum]
  apply Fintype.sum_equiv (ofSym_shape_equiv μ e)
  intro
  rw [← Multiset.prod_hom, Multiset.map_map, ofSym_shape_equiv]
  simp

theorem msymm_isSymmetric : IsSymmetric (msymm σ R μ) :=
  rename_msymm _ _ μ

end MonomialSymmetric

end MvPolynomial
