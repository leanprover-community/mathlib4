/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang, Johan Commelin
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Combinatorics.Partition
import Mathlib.Data.MvPolynomial.Rename
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Data.Sym.Basic

#align_import ring_theory.mv_polynomial.symmetric from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

/-!
# Symmetric Polynomials and Elementary Symmetric Polynomials

This file defines symmetric `MvPolynomial`s and elementary symmetric `MvPolynomial`s.
We also prove some basic facts about them.

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

/- Multiplicativity on partitions -/

/--
  Given a sequence of `MvPolynomial` functions `f` and a partition `μ` of size `n`,
  `muProduct` computes the product of applying each function in `f` to the parts of `μ`.
-/
def muProduct {n : ℕ} (f : ℕ → MvPolynomial σ R) (μ : n.Partition) : MvPolynomial σ R :=
  Multiset.prod (μ.parts.map f)

lemma muProduct_def {n : ℕ} (f : ℕ → MvPolynomial σ R) (μ : n.Partition) :
    muProduct σ R f μ = Multiset.prod (μ.parts.map f) := rfl

@[simp]
theorem muProduct_zero (f : ℕ → MvPolynomial σ R) :
    muProduct σ R f (Nat.Partition.indiscrete 0) = 1 := by
  simp only [muProduct, Nat.Partition.partition_zero_parts, Multiset.map_zero, Multiset.prod_zero]

@[simp]
theorem muProduct_onePart (n : ℕ) (f : ℕ → MvPolynomial σ R) (npos : n > 0) :
    muProduct σ R f (Nat.Partition.indiscrete n) = f n := by
  rw [muProduct, Nat.Partition.indiscrete_parts, Multiset.map_singleton, Multiset.prod_singleton]
  linarith

section ElementarySymmetric

open Finset

/-- The `n`th elementary symmetric `MvPolynomial σ R`. -/
def esymm (n : ℕ) : MvPolynomial σ R :=
  ∑ t in powersetCard n univ, ∏ i in t, X i
#align mv_polynomial.esymm MvPolynomial.esymm

lemma esymm_def (n : ℕ) : esymm σ R n = ∑ t in powersetCard n univ, ∏ i in t, X i := rfl

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

theorem aeval_esymm_eq_multiset_esymm [Algebra R S] (f : σ → S) (n : ℕ) :
    aeval f (esymm σ R n) = (univ.val.map f).esymm n := by
  simp_rw [esymm, aeval_sum, aeval_prod, aeval_X, esymm_map_val]
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

@[simp]
theorem esymm_one : esymm σ R 1 = ∑ i, X i := by
  simp only [esymm, powersetCard_one, sum_map, Function.Embedding.coeFn_mk, prod_singleton]

theorem esymmMu_zero : esymmMu σ R (Nat.Partition.indiscrete 0) = 1 := by
  simp only [esymmMu, esymm_zero, muProduct_zero]

@[simp]
theorem esymmMu_onePart (n : ℕ) : esymmMu σ R (Nat.Partition.indiscrete n) = esymm σ R n := by
  cases n
  · simp only [esymmMu, esymm_zero, muProduct_zero]
  · simp only [esymmMu, gt_iff_lt, Nat.zero_lt_succ, muProduct_onePart]

theorem map_esymm (n : ℕ) (f : R →+* S) : map f (esymm σ R n) = esymm σ S n := by
  simp_rw [esymm, map_sum, map_prod, map_X]
#align mv_polynomial.map_esymm MvPolynomial.map_esymm

theorem rename_esymm (n : ℕ) (e : σ ≃ τ) : rename e (esymm σ R n) = esymm τ R n :=
  calc
    rename e (esymm σ R n) = ∑ x in powersetCard n univ, ∏ i in x, X (e i) := by
      simp_rw [esymm, map_sum, map_prod, rename_X]
    _ = ∑ t in powersetCard n (univ.map e.toEmbedding), ∏ i in t, X i := by
      simp [powersetCard_map, -map_univ_equiv]
      -- Porting note: Why did `mapEmbedding_apply` not work?
      dsimp [mapEmbedding, OrderEmbedding.ofMapLEIff]
      simp
    _ = ∑ t in powersetCard n univ, ∏ i in t, X i := by rw [map_univ_equiv]
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
  rw [disjoint_left, Finsupp.support_single_ne_zero _ one_ne_zero]
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
      (Finsupp.toMultiset ∘ fun t : Finset σ => ∑ i : σ in t, Finsupp.single i 1) = val := by
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

section CompleteHomogeneousSymmetric

open Finset Multiset Sym

variable [DecidableEq σ] [DecidableEq τ]

/-- The `n`th complete homogeneous symmetric `MvPolynomial σ R`. -/
def hsymm (n : ℕ) : MvPolynomial σ R := ∑ s : Sym σ n, (s.1.map X).prod

lemma hsymm_def (n : ℕ) : hsymm σ R n = ∑ s : Sym σ n, (s.1.map X).prod := rfl

/--
`hsymmMu` is the product of the symmetric polynomials `hsymm μᵢ`,
where `μ = (μ₁, μ₂, ...)` is a partition.
-/
def hsymmMu {n : ℕ} (μ : n.Partition) : MvPolynomial σ R :=
  muProduct σ R (hsymm σ R) μ

lemma hsymmMu_def {n : ℕ} (μ : n.Partition) : hsymmMu σ R μ =
    Multiset.prod (μ.parts.map (hsymm σ R)) := rfl

@[simp]
theorem hsymm_zero : hsymm σ R 0 = 1 := by
  simp only [hsymm, univ_unique, eq_nil_of_card_zero, val_eq_coe, Sym.coe_nil, Multiset.map_zero,
    prod_zero, sum_const, Finset.card_singleton, one_smul]

@[simp]
theorem hsymm_one : hsymm σ R 1 = ∑ i, X i := by
  simp only [hsymm, univ_unique]
  symm
  apply Fintype.sum_equiv oneEquiv
  intro i
  simp only [oneEquiv_apply, Multiset.map_singleton, Multiset.prod_singleton]

theorem hsymmMu_zero : hsymmMu σ R (Nat.Partition.indiscrete 0) = 1 := by
  simp only [hsymmMu, hsymm_zero, muProduct_zero]

@[simp]
theorem hsymmMu_onePart (n : ℕ) : hsymmMu σ R (Nat.Partition.indiscrete n) = hsymm σ R n := by
  cases n
  · simp only [hsymmMu, hsymm_zero, muProduct_zero]
  · simp only [hsymmMu, gt_iff_lt, Nat.zero_lt_succ, muProduct_onePart]

theorem map_hsymm (n : ℕ) (f : R →+* S) : map f (hsymm σ R n) = hsymm σ S n := by
  simp_rw [hsymm, map_sum, ← Multiset.prod_hom']
  simp only [val_eq_coe, map_X]

theorem rename_hsymm (n : ℕ) (e : σ ≃ τ) : rename e (hsymm σ R n) = hsymm τ R n := by
  simp_rw [hsymm, map_sum, ← prod_hom', rename_X]
  apply Fintype.sum_equiv (equivCongr e)
  simp only [val_eq_coe, equivCongr_apply, Sym.coe_map, Multiset.map_map, Function.comp_apply,
    implies_true]

theorem hsymm_isSymmetric (n : ℕ) : IsSymmetric (hsymm σ R n) := rename_hsymm _ _ n

end CompleteHomogeneousSymmetric

section PowerSum

open Finset

/-- The degree-`n` power sum -/
def psum (n : ℕ) : MvPolynomial σ R := ∑ i, X i ^ n

lemma psum_def (n : ℕ) : psum σ R n = ∑ i, X i ^ n := rfl

/--
`psumMu` is the product of the symmetric polynomials `psum μᵢ`,
where `μ = (μ₁, μ₂, ...)` is a partition.
-/
def psumMu {n : ℕ} (μ : n.Partition) : MvPolynomial σ R :=
  muProduct σ R (psum σ R) μ

lemma psumMu_def {n : ℕ} (μ : n.Partition) : psumMu σ R μ =
    Multiset.prod (μ.parts.map (psum σ R)) := rfl

@[simp]
theorem psum_zero : psum σ R 0 = Fintype.card σ := by
  simp [psum, _root_.pow_zero, ← cast_card]
  rfl

@[simp]
theorem psum_one : psum σ R 1 = ∑ i, X i := by
  simp only [psum, _root_.pow_one]

@[simp]
theorem psumMu_zero : psumMu σ R (Nat.Partition.indiscrete 0) = 1 := by
  simp only [psumMu, muProduct_zero]

@[simp]
theorem psumMu_onePart (n : ℕ) (npos : n > 0) :
    psumMu σ R (Nat.Partition.indiscrete n) = psum σ R n := by
  simp only [psumMu, npos, muProduct_onePart]

@[simp]
theorem rename_psum (n : ℕ) (e : σ ≃ τ) : rename e (psum σ R n) = psum τ R n := by
  simp_rw [psum, map_sum, map_pow, rename_X, e.sum_comp (X · ^ n)]

theorem psum_isSymmetric (n : ℕ) : IsSymmetric (psum σ R n) := rename_psum _ _ n

end PowerSum

section MonomialSymmetric
-- open Multiset

variable [DecidableEq σ] [DecidableEq τ]

/-- The monomial symmetric `MvPolynomial σ R` with exponent set μ. -/
def msymm {n : ℕ} (μ : n.Partition) : MvPolynomial σ R :=
  ∑ s : {a : Sym σ n // Nat.Partition.ofSym a = μ},  (s.1.1.map X).prod

lemma msymm_def {n : ℕ} (μ : n.Partition) : msymm σ R μ =
    ∑ s : {a : Sym σ n // Nat.Partition.ofSym a = μ}, (s.1.1.map X).prod := rfl

@[simp]
theorem msymm_zero : msymm σ R (Nat.Partition.indiscrete 0) = 1 := by
  rw [msymm, Fintype.sum_subsingleton]
  swap
  exact ⟨(Sym.nil : Sym σ 0), by rfl⟩
  simp only [Sym.val_eq_coe, Sym.coe_nil, Multiset.map_zero, Multiset.prod_zero]

@[simp]
theorem msymm_one : msymm σ R (Nat.Partition.indiscrete 1) = ∑ i, X i := by
  symm
  let f : σ ≃ { a // Nat.Partition.ofSym a = Nat.Partition.indiscrete 1 } := {
    toFun := fun a => ⟨Sym.oneEquiv a, by ext; simp⟩
    invFun := fun a => Sym.oneEquiv.symm a.1
    left_inv := by intro a; simp only [Sym.oneEquiv_apply]; rfl
    right_inv := by intro a; simp only [Equiv.apply_symm_apply, Subtype.coe_eta]
  }
  apply Fintype.sum_equiv f
  intro i
  have : (X i : MvPolynomial σ R) = Multiset.prod (Multiset.map X {i}) := by
    simp only [Multiset.map_singleton, Multiset.prod_singleton]
  rw [this]
  rfl

@[simp]
theorem rename_msymm {n : ℕ} (μ : n.Partition) (e : σ ≃ τ) :
    rename e (msymm σ R μ) = msymm τ R μ := by
  simp only [msymm._eq_1, Sym.val_eq_coe, map_sum]
  let f : {a : Sym σ n // Nat.Partition.ofSym a = μ} ≃ {a : Sym τ n // Nat.Partition.ofSym a = μ} :=
  {
    toFun := fun a => ⟨Sym.equivCongr e a, by
      simp only [Sym.equivCongr_apply, Nat.Partition.ofSymEquiv, a.2]⟩
    invFun := fun a => ⟨Sym.equivCongr e.symm a, by
      simp only [Sym.equivCongr_apply, Nat.Partition.ofSymEquiv, a.2]⟩
    left_inv := by intro a; simp
    right_inv := by intro a; simp
  }
  apply Fintype.sum_equiv f
  intro a
  rw [← Multiset.prod_hom, Multiset.map_map]
  congr
  simp only [Sym.equivCongr_apply, Equiv.coe_fn_mk, Sym.coe_map, Multiset.map_map,
    Function.comp_apply, rename_X, f]

theorem msymm_isSymmetric {n : ℕ} (μ : n.Partition) : IsSymmetric (msymm σ R μ) :=
 rename_msymm _ _ μ

end MonomialSymmetric

end MvPolynomial
