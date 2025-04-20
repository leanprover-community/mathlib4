/-
Copyright (c) 2020 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang, Johan Commelin
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Combinatorics.Enumerative.Partition

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

theorem _root_.Finset.esymm_map_val {σ} (f : σ → R) (s : Finset σ) (n : ℕ) :
    (s.val.map f).esymm n = (s.powersetCard n).sum fun t => t.prod f := by
  simp only [esymm, powersetCard_map, ← Finset.map_val_val_powersetCard, map_map]
  rfl

lemma pow_smul_esymm {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R]
    [SMulCommClass S R R] (s : S) (n : ℕ) (m : Multiset R) :
    s ^ n • m.esymm n = (m.map (s • ·)).esymm n := by
  rw [esymm, smul_sum, map_map]
  trans ((powersetCard n m).map (fun x : Multiset R ↦ s ^ card x • x.prod)).sum
  · refine congr_arg _ (map_congr rfl (fun x hx ↦ ?_))
    rw [Function.comp_apply, (mem_powersetCard.1 hx).2]
  · simp_rw [smul_prod, esymm, powersetCard_map, map_map, Function.comp_def]

-- TODO: `Multiset.insert_eq_cons` being simp means that `esymm {x, y}` is not simp normal form
@[simp] lemma esymm_pair_one (x y : R) :
    esymm (x ::ₘ {y}) 1 = x + y := by
  simp [esymm, powersetCard_one, add_comm]

@[simp] lemma esymm_pair_two (x y : R) :
    esymm (x ::ₘ {y}) 2 = x * y := by
  simp [esymm, powersetCard_one]

end Multiset

namespace MvPolynomial

variable {σ τ : Type*} {R S : Type*}

/-- A `MvPolynomial φ` is symmetric if it is invariant under
permutations of its variables by the `rename` operation -/
def IsSymmetric [CommSemiring R] (φ : MvPolynomial σ R) : Prop :=
  ∀ e : Perm σ, rename e φ = φ

/-- The subalgebra of symmetric `MvPolynomial`s. -/
def symmetricSubalgebra (σ R : Type*) [CommSemiring R] : Subalgebra R (MvPolynomial σ R) where
  carrier := setOf IsSymmetric
  algebraMap_mem' r e := rename_C e r
  mul_mem' ha hb e := by rw [map_mul, ha, hb]
  add_mem' ha hb e := by rw [map_add, ha, hb]

@[simp]
theorem mem_symmetricSubalgebra [CommSemiring R] (p : MvPolynomial σ R) :
    p ∈ symmetricSubalgebra σ R ↔ p.IsSymmetric :=
  Iff.rfl

namespace IsSymmetric

section CommSemiring

variable [CommSemiring R] [CommSemiring S] {φ ψ : MvPolynomial σ R}

@[simp]
theorem C (r : R) : IsSymmetric (C r : MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).algebraMap_mem r

@[simp]
theorem zero : IsSymmetric (0 : MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).zero_mem

@[simp]
theorem one : IsSymmetric (1 : MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).one_mem

theorem add (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ + ψ) :=
  (symmetricSubalgebra σ R).add_mem hφ hψ

theorem mul (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ * ψ) :=
  (symmetricSubalgebra σ R).mul_mem hφ hψ

theorem smul (r : R) (hφ : IsSymmetric φ) : IsSymmetric (r • φ) :=
  (symmetricSubalgebra σ R).smul_mem hφ r

@[simp]
theorem map (hφ : IsSymmetric φ) (f : R →+* S) : IsSymmetric (map f φ) := fun e => by
  rw [← map_rename, hφ]

protected theorem rename (hφ : φ.IsSymmetric) (e : σ ≃ τ) : (rename e φ).IsSymmetric := fun _ => by
  apply rename_injective _ e.symm.injective
  simp_rw [rename_rename, ← Equiv.coe_trans, Equiv.self_trans_symm, Equiv.coe_refl, rename_id_apply]
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

theorem sub (hφ : IsSymmetric φ) (hψ : IsSymmetric ψ) : IsSymmetric (φ - ψ) :=
  (symmetricSubalgebra σ R).sub_mem hφ hψ

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

section ElementarySymmetric

open Finset

/-- The `n`th elementary symmetric `MvPolynomial σ R`.
It is the sum over all the degree n squarefree monomials in `MvPolynomial σ R`. -/
def esymm (n : ℕ) : MvPolynomial σ R :=
  ∑ t ∈ powersetCard n univ, ∏ i ∈ t, X i

/--
`esymmPart` is the product of the symmetric polynomials `esymm μᵢ`,
where `μ = (μ₁, μ₂, ...)` is a partition.
-/
def esymmPart {n : ℕ} (μ : n.Partition) : MvPolynomial σ R := (μ.parts.map (esymm σ R)).prod

/-- The `n`th elementary symmetric `MvPolynomial σ R` is obtained by evaluating the
`n`th elementary symmetric at the `Multiset` of the monomials -/
theorem esymm_eq_multiset_esymm : esymm σ R = (univ.val.map X).esymm := by
  exact funext fun n => (esymm_map_val X _ n).symm

theorem aeval_esymm_eq_multiset_esymm [Algebra R S] (n : ℕ) (f : σ → S) :
    aeval f (esymm σ R n) = (univ.val.map f).esymm n := by
  simp_rw [esymm, aeval_sum, aeval_prod, aeval_X, esymm_map_val]

/-- We can define `esymm σ R n` by summing over a subtype instead of over `powerset_len`. -/
theorem esymm_eq_sum_subtype (n : ℕ) :
    esymm σ R n = ∑ t : {s : Finset σ // #s = n}, ∏ i ∈ (t : Finset σ), X i :=
  sum_subtype _ (fun _ => mem_powersetCard_univ) _

/-- We can define `esymm σ R n` as a sum over explicit monomials -/
theorem esymm_eq_sum_monomial (n : ℕ) :
    esymm σ R n = ∑ t ∈ powersetCard n univ, monomial (∑ i ∈ t, Finsupp.single i 1) 1 := by
  simp_rw [monomial_sum_one]
  rfl

@[simp]
theorem esymm_zero : esymm σ R 0 = 1 := by
  simp only [esymm, powersetCard_zero, sum_singleton, prod_empty]

@[simp]
theorem esymm_one : esymm σ R 1 = ∑ i, X i := by simp [esymm, powersetCard_one]

theorem esymmPart_zero : esymmPart σ R (.indiscrete 0) = 1 := by simp [esymmPart]

@[simp]
theorem esymmPart_indiscrete (n : ℕ) : esymmPart σ R (.indiscrete n) = esymm σ R n := by
  cases n <;> simp [esymmPart]

theorem map_esymm (n : ℕ) (f : R →+* S) : map f (esymm σ R n) = esymm σ S n := by
  simp_rw [esymm, map_sum, map_prod, map_X]

theorem rename_esymm (n : ℕ) (e : σ ≃ τ) : rename e (esymm σ R n) = esymm τ R n :=
  calc
    rename e (esymm σ R n) = ∑ x ∈ powersetCard n univ, ∏ i ∈ x, X (e i) := by
      simp_rw [esymm, map_sum, map_prod, rename_X]
    _ = ∑ t ∈ powersetCard n (univ.map e.toEmbedding), ∏ i ∈ t, X i := by
      simp [powersetCard_map, -map_univ_equiv]
      -- Porting note: Why did `mapEmbedding_apply` not work?
      dsimp [mapEmbedding, OrderEmbedding.ofMapLEIff]
      simp
    _ = ∑ t ∈ powersetCard n univ, ∏ i ∈ t, X i := by rw [map_univ_equiv]

theorem esymm_isSymmetric (n : ℕ) : IsSymmetric (esymm σ R n) := by
  intro
  rw [rename_esymm]

theorem support_esymm'' [DecidableEq σ] [Nontrivial R] (n : ℕ) :
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

theorem support_esymm' [DecidableEq σ] [Nontrivial R] (n : ℕ) : (esymm σ R n).support =
    (powersetCard n (univ : Finset σ)).biUnion fun t => {∑ i ∈ t, Finsupp.single i 1} := by
  rw [support_esymm'']
  congr
  funext
  exact Finsupp.support_single_ne_zero _ one_ne_zero

theorem support_esymm [DecidableEq σ] [Nontrivial R] (n : ℕ) : (esymm σ R n).support =
    (powersetCard n (univ : Finset σ)).image fun t => ∑ i ∈ t, Finsupp.single i 1 := by
  rw [support_esymm']
  exact biUnion_singleton

theorem degrees_esymm [Nontrivial R] {n : ℕ} (hpos : 0 < n) (hn : n ≤ Fintype.card σ) :
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

end ElementarySymmetric

section CompleteHomogeneousSymmetric

open Finset Multiset Sym

variable [DecidableEq σ] [DecidableEq τ]

/-- The `n`th complete homogeneous symmetric `MvPolynomial σ R`.
It is the sum over all the degree n monomials in `MvPolynomial σ R`. -/
def hsymm (n : ℕ) : MvPolynomial σ R := ∑ s : Sym σ n, (s.1.map X).prod

/-- `hsymmPart` is the product of the symmetric polynomials `hsymm μᵢ`,
where `μ = (μ₁, μ₂, ...)` is a partition. -/
def hsymmPart {n : ℕ} (μ : n.Partition) : MvPolynomial σ R := (μ.parts.map (hsymm σ R)).prod

@[simp]
theorem hsymm_zero : hsymm σ R 0 = 1 := by simp [hsymm, eq_nil_of_card_zero]

@[simp]
theorem hsymm_one : hsymm σ R 1 = ∑ i, X i := by
  symm
  apply Fintype.sum_equiv oneEquiv
  simp only [oneEquiv_apply, Multiset.map_singleton, Multiset.prod_singleton, implies_true]

theorem hsymmPart_zero : hsymmPart σ R (.indiscrete 0) = 1 := by simp [hsymmPart]

@[simp]
theorem hsymmPart_indiscrete (n : ℕ) : hsymmPart σ R (.indiscrete n) = hsymm σ R n := by
  cases n <;> simp [hsymmPart]

theorem map_hsymm (n : ℕ) (f : R →+* S) : map f (hsymm σ R n) = hsymm σ S n := by
  simp [hsymm, ← Multiset.prod_hom']

theorem rename_hsymm (n : ℕ) (e : σ ≃ τ) : rename e (hsymm σ R n) = hsymm τ R n := by
  simp_rw [hsymm, map_sum, ← prod_hom', rename_X]
  apply Fintype.sum_equiv (equivCongr e)
  simp

theorem hsymm_isSymmetric (n : ℕ) : IsSymmetric (hsymm σ R n) := rename_hsymm _ _ n

end CompleteHomogeneousSymmetric

section PowerSum

open Finset

/-- The degree-`n` power sum symmetric `MvPolynomial σ R`.
It is the sum over all the `n`-th powers of the variables. -/
def psum (n : ℕ) : MvPolynomial σ R := ∑ i, X i ^ n

/-- `psumPart` is the product of the symmetric polynomials `psum μᵢ`,
where `μ = (μ₁, μ₂, ...)` is a partition. -/
def psumPart {n : ℕ} (μ : n.Partition) : MvPolynomial σ R := (μ.parts.map (psum σ R)).prod

@[simp]
theorem psum_zero : psum σ R 0 = Fintype.card σ := by simp [psum]

@[simp]
theorem psum_one : psum σ R 1 = ∑ i, X i := by simp [psum]

@[simp]
theorem psumPart_zero : psumPart σ R (.indiscrete 0) = 1 := by simp [psumPart]

@[simp]
theorem psumPart_indiscrete {n : ℕ} (npos : n ≠ 0) :
    psumPart σ R (.indiscrete n) = psum σ R n := by simp [psumPart, npos]

@[simp]
theorem rename_psum (n : ℕ) (e : σ ≃ τ) : rename e (psum σ R n) = psum τ R n := by
  simp_rw [psum, map_sum, map_pow, rename_X, e.sum_comp (X · ^ n)]

theorem psum_isSymmetric (n : ℕ) : IsSymmetric (psum σ R n) := rename_psum _ _ n

end PowerSum

section MonomialSymmetric

variable [DecidableEq σ] [DecidableEq τ] {n : ℕ}

/-- The monomial symmetric `MvPolynomial σ R` with exponent set μ.
It is the sum over all the monomials in `MvPolynomial σ R` such that
the multiset of exponents is equal to the multiset of parts of μ. -/
def msymm (μ : n.Partition) : MvPolynomial σ R :=
  ∑ s : {a : Sym σ n // .ofSym a = μ}, (s.1.1.map X).prod

@[simp]
theorem msymm_zero : msymm σ R (.indiscrete 0) = 1 := by
  rw [msymm, Fintype.sum_subsingleton _ ⟨(Sym.nil : Sym σ 0), rfl⟩]
  simp

@[simp]
theorem msymm_one : msymm σ R (.indiscrete 1) = ∑ i, X i := by
  have : (fun (x : Sym σ 1) ↦ x ∈ Set.univ) =
      (fun x ↦ Nat.Partition.ofSym x = Nat.Partition.indiscrete 1) := by
    simp_rw [Set.mem_univ, Nat.Partition.ofSym_one]
  symm
  rw [Fintype.sum_equiv (Equiv.trans Sym.oneEquiv (Equiv.Set.univ (Sym σ 1)).symm)
    _ (fun s ↦ (s.1.1.map X).prod)]
  · apply Fintype.sum_equiv (Equiv.subtypeEquivProp this)
    intro x
    congr
  · intro x
    rw [← Multiset.prod_singleton (X x), ← Multiset.map_singleton]
    congr

@[simp]
theorem rename_msymm (μ : n.Partition) (e : σ ≃ τ) :
    rename e (msymm σ R μ) = msymm τ R μ := by
  rw [msymm, map_sum]
  apply Fintype.sum_equiv (Nat.Partition.ofSymShapeEquiv μ e)
  intro
  rw [← Multiset.prod_hom, Multiset.map_map, Nat.Partition.ofSymShapeEquiv]
  simp

theorem msymm_isSymmetric (μ : n.Partition) : IsSymmetric (msymm σ R μ) :=
  rename_msymm _ _ μ

end MonomialSymmetric

end MvPolynomial
