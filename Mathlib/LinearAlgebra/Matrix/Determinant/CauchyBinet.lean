/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Cauchy–Binet formula

For a rectangular pair `A : Matrix m n R`, `B : Matrix n m R` over a commutative ring,
the determinant of the (square) product `A * B` is the sum, over all `Fintype.card m`-element
subsets `S` of `n`, of the products of the two maximal minors selected by `S`:

`det (A * B) = ∑ S, det (A.submatrix e.symm (S.orderEmbOfFin _)) *
  det (B.submatrix (S.orderEmbOfFin _) e.symm)`

where `e : m ≃ Fin (Fintype.card m)` is the canonical enumeration and `S.orderEmbOfFin`
enumerates `S` in increasing order. If `Fintype.card m > Fintype.card n` the sum is empty and
the determinant vanishes; if `m ≃ n` the formula reduces to `det_mul`.

## Main results

* `Matrix.det_mul_eq_sum_det_submatrix_mul_prod`: the Leibniz-type expansion of `det (A * B)`
  over *all* index functions `g : m → n`, with the column-minor `det (A.submatrix id g)`
  weighted by `∏ i, B (g i) i`.
* `Matrix.det_mul_cauchyBinet`: the Cauchy–Binet formula.

## Implementation notes

The proof expands `det (A * B)` over all functions `g : m → n`
(`det_mul_eq_sum_det_submatrix_mul_prod`), discards the non-injective `g` (a repeated column),
and groups the injective ones by their image `S`: summing over the `(Fintype.card m)!`
relabellings of the columns of one minor reassembles the determinant of the other
(`Matrix.fiberSum`). A linear order on `n` is required only to name the sorted minors.
-/

@[expose] public section

open Equiv Finset

namespace Matrix

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]

/-- Leibniz-type expansion of the determinant of a product: `det (A * B)` is the sum, over
*all* index functions `g : m → n`, of the column-minor `det (A.submatrix id g)` weighted by
`∏ i, B (g i) i`. This is the Cauchy–Binet formula before grouping the functions `g` by their
image. -/
theorem det_mul_eq_sum_det_submatrix_mul_prod (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det = ∑ g : m → n, (A.submatrix id g).det * ∏ i, B (g i) i := by
  conv_lhs => rw [det_apply']
  simp_rw [mul_apply, Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [det_apply', Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id_eq, Finset.prod_mul_distrib]
  ring

omit [Fintype n] in
/-- For a fixed column indexing `φ : Fin (card m) → n`, summing the summand of
`det_mul_eq_sum_det_submatrix_mul_prod` over all relabellings `π` of those columns rebuilds the
product of the two minors: the `A`-minor carries `sign π`, and summing the plain `B`-products
against that sign reconstructs the `B`-determinant. Holds for any `φ`. -/
private theorem fiberSum (A : Matrix m n R) (B : Matrix n m R)
    (φ : Fin (Fintype.card m) → n) :
    ∑ π : Equiv.Perm (Fin (Fintype.card m)),
        (A.submatrix id fun j => φ (π (Fintype.equivFin m j))).det
          * ∏ i, B (φ (π (Fintype.equivFin m i))) i
      = (A.submatrix (Fintype.equivFin m).symm φ).det
          * (B.submatrix φ (Fintype.equivFin m).symm).det := by
  set e := Fintype.equivFin m
  have hA : ∀ π : Equiv.Perm (Fin (Fintype.card m)),
      (A.submatrix id fun j => φ (π (e j))).det
        = ((Equiv.Perm.sign π : ℤ) : R) * (A.submatrix e.symm φ).det := by
    intro π
    have e1 : (A.submatrix id fun j => φ (π (e j)))
        = ((A.submatrix e.symm φ).submatrix id ⇑π).submatrix ⇑e ⇑e := by
      ext i j; simp [submatrix_apply]
    rw [e1, Matrix.det_submatrix_equiv_self e, det_permute']
  have hB : ∀ π : Equiv.Perm (Fin (Fintype.card m)),
      (∏ i, B (φ (π (e i))) i) = ∏ a, B (φ (π a)) (e.symm a) :=
    fun π => Fintype.prod_equiv e _ _ fun i => by simp
  simp_rw [hA, hB]
  rw [det_apply' (B.submatrix φ e.symm), Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  simp only [submatrix_apply]
  ring

section Regroup

variable [LinearOrder n]

omit [DecidableEq m] [Fintype n] in
private theorem card_image_univ {g : m → n} (hg : Function.Injective g) :
    (Finset.image g Finset.univ).card = Fintype.card m := by
  rw [Finset.card_image_of_injective _ hg, Finset.card_univ]

/-- The permutation of `Fin (card m)` recovered from an injective `g : m → n`: it relabels the
sorted image `S = image g` so that `S.orderEmbOfFin ∘ cbPerm ∘ equivFin = g`. -/
private noncomputable def cbPerm {g : m → n} (hg : Function.Injective g) :
    Equiv.Perm (Fin (Fintype.card m)) :=
  Equiv.ofBijective
    (fun a => ((Finset.image g Finset.univ).orderIsoOfFin (card_image_univ hg)).symm
      ⟨g ((Fintype.equivFin m).symm a), Finset.mem_image_of_mem g (Finset.mem_univ _)⟩)
    (Function.Injective.bijective_of_finite (by
      intro a b hab
      have h3 := ((Finset.image g Finset.univ).orderIsoOfFin
        (card_image_univ hg)).symm.injective hab
      exact (Fintype.equivFin m).symm.injective (hg (Subtype.ext_iff.mp h3))))

omit [DecidableEq m] [Fintype n] in
private theorem cbPerm_spec {g : m → n} (hg : Function.Injective g) (j : m) :
    (Finset.image g Finset.univ).orderEmbOfFin (card_image_univ hg)
      (cbPerm hg (Fintype.equivFin m j)) = g j := by
  rw [← Finset.coe_orderIsoOfFin_apply]
  simp only [cbPerm, Equiv.ofBijective_apply, Equiv.symm_apply_apply,
    OrderIso.apply_symm_apply]

omit [DecidableEq m] [Fintype n] in
private theorem image_comp_orderEmbOfFin (S : Finset n) (hS : S.card = Fintype.card m)
    (π : Equiv.Perm (Fin (Fintype.card m))) :
    Finset.image (fun j => S.orderEmbOfFin hS (π (Fintype.equivFin m j))) Finset.univ = S := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩; exact S.orderEmbOfFin_mem hS _
  · intro hx
    have hx' : x ∈ Finset.image (S.orderEmbOfFin hS) Finset.univ := by
      rw [Finset.image_orderEmbOfFin_univ]; exact hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx'
    obtain ⟨a, ha⟩ := hx'
    exact ⟨(Fintype.equivFin m).symm (π.symm a), by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact ha⟩

/-- **The Cauchy–Binet formula.** The determinant of `A * B`, for a rectangular pair
`A : Matrix m n R` and `B : Matrix n m R`, is the sum over all `Fintype.card m`-element
subsets `S` of `n` of the product of the two maximal minors with columns (resp. rows)
selected by `S` in increasing order. -/
theorem det_mul_cauchyBinet (A : Matrix m n R) (B : Matrix n m R) :
    (A * B).det =
      ∑ S : {s : Finset n // s.card = Fintype.card m},
        (A.submatrix (Fintype.equivFin m).symm (S.1.orderEmbOfFin S.2)).det *
        (B.submatrix (S.1.orderEmbOfFin S.2) (Fintype.equivFin m).symm).det := by
  classical
  rw [det_mul_eq_sum_det_submatrix_mul_prod]
  simp_rw [← fiberSum A B]
  rw [Finset.sum_sigma']
  have hvanish : ∀ g : m → n, ¬ Function.Injective g →
      (A.submatrix id g).det * ∏ i, B (g i) i = 0 := by
    intro g hg
    rw [Function.not_injective_iff] at hg
    obtain ⟨a, b, hgab, hab⟩ := hg
    rw [det_zero_of_column_eq hab fun x => by simp [submatrix_apply, hgab], zero_mul]
  rw [← Finset.sum_subset (Finset.filter_subset (fun g => Function.Injective g) Finset.univ)
    (fun g _ hgf => hvanish g fun hinj => hgf (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinj⟩))]
  symm
  refine Finset.sum_bij
    (fun p _ => fun j => p.1.1.orderEmbOfFin p.1.2 (p.2 (Fintype.equivFin m j)))
    ?hi ?inj ?surj ?h
  case hi =>
    intro p _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun a b hab => ?_⟩
    exact (Fintype.equivFin m).injective
      (p.2.injective ((p.1.1.orderEmbOfFin p.1.2).injective hab))
  case inj =>
    rintro ⟨⟨S1, hS1⟩, π1⟩ _ ⟨⟨S2, hS2⟩, π2⟩ _ heq
    dsimp only at heq
    have hSeq : S1 = S2 := by
      rw [← image_comp_orderEmbOfFin S1 hS1 π1, ← image_comp_orderEmbOfFin S2 hS2 π2, heq]
    subst hSeq
    have hπ : π1 = π2 := by
      refine Equiv.ext fun a => ?_
      have h3 := congrFun heq ((Fintype.equivFin m).symm a)
      simp only [Equiv.apply_symm_apply] at h3
      exact (S1.orderEmbOfFin hS1).injective h3
    rw [hπ]
  case surj =>
    intro g hg
    rw [Finset.mem_filter] at hg
    refine ⟨⟨⟨Finset.image g Finset.univ, card_image_univ hg.2⟩, cbPerm hg.2⟩,
      Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
    funext j
    exact cbPerm_spec hg.2 j
  case h =>
    intro p _
    rfl

end Regroup

end Matrix
