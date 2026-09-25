/-
Copyright (c) 2026 Rizwan Gulzar Mir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rizwan Gulzar Mir
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The Cauchy–Binet formula

This file proves the Cauchy–Binet formula: for an `m × n` matrix `A` and an `n × m` matrix `B`
with `m ≤ n`, the determinant of the `m × m` product `A * B` is a sum, over the
`m`-element subsets `S` of the column/row index set, of the products of the corresponding
`m × m` minors `det (A_S) * det (B_S)`.

## Main statement

* `Matrix.det_mul_eq_sum_det_submatrix`: the Cauchy–Binet formula.

## Implementation notes

For a subset `S` of `Fin n` with `S.card = m`, the minor `A_S` is formed using
`S.orderIsoOfFin`, the order-preserving bijection `Fin m ≃o S` coming from the ambient linear
order on `Fin n`. Any other choice of bijection `Fin m ≃ S` would give the same value of
`det A_S * det B_S`, since permuting the enumeration multiplies both factors by the same sign,
which then squares to `1`; the order-preserving choice is used here only because it is
canonical and already available in Mathlib (`Finset.orderIsoOfFin`).

## References

* Cauchy–Binet formula, https://en.wikipedia.org/wiki/Cauchy%E2%80%93Binet_formula
-/

@[expose] public section

open Finset

namespace Matrix

variable {R : Type*} [CommRing R] {m n : ℕ}

/-- **The Cauchy–Binet formula.** For `A : Matrix (Fin m) (Fin n) R` and
`B : Matrix (Fin n) (Fin m) R` with `m ≤ n`, the determinant of `A * B` equals the sum, over
`m`-element subsets `S` of `Fin n`, of the product of the two `m × m` minors of `A` and `B`
obtained by restricting to the columns
(respectively rows) indexed by `S`. -/
theorem det_mul_eq_sum_det_submatrix (_hmn : m ≤ n) (A : Matrix (Fin m) (Fin n) R)
    (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = ∑ S ∈ (univ : Finset (Fin n)).powersetCard m,
      if hS : S.card = m then
        (A.submatrix id (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n))).det *
          (B.submatrix (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n)) id).det
      else 0 := by
  have hstep1 : (A * B).det = ∑ r : Fin m → Fin n,
      (∏ i : Fin m, A i (r i)) * (Matrix.of (fun i : Fin m => B (r i))).det := by
    have hrow : ∀ i : Fin m, (A * B) i = ∑ k : Fin n, A i k • (B k) := by
      intro i
      funext j
      simp [Matrix.mul_apply, Pi.smul_apply, smul_eq_mul]
    calc (A * B).det = Matrix.detRowAlternating (fun i => (A * B) i) := rfl
      _ = Matrix.detRowAlternating (fun i => ∑ k : Fin n, A i k • (B k)) := by
          congr 1; funext i; exact hrow i
      _ = ∑ r : Fin m → Fin n, Matrix.detRowAlternating (fun i => A i (r i) • B (r i)) :=
          MultilinearMap.map_sum _ _
      _ = ∑ r : Fin m → Fin n,
            (∏ i : Fin m, A i (r i)) * (Matrix.of (fun i : Fin m => B (r i))).det := by
          apply Finset.sum_congr rfl
          intro r _
          have := Matrix.detRowAlternating.map_smul_univ (fun i : Fin m => A i (r i))
            (fun i : Fin m => B (r i))
          rw [smul_eq_mul] at this
          rw [this]
          rfl
  set F : (Fin m → Fin n) → R :=
    fun r => (∏ i : Fin m, A i (r i)) * (Matrix.of (fun i : Fin m => B (r i))).det with hF
  have hstep2 : ∀ r : Fin m → Fin n, ¬ Function.Injective r → F r = 0 := by
    intro r hr
    obtain ⟨p, q, hpq, hne⟩ := Function.not_injective_iff.mp hr
    simp only [hF]
    have heqrow :
        (Matrix.of (fun k : Fin m => B (r k))) p = (Matrix.of (fun k : Fin m => B (r k))) q := by
      change B (r p) = B (r q)
      rw [hpq]
    rw [Matrix.det_zero_of_row_eq hne heqrow]
    ring
  have hstep3 : (∑ r : Fin m → Fin n, F r)
      = ∑ r ∈ (univ : Finset (Fin m → Fin n)).filter Function.Injective, F r := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : Function.Injective r
    · simp [hr]
    · simp [hr, hstep2 r hr]
  have hmaps : ∀ r ∈ (univ : Finset (Fin m → Fin n)).filter Function.Injective,
      Finset.image r univ ∈ (univ : Finset (Fin n)).powersetCard m := by
    intro r hr
    rw [Finset.mem_filter] at hr
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ hr.2, Finset.card_univ, Fintype.card_fin]
  have hstep4 : (∑ r ∈ (univ : Finset (Fin m → Fin n)).filter Function.Injective, F r)
      = ∑ S ∈ (univ : Finset (Fin n)).powersetCard m,
          ∑ r ∈ ((univ : Finset (Fin m → Fin n)).filter Function.Injective).filter
              (fun r => Finset.image r univ = S), F r := by
    rw [Finset.sum_fiberwise_of_maps_to hmaps F]
  have hstep5 : ∀ S ∈ (univ : Finset (Fin n)).powersetCard m,
      (∑ r ∈ ((univ : Finset (Fin m → Fin n)).filter Function.Injective).filter
              (fun r => Finset.image r univ = S), F r)
      = (if hS : S.card = m then
          (A.submatrix id (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n))).det *
            (B.submatrix (fun i : Fin m => (S.orderIsoOfFin hS i : Fin n)) id).det
        else 0) := by
    intro S hS_mem
    have hS : S.card = m := (Finset.mem_powersetCard.mp hS_mem).2
    rw [dif_pos hS]
    set coeσ : Fin m → Fin n := fun i => (S.orderIsoOfFin hS i : Fin n) with hcoeσ
    have hcoeσ_inj : Function.Injective coeσ := by
      intro i j hij
      exact (S.orderIsoOfFin hS).injective (Subtype.ext hij)
    have hcoeσ_mem : ∀ i, coeσ i ∈ S := fun i => (S.orderIsoOfFin hS i).2
    have hcoeσ_image : Finset.image coeσ univ = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
        rw [← hi]; exact hcoeσ_mem i
      · rw [Finset.card_image_of_injective _ hcoeσ_inj, Finset.card_univ, Fintype.card_fin, hS]
    set As : Matrix (Fin m) (Fin m) R := A.submatrix id coeσ with hAs
    set Bs : Matrix (Fin m) (Fin m) R := B.submatrix coeσ id with hBs
    set fiber : Finset (Fin m → Fin n) :=
      ((univ : Finset (Fin m → Fin n)).filter Function.Injective).filter
        (fun r => Finset.image r univ = S) with hfiber
    have hmemT : ∀ τ : Equiv.Perm (Fin m), coeσ ∘ τ ∈ fiber := by
      intro τ
      rw [hfiber, Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, hcoeσ_inj.comp τ.injective⟩, ?_⟩
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hx
        rw [← hk]; exact hcoeσ_mem (τ k)
      · rw [Finset.card_image_of_injective _ (hcoeσ_inj.comp τ.injective), Finset.card_univ,
          Fintype.card_fin, hS]
    have hbuild : ∀ r ∈ fiber, ∃ τ : Equiv.Perm (Fin m), coeσ ∘ τ = r := by
      intro r hr
      rw [hfiber, Finset.mem_filter, Finset.mem_filter] at hr
      obtain ⟨⟨-, hrinj⟩, himg⟩ := hr
      have hforward : ∀ k : Fin m, ∃ l : Fin m, coeσ l = r k := by
        intro k
        have hmem : r k ∈ S := by
          rw [← himg]; exact Finset.mem_image_of_mem r (Finset.mem_univ k)
        rw [← hcoeσ_image] at hmem
        obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hmem
        exact ⟨l, hl⟩
      choose g hg using hforward
      have hg_inj : Function.Injective g := by
        intro a b hab
        apply hrinj
        rw [← hg a, ← hg b, hab]
      have hg_bij : Function.Bijective g := (Finite.injective_iff_bijective).mp hg_inj
      exact ⟨Equiv.ofBijective g hg_bij, funext hg⟩
    choose τ_of hτ_of using hbuild
    have huniq : ∀ (r : Fin m → Fin n) (hr : r ∈ fiber) (τ : Equiv.Perm (Fin m)),
        coeσ ∘ τ = r → τ = τ_of r hr := by
      intro r hr τ hτ
      apply Equiv.ext
      intro k
      apply hcoeσ_inj
      have h1 : coeσ (τ k) = r k := congrFun hτ k
      have h2 : coeσ (τ_of r hr k) = r k := congrFun (hτ_of r hr) k
      rw [h1, h2]
    have hbij : (∑ r ∈ fiber, F r) = ∑ τ : Equiv.Perm (Fin m), F (coeσ ∘ τ) := by
      apply Finset.sum_bij' (fun r hr => τ_of r hr) (fun τ _ => coeσ ∘ τ)
      case hi => intro r _; exact Finset.mem_univ _
      case hj => intro τ _; exact hmemT τ
      case left_neg => intro r hr; exact hτ_of r hr
      case right_neg => intro τ _; exact (huniq (coeσ ∘ τ) (hmemT τ) τ rfl).symm
      case h => intro r hr; rw [hτ_of r hr]
    rw [hbij]
    have hBdet : ∀ τ : Equiv.Perm (Fin m), (Matrix.of (fun i : Fin m => B ((coeσ ∘ τ) i))).det
        = Equiv.Perm.sign τ * Bs.det := by
      intro τ
      have heq : (Matrix.of (fun i : Fin m => B ((coeσ ∘ τ) i))) = Bs.submatrix τ id := by
        ext i j
        simp [Bs, Matrix.submatrix_apply]
      rw [heq, Matrix.det_permute]
    have hAsum : As.det =
        ∑ τ : Equiv.Perm (Fin m), Equiv.Perm.sign τ * ∏ i : Fin m, A i ((coeσ ∘ τ) i) := by
      rw [← Matrix.det_transpose As, Matrix.det_apply']
      apply Finset.sum_congr rfl
      intro τ _
      simp [As, Matrix.transpose_apply, Matrix.submatrix_apply, Function.comp_apply]
    calc (∑ τ : Equiv.Perm (Fin m), F (coeσ ∘ τ))
        = ∑ τ : Equiv.Perm (Fin m), (∏ i : Fin m, A i ((coeσ ∘ τ) i)) *
            (Equiv.Perm.sign τ * Bs.det) := by
          apply Finset.sum_congr rfl
          intro τ _
          simp only [hF]
          rw [hBdet τ]
      _ = Bs.det *
            ∑ τ : Equiv.Perm (Fin m), Equiv.Perm.sign τ * ∏ i : Fin m, A i ((coeσ ∘ τ) i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro τ _
          ring
      _ = Bs.det * As.det := by rw [← hAsum]
      _ = As.det * Bs.det := by ring
  rw [hstep1, hstep3, hstep4]
  apply Finset.sum_congr rfl
  intro S hS_mem
  exact hstep5 S hS_mem

end Matrix
