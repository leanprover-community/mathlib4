/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.Algebra.Order.Sub.Unbundled.Hom
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Rat.Floor
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.ModelTheory.Arithmetic.Presburger.Basic
import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Basic
import Mathlib.ModelTheory.Definability
import Mathlib.RingTheory.Localization.Module

/-!
# Presburger definability and semilinear sets

This file defines the semilinear sets and formalizes their equivalence to definability in Presburger
arithemtic. As an application, we prove that the graph of multiplication is not Presburger
definable.

## Main Definitions

- `Set.Linear`: a set is linear if is a finitely generated `ℕ`-submodule added by a single vector
  `v`.
- `Set.Semilinear`: a set is semilinear if it is a finite union of linear sets.
- `Set.ProperLinear`: a linear set is proper if its `ℕ`-submodule generators (periods) are linear
  independent.
- `Set.ProperSemilinear`: a semilinear set is proper if it is a finite union of proper linear sets.

## Main Results

- `Set.Semilinear.proper_semilinear`: every semilinear set is a finite union of proper linear sets.
- `Set.Semilinear` is closed under union, intersection, complement, projection, set addition and
  additive closure.
- `presburger.definable_iff_semilinear`: a set is Presburger definable in `ℕ` if and only if it is
  semilinear.
- `definable₁_iff_ultimately_periodic`: in the 1-dimensional case, a set is Presburger arithmetic
  definable in `ℕ` if and only if it is ultimately periodic, i.e. periodic after some number `k`.
- `presburger.mul_not_definable`: the graph of multiplication is not Presburger definable in `ℕ`.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Seymour Ginsburg and Edwin H. Spanier, *Semigroups, Presburger Formulas, and Languages*][
  ginsburg1966]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}

namespace Set

open Pointwise Submodule Matrix

variable {v : α → ℕ} {s s₁ s₂ : Set (α → ℕ)}

/-- A verison of *Gordan's lemma*: the solution of a homogeneous linear Diophantine equation
  `A *ᵥ x = B *ᵥ x` is a linear set. -/
theorem Linear.of_homogeneous_equation [Fintype β] (A B : Matrix α β ℕ) :
    {x | A *ᵥ x = B *ᵥ x}.Linear := by
  have hpwo := Pi.isPWO {x | A *ᵥ x = B *ᵥ x ∧ x ≠ 0}
  have hantichain := setOf_minimal_antichain {x | A *ᵥ x = B *ᵥ x ∧ x ≠ 0}
  have hfinite := hantichain.finite_of_partiallyWellOrderedOn (hpwo.mono (setOf_minimal_subset _))
  convert span_finset hfinite.toFinset
  ext x
  simp only [Finite.coe_toFinset, mem_setOf_eq, SetLike.mem_coe]
  constructor
  · intro hx₁
    by_cases hx₂ : x = 0
    · simp [hx₂]
    · refine hpwo.wellFoundedOn.induction ⟨hx₁, hx₂⟩ fun y ⟨hy₁, hy₂⟩ ih => ?_
      simp only [mem_setOf_eq, and_imp] at ih
      by_cases hy₃ : Minimal {x | A *ᵥ x = B *ᵥ x ∧ x ≠ 0} y
      · exact mem_span_of_mem hy₃
      · rcases exists_lt_of_not_minimal ⟨hy₁, hy₂⟩ hy₃ with ⟨z, hz₁, hz₂, hz₃⟩
        rw [← tsub_add_cancel_of_le hz₁.le]
        apply add_mem
        · apply ih
          · rw [← tsub_add_cancel_of_le hz₁.le] at hy₁
            simp only [mulVec_add, hz₂, add_right_cancel_iff] at hy₁
            exact hy₁
          · exact (tsub_pos_of_lt hz₁).ne'
          · exact tsub_le_self
          · rw [le_tsub_iff_le_tsub (le_refl _) hz₁.le, tsub_self]
            exact (pos_of_ne_zero hz₃).not_ge
        · exact ih _ hz₂ hz₃ hz₁.le hz₁.not_ge
  · intro hx
    induction hx using span_induction with
    | mem x hx => exact hx.1.1
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [mulVec_add, hx, hy]
    | smul n x _ hx =>
      simp only [mulVec_smul, hx]

lemma Linear.iff_eq_setOf_vadd_mulVec :
    s.Linear ↔ ∃ (v : α → ℕ) (n : ℕ) (A : Matrix α (Fin n) ℕ), s = {v + A *ᵥ x | x} := by
  classical
  constructor
  · rintro ⟨v, t, rfl⟩
    refine ⟨v, t.card, of fun i j => (t.equivFin.symm j).1 i, ?_⟩
    ext x
    simp only [mem_vadd_set, SetLike.mem_coe, vadd_eq_add, mem_setOf_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [mem_span_finset, Function.support_subset_iff, Finset.mem_coe] at hy
      rcases hy with ⟨f, _, rfl⟩
      exists fun i => f (t.equivFin.symm i).1
      simp only [mulVec_eq_sum, op_smul_eq_smul, add_right_inj]
      apply Finset.sum_nbij fun i => (t.equivFin.symm i).1
      · simp
      · simp [Subtype.val_inj]
      · intro z hz
        exists t.equivFin ⟨z, hz⟩
        simp
      · intro i _
        ext j
        simp
    · rintro ⟨f, rfl⟩
      simp only [mulVec_eq_sum, op_smul_eq_smul, add_right_inj, exists_eq_right]
      refine sum_mem fun i _ => smul_mem _ _ (mem_span_of_mem ?_)
      eta_expand
      simp
  · rintro ⟨v, n, A, rfl⟩
    refine ⟨v, (Finset.univ : Finset _).image A.col, ?_⟩
    ext x
    simp [mem_vadd_set, ← range_mulVecLin]

/-- The solution of a linear Diophantine equation `u + A *ᵥ x = v + B *ᵥ x` is a semilinear set. -/
theorem Semilinear.of_linear_equation [Fintype β] (u v : α → ℕ) (A B : Matrix α β ℕ) :
    {x | u + A *ᵥ x = v + B *ᵥ x}.Semilinear := by
  have hpwo := Pi.isPWO {x | u + A *ᵥ x = v + B *ᵥ x}
  have hantichain := setOf_minimal_antichain {x | u + A *ᵥ x = v + B *ᵥ x}
  have hfinite := hantichain.finite_of_partiallyWellOrderedOn (hpwo.mono (setOf_minimal_subset _))
  convert hfinite.semilinear.add (Linear.of_homogeneous_equation A B).semilinear using 1
  ext x
  simp only [mem_setOf_eq, mem_add]
  constructor
  · intro hx
    obtain ⟨y, hy₁, hy₂⟩ := hpwo.exists_le_minimal hx
    refine ⟨y, hy₂, x - y, ?_, add_tsub_cancel_of_le hy₁⟩
    rw [← add_tsub_cancel_of_le hy₁] at hx
    simp only [mulVec_add, ← add_assoc] at hx
    rw [hy₂.1, add_left_cancel_iff] at hx
    exact hx
  · rintro ⟨y, ⟨hy, _⟩, z, hz₁, rfl⟩
    simp only [mulVec_add, ← add_assoc]
    congr 1

lemma Linear.preimage [Fintype β] (hs : s.Linear) (f : (β → ℕ) →ₗ[ℕ] (α → ℕ)) :
    (f ⁻¹' s).Semilinear := by
  classical
  rw [iff_eq_setOf_vadd_mulVec] at hs
  rcases hs with ⟨v, n, A, rfl⟩
  convert (Semilinear.of_linear_equation (α := α) (β := β ⊕ Fin n)
    v 0 (Matrix.fromCols 0 A) (Matrix.fromCols f.toMatrix' 0)).proj using 1
  ext x
  refine exists_congr fun y => ?_
  simp

theorem Semilinear.preimage [Fintype β] (hs : s.Semilinear) (f : (β → ℕ) →ₗ[ℕ] (α → ℕ)) :
    (f ⁻¹' s).Semilinear := by
  classical
  rcases hs with ⟨S, hS, rfl⟩
  simp_rw [sUnion_eq_biUnion, Finset.mem_coe, preimage_iUnion]
  exact biUnion_finset fun s hs => (hS s hs).preimage f

lemma Linear.inter [Fintype α] (hs₁ : s₁.Linear) (hs₂ : s₂.Linear) : (s₁ ∩ s₂).Semilinear := by
  classical
  rw [iff_eq_setOf_vadd_mulVec] at hs₁ hs₂
  rcases hs₁ with ⟨u, n, A, rfl⟩
  rcases hs₂ with ⟨v, m, B, rfl⟩
  convert (Semilinear.of_linear_equation (α := α ⊕ α) (β := α ⊕ (Fin n ⊕ Fin m))
    (Sum.elim u v) 0
    (fromRows (fromCols 0 (fromCols A 0)) (fromCols 0 (fromCols 0 B)))
    (fromRows (fromCols 1 0) (fromCols 1 0))).proj using 1
  ext z
  simp only [mem_inter_iff, mem_setOf_eq, zero_add, fromRows_fromCols_eq_fromBlocks]
  constructor
  · intro ⟨⟨x, hx⟩, y, hy⟩
    exists Sum.elim x y
    ext i
    cases i with
    | inl => simp [fromBlocks_mulVec, ← hx]
    | inr => simp [fromBlocks_mulVec, ← hy]
  · intro ⟨y, hy⟩
    simp only [fromBlocks_mulVec, Sum.elim_comp_inl, zero_mulVec, Sum.elim_comp_inr, zero_add,
      one_mulVec, add_zero] at hy
    refine ⟨⟨y ∘ Sum.inl, ?_⟩, y ∘ Sum.inr, ?_⟩
      <;> ext i
      <;> [have := congr_fun hy (Sum.inl i); have := congr_fun hy (Sum.inr i)]
      <;> rw [← Sum.elim_comp_inl_inr y] at this
      <;> simp only [fromCols_mulVec_sumElim, zero_mulVec, add_zero, zero_add, Pi.add_apply,
        Sum.elim_inl, Sum.elim_inr] at this
      <;> exact this

/-- Semilinear sets are closed under intersection. -/
theorem Semilinear.inter [Fintype α] (hs₁ : s₁.Semilinear) (hs₂ : s₂.Semilinear) :
    (s₁ ∩ s₂).Semilinear := by
  classical
  rcases hs₁ with ⟨S₁, hS₁, rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, rfl⟩
  rw [sUnion_inter_sUnion, ← Finset.coe_product]
  apply biUnion_finset
  simp only [Finset.mem_product, and_imp, Prod.forall]
  intro s₁ s₂ hs₁ hs₂
  exact (hS₁ s₁ hs₁).inter (hS₂ s₂ hs₂)

theorem Semilinear.sInter_finset [Fintype α] {S : Finset (Set (α → ℕ))}
    (hS : ∀ s ∈ S, s.Semilinear) : (⋂₀ (S : Set (Set (α → ℕ)))).Semilinear := by
  classical
  induction S using Finset.induction with
  | empty => simpa using univ
  | insert s S _ ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hS
    simpa using inter hS.1 (ih hS.2)

theorem Semilinear.iInter_fintype [Fintype α] [Fintype ι] {s : ι → Set (α → ℕ)}
    (hs : ∀ i, (s i).Semilinear) : (⋂ i, s i).Semilinear := by
  classical
  rw [← sInter_range, ← image_univ, ← Finset.coe_univ, ← Finset.coe_image]
  apply sInter_finset
  simpa

theorem Semilinear.biInter_finset [Fintype α] {s : Finset ι} {t : ι → Set (α → ℕ)}
    (ht : ∀ i ∈ s, (t i).Semilinear) : (⋂ i ∈ s, t i).Semilinear := by
  classical
  simp_rw [← Finset.mem_coe, ← sInter_image, ← Finset.coe_image]
  apply sInter_finset
  simpa

private def toRatVec : (α → ℕ) →ₗ[ℕ] (α → ℚ) :=
  LinearMap.compLeft (Nat.castAddMonoidHom ℚ).toNatLinearMap α

private theorem toRatVec_inj (x y : α → ℕ) : toRatVec x = toRatVec y ↔ x = y := by
  refine ⟨fun h => ?_, congr_arg toRatVec⟩
  ext i
  simpa [toRatVec] using congr_fun h i

private theorem toRatVec_mono (x y : α → ℕ) : toRatVec x ≤ toRatVec y ↔ x ≤ y := by
  rw [Pi.le_def, Pi.le_def]
  apply forall_congr'
  simp [toRatVec]

private theorem toRatVec_nonneg (x : α → ℕ) : 0 ≤ toRatVec x := by
  rw [← map_zero toRatVec, toRatVec_mono]
  simp

private theorem linearIndepOn_toRatVec {s : Finset (α → ℕ)}
    (hs : LinearIndepOn ℕ id (s : Set (α → ℕ))) : LinearIndepOn ℚ toRatVec (s : Set (α → ℕ)) := by
  classical
  rw [LinearIndepOn, ← LinearIndependent.iff_fractionRing ℤ ℚ, ← LinearIndepOn,
    linearIndepOn_finset_iff]
  intro f heq i hi
  rw [linearIndepOn_finset_iffₛ] at hs
  specialize hs (Int.toNat ∘ f) (Int.toNat ∘ (- ·) ∘ f) ?_ i hi
  · simp only [Function.comp_apply, Function.id_def]
    suffices toRatVec (∑ x ∈ s, (f x).toNat • x) - toRatVec (∑ x ∈ s, (-f x).toNat • x) =
        ∑ i ∈ s, f i • toRatVec i by
      simpa only [heq, sub_eq_zero, toRatVec_inj] using this
    clear hs heq i hi
    induction s using Finset.induction_on with
    | empty => simp
    | insert x t₁ hx ih =>
      simp only [Finset.sum_insert hx] at ih ⊢
      rw [← ih, map_add, map_add, add_sub_add_comm, map_smul, map_smul]
      conv => rhs; arg 1; rw [← Int.toNat_sub_toNat_neg (f x), sub_smul]
      rfl
  · cases hfi : f i
    · simpa [hfi] using hs
    · simp [hfi, Int.neg_negSucc] at hs

lemma ProperLinear.compl [Fintype α] (hs : s.ProperLinear) : sᶜ.Semilinear := by
  classical
  rcases hs with ⟨v, t₁, ht₁, hs⟩
  have ht₁' := linearIndepOn_toRatVec ht₁

  let t := Finite.toFinset
    (s := ht₁'.extend (@subset_union_left _ (t₁ : Set (α → ℕ))
      ((Finset.univ : Finset α).image (Pi.basisFun ℕ α))))
    ((t₁.finite_toSet.union (Finset.finite_toSet _)).subset (LinearIndepOn.extend_subset _ _))
  have ht₁subset : t₁ ⊆ t := by
    rw [← Finset.coe_subset]
    simp only [Finite.coe_toFinset, t]
    exact ht₁'.subset_extend _
  have htindep : LinearIndepOn ℚ toRatVec (t : Set (α → ℕ)) := by
    simp only [Finite.coe_toFinset, t]
    exact ht₁'.linearIndepOn_extend _
  have htspan : ⊤ ≤ Submodule.span ℚ (toRatVec '' (t : Set (α → ℕ))) := by
    simp only [Finite.coe_toFinset, t]
    rw [ht₁'.span_image_extend_eq_span_image]
    apply (span_mono (image_mono subset_union_right)).trans'
    convert top_le_iff.2 (Pi.basisFun ℚ α).span_eq
    ext x
    simp only [Finset.coe_image, Pi.basisFun_apply, Finset.coe_univ, image_univ, mem_image,
      mem_range, exists_exists_eq_and]
    congr! with i
    ext j
    simp [toRatVec, Pi.single_apply]
  rw [image_eq_range] at htspan

  let b := Basis.mk htindep htspan
  have hb : ∀ i, b i = toRatVec i.1 := by simp [b]
  let f : (α → ℕ) → t → ℤ := fun x i => ⌊b.repr (toRatVec x - toRatVec v) i⌋
  let g : (α → ℕ) → (α → ℕ) := fun x => x + ∑ i, (- f x i).toNat • i.1 - ∑ i, (f x i).toNat • i.1
  have hf_toNat_sum_le : ∀ x,
      ∑ i : t, (f x i).toNat • i.1 ≤ x + ∑ i : t, (- f x i).toNat • i.1 := by
    intro x
    rw [← toRatVec_mono]
    simp only [f, map_add, map_sum, map_smul]
    rw [← sub_le_iff_le_add, ← Finset.sum_sub_distrib]
    conv =>
      enter [1, 2, _]
      rw [← Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul ℤ, ← sub_smul,
        Int.toNat_sub_toNat_neg, ← Int.cast_smul_eq_zsmul ℚ]
    trans toRatVec x - toRatVec v
    · conv => rhs; rw [← b.sum_repr (toRatVec x - toRatVec v)]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hb]
      exact smul_le_smul_of_nonneg_right (Int.floor_le _) (toRatVec_nonneg _)
    · simp [toRatVec_nonneg]
  have hx_add_f_neg_toNat_sum : ∀ x,
      x + ∑ i, (- f x i).toNat • i.1 = g x + ∑ i, (f x i).toNat • i.1 := by
    intro x
    simp only [g]
    rw [tsub_add_cancel_of_le (hf_toNat_sum_le x)]
  have hg_toRatVec : ∀ x, toRatVec (g x) =
      toRatVec v + ∑ i, Int.fract (b.repr (toRatVec x - toRatVec v) i) • toRatVec i.1 := by
    intro x
    simp only [g]
    rw [← map_tsub_of_le _ _ _ (hf_toNat_sum_le x)]
    simp only [map_add, map_sum, map_smul]
    rw [← sub_add_eq_add_sub, sub_add, ← Finset.sum_sub_distrib]
    conv =>
      enter [1, 2, 2, _]
      rw [← Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul ℤ, ← sub_smul,
        Int.toNat_sub_toNat_neg]
    erw [sub_eq_iff_eq_add, add_assoc, ← sub_eq_iff_eq_add', ← Finset.sum_add_distrib]
    simp only [f]
    conv =>
      enter [2, 2, _]
      rw [← Int.cast_smul_eq_zsmul ℚ, ← add_smul, Int.fract_add_floor, ← hb]
    rw [b.sum_repr]
  have hg_le_v_add : ∀ x, g x ≤ v + ∑ i : t, i.1 := by
    intro x
    rw [← toRatVec_mono, hg_toRatVec, map_add, map_sum, add_le_add_iff_left]
    exact Finset.sum_le_sum fun i _ =>
      smul_le_of_le_one_left (toRatVec_nonneg _) (Int.fract_lt_one _).le
  have hg_add_of_mem_span : ∀ x, ∀ y ∈ span ℕ t, g (x + y) = g x := by
    intro x y hy
    rw [mem_span_finset'] at hy
    rcases hy with ⟨h, rfl⟩
    rw [← toRatVec_inj, hg_toRatVec, hg_toRatVec]
    congr! 3 with i
    rw [map_add, ← sub_add_eq_add_sub]
    simp [-nsmul_eq_mul, ← hb, Finsupp.single_apply]
  have hf_add_smul_self : ∀ x (n : ℕ) (i : t), f (x + n • i.1) i = f x i + n := by
    intro x n i
    simp only [f]
    rw [map_add, ← sub_add_eq_add_sub]
    simp [-nsmul_eq_mul, ← hb]
  have hf_add_sum : ∀ x (h : (α → ℕ) → ℕ) i, f (x + ∑ j ∈ t, h j • j) i = f x i + h i.1 := by
    intro x h i
    simp only [f]
    rw [map_add, ← sub_add_eq_add_sub, ← Finset.sum_coe_sort]
    simp [-nsmul_eq_mul, ← hb, Finsupp.single_apply]
  have hf_add_sum_of_subset_of_notMem : ∀ {x} {h : (α → ℕ) → ℕ} {t'} (ht' : t' ⊆ t) {i}
      (hi : i.1 ∉ t'), f (x + ∑ j ∈ t', h j • j) i = f x i := by
    intro x h t' ht' i hi
    simp only [f]
    rw [map_add, ← sub_add_eq_add_sub, ← Finset.sum_indicator_subset _ ht', ← Finset.sum_coe_sort]
    simp [-nsmul_eq_mul, indicator_apply, Finset.sum_ite, ← hb, Finsupp.single_apply, hi]
  have hfv : ∀ i, f v i = 0 := by simp [f]
  have hgv : g v = v := by simp [g, hfv]
  have hgidem : ∀ x, g (g x) = g x := by
    intro x
    rw [← toRatVec_inj, hg_toRatVec (g x)]
    suffices ∀ i, 0 ≤ (b.repr (toRatVec (g x) - toRatVec v)) i
        ∧ (b.repr (toRatVec (g x) - toRatVec v)) i < 1 by
      simp_rw [fun i => Int.fract_eq_self.2 (this i), ← hb]
      rw [b.sum_repr]
      simp
    refine fun i => ⟨?_, ?_⟩
    · rw [hg_toRatVec, add_sub_cancel_left]
      simp [← hb, Finsupp.single_apply]
    · rw [hg_toRatVec, add_sub_cancel_left]
      simp [← hb, Finsupp.single_apply, Int.fract_lt_one]

  have hs' : ∀ x, x ∈ s ↔ g x = v ∧ ∀ i, 0 ≤ f x i ∧ (i.1 ∉ t₁ → f x i = 0) := by
    intro x
    simp only [hs, mem_vadd_set, SetLike.mem_coe, vadd_eq_add]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, fun i => ?_⟩
      · rw [hg_add_of_mem_span _ _ (span_mono (Finset.coe_subset.2 ht₁subset) hy), hgv]
      · rw [mem_span_finset] at hy
        rcases hy with ⟨h, hh, hy⟩
        simp only [Function.support_subset_iff', Finset.mem_coe] at hh
        rw [← add_zero (Finset.sum _ _),
          ← Finset.sum_eq_zero (s := t \ t₁) (f := fun a => h a • a),
          ← Finset.sum_union Finset.sdiff_disjoint.symm,
          Finset.union_sdiff_of_subset ht₁subset] at hy
        · simp only [← hy, hf_add_sum]
          grind
        · intro x hx
          simp only [Finset.mem_sdiff] at hx
          simp [hh x hx.2]
    · intro ⟨hgx, hfx⟩
      refine ⟨∑ i ∈ {i : t | i.1 ∈ t₁}, (f x i).toNat • i.1,
        sum_mem fun i hi => smul_mem _ _ (mem_span_of_mem (Finset.mem_filter.1 hi).2), ?_⟩
      rw [Finset.sum_filter, ← hgx]
      conv => rhs; rw [← add_zero x, ← Finset.sum_const_zero (ι := t) (s := Finset.univ)]
      convert (hx_add_f_neg_toNat_sum x).symm using 3 with i _ i
      · split_ifs with hi
        · simp
        · simp [(hfx i).2 hi]
      · simp [Int.toNat_eq_zero.2 (neg_nonpos.2 (hfx i).1)]

  let s₁ : Set (α → ℕ) := {x | x ≠ v ∧ ∃ y, x = g y}
  have hs₁ : s₁.Finite := by
    apply (Finset.Iic (v + ∑ i : t, i.1)).finite_toSet.subset
    rintro _ ⟨_, x, rfl⟩
    simpa only [Finset.coe_Iic, mem_Iic] using hg_le_v_add x

  let s₁' : Set (α → ℕ) := {x | g x ≠ v}
  have hs₁' : s₁'.Semilinear := by
    convert_to (⋃ u ∈ s₁, {x | ∃ y ∈ span ℕ t, ∃ y' ∈ span ℕ t, x + y' = u + y}).Semilinear using 1
    · ext x
      simp only [s₁', s₁, mem_iUnion, mem_setOf, exists_prop]
      constructor
      · intro hgx
        refine ⟨g x, ⟨hgx, x, rfl⟩, ∑ i, (f x i).toNat • i.1, ?_, ∑ i, (-f x i).toNat • i.1, ?_, ?_⟩
        · exact sum_mem fun i _ => smul_mem _ _ (mem_span_of_mem i.2)
        · exact sum_mem fun i _ => smul_mem _ _ (mem_span_of_mem i.2)
        · exact hx_add_f_neg_toNat_sum x
      · rintro ⟨_, ⟨hgz, ⟨z, rfl⟩⟩, y, hy, y', hy', heq⟩
        apply congr_arg g at heq
        rw [hg_add_of_mem_span _ _ hy', hg_add_of_mem_span _ _ hy, hgidem] at heq
        rwa [heq]
    · simp_rw [← hs₁.mem_toFinset]
      refine Semilinear.biUnion_finset fun i _ => Semilinear.proj' ?_
      rw [setOf_and]
      apply Semilinear.inter
      · exact (Semilinear.span_finset t).preimage (LinearMap.funLeft ℕ ℕ Sum.inr)
      · apply Semilinear.proj'
        rw [setOf_and]
        apply Semilinear.inter
        · exact (Semilinear.span_finset t).preimage (LinearMap.funLeft ℕ ℕ Sum.inr)
        · convert Semilinear.of_linear_equation (α := α) (β := (α ⊕ α) ⊕ α) 0 i
            (Matrix.fromCols (Matrix.fromCols 1 0) 1) (Matrix.fromCols (Matrix.fromCols 0 1) 0)
            using 1
          ext x
          simp only [mem_setOf, zero_add]
          conv => rhs; rw [← Sum.elim_comp_inl_inr x, ← Sum.elim_comp_inl_inr (x ∘ Sum.inl)]
          simp [-Sum.elim_comp_inl_inr]

  let s₂ : Set (α → ℕ) := {x | g x = v ∧ ∃ i, f x i < 0 ∨ i.1 ∉ t₁ ∧ 0 < f x i}
  have hs₂ : s₂.Semilinear := by
    convert_to ((⋃ i : t,
        {x | ∃ y ∈ span ℕ {i.1}, ∃ z ∈ span ℕ (t \ {i.1} : Set (α → ℕ)),
          ∃ z' ∈ span ℕ (t \ {i.1}: Set (α → ℕ)), x + i.1 + y + z' = v + z})
      ∪ ⋃ i ∈ ({i : t | i.1 ∉ t₁} : Finset _),
        {x | ∃ y ∈ span ℕ {i.1}, ∃ z ∈ span ℕ (t \ {i.1} : Set (α → ℕ)),
          ∃ z' ∈ span ℕ (t \ {i.1} : Set (α → ℕ)), x + z' = v + i.1 + y + z}).Semilinear using 1
    · ext x
      simp only [s₂, mem_iUnion, mem_union, mem_setOf, exists_prop]
      constructor
      · rintro ⟨hgx, i, hfxi | ⟨hi, hfxi⟩⟩
        · refine Or.inl ⟨i, ((- f x i).toNat - 1) • i.1, ?_,
            ∑ j ∈ (Finset.univ.erase i : Finset t), (f x j).toNat • j.1, ?_,
            ∑ j ∈ (Finset.univ.erase i : Finset t), (- f x j).toNat • j.1, ?_, ?_⟩
          · exact smul_mem _ _ (mem_span_of_mem (mem_singleton i.1))
          · refine sum_mem fun j hj => smul_mem _ _ (mem_span_of_mem ?_)
            simpa [Subtype.val_inj] using hj
          · refine sum_mem fun j hj => smul_mem _ _ (mem_span_of_mem ?_)
            simpa [Subtype.val_inj] using hj
          · rw [add_assoc x, ← succ_nsmul',
              tsub_add_cancel_of_le
                ((Int.le_toNat (neg_pos.2 hfxi).le).2 (le_neg.1 (Int.cast_le_neg_one_of_neg hfxi))),
              add_assoc x,
              Finset.add_sum_erase _ (fun j => (- f x j).toNat • j.1) (Finset.mem_univ i),
              ← add_zero (Finset.sum (Finset.univ.erase i) _),
              ← zero_nsmul i.1, ← Int.toNat_eq_zero.2 hfxi.le,
              Finset.sum_erase_add _ _ (Finset.mem_univ i), ← hgx]
            exact hx_add_f_neg_toNat_sum x
        · refine Or.inr ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, ((f x i).toNat - 1) • i.1,
            ?_, ∑ j ∈ (Finset.univ.erase i : Finset t), (f x j).toNat • j.1, ?_,
            ∑ j ∈ (Finset.univ.erase i : Finset t), (- f x j).toNat • j.1, ?_, ?_⟩
          · exact smul_mem _ _ (mem_span_of_mem (mem_singleton i.1))
          · refine sum_mem fun j hj => smul_mem _ _ (mem_span_of_mem ?_)
            simpa [Subtype.val_inj] using hj
          · refine sum_mem fun j hj => smul_mem _ _ (mem_span_of_mem ?_)
            simpa [Subtype.val_inj] using hj
          · rw [add_assoc v, ← succ_nsmul',
              tsub_add_cancel_of_le ((Int.le_toNat hfxi.le).2 (Int.add_one_le_of_lt hfxi)),
              add_assoc v,
              Finset.add_sum_erase _ (fun j => (f x j).toNat • j.1) (Finset.mem_univ i),
              ← add_zero (Finset.sum (Finset.univ.erase i) _),
              ← zero_nsmul i.1, ← Int.toNat_eq_zero.2 (neg_neg_iff_pos.2 hfxi).le,
              Finset.sum_erase_add _ _ (Finset.mem_univ i), ← hgx]
            exact hx_add_f_neg_toNat_sum x
      · rintro (⟨i, y, hy, z, hz, z', hz', heq⟩ | ⟨i, hi, y, hy, z, hz, z', hz', heq⟩)
        · refine ⟨?_, i, Or.inl ?_⟩
          · apply congr_arg g at heq
            rw [hg_add_of_mem_span _ _ (span_mono diff_subset hz'),
              hg_add_of_mem_span _ _ (span_mono (singleton_subset_iff.2 i.2) hy),
              hg_add_of_mem_span _ _ (mem_span_of_mem i.2),
              hg_add_of_mem_span _ _ (span_mono diff_subset hz), hgv] at heq
            exact heq
          · simp only [mem_span_singleton] at hy
            rcases hy with ⟨n, rfl⟩
            rw [← Finset.coe_erase, mem_span_finset] at hz hz'
            rcases hz with ⟨h, _, rfl⟩
            rcases hz' with ⟨h', _, rfl⟩
            apply congr_arg f at heq
            apply congr_fun (a := i) at heq
            rw [add_assoc x, ← succ_nsmul',
              hf_add_sum_of_subset_of_notMem (Finset.erase_subset _ _) (Finset.notMem_erase _ _),
              hf_add_smul_self,
              hf_add_sum_of_subset_of_notMem (Finset.erase_subset _ _) (Finset.notMem_erase _ _),
              hfv] at heq
            simp only [Nat.cast_add, Nat.cast_one] at heq
            rw [← eq_neg_iff_add_eq_zero] at heq
            simpa [heq] using neg_one_lt_zero.trans_le (Nat.cast_nonneg _)
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          refine ⟨?_, i, Or.inr ⟨hi, ?_⟩⟩
          · apply congr_arg g at heq
            rw [hg_add_of_mem_span _ _ (span_mono diff_subset hz'),
              hg_add_of_mem_span _ _ (span_mono diff_subset hz),
              hg_add_of_mem_span _ _ (span_mono (singleton_subset_iff.2 i.2) hy),
              hg_add_of_mem_span _ _ (mem_span_of_mem i.2), hgv] at heq
            exact heq
          · simp only [mem_span_singleton] at hy
            rcases hy with ⟨n, rfl⟩
            rw [← Finset.coe_erase, mem_span_finset] at hz hz'
            rcases hz with ⟨h, _, rfl⟩
            rcases hz' with ⟨h', _, rfl⟩
            apply congr_arg f at heq
            apply congr_fun (a := i) at heq
            rw [hf_add_sum_of_subset_of_notMem (Finset.erase_subset _ _) (Finset.notMem_erase _ _),
              add_assoc v, ← succ_nsmul',
              hf_add_sum_of_subset_of_notMem (Finset.erase_subset _ _) (Finset.notMem_erase _ _),
              hf_add_smul_self, hfv] at heq
            simp only [Nat.cast_add, Nat.cast_one, zero_add] at heq
            simp [heq]
    · apply Semilinear.union
      · refine Semilinear.iUnion_fintype fun i => Semilinear.proj' ?_
        rw [setOf_and]
        apply Semilinear.inter
        · simp_rw [← Finset.coe_singleton]
          exact (Semilinear.span_finset _).preimage (LinearMap.funLeft ℕ ℕ Sum.inr)
        · apply Semilinear.proj'
          rw [setOf_and]
          apply Semilinear.inter
          · simp_rw [← Finset.coe_erase]
            exact (Semilinear.span_finset _).preimage (LinearMap.funLeft ℕ ℕ Sum.inr)
          · apply Semilinear.proj'
            rw [setOf_and]
            apply Semilinear.inter
            · simp_rw [← Finset.coe_erase]
              exact (Semilinear.span_finset _).preimage (LinearMap.funLeft ℕ ℕ Sum.inr)
            · convert Semilinear.of_linear_equation (α := α) (β := ((α ⊕ α) ⊕ α) ⊕ α) i.1 v
                (Matrix.fromCols (Matrix.fromCols (Matrix.fromCols 1 1) 0) 1)
                (Matrix.fromCols (Matrix.fromCols (Matrix.fromCols 0 0) 1) 0) using 1
              ext x
              simp only [mem_setOf]
              conv =>
                rhs
                rw [← Sum.elim_comp_inl_inr x, ← Sum.elim_comp_inl_inr (x ∘ Sum.inl),
                  ← Sum.elim_comp_inl_inr ((x ∘ Sum.inl) ∘ Sum.inl)]
              simp [-Sum.elim_comp_inl_inr, add_assoc, add_left_comm _ i.1]
      · refine Semilinear.biUnion_finset fun i _ => Semilinear.proj' ?_
        rw [setOf_and]
        apply Semilinear.inter
        · simp_rw [← Finset.coe_singleton]
          exact (Semilinear.span_finset _).preimage (LinearMap.funLeft ℕ ℕ Sum.inr)
        · apply Semilinear.proj'
          rw [setOf_and]
          apply Semilinear.inter
          · simp_rw [← Finset.coe_erase]
            exact (Semilinear.span_finset _).preimage (LinearMap.funLeft ℕ ℕ Sum.inr)
          · apply Semilinear.proj'
            rw [setOf_and]
            apply Semilinear.inter
            · simp_rw [← Finset.coe_erase]
              exact (Semilinear.span_finset _).preimage (LinearMap.funLeft ℕ ℕ Sum.inr)
            · convert Semilinear.of_linear_equation (α := α) (β := ((α ⊕ α) ⊕ α) ⊕ α) 0 (v + i.1)
                (Matrix.fromCols (Matrix.fromCols (Matrix.fromCols 1 0) 0) 1)
                (Matrix.fromCols (Matrix.fromCols (Matrix.fromCols 0 1) 1) 0) using 1
              ext x
              simp only [mem_setOf]
              conv =>
                rhs
                rw [← Sum.elim_comp_inl_inr x, ← Sum.elim_comp_inl_inr (x ∘ Sum.inl),
                  ← Sum.elim_comp_inl_inr ((x ∘ Sum.inl) ∘ Sum.inl)]
              simp [-Sum.elim_comp_inl_inr, add_assoc]

  convert hs₁'.union hs₂ using 1
  ext x
  simp only [s₁', s₂, mem_compl_iff, hs', Subtype.forall, not_and, not_forall, ne_eq,
    Subtype.exists, mem_union, mem_setOf_eq]
  clear_value f g
  clear hx_add_f_neg_toNat_sum
  grind

/-- Semilinear sets are closed under complement. -/
theorem Semilinear.compl [Fintype α] (hs : s.Semilinear) : sᶜ.Semilinear := by
  classical
  rcases hs.proper_semilinear with ⟨S, hS, rfl⟩
  simp_rw [sUnion_eq_biUnion, Finset.mem_coe, compl_iUnion]
  exact biInter_finset fun s hs => (hS s hs).compl

variable {A : Set ℕ} [Fintype α]

open FirstOrder Language

theorem Linear.definable (hs : s.Linear) : A.Definable presburger s := by
  classical
  rcases hs with ⟨v, t, rfl⟩
  refine ⟨Formula.iExs t (Formula.iInf fun i : α =>
    (Term.var (Sum.inl i)).equal
      (Term.varsToConstants
        ((v i : presburger.Term _) + presburger.sum Finset.univ fun x : t =>
          x.1 i • Term.var (Sum.inr (Sum.inr x))))), ?_⟩
  ext x
  simpa [mem_vadd_set, mem_span_finset'] using exists_congr fun a =>
    funext_iff.trans <| forall_congr' fun b => Eq.comm.trans <|
      Eq.congr_right <| congr_arg (v b + ·) <| (Finset.sum_apply _ _ _).trans <|
        Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem Semilinear.definable (hs : s.Semilinear) : A.Definable presburger s := by
  rcases hs with ⟨S, hS, rfl⟩
  choose φ hφ using fun s : S => (hS s.1 s.2).definable
  refine ⟨Formula.iSup φ, ?_⟩
  ext x
  have := fun s hs x => Set.ext_iff.1 (hφ ⟨s, hs⟩).symm x
  simp only [mem_setOf_eq] at this
  simp [this]

end Set

namespace FirstOrder.Language.presburger

open Set Matrix

variable {A : Set ℕ} [Fintype α]

lemma term_realize_eq_add_dotProduct (t : presburger[[A]].Term α) :
    ∃ (k : ℕ) (u : α → ℕ), ∀ (v : α → ℕ), t.realize v = k + u ⬝ᵥ v := by
  classical
  induction t with simp only [Term.realize]
  | var i => refine ⟨0, Pi.single i 1, ?_⟩; simp
  | @func l f ts ih =>
    cases f with
    | inl f =>
      choose k u ih using ih
      cases f with
      | zero =>
        refine ⟨0, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]
        simp
      | one =>
        refine ⟨1, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInl]
        simp [ih]
      | add =>
        refine ⟨k 0 + k 1, u 0 + u 1, fun v => ?_⟩
        rw [withConstants_funMap_sumInl, add_dotProduct, add_left_comm, add_assoc, add_left_comm,
          ← add_assoc]
        simp [ih]
    | inr f =>
      cases l with
      | zero =>
        refine ⟨f, 0, fun v => ?_⟩
        rw [withConstants_funMap_sumInr]
        simp only [constantsOn_Functions, constantsOnFunc.eq_1, coe_con, zero_dotProduct, add_zero]
        rfl
      | succ => nomatch f

lemma boundedFormula_realize_semilinear {n} (φ : presburger[[A]].BoundedFormula α n) :
    {v : α ⊕ Fin n → ℕ | φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr)}.Semilinear := by
  induction φ with simp only [BoundedFormula.Realize]
  | equal t₁ t₂ =>
    rcases term_realize_eq_add_dotProduct t₁ with ⟨k₁, u₁, ht₁⟩
    rcases term_realize_eq_add_dotProduct t₂ with ⟨k₂, u₂, ht₂⟩
    convert Semilinear.of_linear_equation ![k₁] ![k₂] (.of ![u₁]) (.of ![u₂])
    simp [ht₁, ht₂]
  | rel f => nomatch f
  | falsum => exact Semilinear.empty
  | imp _ _ ih₁ ih₂ =>
    convert (ih₂.compl.inter ih₁).compl using 1
    simp [setOf_inter_eq_sep, imp_iff_not_or, compl_setOf]
  | @all n φ ih =>
    let e := (Equiv.sumAssoc α (Fin n) (Fin 1)).trans (Equiv.sumCongr (.refl α) finSumFinEquiv)
    convert (ih.compl.reindex e).proj.compl using 1
    simp_rw [compl_setOf, not_exists, Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi, mem_image,
      not_exists, mem_setOf, not_and, not_imp_not]
    congr! 3 with x k
    constructor
    · intro hφ y hy
      convert hφ using 1 <;> ext i
      · apply congr_fun (a := e.symm (Sum.inl i)) at hy
        simpa [e] using hy
      · apply congr_fun (a := e.symm (Sum.inr i)) at hy
        cases i using Fin.lastCases <;> simpa [e] using hy
    · intro h
      convert h (fun y => Sum.elim x ![k] (e.symm y)) ?_ using 1
      · ext i
        cases i using Fin.lastCases <;> simp [e]
      · ext i
        cases i with
        | inl => simp
        | inr i => fin_cases i; simp

lemma formula_realize_semilinear (φ : presburger[[A]].Formula α) :
    (setOf φ.Realize : Set (α → ℕ)).Semilinear := by
  convert (boundedFormula_realize_semilinear φ).reindex (Equiv.sumEmpty α (Fin 0)).symm
  ext x
  simp only [mem_setOf_eq, mem_image]
  rw [((Equiv.sumEmpty α (Fin 0)).arrowCongr (.refl ℕ)).exists_congr_left]
  simp [Formula.Realize, Unique.eq_default, Function.comp_def]

/-- A set is Presburger definable in `ℕ` if and only if it is semilinear. -/
theorem definable_iff_semilinear {s : Set (α → ℕ)} :
    A.Definable presburger s ↔ s.Semilinear :=
  ⟨fun ⟨φ, hφ⟩ => hφ ▸ formula_realize_semilinear φ, Semilinear.definable⟩

/-- In the 1-dimensional case, a set is Presburger arithmetic definable in `ℕ` if and only if it
  is ultimately periodic, i.e. periodic after some number `k`. -/
theorem definable₁_iff_ultimately_periodic {s : Set ℕ} :
    A.Definable₁ presburger s ↔ ∃ k, ∃ p > 0, ∀ x ≥ k, x ∈ s ↔ x + p ∈ s := by
  rw [Definable₁, definable_iff_semilinear]
  constructor
  · intro hs
    apply Semilinear.proper_semilinear at hs
    rcases hs with ⟨S, hS, hs⟩
    simp only [Set.ext_iff, mem_setOf_eq, mem_sUnion, Finset.mem_coe] at hs
    replace hs := (hs ![·])
    simp only [Fin.isValue, cons_val_fin_one] at hs
    replace hS : ∀ t ∈ S, ∃ k, ∃ p > 0, ∀ x ≥ k, ![x] ∈ t ↔ ![x + p] ∈ t := by
      intro t ht
      apply hS at ht
      rcases ht with ⟨v, t, ht, rfl⟩
      have hcard : t.card ≤ 1 := by
        by_contra hcard
        simp only [not_le, Finset.one_lt_card_iff] at hcard
        rcases hcard with ⟨a, b, ha, hb, hab⟩
        have hb' : b ≠ 0 := by
          intro hb'
          apply ht.zero_notMem_image
          simp [← hb', hb]
        simp only [ne_eq, funext_iff, Fin.forall_fin_one, Pi.zero_apply] at hb'
        revert ht
        simp only [imp_false, not_linearIndepOn_finset_iffₛ, id_eq]
        refine ⟨Pi.single a (b 0), Pi.single b (a 0), ?_, a, ha, ?_⟩
        · simpa [Pi.single_apply, ha, hb, funext_iff (f := (b 0 : Fin 1 → ℕ) * a),
            Fin.forall_fin_one] using mul_comm (b 0) (a 0)
        · simp [hab, hb']
      simp_rw [Finset.card_le_one_iff_subset_singleton, Finset.subset_singleton_iff] at hcard
      rcases hcard with ⟨u, (rfl | rfl)⟩
      · refine ⟨v 0 + 1, 1, zero_lt_one, fun x hx => ?_⟩
        have hx' : x ≠ v 0 := (Nat.lt_of_succ_le hx).ne'
        have hx'' : x + 1 ≠ v 0 := (Nat.lt_of_succ_le (Nat.le_succ_of_le hx)).ne'
        simp [funext_iff, Fin.forall_fin_one, hx', hx'']
      · have hu : u ≠ 0 := by
          intro hu
          apply ht.zero_notMem_image
          simp [hu]
        simp only [ne_eq, funext_iff, Fin.forall_fin_one, Pi.zero_apply, Nat.ne_zero_iff_zero_lt]
          at hu
        refine ⟨v 0, u 0, hu, fun x hx => ?_⟩
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Finset.coe_singleton, mem_vadd_set,
          SetLike.mem_coe, Submodule.mem_span_singleton, nsmul_eq_mul, funext_iff, Pi.mul_apply,
          Pi.natCast_apply, Nat.cast_id, Fin.forall_fin_one, Fin.isValue, vadd_eq_add, Pi.add_apply,
          cons_val_fin_one]
        constructor
        · rintro ⟨y, ⟨a, ha⟩, rfl⟩
          refine ⟨y + u, ⟨a + 1, ?_⟩, ?_⟩ <;> simp [← ha, Nat.add_one_mul, add_assoc]
        · rintro ⟨y, ⟨a, ha⟩, heq⟩
          rw [← ha] at heq
          cases a with
          | zero =>
            rw [zero_mul, add_zero] at heq
            simp only [heq, add_le_iff_nonpos_right, nonpos_iff_eq_zero] at hx
            simp [hx] at hu
          | succ a =>
            rw [add_one_mul, ← add_assoc, add_right_cancel_iff] at heq
            refine ⟨a * u 0, ⟨a, rfl⟩, heq⟩
    choose! k p hS hS' using hS
    refine ⟨S.sup k, S.lcm p, ?_, fun x hx => ?_⟩
    · rw [gt_iff_lt, Nat.pos_iff_ne_zero, ne_eq]
      simpa [Finset.lcm_eq_zero_iff, ← Nat.pos_iff_ne_zero]
    · simp only [ge_iff_le, Finset.sup_le_iff] at hx
      rw [hs, hs]
      refine exists_congr fun t => and_congr_right fun ht => ?_
      have hpt : p t ∣ S.lcm p := Finset.dvd_lcm ht
      rw [dvd_iff_exists_eq_mul_left] at hpt
      rcases hpt with ⟨m, hpt⟩
      rw [hpt]
      clear hpt
      induction m with
      | zero => simp
      | succ m ih =>
        simp [← ih, Nat.succ_mul, ← add_assoc,
          ← hS' t ht (x + m * p t) (le_add_of_le_left (hx t ht))]
  · intro ⟨k, p, hp, hs⟩
    have h₁ : {x ∈ s | x < k}.Finite := (Set.finite_lt_nat k).subset (sep_subset_setOf _ _)
    have h₂ : {x ∈ s | k ≤ x ∧ x < k + p}.Finite :=
      (Set.finite_Ico k (k + p)).subset (sep_subset_setOf _ _)
    convert (h₁.image (![·])).semilinear.union
      ((h₂.image (![·])).semilinear.add (Semilinear.singleton ![p]).span) using 1
    ext v
    simp only [mem_setOf_eq, Nat.succ_eq_add_one, Nat.reduceAdd, sep_and, mem_union,
      mem_image, mem_add, mem_inter_iff, SetLike.mem_coe, Submodule.mem_span_singleton, smul_cons,
      smul_eq_mul, Matrix.smul_empty, exists_exists_eq_and, add_cons, empty_add_empty,
      exists_exists_and_eq_and, head_cons]
    constructor
    · intro hv
      by_cases hv' : v 0 < k
      · refine Or.inl ⟨v 0, ⟨hv, hv'⟩, ?_⟩
        simp [funext_iff, Fin.forall_fin_one]
      · simp only [not_lt] at hv'
        refine Or.inr ⟨k + (v 0 - k) % p, ⟨⟨?_1, ?_2⟩, ?_1, ?_3⟩, (v 0 - k) / p, ?_4⟩
        · rw [← add_tsub_cancel_of_le hv', ← Nat.mod_add_div' (v 0 - k) p, ← add_assoc] at hv
          generalize (v 0 - k) / p = m at hv
          induction m with
          | zero => simpa using hv
          | succ m ih =>
            refine ih ?_
            rwa [hs _ (Nat.le_add_right_of_le (Nat.le_add_right _ _)), add_assoc, ← Nat.add_one_mul]
        · apply Nat.le_add_right
        · apply Nat.add_lt_add_left (Nat.mod_lt _ hp)
        · rw [add_assoc, Nat.mod_add_div', add_tsub_cancel_of_le hv']
          simp [funext_iff, Fin.forall_fin_one]
    · rintro (⟨x, ⟨hx, _⟩, rfl⟩ | ⟨x, ⟨⟨hx, hx'⟩, _⟩, m, rfl⟩)
        <;> simp only [cons_val_fin_one]
      · exact hx
      · induction m with
        | zero => simpa
        | succ m ih =>
          rw [hs _ (le_add_right hx')] at ih
          rwa [Nat.add_one_mul, ← add_assoc]

/-- The graph of multiplication is not Presburger definable in `ℕ`. -/
theorem mul_not_definable :
    ¬ A.Definable presburger {v : Fin 3 → ℕ | v 0 = v 1 * v 2} := by
  intro hmul
  have hsqr : A.Definable₁ presburger {x * x | x : ℕ} := by
    rcases hmul with ⟨φ, hφ⟩
    exists Formula.iExs (Fin 1) (φ.subst ![Term.var (.inl 0), Term.var (.inr 0), Term.var (.inr 0)])
    simp only [setOf] at hφ
    ext x
    simp only [Fin.isValue, mem_setOf_eq, Formula.Realize, BoundedFormula.realize_iExs,
      BoundedFormula.realize_subst]
    constructor
    · intro ⟨y, h⟩
      refine ⟨![y], ?_⟩
      rw [← Formula.Realize, ← hφ]
      simp [h]
    · intro ⟨v, h⟩
      rw [← Formula.Realize, ← hφ] at h
      simp only [Fin.isValue, Matrix.cons_val_zero, Term.realize_var, Sum.elim_inl,
        Matrix.cons_val_one, Sum.elim_inr, Matrix.cons_val] at h
      exact ⟨v 0, h.symm⟩
  rw [definable₁_iff_ultimately_periodic] at hsqr
  rcases hsqr with ⟨k, p, hp, h⟩
  specialize h ((max k p) * (max k p)) ((Nat.le_mul_self _).trans' (le_max_left _ _))
  simp only [mem_setOf_eq, exists_apply_eq_apply, true_iff] at h
  rcases h with ⟨x, h₁⟩
  by_cases h₂ : x ≤ max k p
  · apply Nat.mul_self_le_mul_self at h₂
    grind
  · simp only [not_le, Nat.lt_iff_add_one_le] at h₂
    apply Nat.mul_self_le_mul_self at h₂
    grind

end FirstOrder.Language.presburger
