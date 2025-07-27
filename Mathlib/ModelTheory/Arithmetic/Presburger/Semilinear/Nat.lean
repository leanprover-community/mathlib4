/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.Algebra.Order.Sub.Unbundled.Hom
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Rat.Floor
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.Module

/-!
# Semilinear sets in `ℕ`

This file proves that the semilinear sets in `α → ℕ` (with finite `α`) are closed under intersection
and complement.

## Main Results

- `Set.Semilinear.of_linear_equation`: the solution of a linear Diophantine equation
  `u + A *ᵥ x = v + B *ᵥ x` is a semilinear set.
- `Set.Semilinear.inter`: semilinear sets in `α → ℕ` (with finite `α`) are closed under
  intersection.
- `Set.Semilinear.compl`: semilinear sets in `α → ℕ` (with finite `α`) are closed under complement.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
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

theorem Linear.preimage [Fintype β] (hs : s.Linear) (f : (β → ℕ) →ₗ[ℕ] (α → ℕ)) :
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

/-- Semilinear sets in `α → ℕ` (with finite `α`) are closed under intersection. -/
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
  | empty =>
    have : AddMonoid.FG (α → ℕ) := Module.Finite.iff_addMonoid_fg.1 inferInstance
    simpa using univ
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

namespace ProperLinear

variable (hs : s.ProperLinear)

private noncomputable def base : α → ℕ := hs.choose

private noncomputable def periods : Finset (α → ℕ) := hs.choose_spec.choose

private theorem linearIndepOn_periods : LinearIndepOn ℕ id (hs.periods : Set (α → ℕ)) :=
  hs.choose_spec.choose_spec.1

private theorem eq_base_vadd_span_periods :
    s = hs.base +ᵥ (span ℕ (hs.periods : Set (α → ℕ)) : Set (α → ℕ)) :=
  hs.choose_spec.choose_spec.2

variable [Fintype α]

private noncomputable def extendedPeriods : Finset (α → ℕ) :=
  Finite.toFinset
    (s := (linearIndepOn_toRatVec hs.linearIndepOn_periods).extend
      (@subset_union_left _ (hs.periods : Set (α → ℕ))
        ((Finset.univ : Finset α).image (Pi.basisFun ℕ α))))
    ((hs.periods.finite_toSet.union (Finset.finite_toSet _)).subset
      (LinearIndepOn.extend_subset _ _))

private theorem periods_subset_extendedPeriods : hs.periods ⊆ hs.extendedPeriods := by
  simpa [extendedPeriods] using (linearIndepOn_toRatVec hs.linearIndepOn_periods).subset_extend _

private theorem linearIndepOn_extendedPeriods :
    LinearIndepOn ℚ toRatVec (hs.extendedPeriods : Set (α → ℕ)) := by
  simpa [extendedPeriods] using
    (linearIndepOn_toRatVec hs.linearIndepOn_periods).linearIndepOn_extend _

private theorem span_extendedPeriods :
    span ℚ (toRatVec '' (hs.extendedPeriods : Set (α → ℕ))) = ⊤ := by
  classical
  simp only [extendedPeriods, Finite.coe_toFinset]
  rw [(linearIndepOn_toRatVec hs.linearIndepOn_periods).span_image_extend_eq_span_image,
    ← top_le_iff]
  apply (span_mono (image_mono subset_union_right)).trans'
  rw [top_le_iff]
  convert (Pi.basisFun ℚ α).span_eq
  ext x
  simp only [Finset.coe_image, Finset.coe_univ, image_univ, mem_image, mem_range,
    exists_exists_eq_and]
  congr! with i
  ext j
  simp [toRatVec, Pi.basisFun_apply, Pi.single_apply]

open Module

private noncomputable def basis : Basis hs.extendedPeriods ℚ (α → ℚ) :=
  Basis.mk hs.linearIndepOn_extendedPeriods
    (image_eq_range _ _ ▸ top_le_iff.2 hs.span_extendedPeriods)

private theorem basis_apply {i} : hs.basis i = toRatVec i.1 := by
  simp [basis]

private noncomputable def floor (x i) :=
  ⌊hs.basis.repr (toRatVec x - toRatVec hs.base) i⌋

private noncomputable def fract (x) :=
  x + ∑ i, (- hs.floor x i).toNat • i.1 - ∑ i, (hs.floor x i).toNat • i.1

private theorem floor_base (i) : hs.floor hs.base i = 0 := by simp [floor]

private theorem fract_base : hs.fract hs.base = hs.base := by simp [fract, hs.floor_base]

private theorem floor_add_smul_self {x i} {n : ℕ} :
    hs.floor (x + n • i.1) i = hs.floor x i + n := by
  simp only [floor]
  rw [map_add, ← sub_add_eq_add_sub]
  simp [-nsmul_eq_mul, ← hs.basis_apply]

private theorem floor_add_sum {f : (α → ℕ) → ℕ} {x i} :
    hs.floor (x + ∑ j ∈ hs.extendedPeriods, f j • j) i = hs.floor x i + f i.1 := by
  simp only [floor]
  rw [map_add, ← sub_add_eq_add_sub, ← Finset.sum_coe_sort]
  simp [-nsmul_eq_mul, ← hs.basis_apply, Finsupp.single_apply]

private theorem floor_add_sum_of_subset_of_notMem {f : (α → ℕ) → ℕ} {x i t}
    (ht : t ⊆ hs.extendedPeriods) (hi : i.1 ∉ t) :
    hs.floor (x + ∑ j ∈ t, f j • j) i = hs.floor x i := by
  simp only [floor]
  rw [map_add, ← sub_add_eq_add_sub, ← Finset.sum_indicator_subset _ ht, ← Finset.sum_coe_sort]
  simp [-nsmul_eq_mul, indicator_apply, Finset.sum_ite, ← hs.basis_apply, Finsupp.single_apply, hi]

private theorem floor_toNat_sum_le (x) :
    ∑ i, (hs.floor x i).toNat • i.1 ≤ x + ∑ i, (- hs.floor x i).toNat • i.1 := by
  rw [← toRatVec_mono]
  simp only [floor, map_add, map_sum, map_smul]
  rw [← sub_le_iff_le_add, ← Finset.sum_sub_distrib]
  conv =>
    enter [1, 2, _]
    rw [← Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul ℤ, ← sub_smul,
      Int.toNat_sub_toNat_neg, ← Int.cast_smul_eq_zsmul ℚ]
  trans toRatVec x - toRatVec hs.base
  · conv => rhs; rw [← hs.basis.sum_repr (toRatVec x - toRatVec hs.base)]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [basis_apply]
    exact smul_le_smul_of_nonneg_right (Int.floor_le _) (toRatVec_nonneg _)
  · simp [toRatVec_nonneg]

private theorem add_floor_neg_toNat_sum_eq (x) :
    x + ∑ i, (- hs.floor x i).toNat • i.1 = hs.fract x + ∑ i, (hs.floor x i).toNat • i.1 := by
  simp only [fract]
  rw [tsub_add_cancel_of_le (hs.floor_toNat_sum_le x)]

private theorem toRatVec_fract_eq (x) :
    toRatVec (hs.fract x) = toRatVec hs.base +
      ∑ i, Int.fract (hs.basis.repr (toRatVec x - toRatVec hs.base) i) • toRatVec i.1 := by
  simp only [fract]
  rw [← map_tsub_of_le _ _ _ (hs.floor_toNat_sum_le x)]
  simp only [map_add, map_sum, map_smul]
  rw [← sub_add_eq_add_sub, sub_add, ← Finset.sum_sub_distrib]
  conv =>
    enter [1, 2, 2, _]
    rw [← Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul ℤ, ← sub_smul,
      Int.toNat_sub_toNat_neg]
  erw [sub_eq_iff_eq_add, add_assoc, ← sub_eq_iff_eq_add', ← Finset.sum_add_distrib]
  simp only [floor]
  conv =>
    enter [2, 2, _]
    rw [← Int.cast_smul_eq_zsmul ℚ, ← add_smul, Int.fract_add_floor, ← hs.basis_apply]
  rw [hs.basis.sum_repr]

private theorem fract_le_base_add (x) : hs.fract x ≤ hs.base + ∑ i : hs.extendedPeriods, i.1 := by
  rw [← toRatVec_mono, hs.toRatVec_fract_eq, map_add, map_sum, add_le_add_iff_left]
  exact Finset.sum_le_sum fun i _ =>
    smul_le_of_le_one_left (toRatVec_nonneg _) (Int.fract_lt_one _).le

private theorem fract_add_of_mem_span {x y} (hy : y ∈ span ℕ hs.extendedPeriods) :
    hs.fract (x + y) = hs.fract x := by
  rw [mem_span_finset'] at hy
  rcases hy with ⟨h, rfl⟩
  rw [← toRatVec_inj, hs.toRatVec_fract_eq, hs.toRatVec_fract_eq]
  congr! 3 with i
  rw [map_add, ← sub_add_eq_add_sub]
  simp [-nsmul_eq_mul, ← hs.basis_apply, Finsupp.single_apply]

private theorem fract_idem (x) : hs.fract (hs.fract x) = hs.fract x := by
  rw [← toRatVec_inj, hs.toRatVec_fract_eq (hs.fract x)]
  suffices ∀ i, 0 ≤ (hs.basis.repr (toRatVec (hs.fract x) - toRatVec hs.base)) i
      ∧ (hs.basis.repr (toRatVec (hs.fract x) - toRatVec hs.base)) i < 1 by
    simp_rw [fun i => Int.fract_eq_self.2 (this i), ← hs.basis_apply]
    rw [hs.basis.sum_repr]
    simp
  refine fun i => ⟨?_, ?_⟩
  · rw [hs.toRatVec_fract_eq, add_sub_cancel_left]
    simp [← hs.basis_apply, Finsupp.single_apply]
  · rw [hs.toRatVec_fract_eq, add_sub_cancel_left]
    simp [← hs.basis_apply, Finsupp.single_apply, Int.fract_lt_one]

include hs in
lemma compl : sᶜ.Semilinear := by
  classical
  have hs' : ∀ x, x ∈ s ↔
      hs.fract x = hs.base ∧ ∀ i, 0 ≤ hs.floor x i ∧ (i.1 ∉ hs.periods → hs.floor x i = 0) := by
    intro x
    nth_rw 1 [hs.eq_base_vadd_span_periods]
    simp only [mem_vadd_set, SetLike.mem_coe, vadd_eq_add]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, fun i => ?_⟩
      · rw [hs.fract_add_of_mem_span, hs.fract_base]
        exact span_mono (Finset.coe_subset.2 hs.periods_subset_extendedPeriods) hy
      · rw [mem_span_finset] at hy
        rcases hy with ⟨f, hf, hy⟩
        simp only [Function.support_subset_iff', Finset.mem_coe] at hf
        rw [← add_zero (Finset.sum _ _),
          ← Finset.sum_eq_zero (s := hs.extendedPeriods \ hs.periods) (f := fun a => f a • a),
          ← Finset.sum_union Finset.sdiff_disjoint.symm,
          Finset.union_sdiff_of_subset hs.periods_subset_extendedPeriods] at hy
        · simp only [← hy, hs.floor_add_sum, hs.floor_base]
          grind
        · intro x hx
          simp only [Finset.mem_sdiff] at hx
          simp [hf x hx.2]
    · intro ⟨hx₁, hx₂⟩
      refine ⟨∑ i ∈ {i : hs.extendedPeriods | i.1 ∈ hs.periods}, (hs.floor x i).toNat • i.1,
        sum_mem fun i hi => smul_mem _ _ (mem_span_of_mem (Finset.mem_filter.1 hi).2), ?_⟩
      rw [Finset.sum_filter, ← hx₁]
      conv =>
        rhs
        rw [← add_zero x, ← Finset.sum_const_zero (ι := hs.extendedPeriods) (s := Finset.univ)]
      convert (hs.add_floor_neg_toNat_sum_eq x).symm using 3 with i _ i
      · split_ifs with hi
        · simp
        · simp [(hx₂ i).2 hi]
      · simp [fun i => Int.toNat_eq_zero.2 (neg_nonpos.2 (hx₂ i).1)]

  let s₁ : Set (α → ℕ) := {x | x ≠ hs.base ∧ ∃ y, x = hs.fract y}
  have hs₁ : s₁.Finite := by
    apply (Finset.Iic (hs.base + ∑ i : hs.extendedPeriods, i.1)).finite_toSet.subset
    rintro _ ⟨_, x, rfl⟩
    simpa only [Finset.coe_Iic, mem_Iic] using hs.fract_le_base_add x

  let s₂ : Set (α → ℕ) := {x | hs.fract x ≠ hs.base}
  have hs₂ : s₂.Semilinear := by
    convert_to (⋃ u ∈ s₁, {x | ∃ y ∈ span ℕ hs.extendedPeriods, ∃ y' ∈ span ℕ hs.extendedPeriods,
      x + y' = u + y}).Semilinear using 1
    · ext x
      simp only [s₂, s₁, mem_iUnion, mem_setOf, exists_prop]
      constructor
      · intro hx
        refine ⟨hs.fract x, ⟨hx, x, rfl⟩, ∑ i, (hs.floor x i).toNat • i.1, ?_,
          ∑ i, (-hs.floor x i).toNat • i.1, ?_, ?_⟩
        · exact sum_mem fun i _ => smul_mem _ _ (mem_span_of_mem i.2)
        · exact sum_mem fun i _ => smul_mem _ _ (mem_span_of_mem i.2)
        · exact hs.add_floor_neg_toNat_sum_eq x
      · rintro ⟨_, ⟨hz, ⟨z, rfl⟩⟩, y, hy, y', hy', heq⟩
        apply congr_arg hs.fract at heq
        rw [hs.fract_add_of_mem_span hy', hs.fract_add_of_mem_span hy, hs.fract_idem] at heq
        rwa [heq]
    · simp_rw [← hs₁.mem_toFinset]
      refine Semilinear.biUnion_finset fun i _ => Semilinear.proj' ?_
      rw [setOf_and]
      apply Semilinear.inter
      · exact (Semilinear.span_finset _).preimage (LinearMap.funLeft ℕ ℕ Sum.inr)
      · apply Semilinear.proj'
        rw [setOf_and]
        apply Semilinear.inter
        · exact (Semilinear.span_finset _).preimage (LinearMap.funLeft ℕ ℕ Sum.inr)
        · convert Semilinear.of_linear_equation (α := α) (β := (α ⊕ α) ⊕ α) 0 i
            (Matrix.fromCols (Matrix.fromCols 1 0) 1) (Matrix.fromCols (Matrix.fromCols 0 1) 0)
            using 1
          ext x
          simp only [mem_setOf, zero_add]
          conv => rhs; rw [← Sum.elim_comp_inl_inr x, ← Sum.elim_comp_inl_inr (x ∘ Sum.inl)]
          simp [-Sum.elim_comp_inl_inr]

  let s₃ : Set (α → ℕ) :=
    {x | hs.fract x = hs.base ∧ ∃ i, hs.floor x i < 0 ∨ i.1 ∉ hs.periods ∧ 0 < hs.floor x i}
  have hs₃ : s₃.Semilinear := by
    convert_to ((⋃ i : hs.extendedPeriods,
        {x | ∃ y ∈ span ℕ {i.1}, ∃ z ∈ span ℕ (hs.extendedPeriods \ {i.1} : Set (α → ℕ)),
          ∃ z' ∈ span ℕ (hs.extendedPeriods \ {i.1}: Set (α → ℕ)), x + i.1 + y + z' = hs.base + z})
      ∪ ⋃ i ∈ ({i : hs.extendedPeriods | i.1 ∉ hs.periods} : Finset _),
        {x | ∃ y ∈ span ℕ {i.1}, ∃ z ∈ span ℕ (hs.extendedPeriods \ {i.1} : Set (α → ℕ)),
          ∃ z' ∈ span ℕ (hs.extendedPeriods \ {i.1} : Set (α → ℕ)),
            x + z' = hs.base + i.1 + y + z}).Semilinear using 1
    · ext x
      simp only [s₃, mem_iUnion, mem_union, mem_setOf, exists_prop]
      constructor
      · rintro ⟨hx₁, i, hx₂ | ⟨hi, hx₂⟩⟩
        · refine Or.inl ⟨i, ((- hs.floor x i).toNat - 1) • i.1, ?_,
            ∑ j ∈ (Finset.univ.erase i : Finset _), (hs.floor x j).toNat • j.1, ?_,
            ∑ j ∈ (Finset.univ.erase i : Finset _), (- hs.floor x j).toNat • j.1, ?_, ?_⟩
          · exact smul_mem _ _ (mem_span_of_mem (mem_singleton i.1))
          · refine sum_mem fun j hj => smul_mem _ _ (mem_span_of_mem ?_)
            simpa [Subtype.val_inj] using hj
          · refine sum_mem fun j hj => smul_mem _ _ (mem_span_of_mem ?_)
            simpa [Subtype.val_inj] using hj
          · rw [add_assoc x, ← succ_nsmul',
              tsub_add_cancel_of_le
                ((Int.le_toNat (neg_pos.2 hx₂).le).2 (le_neg.1 (Int.cast_le_neg_one_of_neg hx₂))),
              add_assoc x,
              Finset.add_sum_erase _ (fun j => (- hs.floor x j).toNat • j.1) (Finset.mem_univ i),
              ← add_zero (Finset.sum (Finset.univ.erase i) _),
              ← zero_nsmul i.1, ← Int.toNat_eq_zero.2 hx₂.le,
              Finset.sum_erase_add _ _ (Finset.mem_univ i), ← hx₁]
            exact hs.add_floor_neg_toNat_sum_eq x
        · refine Or.inr ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩,
            ((hs.floor x i).toNat - 1) • i.1, ?_,
            ∑ j ∈ (Finset.univ.erase i : Finset _), (hs.floor x j).toNat • j.1, ?_,
            ∑ j ∈ (Finset.univ.erase i : Finset _), (- hs.floor x j).toNat • j.1, ?_, ?_⟩
          · exact smul_mem _ _ (mem_span_of_mem (mem_singleton i.1))
          · refine sum_mem fun j hj => smul_mem _ _ (mem_span_of_mem ?_)
            simpa [Subtype.val_inj] using hj
          · refine sum_mem fun j hj => smul_mem _ _ (mem_span_of_mem ?_)
            simpa [Subtype.val_inj] using hj
          · rw [add_assoc hs.base, ← succ_nsmul',
              tsub_add_cancel_of_le ((Int.le_toNat hx₂.le).2 (Int.add_one_le_of_lt hx₂)),
              add_assoc hs.base,
              Finset.add_sum_erase _ (fun j => (hs.floor x j).toNat • j.1) (Finset.mem_univ i),
              ← add_zero (Finset.sum (Finset.univ.erase i) _),
              ← zero_nsmul i.1, ← Int.toNat_eq_zero.2 (neg_neg_iff_pos.2 hx₂).le,
              Finset.sum_erase_add _ _ (Finset.mem_univ i), ← hx₁]
            exact hs.add_floor_neg_toNat_sum_eq x
      · rintro (⟨i, y, hy, z, hz, z', hz', heq⟩ | ⟨i, hi, y, hy, z, hz, z', hz', heq⟩)
        · refine ⟨?_, i, Or.inl ?_⟩
          · apply congr_arg hs.fract at heq
            rw [hs.fract_add_of_mem_span (span_mono diff_subset hz'),
              hs.fract_add_of_mem_span (span_mono (singleton_subset_iff.2 i.2) hy),
              hs.fract_add_of_mem_span (mem_span_of_mem i.2),
              hs.fract_add_of_mem_span (span_mono diff_subset hz), hs.fract_base] at heq
            exact heq
          · simp only [mem_span_singleton] at hy
            rcases hy with ⟨n, rfl⟩
            rw [← Finset.coe_erase, mem_span_finset] at hz hz'
            rcases hz with ⟨h, _, rfl⟩
            rcases hz' with ⟨h', _, rfl⟩
            apply congr_arg hs.floor at heq
            apply congr_fun (a := i) at heq
            rw [add_assoc x, ← succ_nsmul',
              hs.floor_add_sum_of_subset_of_notMem (Finset.erase_subset _ _)
                (Finset.notMem_erase _ _),
              hs.floor_add_smul_self,
              hs.floor_add_sum_of_subset_of_notMem (Finset.erase_subset _ _)
                (Finset.notMem_erase _ _), hs.floor_base] at heq
            simp only [Nat.cast_add, Nat.cast_one] at heq
            rw [← eq_neg_iff_add_eq_zero] at heq
            simpa [heq] using neg_one_lt_zero.trans_le (Nat.cast_nonneg _)
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          refine ⟨?_, i, Or.inr ⟨hi, ?_⟩⟩
          · apply congr_arg hs.fract at heq
            rw [hs.fract_add_of_mem_span (span_mono diff_subset hz'),
              hs.fract_add_of_mem_span (span_mono diff_subset hz),
              hs.fract_add_of_mem_span (span_mono (singleton_subset_iff.2 i.2) hy),
              hs.fract_add_of_mem_span (mem_span_of_mem i.2), hs.fract_base] at heq
            exact heq
          · simp only [mem_span_singleton] at hy
            rcases hy with ⟨n, rfl⟩
            rw [← Finset.coe_erase, mem_span_finset] at hz hz'
            rcases hz with ⟨h, _, rfl⟩
            rcases hz' with ⟨h', _, rfl⟩
            apply congr_arg hs.floor at heq
            apply congr_fun (a := i) at heq
            rw [hs.floor_add_sum_of_subset_of_notMem (Finset.erase_subset _ _)
                (Finset.notMem_erase _ _),
              add_assoc hs.base, ← succ_nsmul',
              hs.floor_add_sum_of_subset_of_notMem (Finset.erase_subset _ _)
                (Finset.notMem_erase _ _),
              hs.floor_add_smul_self, hs.floor_base] at heq
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
            · convert Semilinear.of_linear_equation (α := α) (β := ((α ⊕ α) ⊕ α) ⊕ α)
                i.1 hs.base
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
            · convert Semilinear.of_linear_equation (α := α) (β := ((α ⊕ α) ⊕ α) ⊕ α)
                0 (hs.base + i.1)
                (Matrix.fromCols (Matrix.fromCols (Matrix.fromCols 1 0) 0) 1)
                (Matrix.fromCols (Matrix.fromCols (Matrix.fromCols 0 1) 1) 0) using 1
              ext x
              simp only [mem_setOf]
              conv =>
                rhs
                rw [← Sum.elim_comp_inl_inr x, ← Sum.elim_comp_inl_inr (x ∘ Sum.inl),
                  ← Sum.elim_comp_inl_inr ((x ∘ Sum.inl) ∘ Sum.inl)]
              simp [-Sum.elim_comp_inl_inr, add_assoc]

  convert hs₂.union hs₃ using 1
  ext x
  simp only [s₂, s₃, mem_compl_iff, hs', Subtype.forall, not_and, not_forall, ne_eq, Subtype.exists,
    mem_union, mem_setOf_eq]
  grind

end ProperLinear

/-- Semilinear sets in `α → ℕ` (with finite `α`) are closed under complement. -/
theorem Semilinear.compl [Fintype α] (hs : s.Semilinear) : sᶜ.Semilinear := by
  classical
  rcases hs.proper_semilinear with ⟨S, hS, rfl⟩
  simp_rw [sUnion_eq_biUnion, Finset.mem_coe, compl_iUnion]
  exact biInter_finset fun s hs => (hS s hs).compl

end Set
