/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.Algebra.Order.Sub.Unbundled.Hom
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Rat.Floor
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Localization.Module

/-!
# Semilinear sets in `ℕ ^ k`

This file proves that the semilinear sets in `ℕ ^ k` are closed under intersection, complement and
set difference.

## Main Results

- `Nat.addSubmonoidFG_eqLocusM`: a verison of *Gordan's lemma*, `{ x | f x = g x }` is a finitely
  generated `AddSubmonoid` in `ℕ ^ k`.
- `Nat.isSemilinearSet_setOf_eq`: the set of solutions of a linear equation `a + f x = b + g y` is a
  semilinear set.
- `Nat.isSemilinearSet_inter`, `Nat.isSemilinearSet_compl`, `Nat.isSemilinearSet_diff`: semilinear
  sets in `ℕ ^ k` are closed under intersection, complement and set difference.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

variable {M ι κ : Type*} [AddCommMonoid M]

open Set Pointwise AddSubmonoid Matrix

/-! ### Semilinear sets in `ℕ ^ k` are closed under intersection -/

/-- Any subtractive `AddSubmonoid` in `ℕ ^ k` is linear. -/
theorem Nat.addSubmonoidFG_of_subtractive [Finite ι] {P : AddSubmonoid (ι → ℕ)}
    (hP : ∀ x ∈ P, ∀ y, x + y ∈ P → y ∈ P) : P.FG := by
  have hpwo := Pi.isPWO { x | x ∈ P ∧ x ≠ 0 }
  rw [fg_iff]
  refine ⟨_, ?_, (setOf_minimal_antichain _).finite_of_partiallyWellOrderedOn
    (hpwo.mono (setOf_minimal_subset _))⟩
  ext x
  constructor
  · intro hx
    rw [← P.closure_eq]
    exact closure_mono ((setOf_minimal_subset _).trans fun _ => And.left) hx
  · intro hx₁
    by_cases hx₂ : x = 0
    · simp [hx₂]
    refine hpwo.wellFoundedOn.induction ⟨hx₁, hx₂⟩ fun y ⟨hy₁, hy₂⟩ ih => ?_
    simp only [mem_setOf_eq, and_imp] at ih
    by_cases hy₃ : Minimal { x | x ∈ P ∧ x ≠ 0 } y
    · exact mem_closure_of_mem hy₃
    rcases exists_lt_of_not_minimal ⟨hy₁, hy₂⟩ hy₃ with ⟨z, hz₁, hz₂, hz₃⟩
    rw [← tsub_add_cancel_of_le hz₁.le]
    apply add_mem
    · apply ih
      · rw [← add_tsub_cancel_of_le hz₁.le] at hy₁
        exact hP _ hz₂ _ hy₁
      · exact (tsub_pos_of_lt hz₁).ne'
      · exact tsub_le_self
      · rw [le_tsub_iff_le_tsub (le_refl _) hz₁.le, tsub_self]
        exact (pos_of_ne_zero hz₃).not_ge
    · exact ih _ hz₂ hz₃ hz₁.le hz₁.not_ge

/-- A verison of *Gordan's lemma*: `{ x | f x = g x }` is a finitely generated `AddSubmonoid` in
`ℕ ^ k`. -/
theorem Nat.addSubmonoidFG_eqLocusM [Finite ι] [IsCancelAdd M] (f g : (ι → ℕ) →+ M) :
    (f.eqLocusM g).FG :=
  addSubmonoidFG_of_subtractive (by simp_all)

/-- The set of solutions of a linear equation `a + f x = b + g y` is a semilinear set. -/
theorem Nat.isSemilinearSet_setOf_eq [Finite ι] [IsCancelAdd M] {F : Type*} [FunLike F (ι → ℕ) M]
    [AddMonoidHomClass F (ι → ℕ) M] (a b : M) (f g : F) :
    IsSemilinearSet { x | a + f x = b + g x } := by
  have hpwo := Pi.isPWO { x | a + f x = b + g x }
  convert (IsSemilinearSet.of_finite <| (setOf_minimal_antichain _).finite_of_partiallyWellOrderedOn
    (hpwo.mono (setOf_minimal_subset _))).add
      (IsSemilinearSet.of_fg (addSubmonoidFG_eqLocusM (f : (ι → ℕ) →+ M) g)) using 1
  ext x
  simp only [mem_setOf_eq, mem_add]
  constructor
  · intro hx
    obtain ⟨y, hy₁, hy₂⟩ := hpwo.exists_le_minimal hx
    refine ⟨y, hy₂, x - y, ?_, add_tsub_cancel_of_le hy₁⟩
    rw [← add_tsub_cancel_of_le hy₁] at hx
    simp_rw [map_add, ← add_assoc] at hx
    rwa [hy₂.1, add_left_cancel_iff] at hx
  · rintro ⟨y, ⟨hy, -⟩, z, hz₁, rfl⟩
    simp only [SetLike.mem_coe, AddMonoidHom.mem_eqLocusM, AddMonoidHom.coe_coe] at hz₁
    simpa [← add_assoc, hz₁]

theorem Nat.isSemilinearSet_setOf_mulVec_eq [Fintype κ] (u v : ι → ℕ) (A B : Matrix ι κ ℕ) :
    IsSemilinearSet { x | u + A *ᵥ x = v + B *ᵥ x } :=
  isSemilinearSet_setOf_eq u v A.mulVecLin B.mulVecLin

theorem isLinearSet_iff_exists_fin_addMonoidHom {s : Set M} :
    IsLinearSet s ↔ ∃ (a : M) (n : ℕ) (f : (Fin n → ℕ) →+ M), s = a +ᵥ Set.range f := by
  simp_rw [isLinearSet_iff_exists_fg_eq_vadd, fg_iff_exists_fin_addMonoidHom]
  refine exists_congr fun a => ⟨fun ⟨P, ⟨n, f, hf⟩, hs⟩ => ⟨n, f, ?_⟩, fun ⟨n, f, hs⟩ =>
    ⟨_, ⟨n, f, rfl⟩, ?_⟩⟩
  · rw [← AddMonoidHom.coe_mrange, hf, hs]
  · rw [AddMonoidHom.coe_mrange, hs]

theorem Nat.isLinearSet_iff_exists_matrix {s : Set (ι → ℕ)} :
    IsLinearSet s ↔ ∃ (v : ι → ℕ) (n : ℕ) (A : Matrix ι (Fin n) ℕ), s = { v + A *ᵥ x | x } := by
  rw [isLinearSet_iff_exists_fin_addMonoidHom]
  refine exists₂_congr fun v n => ⟨fun ⟨f, hf⟩ => ⟨f.toNatLinearMap.toMatrix', ?_⟩, fun ⟨A, hA⟩ =>
    ⟨A.mulVecLin, ?_⟩⟩ <;> ext <;> simp [*, mem_vadd_set]

lemma Nat.isSemilinearSet_preimage_of_isLinearSet [Finite ι] [IsCancelAdd M] {F : Type*}
    [FunLike F (ι → ℕ) M] [AddMonoidHomClass F (ι → ℕ) M] {s : Set M} (hs : IsLinearSet s) (f : F) :
    IsSemilinearSet (f ⁻¹' s) := by
  rw [isLinearSet_iff_exists_fin_addMonoidHom] at hs
  rcases hs with ⟨a, n, g, rfl⟩
  change IsSemilinearSet { x | f x ∈ _ }
  simp only [mem_vadd_set, mem_range, vadd_eq_add, exists_exists_eq_and]
  apply IsSemilinearSet.proj'
  convert isSemilinearSet_setOf_eq a 0 (g.comp (LinearMap.funLeft ℕ ℕ Sum.inr).toAddMonoidHom)
    ((f : (ι → ℕ) →+ M).comp (LinearMap.funLeft ℕ ℕ Sum.inl).toAddMonoidHom)
  simp [LinearMap.funLeft]

theorem Nat.isSemilinearSet_preimage [Finite ι] [IsCancelAdd M] {F : Type*} [FunLike F (ι → ℕ) M]
    [AddMonoidHomClass F (ι → ℕ) M] {s : Set M} (hs : IsSemilinearSet s) (f : F) :
    IsSemilinearSet (f ⁻¹' s) := by
  rcases hs with ⟨S, hS, hS', rfl⟩
  simp_rw [sUnion_eq_biUnion, preimage_iUnion]
  exact .biUnion hS fun s hs => isSemilinearSet_preimage_of_isLinearSet (hS' s hs) f

variable {s s₁ s₂ : Set (ι → ℕ)}

lemma Nat.isSemilinearSet_inter_of_isLinearSet [Finite ι] (hs₁ : IsLinearSet s₁)
    (hs₂ : IsLinearSet s₂) : IsSemilinearSet (s₁ ∩ s₂) := by
  classical
  haveI := Fintype.ofFinite ι
  rw [isLinearSet_iff_exists_matrix] at hs₁ hs₂
  rcases hs₁ with ⟨u, n, A, rfl⟩
  rcases hs₂ with ⟨v, m, B, rfl⟩
  simp_rw [← setOf_and, exists_and_exists_comm]
  refine IsSemilinearSet.proj' (IsSemilinearSet.proj' ?_)
  convert isSemilinearSet_setOf_mulVec_eq (κ := (ι ⊕ Fin n) ⊕ Fin m) (Sum.elim u v) 0
    (fromBlocks (fromCols 0 A) 0 0 B) (fromBlocks (fromCols 1 0) 0 (fromCols 1 0) 0)
  simp [fromBlocks_mulVec, fromCols_mulVec, ← Sum.elim_add_add, Sum.elim_eq_iff]

/-- Semilinear sets in `ℕ ^ k` are closed under intersection. -/
theorem Nat.isSemilinearSet_inter [Finite ι] (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) :
    IsSemilinearSet (s₁ ∩ s₂) := by
  rcases hs₁ with ⟨S₁, hS₁, hS₁', rfl⟩
  rcases hs₂ with ⟨S₂, hS₂, hS₂', rfl⟩
  rw [sUnion_inter_sUnion]
  exact .biUnion (hS₁.prod hS₂) fun s hs =>
    isSemilinearSet_inter_of_isLinearSet (hS₁' _ hs.1) (hS₂' _ hs.2)

theorem Nat.isSemilinearSet_sInter [Finite ι] {S : Set (Set (ι → ℕ))} (hS : S.Finite)
    (hS' : ∀ s ∈ S, IsSemilinearSet s) : IsSemilinearSet (⋂₀ S) := by
  induction S, hS using Finite.induction_on with
  | empty => simp
  | insert _ _ ih =>
    simp_rw [mem_insert_iff, forall_eq_or_imp] at hS'
    simpa using isSemilinearSet_inter hS'.1 (ih hS'.2)

theorem Nat.isSemilinearSet_biInter [Finite κ] {s : Set ι} {t : ι → Set (κ → ℕ)} (hs : s.Finite)
    (ht : ∀ i ∈ s, IsSemilinearSet (t i)) : IsSemilinearSet (⋂ i ∈ s, t i) := by
  rw [← sInter_image]
  apply isSemilinearSet_sInter (hs.image t)
  simpa

theorem Nat.isSemilinearSet_biInter_finset [Finite κ] {s : Finset ι} {t : ι → Set (κ → ℕ)}
    (ht : ∀ i ∈ s, IsSemilinearSet (t i)) : IsSemilinearSet (⋂ i ∈ s, t i) :=
  isSemilinearSet_biInter s.finite_toSet ht

/-! ### Semilinear sets in `ℕ ^ k` are closed under complement and set difference

We first show that the complement of a proper linear set `s` in `ℕ ^ k` is semilinear, through
several private defintions:

1. `base`, `periods`: the base vector and the set of periods of the proper linear set `s`.
2. `basisSet`, `basis`: the linearly independent periods of `s` can be extended to a basis of
  `ℚ ^ k`.
3. `fundamentalDomain`: the set of vectors in `ℕ ^ k`, starting from `base`, with coordinates under
  `basis` in `[0, 1) ^ k`.
4. `floor`, `fract`: every vector in `ℕ ^ k` can be decomposed into a `ℤ`-linear combination of
  `basisSet` and a vector in `fundamentalDomain`.
5. `setOfFractNe`, `setOfFloorNeg`, `setOfFloorPos`: the complement of `s` is decomposed into three
  semilinear sets.

Closure of semilinear sets under complement and set difference follows.
-/

private def toRatVec : (ι → ℕ) →+ (ι → ℚ) :=
  LinearMap.compLeft (Nat.castAddMonoidHom ℚ).toNatLinearMap ι

private theorem toRatVec_inj (x y : ι → ℕ) : toRatVec x = toRatVec y ↔ x = y := by
  refine ⟨fun h => ?_, congr_arg toRatVec⟩
  ext i
  simpa [toRatVec] using congr_fun h i

private theorem toRatVec_mono (x y : ι → ℕ) : toRatVec x ≤ toRatVec y ↔ x ≤ y := by
  rw [Pi.le_def, Pi.le_def]
  apply forall_congr'
  simp [toRatVec]

private theorem toRatVec_nonneg (x : ι → ℕ) : 0 ≤ toRatVec x := by
  rw [← map_zero toRatVec, toRatVec_mono]
  simp

private theorem linearIndepOn_toRatVec {s : Set (ι → ℕ)} (hs : LinearIndepOn ℕ id s) :
    LinearIndepOn ℚ toRatVec s := by
  rw [LinearIndepOn, ← LinearIndependent.iff_fractionRing ℤ ℚ, ← LinearIndepOn, linearIndepOn_iff'']
  intro t f ht hf heq i hi
  rw [linearIndepOn_iff_linearIndepOn_finset] at hs
  specialize hs t ht
  rw [linearIndepOn_finset_iffₛ] at hs
  specialize hs (Int.toNat ∘ f) (Int.toNat ∘ (- ·) ∘ f) ?_ i hi
  · simp_rw [← toRatVec_inj, map_sum]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← heq]
    refine Finset.sum_congr rfl fun j hj => ?_
    conv_rhs => rw [← (f j).toNat_sub_toNat_neg]
    simp only [sub_smul, map_nsmul, natCast_zsmul, Function.comp_apply, id_eq]
  · rw [← (f i).toNat_sub_toNat_neg, sub_eq_zero, Int.natCast_inj]
    simpa using hs

namespace IsProperLinearSet

variable (hs : IsProperLinearSet s)

open Module Submodule

private noncomputable def base : ι → ℕ := hs.choose

private noncomputable def periods : Set (ι → ℕ) := hs.choose_spec.choose

private theorem finite_periods : hs.periods.Finite := hs.choose_spec.choose_spec.1

private theorem linearIndepOn_periods : LinearIndepOn ℕ id (hs.periods : Set (ι → ℕ)) :=
  hs.choose_spec.choose_spec.2.1

private theorem eq_base_vadd_closure_periods : s = hs.base +ᵥ (closure hs.periods : Set (ι → ℕ)) :=
  hs.choose_spec.choose_spec.2.2

variable [Finite ι]

private noncomputable def basisSet : Set (ι → ℕ) :=
  (linearIndepOn_toRatVec hs.linearIndepOn_periods).extend
    (@subset_union_left _ hs.periods <| range (Pi.basisFun ℕ ι))

private theorem periods_subset_basisSet : hs.periods ⊆ hs.basisSet :=
  (linearIndepOn_toRatVec hs.linearIndepOn_periods).subset_extend _

private theorem basisSet_subset_union : hs.basisSet ⊆ hs.periods ∪ range (Pi.basisFun ℕ ι) :=
  (linearIndepOn_toRatVec hs.linearIndepOn_periods).extend_subset _

private theorem finite_basisSet : hs.basisSet.Finite :=
  (hs.finite_periods.union (finite_range _)).subset hs.basisSet_subset_union

private noncomputable local instance : Fintype hs.basisSet :=
  hs.finite_basisSet.fintype

private theorem linearIndepOn_basisSet : LinearIndepOn ℚ toRatVec hs.basisSet :=
  (linearIndepOn_toRatVec hs.linearIndepOn_periods).linearIndepOn_extend _

private theorem span_basisSet : span ℚ (toRatVec '' hs.basisSet) = ⊤ := by
  classical
  rw [basisSet, (linearIndepOn_toRatVec hs.linearIndepOn_periods).span_image_extend_eq_span_image,
    ← top_le_iff]
  apply (span_mono (image_mono subset_union_right)).trans'
  rw [top_le_iff]
  convert (Pi.basisFun ℚ ι).span_eq
  ext
  simp only [mem_image, mem_range, exists_exists_eq_and]
  congr!
  ext
  simp [toRatVec, Pi.basisFun_apply, Pi.single_apply]

private noncomputable def basis : Basis hs.basisSet ℚ (ι → ℚ) :=
  Basis.mk hs.linearIndepOn_basisSet (image_eq_range _ _ ▸ top_le_iff.2 hs.span_basisSet)

private theorem basis_apply (i) : hs.basis i = toRatVec i.1 := by
  simp [basis]

private noncomputable def fundamentalDomain : Set (ι → ℕ) :=
  { x | ∀ i, hs.basis.repr (toRatVec x - toRatVec hs.base) i ∈ Ico 0 1 }

private theorem finite_fundamentalDomain : hs.fundamentalDomain.Finite := by
  classical
  haveI := Fintype.ofFinite ι
  apply (finite_Iic (hs.base + ∑ i : hs.basisSet, i.1)).subset
  intro x hx
  rw [mem_Iic, ← toRatVec_mono, map_add, map_sum, ← add_sub_cancel (toRatVec hs.base) (toRatVec x),
    add_le_add_iff_left, ← hs.basis.sum_repr (toRatVec x - toRatVec hs.base)]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [← hs.basis_apply i]
  apply smul_le_of_le_one_left
  · rw [hs.basis_apply]
    exact toRatVec_nonneg _
  · exact (hx i).2.le

private noncomputable def floor (x i) :=
  ⌊hs.basis.repr (toRatVec x - toRatVec hs.base) i⌋

private noncomputable def fract (x) :=
  x + ∑ i, (- hs.floor x i).toNat • i.1 - ∑ i, (hs.floor x i).toNat • i.1

private theorem floor_base (i) : hs.floor hs.base i = 0 := by simp [floor]

private theorem fract_base : hs.fract hs.base = hs.base := by simp [fract, hs.floor_base]

private theorem floor_add_nsmul_self {x i} {n : ℕ} :
    hs.floor (x + n • i.1) i = hs.floor x i + n := by
  simp only [floor]
  rw [map_add, ← sub_add_eq_add_sub]
  simp [-nsmul_eq_mul, ← hs.basis_apply]

private theorem floor_add_sum {f : (ι → ℕ) → ℕ} {x i} :
    hs.floor (x + ∑ j : hs.basisSet, f j • j.1) i = hs.floor x i + f i.1 := by
  classical
  simp only [floor]
  rw [map_add, ← sub_add_eq_add_sub, ← Finset.sum_coe_sort]
  simp [-nsmul_eq_mul, ← hs.basis_apply, Finsupp.single_apply]

private theorem floor_le_floor_add_of_mem_closure {x y i} (hy : y ∈ closure hs.basisSet) :
    hs.floor x i ≤ hs.floor (x + y) i := by
  classical
  simp only [floor]
  apply Int.floor_le_floor
  simp_rw [map_add, add_sub_right_comm, map_add, Finsupp.add_apply, le_add_iff_nonneg_right]
  rw [mem_closure_iff_of_fintype] at hy
  rcases hy with ⟨f, rfl⟩
  simp_rw [map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
  apply Finset.sum_nonneg
  simp [-nsmul_eq_mul, ← hs.basis_apply, Finsupp.single_apply, ite_nonneg]

private theorem floor_add_of_mem_closure {x y i t} (ht : t ⊆ hs.basisSet) (hi : i.1 ∉ t)
    (hy : y ∈ closure t) : hs.floor (x + y) i = hs.floor x i := by
  classical
  suffices hs.basis.repr (toRatVec y) i = 0 by
    simp [floor, this]
  induction hy using AddSubmonoid.closure_induction with
  | mem y hy =>
    rw [← hs.basis_apply ⟨y, ht hy⟩]
    simpa [Finsupp.single_apply, ← Subtype.val_inj] using ne_of_mem_of_not_mem hy hi
  | zero => simp
  | add _ _ _ _ ih₁ ih₂ => simp [ih₁, ih₂]

private theorem floor_toNat_sum_le (x) :
    ∑ i, (hs.floor x i).toNat • i.1 ≤ x + ∑ i, (- hs.floor x i).toNat • i.1 := by
  rw [← toRatVec_mono]
  simp only [floor, map_add, map_sum, map_nsmul]
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
  simp only [map_add, map_sum, map_nsmul]
  rw [← sub_add_eq_add_sub, sub_add, ← Finset.sum_sub_distrib]
  conv =>
    enter [1, 2, 2, _]
    rw [← Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul ℤ, ← sub_smul,
      Int.toNat_sub_toNat_neg]
  rw [sub_eq_iff_eq_add, add_assoc, ← sub_eq_iff_eq_add', ← Finset.sum_add_distrib]
  simp only [floor]
  conv =>
    enter [2, 2, _]
    rw [← Int.cast_smul_eq_zsmul ℚ, ← add_smul, Int.fract_add_floor, ← hs.basis_apply]
  rw [hs.basis.sum_repr]

private theorem fract_add_of_mem_closure {x y} (hy : y ∈ closure hs.basisSet) :
    hs.fract (x + y) = hs.fract x := by
  classical
  rw [mem_closure_iff_of_fintype] at hy
  rcases hy with ⟨f, t, ht, hf, rfl⟩
  rw [← toRatVec_inj, hs.toRatVec_fract_eq, hs.toRatVec_fract_eq]
  congr! 3
  rw [map_add, ← sub_add_eq_add_sub]
  simp [-nsmul_eq_mul, ← hs.basis_apply, Finsupp.single_apply]

private theorem fract_mem_fundamentalDomain (x) : hs.fract x ∈ hs.fundamentalDomain := by
  classical
  intro i
  constructor
  · rw [hs.toRatVec_fract_eq, add_sub_cancel_left]
    simp [← hs.basis_apply, Finsupp.single_apply]
  · rw [hs.toRatVec_fract_eq, add_sub_cancel_left]
    simp [← hs.basis_apply, Finsupp.single_apply, Int.fract_lt_one]

private theorem fract_eq_self_of_mem_fundamentalDomain {x} (hx : x ∈ hs.fundamentalDomain) :
    hs.fract x = x := by
  rw [← toRatVec_inj, hs.toRatVec_fract_eq]
  conv_lhs =>
    enter [2, 2, i]
    rw [Int.fract_eq_self.2 (hx i), ← hs.basis_apply]
  rw [hs.basis.sum_repr]
  simp

private theorem mem_iff_fract_eq_and_floor_nonneg (x) :
    x ∈ s ↔
      hs.fract x = hs.base ∧ ∀ i, 0 ≤ hs.floor x i ∧ (i.1 ∉ hs.periods → hs.floor x i = 0) := by
  classical
  nth_rw 1 [hs.eq_base_vadd_closure_periods]
  simp only [mem_vadd_set, SetLike.mem_coe, vadd_eq_add]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, fun i => ⟨?_, fun hi => ?_⟩⟩
    · rw [hs.fract_add_of_mem_closure, hs.fract_base]
      exact closure_mono hs.periods_subset_basisSet hy
    · rw [← hs.floor_base i]
      exact hs.floor_le_floor_add_of_mem_closure (closure_mono hs.periods_subset_basisSet hy)
    · rw [hs.floor_add_of_mem_closure hs.periods_subset_basisSet hi hy, hs.floor_base]
  · intro ⟨hx₁, hx₂⟩
    refine ⟨∑ i : hs.basisSet with i.1 ∈ hs.periods, (hs.floor x i).toNat • i.1,
      sum_mem fun i hi => nsmul_mem (mem_closure_of_mem (Finset.mem_filter.1 hi).2) _, ?_⟩
    rw [Finset.sum_filter, ← hx₁]
    conv_rhs =>
      rw [← add_zero x, ← Finset.sum_const_zero (ι := hs.basisSet) (s := Finset.univ)]
    convert (hs.add_floor_neg_toNat_sum_eq x).symm using 3 with i _ i
    · split_ifs with hi
      · simp
      · simp [(hx₂ i).2 hi]
    · simp [fun i => Int.toNat_eq_zero.2 (neg_nonpos.2 (hx₂ i).1)]

private noncomputable def setOfFractNe : Set (ι → ℕ) := { x | hs.fract x ≠ hs.base }

private theorem isSemilinearSet_setOfFractNe : IsSemilinearSet hs.setOfFractNe := by
  convert_to IsSemilinearSet (⋃ u ∈ hs.fundamentalDomain \ {hs.base}, { x |
    ∃ y ∈ closure hs.basisSet, ∃ y' ∈ closure hs.basisSet, x + y' = u + y }) using 1
  · ext x
    simp only [setOfFractNe, mem_iUnion, mem_setOf_eq, exists_prop]
    constructor
    · intro hx
      refine ⟨hs.fract x, ⟨hs.fract_mem_fundamentalDomain x, hx⟩, ∑ i, (hs.floor x i).toNat • i.1,
        ?_, ∑ i, (-hs.floor x i).toNat • i.1, ?_, ?_⟩
      · exact sum_mem fun i _ => nsmul_mem (mem_closure_of_mem i.2) _
      · exact sum_mem fun i _ => nsmul_mem (mem_closure_of_mem i.2) _
      · exact hs.add_floor_neg_toNat_sum_eq x
    · rintro ⟨u, ⟨hu, hu'⟩, y, hy, y', hy', heq⟩
      apply congr_arg hs.fract at heq
      rw [hs.fract_add_of_mem_closure hy', hs.fract_add_of_mem_closure hy,
        hs.fract_eq_self_of_mem_fundamentalDomain hu] at heq
      rwa [heq]
  · refine .biUnion hs.finite_fundamentalDomain.diff fun i hi => .proj' ?_
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite hs.finite_basisSet) (LinearMap.funLeft ℕ ℕ Sum.inr)
    apply IsSemilinearSet.proj'
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite hs.finite_basisSet) (LinearMap.funLeft ℕ ℕ Sum.inr)
    classical
    haveI := Fintype.ofFinite ι
    convert Nat.isSemilinearSet_setOf_mulVec_eq (κ := (ι ⊕ ι) ⊕ ι) 0 i
      (Matrix.fromCols (Matrix.fromCols 1 0) 1) (Matrix.fromCols (Matrix.fromCols 0 1) 0)
      using 4 <;> simp [fromCols_mulVec]

private noncomputable def setOfFloorNeg : Set (ι → ℕ) :=
  { x | hs.fract x = hs.base ∧ ∃ i, hs.floor x i < 0 }

private theorem isSemilinearSet_setOfFloorNeg : IsSemilinearSet hs.setOfFloorNeg := by
  classical
  convert_to IsSemilinearSet (⋃ i : hs.basisSet, { x | ∃ y ∈ closure {i.1},
    ∃ z ∈ closure (hs.basisSet \ {i.1}), ∃ z' ∈ closure (hs.basisSet \ {i.1}),
      x + i.1 + y + z' = hs.base + z }) using 1
  · ext x
    simp only [setOfFloorNeg, mem_iUnion, mem_setOf_eq]
    constructor
    · intro ⟨hx, i, hi⟩
      refine ⟨i, ((- hs.floor x i).toNat - 1) • i.1, ?_,
        ∑ j ∈ Finset.univ.erase i, (hs.floor x j).toNat • j.1, ?_,
        ∑ j ∈ Finset.univ.erase i, (- hs.floor x j).toNat • j.1, ?_, ?_⟩
      · exact nsmul_mem (mem_closure_of_mem (mem_singleton i.1)) _
      · refine sum_mem fun j hj => nsmul_mem (mem_closure_of_mem ?_) _
        simpa [Subtype.val_inj] using hj
      · refine sum_mem fun j hj => nsmul_mem (mem_closure_of_mem ?_) _
        simpa [Subtype.val_inj] using hj
      · rw [add_assoc x, ← succ_nsmul',
          tsub_add_cancel_of_le
            ((Int.le_toNat (neg_pos.2 hi).le).2 (le_neg.1 (Int.cast_le_neg_one_of_neg hi))),
          add_assoc x,
          Finset.add_sum_erase _ (fun j => (- hs.floor x j).toNat • j.1) (Finset.mem_univ i),
          ← add_zero (Finset.sum (Finset.univ.erase i) _),
          ← zero_nsmul i.1, ← Int.toNat_eq_zero.2 hi.le,
          Finset.sum_erase_add _ _ (Finset.mem_univ i), ← hx]
        exact hs.add_floor_neg_toNat_sum_eq x
    · intro ⟨i, y, hy, z, hz, z', hz', heq⟩
      refine ⟨?_, i, ?_⟩
      · apply congr_arg hs.fract at heq
        rwa [hs.fract_add_of_mem_closure (closure_mono diff_subset hz'),
          hs.fract_add_of_mem_closure (closure_mono (singleton_subset_iff.2 i.2) hy),
          hs.fract_add_of_mem_closure (mem_closure_of_mem i.2),
          hs.fract_add_of_mem_closure (closure_mono diff_subset hz), hs.fract_base] at heq
      · rw [mem_closure_singleton] at hy
        rcases hy with ⟨n, rfl⟩
        apply congr_arg (hs.floor · i) at heq
        rw [hs.floor_add_of_mem_closure diff_subset (notMem_diff_of_mem (mem_singleton i.1)) hz,
          hs.floor_add_of_mem_closure diff_subset (notMem_diff_of_mem (mem_singleton i.1)) hz',
          hs.floor_base, add_assoc x, ← succ_nsmul', hs.floor_add_nsmul_self,
          ← eq_neg_iff_add_eq_zero] at heq
        simpa [heq] using neg_one_lt_zero.trans_le (Nat.cast_nonneg _)
  · refine .iUnion fun i => .proj' ?_
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite (finite_singleton _)) (LinearMap.funLeft ℕ ℕ Sum.inr)
    apply IsSemilinearSet.proj'
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite hs.finite_basisSet.diff) (LinearMap.funLeft ℕ ℕ Sum.inr)
    apply IsSemilinearSet.proj'
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite hs.finite_basisSet.diff) (LinearMap.funLeft ℕ ℕ Sum.inr)
    haveI := Fintype.ofFinite ι
    convert Nat.isSemilinearSet_setOf_mulVec_eq (κ := ((ι ⊕ ι) ⊕ ι) ⊕ ι) i.1 hs.base
      (Matrix.fromCols (Matrix.fromCols (Matrix.fromCols 1 1) 0) 1)
      (Matrix.fromCols (Matrix.fromCols (Matrix.fromCols 0 0) 1) 0) using 4
      <;> simp [add_comm _ i.1, add_assoc, fromCols_mulVec]

private noncomputable def setOfFloorPos : Set (ι → ℕ) :=
  { x | hs.fract x = hs.base ∧ ∃ i, i.1 ∉ hs.periods ∧ 0 < hs.floor x i }

private theorem isSemilinearSet_setOfFloorPos : IsSemilinearSet hs.setOfFloorPos := by
  classical
  convert_to IsSemilinearSet (⋃ i ∈ { i : hs.basisSet | i.1 ∉ hs.periods },
    { x | ∃ y ∈ closure {i.1}, ∃ z ∈ closure (hs.basisSet \ {i.1}),
      ∃ z' ∈ closure (hs.basisSet \ {i.1}), x + z' = hs.base + i.1 + y + z }) using 1
  · ext x
    simp only [setOfFloorPos, mem_iUnion, mem_setOf_eq, exists_prop]
    constructor
    · intro ⟨hx, i, hi, hi'⟩
      refine ⟨i, hi, ((hs.floor x i).toNat - 1) • i.1, ?_,
          ∑ j ∈ Finset.univ.erase i, (hs.floor x j).toNat • j.1, ?_,
          ∑ j ∈ Finset.univ.erase i, (- hs.floor x j).toNat • j.1, ?_, ?_⟩
      · exact nsmul_mem (mem_closure_of_mem (mem_singleton i.1)) _
      · refine sum_mem fun j hj => nsmul_mem (mem_closure_of_mem ?_) _
        simpa [Subtype.val_inj] using hj
      · refine sum_mem fun j hj => nsmul_mem (mem_closure_of_mem ?_) _
        simpa [Subtype.val_inj] using hj
      · rw [add_assoc hs.base, ← succ_nsmul',
          tsub_add_cancel_of_le ((Int.le_toNat hi'.le).2 (Int.add_one_le_of_lt hi')),
          add_assoc hs.base,
          Finset.add_sum_erase _ (fun j => (hs.floor x j).toNat • j.1) (Finset.mem_univ i),
          ← add_zero (Finset.sum (Finset.univ.erase i) _),
          ← zero_nsmul i.1, ← Int.toNat_eq_zero.2 (neg_neg_iff_pos.2 hi').le,
          Finset.sum_erase_add _ _ (Finset.mem_univ i), ← hx]
        exact hs.add_floor_neg_toNat_sum_eq x
    · intro ⟨i, hi, y, hy, z, hz, z', hz', heq⟩
      refine ⟨?_, i, hi, ?_⟩
      · apply congr_arg hs.fract at heq
        rwa [hs.fract_add_of_mem_closure (closure_mono diff_subset hz'),
          hs.fract_add_of_mem_closure (closure_mono diff_subset hz),
          hs.fract_add_of_mem_closure (closure_mono (singleton_subset_iff.2 i.2) hy),
          hs.fract_add_of_mem_closure (mem_closure_of_mem i.2), hs.fract_base] at heq
      · rw [mem_closure_singleton] at hy
        rcases hy with ⟨n, rfl⟩
        apply congr_arg (hs.floor · i) at heq
        rw [hs.floor_add_of_mem_closure diff_subset (notMem_diff_of_mem (mem_singleton i.1)) hz,
          hs.floor_add_of_mem_closure diff_subset (notMem_diff_of_mem (mem_singleton i.1)) hz',
          add_assoc hs.base, ← succ_nsmul', hs.floor_add_nsmul_self, hs.floor_base, zero_add] at heq
        simp [heq]
  · refine .biUnion (finite_univ.subset (subset_univ _)) fun i hi => .proj' ?_
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite (finite_singleton _)) (LinearMap.funLeft ℕ ℕ Sum.inr)
    apply IsSemilinearSet.proj'
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite hs.finite_basisSet.diff) (LinearMap.funLeft ℕ ℕ Sum.inr)
    apply IsSemilinearSet.proj'
    rw [setOf_and]
    apply Nat.isSemilinearSet_inter <| Nat.isSemilinearSet_preimage
      (.closure_of_finite hs.finite_basisSet.diff) (LinearMap.funLeft ℕ ℕ Sum.inr)
    haveI := Fintype.ofFinite ι
    convert Nat.isSemilinearSet_setOf_mulVec_eq (κ := ((ι ⊕ ι) ⊕ ι) ⊕ ι) 0 (hs.base + i.1)
        (Matrix.fromCols (Matrix.fromCols (Matrix.fromCols 1 0) 0) 1)
        (Matrix.fromCols (Matrix.fromCols (Matrix.fromCols 0 1) 1) 0) using 4
      <;> simp [add_assoc, fromCols_mulVec]

end IsProperLinearSet

lemma Nat.isSemilinearSet_compl_of_isProperLinearSet [Finite ι] (hs : IsProperLinearSet s) :
    IsSemilinearSet sᶜ := by
  convert hs.isSemilinearSet_setOfFractNe.union <| hs.isSemilinearSet_setOfFloorNeg.union <|
    hs.isSemilinearSet_setOfFloorPos using 1
  ext
  simp only [mem_compl_iff, hs.mem_iff_fract_eq_and_floor_nonneg, IsProperLinearSet.setOfFractNe,
    IsProperLinearSet.setOfFloorNeg, IsProperLinearSet.setOfFloorPos, mem_union, mem_setOf_eq]
  grind

/-- Semilinear sets in `ℕ ^ k` are closed under complement. -/
theorem Nat.isSemilinearSet_compl [Finite ι] (hs : IsSemilinearSet s) : IsSemilinearSet sᶜ := by
  rcases hs.isProperSemilinearSet with ⟨S, hS, hS', rfl⟩
  simp_rw [sUnion_eq_biUnion, compl_iUnion]
  exact isSemilinearSet_biInter hS fun s hs => isSemilinearSet_compl_of_isProperLinearSet (hS' s hs)

/-- Semilinear sets in `ℕ ^ k` are closed under set difference. -/
theorem Nat.isSemilinearSet_diff [Finite ι] (hs₁ : IsSemilinearSet s₁) (hs₂ : IsSemilinearSet s₂) :
    IsSemilinearSet (s₁ \ s₂) :=
  isSemilinearSet_inter hs₁ (isSemilinearSet_compl hs₂)
