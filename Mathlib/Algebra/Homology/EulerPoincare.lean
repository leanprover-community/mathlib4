/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# The Euler-Poincaré Formula

This file proves the Euler-Poincaré formula for bounded chain complexes of
finite-dimensional modules over a division ring.

## Main Result

* `ChainComplex.eulerChar_eq_homologyEulerChar`: For ℤ-indexed bounded complexes of
  finite-dimensional modules over a division ring, the alternating sum of dimensions equals
  the alternating sum of homology dimensions.

-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex

variable {k : Type*} [DivisionRing k]

namespace ChainComplex

lemma Int.natAbs_add_one_eq_add_one_or_sub_one (j : ℤ) :
    (j + 1).natAbs = j.natAbs + 1 ∨ j.natAbs = (j + 1).natAbs + 1 := by
  omega

lemma Finset.Ico_eq_singleton_union_Ico_succ (a b : ℤ) (hab : a ≤ b) :
    Finset.Ico a (b + 1) = {a} ∪ Finset.Ico (a + 1) (b + 1) := by
  ext x; simp [Finset.mem_Ico]; omega

lemma Finset.Ico_eq_Ico_union_singleton (a b : ℤ) (hab : a ≤ b) :
    Finset.Ico a (b + 1) = Finset.Ico a b ∪ {b} := by
  ext x; simp [Finset.mem_Ico]; omega

/-- Telescoping cancellation for alternating sums with shift decomposition. -/
private lemma sum_Ico_alternating_shift_decomp {α : Type*} [Ring α] (a b : ℤ)
    (hab : a ≤ b) (s h p c : ℤ → α)
    (h_decomp : ∀ k ∈ Finset.Ico a (b + 1), s k = h k + p k + c k)
    (h_shift : ∀ k ∈ Finset.Ico a b, p (k + 1) = c k)
    (h_pa : p a = 0)
    (h_cb : c b = 0) :
    ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * s k =
    ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * h k := by
  rw [show ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * s k =
      ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * (h k + p k + c k) from
    Finset.sum_congr rfl fun k hk => by rw [h_decomp k hk]]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  suffices h_cancel : ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * p k +
                     ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * c k = 0 by
    rw [add_assoc, h_cancel, add_zero]
  have split_first := Finset.Ico_eq_singleton_union_Ico_succ a b hab
  have split_last := Finset.Ico_eq_Ico_union_singleton a b hab
  have hp : ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * p k =
      (-1 : α)^a.natAbs * p a +
      ∑ k ∈ Finset.Ico (a + 1) (b + 1), (-1 : α)^k.natAbs * p k := by
    rw [split_first, Finset.sum_union]
    · simp [Finset.sum_singleton]
    · simp [Finset.disjoint_singleton_left, Finset.mem_Ico]
  rw [hp, h_pa, mul_zero, zero_add]
  have hc : ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * c k =
      ∑ k ∈ Finset.Ico a b, (-1 : α)^k.natAbs * c k +
      (-1 : α)^b.natAbs * c b := by
    rw [split_last, Finset.sum_union]
    · simp [Finset.sum_singleton]
    · simp [Finset.disjoint_singleton_right, Finset.mem_Ico]
  rw [hc, h_cb, mul_zero, add_zero]
  rw [show ∑ k ∈ Finset.Ico a b, (-1 : α)^k.natAbs * c k =
      ∑ k ∈ Finset.Ico a b, (-1 : α)^k.natAbs * p (k + 1) from
    Finset.sum_congr rfl fun k hk => by rw [(h_shift k hk).symm]]
  have index_shift :
      Finset.Ico (a + 1) (b + 1) = (Finset.Ico a b).image (· + 1) := by
    ext x
    simp [Finset.mem_Ico]
  rw [index_shift, Finset.sum_image]
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intros j hj
    rw [← add_mul]
    suffices (-1 : α)^(j + 1).natAbs + (-1 : α)^j.natAbs = 0 by
      rw [this, zero_mul]
    rcases Int.natAbs_add_one_eq_add_one_or_sub_one j with h1 | h1 <;>
      simp only [h1, pow_add, pow_one, mul_neg, mul_one, neg_add_cancel, add_neg_cancel]
  · intro x _ y _ h; simp at h; omega

end ChainComplex

/-! ### Dimension lemmas for homological complex differentials

The following lemmas are stated for an arbitrary `HomologicalComplex (ModuleCat k) c`,
making them applicable to ℕ-indexed, ℤ-indexed, or any other complex shape. -/

namespace HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι}

/-- If `xNext i` is zero, then `dFrom i` has zero range. -/
lemma dFrom_zero_range (C : HomologicalComplex (ModuleCat k) c) (i : ι)
    (h : IsZero (C.xNext i)) :
    LinearMap.range (C.dFrom i).hom = ⊥ := by
  rw [h.eq_zero_of_tgt (C.dFrom i), ModuleCat.hom_zero, LinearMap.range_zero]

/-- If `xPrev j` is zero, then `dTo j` has zero range. -/
lemma dTo_zero_range (C : HomologicalComplex (ModuleCat k) c) (j : ι)
    (h : IsZero (C.xPrev j)) :
    LinearMap.range (C.dTo j).hom = ⊥ := by
  rw [h.eq_zero_of_src (C.dTo j), ModuleCat.hom_zero, LinearMap.range_zero]

/-- `finrank(range(dFrom i)) = finrank(range(C.d i j))`. -/
lemma dFrom_range_finrank_eq_d (C : HomologicalComplex (ModuleCat k) c) {i j : ι}
    (r : c.Rel i j) :
    Module.finrank k (LinearMap.range (C.dFrom i).hom) =
    Module.finrank k (LinearMap.range (C.d i j).hom) := by
  rw [C.dFrom_eq r, show ((C.d i j) ≫ (C.xNextIso r).inv).hom =
    (C.xNextIso r).toLinearEquiv.symm.toLinearMap ∘ₗ (C.d i j).hom from rfl,
    LinearMap.range_comp,
    ← LinearEquiv.finrank_map_eq (C.xNextIso r).toLinearEquiv.symm]

/-- `finrank(range(dTo j)) = finrank(range(C.d i j))`. -/
lemma dTo_range_finrank_eq_d (C : HomologicalComplex (ModuleCat k) c) {i j : ι}
    (r : c.Rel i j) :
    Module.finrank k (LinearMap.range (C.dTo j).hom) =
    Module.finrank k (LinearMap.range (C.d i j).hom) := by
  rw [C.dTo_eq r, show ((C.xPrevIso r).hom ≫ C.d i j).hom =
    (C.d i j).hom ∘ₗ (C.xPrevIso r).toLinearEquiv.toLinearMap from rfl,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- The range of `dTo i` is contained in the kernel of `dFrom i`. -/
lemma range_dTo_le_ker_dFrom
    (C : HomologicalComplex (ModuleCat k) c) (i : ι) :
    LinearMap.range (C.dTo i).hom ≤
    LinearMap.ker (C.dFrom i).hom := by
  rw [LinearMap.range_le_ker_iff]
  exact congr_arg ModuleCat.Hom.hom (C.dTo_comp_dFrom i)

end HomologicalComplex

namespace ChainComplex

/-- The range of `dFrom (i + 1)` has the same dimension as the range of `dTo i`
for ℤ-indexed chain complexes. -/
lemma dFrom_succ_range_finrank_eq_dTo
    (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ) :
    Module.finrank k (LinearMap.range (C.dFrom (i + 1)).hom) =
    Module.finrank k (LinearMap.range (C.dTo i).hom) := by
  have rel : (ComplexShape.down ℤ).Rel (i + 1) i := by
    simp [ComplexShape.down, ComplexShape.down']
  rw [dFrom_range_finrank_eq_d C rel, dTo_range_finrank_eq_d C rel]

/-- The dimension of the range of moduleCatToCycles equals
the dimension of the range of dTo. -/
lemma moduleCatToCycles_range_finrank_eq
    (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ) :
    Module.finrank k
      (LinearMap.range (C.sc i).moduleCatToCycles) =
    Module.finrank k (LinearMap.range (C.dTo i).hom) := by
  have range_formula :
      LinearMap.range (C.sc i).moduleCatToCycles =
      (LinearMap.range (C.dTo i).hom).comap
        (LinearMap.ker (C.dFrom i).hom).subtype := by
    rw [LinearMap.range_codRestrict]
    congr 1
  rw [range_formula]
  have h_le := range_dTo_le_ker_dFrom C i
  rw [← LinearEquiv.finrank_eq
    (Submodule.comapSubtypeEquivOfLe h_le)]
  rfl

/-- The dimension of homology plus the dimension of boundaries
equals the dimension of cycles. -/
lemma homology_finrank_formula
    (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ)
    [C.HasHomology i] [Module.Finite k (C.X i)] :
    (Module.finrank k (C.homology i) : ℤ) +
    (Module.finrank k
      (LinearMap.range (C.dTo i).hom) : ℤ) =
    (Module.finrank k
      (LinearMap.ker (C.dFrom i).hom) : ℤ) := by
  have h_eq : Module.finrank k (C.homology i) =
      Module.finrank k (LinearMap.ker (C.dFrom i).hom ⧸
        LinearMap.range (C.sc i).moduleCatToCycles) :=
    (LinearEquiv.finrank_eq (C.sc i).moduleCatHomologyIso.toLinearEquiv).trans rfl
  have dim_im := moduleCatToCycles_range_finrank_eq C i
  have quot := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (C.sc i).moduleCatToCycles :
      Submodule k (LinearMap.ker (C.dFrom i).hom))
  exact_mod_cast show Module.finrank k (C.homology i) +
      Module.finrank k (LinearMap.range (C.dTo i).hom) =
      Module.finrank k (LinearMap.ker (C.dFrom i).hom) by
    rw [h_eq, ← dim_im]; exact quot

/-- Rank-nullity for `dFrom i`. -/
lemma chain_dimension_decomposition
    (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ)
    [Module.Finite k (C.X i)] :
    (Module.finrank k (C.X i) : ℤ) =
    (Module.finrank k
      (LinearMap.ker (C.dFrom i).hom) : ℤ) +
    (Module.finrank k
      (LinearMap.range (C.dFrom i).hom) : ℤ) := by
  have := LinearMap.finrank_range_add_finrank_ker (C.dFrom i).hom
  omega

/-- `↑(n.negOnePow) = (-1) ^ n.natAbs` as an integer. -/
private lemma negOnePow_val (n : ℤ) :
    (↑(n.negOnePow) : ℤ) = (-1) ^ n.natAbs :=
  Int.coe_negOnePow ℤ n

/-- `IsZero` implies `finrank` is zero. -/
private lemma finrank_eq_zero_of_isZero (M : ModuleCat k)
    (h : IsZero M) : Module.finrank k M = 0 := by
  haveI := ModuleCat.subsingleton_of_isZero h
  exact Module.finrank_zero_of_subsingleton

private lemma isZero_outside_Ico (C : ChainComplex (ModuleCat k) ℤ) (a b i : ℤ)
    (hi : i ∉ (Finset.Ico a (b + 1) : Set ℤ))
    (hbelow : ∀ i < a, IsZero (C.X i))
    (habove : ∀ i > b, IsZero (C.X i)) : IsZero (C.X i) := by
  simp only [Finset.coe_Ico, Set.mem_Ico, not_and, not_lt] at hi
  exact if h : i < a then hbelow i h else habove i (by omega)

/-- For bounded chain complexes that vanish outside a finite interval [a,b],
    the Euler characteristic equals the homological Euler characteristic.
    This is the Euler-Poincaré formula. -/
theorem eulerChar_eq_homologyEulerChar
    (C : ChainComplex (ModuleCat k) ℤ)
    (a b : ℤ) (hab : a ≤ b)
    [∀ i : ℤ, C.HasHomology i]
    [∀ i : ℤ, Module.Finite k (C.X i)]
    (hC_bounded_below : ∀ i < a, IsZero (C.X i))
    (hC_bounded_above : ∀ i > b, IsZero (C.X i)) :
    C.eulerChar = C.homologyEulerChar := by
  -- Reduce both finsum-based definitions to finite sums over Finset.Ico a (b+1)
  have h_supp_X : GradedObject.finrankSupport C.X ⊆
      ↑(Finset.Ico a (b + 1)) := by
    rw [GradedObject.finrankSupport_subset_iff]
    intro i hi
    exact finrank_eq_zero_of_isZero _
      (isZero_outside_Ico C a b i hi hC_bounded_below hC_bounded_above)
  have h_supp_H : GradedObject.finrankSupport
      (fun i => C.homology i) ⊆
      ↑(Finset.Ico a (b + 1)) := by
    rw [GradedObject.finrankSupport_subset_iff]
    intro i hi
    exact finrank_eq_zero_of_isZero _ (ShortComplex.isZero_homology_of_isZero_X₂ _
      (isZero_outside_Ico C a b i hi hC_bounded_below hC_bounded_above))
  rw [C.eulerChar_eq_sum_finSet_of_finrankSupport_subset
    (Finset.Ico a (b + 1)) h_supp_X,
    C.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
    (Finset.Ico a (b + 1)) h_supp_H]
  -- Bridge from (c.χ i : ℤ) to (-1)^i.natAbs
  simp only [ComplexShape.eulerCharSignsDownInt_χ]
  simp_rw [negOnePow_val]
  -- Now both sides use (-1)^i.natAbs, apply the telescoping argument
  apply sum_Ico_alternating_shift_decomp a b hab
    (fun i => (Module.finrank k (C.X i) : ℤ))
    (fun i => (Module.finrank k (C.homology i) : ℤ))
    (fun i => (Module.finrank k
      (LinearMap.range (C.dFrom i).hom) : ℤ))
    (fun i => (Module.finrank k
      (LinearMap.range (C.dTo i).hom) : ℤ))
  -- s(j) = h(j) + p(j) + c(j)
  · intro j _
    rw [chain_dimension_decomposition C j,
      ← homology_finrank_formula C j]; ring
  -- p(j+1) = c(j)
  · intro j _
    exact_mod_cast dFrom_succ_range_finrank_eq_dTo C j
  -- p(a) = 0
  · have : LinearMap.range (C.dFrom a).hom = ⊥ := by
      apply dFrom_zero_range
      simp only [xNext,
        show (ComplexShape.down ℤ).next a = a - 1 from
          by simp]
      exact hC_bounded_below _ (by omega)
    rw [this]; simp
  -- c(b) = 0
  · have : LinearMap.range (C.dTo b).hom = ⊥ := by
      apply dTo_zero_range
      simp only [xPrev,
        show (ComplexShape.down ℤ).prev b = b + 1 from
          by simp]
      exact hC_bounded_above _ (by omega)
    rw [this]; simp

end ChainComplex
