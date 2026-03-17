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
public import Mathlib.Data.Int.SuccPred
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
  simp only [ComplexShape.eulerCharSignsDownInt_χ]
  simp_rw [show ∀ n : ℤ, (n.negOnePow : ℤ) = (-1) ^ n.natAbs
    from Int.coe_negOnePow ℤ]
  -- Decompose finrank(X i) = finrank(homology i) + finrank(range dFrom i) + finrank(range dTo i)
  rw [show ∑ x ∈ Finset.Ico a (b + 1),
        (-1 : ℤ) ^ x.natAbs * ↑(Module.finrank k ↑(C.X x)) =
      ∑ x ∈ Finset.Ico a (b + 1), (-1 : ℤ) ^ x.natAbs *
        (↑(Module.finrank k (C.homology x)) +
         ↑(Module.finrank k ↥(LinearMap.range (C.dFrom x).hom)) +
         ↑(Module.finrank k ↥(LinearMap.range (C.dTo x).hom)))
    from Finset.sum_congr rfl fun x _ => by
      rw [chain_dimension_decomposition C x,
        ← homology_finrank_formula C x]; ring]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Suffices to show the p-sum and c-sum cancel
  suffices h_cancel :
      ∑ x ∈ Finset.Ico a (b + 1),
        (-1 : ℤ) ^ x.natAbs *
          ↑(Module.finrank k ↥(LinearMap.range (C.dFrom x).hom)) +
      ∑ x ∈ Finset.Ico a (b + 1),
        (-1 : ℤ) ^ x.natAbs *
          ↑(Module.finrank k ↥(LinearMap.range (C.dTo x).hom)) = 0 by
    linarith
  -- Split first element from p-sum: p(a) = 0
  have hp_a : (Module.finrank k
      ↥(LinearMap.range (C.dFrom a).hom) : ℤ) = 0 := by
    have : LinearMap.range (C.dFrom a).hom = ⊥ := by
      apply dFrom_zero_range
      simp only [xNext,
        show (ComplexShape.down ℤ).next a = a - 1 from by simp]
      exact hC_bounded_below _ (by omega)
    rw [this]; simp
  have hp_split : ∑ x ∈ Finset.Ico a (b + 1),
      (-1 : ℤ) ^ x.natAbs *
        ↑(Module.finrank k ↥(LinearMap.range (C.dFrom x).hom)) =
      ∑ x ∈ Finset.Ico (a + 1) (b + 1),
        (-1 : ℤ) ^ x.natAbs *
          ↑(Module.finrank k ↥(LinearMap.range (C.dFrom x).hom)) := by
    rw [← Finset.insert_Ico_add_one_left_eq_Ico (show a < b + 1 by omega),
      Finset.sum_insert (by simp [Finset.mem_Ico]),
      hp_a, mul_zero, zero_add]
  -- Split last element from c-sum: c(b) = 0
  have hc_b : (Module.finrank k
      ↥(LinearMap.range (C.dTo b).hom) : ℤ) = 0 := by
    have : LinearMap.range (C.dTo b).hom = ⊥ := by
      apply dTo_zero_range
      simp only [xPrev,
        show (ComplexShape.down ℤ).prev b = b + 1 from by simp]
      exact hC_bounded_above _ (by omega)
    rw [this]; simp
  have hc_split : ∑ x ∈ Finset.Ico a (b + 1),
      (-1 : ℤ) ^ x.natAbs *
        ↑(Module.finrank k ↥(LinearMap.range (C.dTo x).hom)) =
      ∑ x ∈ Finset.Ico a b,
        (-1 : ℤ) ^ x.natAbs *
          ↑(Module.finrank k ↥(LinearMap.range (C.dTo x).hom)) := by
    rw [← Finset.insert_Ico_right_eq_Ico_add_one hab,
      Finset.sum_insert Finset.right_notMem_Ico,
      hc_b, mul_zero, zero_add]
  rw [hp_split, hc_split]
  -- Rewrite c(k) = p(k+1) via dFrom_succ_range_finrank_eq_dTo
  rw [show ∑ x ∈ Finset.Ico a b,
        (-1 : ℤ) ^ x.natAbs *
          ↑(Module.finrank k ↥(LinearMap.range (C.dTo x).hom)) =
      ∑ x ∈ Finset.Ico a b,
        (-1 : ℤ) ^ x.natAbs *
          ↑(Module.finrank k ↥(LinearMap.range (C.dFrom (x + 1)).hom))
    from Finset.sum_congr rfl fun x _ => by
      rw [dFrom_succ_range_finrank_eq_dTo C x]]
  -- Apply the general alternating cancellation lemma
  exact Finset.sum_Ico_add_sum_Ico_shift_neg_cancel _ _ a b 1
    (fun j => by simp [← Int.coe_negOnePow, Int.negOnePow_succ])

end ChainComplex
