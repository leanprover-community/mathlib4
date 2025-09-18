/-
Copyright (c) 2024 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# The Euler-Poincaré Formula

This file proves the Euler-Poincaré formula for bounded chain complexes of
finite-dimensional modules over a division ring.

## Main Result

* `eulerChar_eq_homology_eulerChar`: For ℤ-indexed bounded complexes of
  finite-dimensional modules over a division ring, the alternating sum of dimensions equals
  the alternating sum of homology dimensions

-/

open CategoryTheory Limits HomologicalComplex

variable {k : Type*} [DivisionRing k]

namespace ChainComplex

/-- For consecutive integers j and j+1, their absolute values differ by exactly 1. -/
lemma Int.natAbs_add_one_eq_add_one_or_sub_one (j : ℤ) :
    (j + 1).natAbs = j.natAbs + 1 ∨ j.natAbs = (j + 1).natAbs + 1 := by
  omega

/-- An interval [a, b+1) can be split as {a} ∪ [a+1, b+1) when a ≤ b. -/
lemma Finset.Ico_eq_singleton_union_Ico_succ (a b : ℤ) (hab : a ≤ b) :
    Finset.Ico a (b + 1) = {a} ∪ Finset.Ico (a + 1) (b + 1) := by
  have h1 : Finset.Ico a (b + 1) = Finset.Icc a b := by
    ext x
    simp [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have h2 : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
    ext x
    simp [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [h1, ← Finset.Ioc_insert_left hab, Finset.insert_eq, Finset.union_comm, h2,
      Finset.union_comm]

/-- An interval [a, b+1) can be split as [a, b) ∪ {b} when a ≤ b. -/
lemma Finset.Ico_eq_Ico_union_singleton (a b : ℤ) (hab : a ≤ b) :
    Finset.Ico a (b + 1) = Finset.Ico a b ∪ {b} := by
  have h1 : Finset.Ico a (b + 1) = Finset.Icc a b := by
    ext x
    simp [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [h1, ← Finset.Ico_insert_right hab, Finset.insert_eq, Finset.union_comm]

/-- Alternating sum lemma for integer intervals.
    If a sequence decomposes as `s(k) = h(k) + b(k) + c(k)` where the terms
    satisfy a shift relation `b(k+1) = c(k)` with boundary conditions `b(a) = 0`
    and `c(b) = 0`, then the alternating sum equals the alternating sum of h terms
    (the b and c terms telescope and cancel). More precisely:

    ∑_{k=a}^b (-1)^k s_k = ∑_{k=a}^b (-1)^k h_k -/
private lemma sum_Ico_alternating_shift_decomp {α : Type*} [Ring α] (a b : ℤ)
    (hab : a ≤ b) (s h p c : ℤ → α)
    (h_decomp : ∀ k ∈ Finset.Ico a (b + 1), s k = h k + p k + c k)
    (h_shift : ∀ k ∈ Finset.Ico a b, p (k + 1) = c k)
    (h_pa : p a = 0)
    (h_cb : c b = 0) :
    ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * s k =
    ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * h k := by
  have expand : ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * s k =
      ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * (h k + p k + c k) := by
    apply Finset.sum_congr rfl
    intros k hk
    rw [h_decomp k hk]
  rw [expand]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

  suffices h_cancel : ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * p k +
                     ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * c k = 0 by
    rw [add_assoc, h_cancel, add_zero]

  have split_first := Finset.Ico_eq_singleton_union_Ico_succ a b hab
  have split_last := Finset.Ico_eq_Ico_union_singleton a b hab

  have hp : ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * p k =
      (-1 : α)^a.natAbs * p a + ∑ k ∈ Finset.Ico (a + 1) (b + 1), (-1 : α)^k.natAbs * p k := by
    rw [split_first, Finset.sum_union]
    · simp [Finset.sum_singleton]
    · simp [Finset.disjoint_singleton_left, Finset.mem_Ico]
  rw [hp, h_pa, mul_zero, zero_add]

  have hc : ∑ k ∈ Finset.Ico a (b + 1), (-1 : α)^k.natAbs * c k =
      ∑ k ∈ Finset.Ico a b, (-1 : α)^k.natAbs * c k + (-1 : α)^b.natAbs * c b := by
    rw [split_last, Finset.sum_union]
    · simp [Finset.sum_singleton]
    · simp [Finset.disjoint_singleton_right, Finset.mem_Ico]
  rw [hc, h_cb, mul_zero, add_zero]

  have c_as_p : ∑ k ∈ Finset.Ico a b, (-1 : α)^k.natAbs * c k =
      ∑ k ∈ Finset.Ico a b, (-1 : α)^k.natAbs * p (k + 1) := by
    apply Finset.sum_congr rfl
    intros k hk
    congr 1
    exact (h_shift k hk).symm
  rw [c_as_p]

  have index_shift : Finset.Ico (a + 1) (b + 1) = (Finset.Ico a b).image (· + 1) := by
    ext x
    simp [Finset.mem_Ico]

  rw [index_shift, Finset.sum_image]
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intros j hj
    rw [← add_mul]
    suffices (-1 : α)^(j + 1).natAbs + (-1 : α)^j.natAbs = 0 by
      rw [this, zero_mul]
    have h := Int.natAbs_add_one_eq_add_one_or_sub_one j
    cases h with
    | inl h1 =>
      rw [h1, pow_add, pow_one]
      simp only [mul_neg, mul_one, neg_add_cancel]
    | inr h2 =>
      rw [h2, pow_add, pow_one]
      simp only [mul_neg, mul_one, add_neg_cancel]
  · intros x _ y _ h
    simp at h
    omega

/-- If the target object is zero, then dFrom is the zero map. -/
lemma dFrom_eq_zero_of_isZero (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ)
    (h : IsZero (C.X (i - 1))) : C.dFrom i = 0 := by
  have next_eq : (ComplexShape.down ℤ).next i = i - 1 := by simp
  have hzero : IsZero (C.xNext i) := by
    rw [xNext, next_eq]
    exact h
  exact IsZero.eq_zero_of_tgt hzero (C.dFrom i)

/-- If the source object is zero, then dTo is the zero map. -/
lemma dTo_eq_zero_of_isZero (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ)
    (h : IsZero (C.X (i + 1))) : C.dTo i = 0 := by
  have prev_eq : (ComplexShape.down ℤ).prev i = i + 1 := by simp
  have hzero : IsZero (C.xPrev i) := by
    rw [xPrev, prev_eq]
    exact h
  exact IsZero.eq_zero_of_src hzero (C.dTo i)

/-- If the target object is zero, then dFrom has zero range. -/
lemma dFrom_zero_range (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ)
    (h : IsZero (C.X (i - 1))) :
    LinearMap.range (C.dFrom i).hom = ⊥ := by
  rw [dFrom_eq_zero_of_isZero C i h, ModuleCat.hom_zero, LinearMap.range_zero]

/-- If the source object is zero, then dTo has zero range. -/
lemma dTo_zero_range (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ)
    (h : IsZero (C.X (i + 1))) :
    LinearMap.range (C.dTo i).hom = ⊥ := by
  rw [dTo_eq_zero_of_isZero C i h, ModuleCat.hom_zero, LinearMap.range_zero]

/-- The range of dFrom has the same dimension as the underlying differential. -/
lemma dFrom_range_finrank_eq_d (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ) :
    Module.finrank k (LinearMap.range (C.dFrom (i + 1)).hom) =
    Module.finrank k (LinearMap.range (C.d (i + 1) i).hom) := by
  have rel : (ComplexShape.down ℤ).Rel (i + 1) i := by
    simp [ComplexShape.down, ComplexShape.down']
  have dFrom_eq : C.dFrom (i + 1) = C.d (i + 1) i ≫ (C.xNextIso rel).inv := C.dFrom_eq rel
  rw [dFrom_eq]
  have : ((C.d (i + 1) i) ≫ (C.xNextIso rel).inv).hom =
         (C.xNextIso rel).toLinearEquiv.symm.toLinearMap ∘ₗ (C.d (i + 1) i).hom := rfl
  rw [this, LinearMap.range_comp]
  rw [← LinearEquiv.finrank_map_eq (C.xNextIso rel).toLinearEquiv.symm]

/-- The range of dTo has the same dimension as the underlying differential. -/
lemma dTo_range_finrank_eq_d (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ) :
    Module.finrank k (LinearMap.range (C.dTo i).hom) =
    Module.finrank k (LinearMap.range (C.d (i + 1) i).hom) := by
  have rel : (ComplexShape.down ℤ).Rel (i + 1) i := by
    simp [ComplexShape.down, ComplexShape.down']
  have dTo_eq : C.dTo i = (C.xPrevIso rel).hom ≫ C.d (i + 1) i := C.dTo_eq rel
  rw [dTo_eq]
  have : ((C.xPrevIso rel).hom ≫ C.d (i + 1) i).hom =
         (C.d (i + 1) i).hom ∘ₗ (C.xPrevIso rel).toLinearEquiv.toLinearMap := rfl
  rw [this, LinearMap.range_comp]
  have hsurj : Function.Surjective (C.xPrevIso rel).toLinearEquiv.toLinearMap :=
    (C.xPrevIso rel).toLinearEquiv.surjective
  rw [LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]

lemma dFrom_succ_range_finrank_eq_dTo (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ) :
    Module.finrank k (LinearMap.range (C.dFrom (i + 1)).hom) =
    Module.finrank k (LinearMap.range (C.dTo i).hom) := by
  rw [dFrom_range_finrank_eq_d, dTo_range_finrank_eq_d]

/-- The range of dTo i is contained in the kernel of dFrom i. -/
lemma range_dTo_le_ker_dFrom (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ) :
    LinearMap.range (C.dTo i).hom ≤ LinearMap.ker (C.dFrom i).hom := by
  intro x hx
  simp only [LinearMap.mem_range] at hx
  obtain ⟨y, rfl⟩ := hx
  simp only [LinearMap.mem_ker]
  change (C.dFrom i).hom ((C.dTo i).hom y) = 0
  have : (C.dTo i ≫ C.dFrom i) y = 0 := by
    rw [C.d_comp_d]
    rfl
  convert this

/-- The dimension of the range of moduleCatToCycles equals the dimension of the range of dTo. -/
lemma moduleCatToCycles_range_finrank_eq (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ) :
    Module.finrank k (LinearMap.range (C.sc i).moduleCatToCycles) =
    Module.finrank k (LinearMap.range (C.dTo i).hom) := by
  have range_formula : LinearMap.range (C.sc i).moduleCatToCycles =
      (LinearMap.range (C.dTo i).hom).comap (LinearMap.ker (C.dFrom i).hom).subtype := by
    rw [LinearMap.range_codRestrict]
    congr 1
  rw [range_formula]
  have h_le := range_dTo_le_ker_dFrom C i
  rw [← LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe h_le)]
  rfl

/-- The dimension of homology plus the dimension of boundaries equals the dimension of cycles. -/
lemma homology_finrank_formula (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ)
    [C.HasHomology i] [Module.Finite k (C.X i)] :
    (Module.finrank k (C.homology i) : ℤ) +
    (Module.finrank k (LinearMap.range (C.dTo i).hom) : ℤ) =
    (Module.finrank k (LinearMap.ker (C.dFrom i).hom) : ℤ) := by
  let S := C.sc i
  let data := S.moduleCatLeftHomologyData

  have homology_iso : C.homology i ≅ data.H := S.moduleCatHomologyIso
  have cycles_iso : C.cycles i ≅ data.K := S.moduleCatCyclesIso

  -- Use the lemma about the range of moduleCatToCycles
  have dim_image := moduleCatToCycles_range_finrank_eq C i

  have dim_homology : Module.finrank k (C.homology i) = Module.finrank k data.H := by
    exact LinearEquiv.finrank_eq homology_iso.toLinearEquiv
  have dim_cycles : Module.finrank k (C.cycles i) = Module.finrank k data.K := by
    exact LinearEquiv.finrank_eq cycles_iso.toLinearEquiv

  have data_K_eq : data.K = ModuleCat.of k (LinearMap.ker (C.dFrom i).hom) := rfl
  have data_H_eq : data.H = ModuleCat.of k (LinearMap.ker (C.dFrom i).hom ⧸
    LinearMap.range S.moduleCatToCycles) := rfl

  calc (Module.finrank k (C.homology i) : ℤ) +
       (Module.finrank k (LinearMap.range (C.dTo i).hom) : ℤ)
      = (Module.finrank k data.H : ℤ) +
        (Module.finrank k (LinearMap.range (C.dTo i).hom) : ℤ) := by
          simp only [dim_homology]
    _ = (Module.finrank k data.H : ℤ) +
        (Module.finrank k (LinearMap.range S.moduleCatToCycles) : ℤ) := by
          rw [dim_image]
    _ = (Module.finrank k (LinearMap.ker (C.dFrom i).hom) : ℤ) := by
          have h := Submodule.finrank_quotient_add_finrank
            (LinearMap.range S.moduleCatToCycles : Submodule k (LinearMap.ker (C.dFrom i).hom))
          have eq1 : Module.finrank k data.H =
            Module.finrank k (LinearMap.ker (C.dFrom i).hom ⧸
              LinearMap.range S.moduleCatToCycles) := by
            rw [data_H_eq]
          rw [eq1]
          norm_cast

/-- The dimension of a chain space equals the dimension of its kernel plus
    the dimension of its image (rank-nullity theorem). -/
lemma chain_dimension_decomposition (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ)
    [Module.Finite k (C.X i)] :
    (Module.finrank k (C.X i) : ℤ) =
    (Module.finrank k (LinearMap.ker (C.dFrom i).hom) : ℤ) +
    (Module.finrank k (LinearMap.range (C.dFrom i).hom) : ℤ) := by
  rw [← LinearMap.finrank_range_add_finrank_ker (C.dFrom i).hom]
  rw [add_comm]
  rfl

/-- The dimension of cycles decomposes as the sum of homology dimension
    and dimension of boundaries. -/
lemma cycles_dimension_decomposition (C : ChainComplex (ModuleCat k) ℤ) (i : ℤ)
    [C.HasHomology i] [Module.Finite k (C.X i)] :
    (Module.finrank k (LinearMap.ker (C.dFrom i).hom) : ℤ) =
    (Module.finrank k (C.homology i) : ℤ) +
    (Module.finrank k (LinearMap.range (C.dTo i).hom) : ℤ) := by
  rw [← homology_finrank_formula C i]

/-- For bounded chain complexes that vanish outside a finite interval [a,b],
    the bounded Euler characteristic equals the homology bounded Euler characteristic. -/
theorem eulerChar_eq_homology_eulerChar (C : ChainComplex (ModuleCat k) ℤ)
    (a b : ℤ) (hab : a ≤ b)
    [∀ i : ℤ, C.HasHomology i]
    [∀ i : ℤ, Module.Finite k (C.X i)]
    (hC_bounded_below : ∀ i < a, IsZero (C.X i))
    (hC_bounded_above : ∀ i > b, IsZero (C.X i)) :
    boundedEulerChar C (Finset.Ico a (b + 1)) 0 =
    homologyBoundedEulerChar C (Finset.Ico a (b + 1)) 0 := by
  -- Expand definitions directly
  rw [boundedEulerChar, homologyBoundedEulerChar]

  -- Simplify (i - 0) to i
  conv_lhs => arg 2; ext; arg 1; arg 2; rw [sub_zero]
  conv_rhs => arg 2; ext; arg 1; arg 2; rw [sub_zero]

  let s := fun i => (Module.finrank k (C.X i) : ℤ)
  let h := fun i => (Module.finrank k (C.homology i) : ℤ)
  let p := fun i => (Module.finrank k (LinearMap.range (C.dFrom i).hom) : ℤ)
  let c := fun i => (Module.finrank k (LinearMap.range (C.dTo i).hom) : ℤ)

  -- Apply the telescoping sum lemma
  apply sum_Ico_alternating_shift_decomp a b hab s h p c

  -- s(k) = h(k) + p(k) + c(k)
  · intros k hk
    simp only [Finset.mem_Ico] at hk
    unfold s h p c
    -- Use chain_dimension_decomposition and cycles_dimension_decomposition
    rw [chain_dimension_decomposition C k]
    rw [cycles_dimension_decomposition C k]
    ring

  -- p(k+1) = c(k)
  · intros k hk
    simp only [Finset.mem_Ico] at hk
    unfold p c
    congr 1
    exact dFrom_succ_range_finrank_eq_dTo C k

  -- p(a) = 0
  · unfold p
    have ha_zero : IsZero (C.X (a - 1)) := hC_bounded_below (a - 1) (by omega)
    have : LinearMap.range (C.dFrom a).hom = ⊥ := by
      exact dFrom_zero_range C a ha_zero
    rw [this]
    simp

  -- c(b) = 0
  · unfold c
    have hb_zero : IsZero (C.X (b + 1)) := hC_bounded_above (b + 1) (by omega)
    have : LinearMap.range (C.dTo b).hom = ⊥ := by
      exact dTo_zero_range C b hb_zero
    rw [this]
    simp

end ChainComplex
