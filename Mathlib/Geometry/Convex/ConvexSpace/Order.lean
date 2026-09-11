/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Ordered convex spaces

This file orders the standard simplex over a partial order by stochastic dominance and defines
ordered convex spaces, namely convex spaces over a partial order in which taking convex
combinations is monotone.

## Main declarations

* `Convexity.StdSimplex.mass`: The mass function of a distribution `w`, namely the map sending a
  set `s` to the total weight that `w` puts on `s`.
* `Convexity.StdSimplex.instPartialOrder`: The stochastic dominance order on `StdSimplex R X`,
  namely `w₁ ≤ w₂` iff `w₁` puts less mass than `w₂` on every upper set.
* `Convexity.IsOrderedConvexSpace`: Typeclass for a convex space over a partial order in which
  `sConvexComb` is monotone for stochastic dominance.
-/

open Finsupp Set

public section

namespace Convexity
variable {I R X : Type*}

section ConvexSpace
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]

instance : ConvexSpace R Xᵒᵈ := ‹ConvexSpace R X›

@[simp]
lemma toDual_sConvexComb (w : StdSimplex R X) :
    OrderDual.toDual w.sConvexComb = w.iConvexComb OrderDual.toDual :=
  congr(sConvexComb $(StdSimplex.map_id w)).symm

@[simp]
lemma ofDual_sConvexComb (w : StdSimplex R Xᵒᵈ) :
    OrderDual.ofDual w.sConvexComb = w.iConvexComb OrderDual.ofDual :=
  congr(sConvexComb $(StdSimplex.map_id w)).symm

@[fun_prop]
lemma isAffineMap_toDual : IsAffineMap R (OrderDual.toDual : X → Xᵒᵈ) where
  map_sConvexComb := toDual_sConvexComb

@[fun_prop]
lemma isAffineMap_ofDual : IsAffineMap R (OrderDual.ofDual : Xᵒᵈ → X) where
  map_sConvexComb := ofDual_sConvexComb

@[simp]
lemma toDual_iConvexComb (w : StdSimplex R I) (f : I → X) :
    OrderDual.toDual (w.iConvexComb f) = w.iConvexComb (fun i ↦ OrderDual.toDual (f i)) :=
  isAffineMap_toDual.map_iConvexComb ..

@[simp]
lemma ofDual_iConvexComb (w : StdSimplex R I) (f : I → Xᵒᵈ) :
    OrderDual.ofDual (w.iConvexComb f) = w.iConvexComb (fun i ↦ OrderDual.ofDual (f i)) :=
  isAffineMap_ofDual.map_iConvexComb ..

@[simp]
lemma toDual_convexCombPair (a b : R) (ha hb hab) (x y : X) :
    OrderDual.toDual (convexCombPair a b ha hb hab x y) =
      convexCombPair a b ha hb hab (OrderDual.toDual x) (OrderDual.toDual y) :=
  isAffineMap_toDual.map_convexCombPair ..

@[simp]
lemma ofDual_convexCombPair (a b : R) (ha hb hab) (x y : Xᵒᵈ) :
    OrderDual.ofDual (convexCombPair a b ha hb hab x y) =
      convexCombPair a b ha hb hab (OrderDual.ofDual x) (OrderDual.ofDual y) :=
  isAffineMap_ofDual.map_convexCombPair ..

end ConvexSpace

namespace StdSimplex
section Mass
variable [Semiring R] [PartialOrder R] {w w₁ w₂ : StdSimplex R X} {s t : Set X}

variable (w) in
/-- The mass function of a distribution `w`: `w.mass s` is the total weight that `w` puts on `s`. -/
noncomputable def mass (s : Set X) : R :=
  open scoped Classical in (w.weights.filter (· ∈ s)).sum fun _x r ↦ r

lemma mass_eq_finsuppSum (w : StdSimplex R X) (s : Set X) [DecidablePred (· ∈ s)] :
    w.mass s = (w.weights.filter (· ∈ s)).sum fun _x r ↦ r := by rw [mass]; congr!

lemma mass_eq_sum (w : StdSimplex R X) (s : Set X) [DecidablePred (· ∈ s)] :
    w.mass s = ∑ x ∈ w.weights.support with x ∈ s, w.weights x := by
  rw [mass_eq_finsuppSum, sum_filter_index, support_filter]

@[simp] lemma mass_empty (w : StdSimplex R X) : w.mass ∅ = 0 := by simp [mass_eq_sum]

@[simp] lemma mass_univ (w : StdSimplex R X) : w.mass univ = 1 := by
  simpa [mass_eq_sum, Finsupp.sum] using w.total

lemma mass_union_of_disjoint (hst : Disjoint s t) (w : StdSimplex R X) :
    w.mass (s ∪ t) = w.mass s + w.mass t := by
  classical
  simp only [mass_eq_sum, mem_union, Finset.filter_or]
  grind [Finset.sum_union, Finset.disjoint_left]

@[simp] lemma mass_singleton (w : StdSimplex R X) (x : X) : w.mass {x} = w.weights x := by
  classical simp [mass_eq_sum, Finset.sum_filter, eq_comm]

@[simp]
lemma mass_add_mass_compl (w : StdSimplex R X) (s : Set X) : w.mass s + w.mass sᶜ = 1 := by
  classical simpa [mass_eq_sum, Finset.sum_filter_add_sum_filter_not, Finsupp.sum] using w.total

variable [IsStrictOrderedRing R]

@[simp] lemma mass_nonneg (w : StdSimplex R X) (s : Set X) : 0 ≤ w.mass s := by
  classical rw [mass_eq_sum]; exact Finset.sum_nonneg fun _ _ ↦ w.weights_nonneg _

@[simp] lemma mass_single (x : X) (s : Set X) [Decidable (x ∈ s)] :
    (single x : StdSimplex R X).mass s = if x ∈ s then 1 else 0 := by
  classical rw [mass_eq_sum, weights_single]; split <;> simp [Finset.filter_singleton, *]

@[simp] lemma mass_map (w : StdSimplex R I) (f : I → X) (s : Set X) :
    (w.map f).mass s = w.mass (f ⁻¹' s) := by
  classical simp [mass_eq_finsuppSum, sum_mapDomain_index]

@[gcongr] lemma mass_mono (w : StdSimplex R X) (hst : s ⊆ t) : w.mass s ≤ w.mass t := by
  classical rw [mass_eq_sum, mass_eq_sum]; gcongr; simp

@[simp] lemma mass_le_one : w.mass s ≤ 1 := by
  rw [← mass_add_mass_compl]; exact le_add_of_nonneg_right (mass_nonneg ..)

lemma mass_eq_zero_iff : w.mass s = 0 ↔ ∀ x, w.weights x ≠ 0 → x ∉ s := by
  classical
  rw [mass_eq_sum, Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ w.weights_nonneg _]
  simp +contextual [Finset.mem_filter, not_imp_not, eq_comm]

lemma mass_eq_one_iff : w.mass s = 1 ↔ ∀ x, w.weights x ≠ 0 → x ∈ s := by
  rw [← w.mass_add_mass_compl s, left_eq_add, mass_eq_zero_iff]; simp

@[simp]
lemma mass_compl_le_mass_compl_iff : w₁.mass sᶜ ≤ w₂.mass sᶜ ↔ w₂.mass s ≤ w₁.mass s :=
  le_iff_ge_of_add_eq_add <| by simp [add_comm]

end Mass

section PartialOrder
variable [Semiring R] [PartialOrder R] [PartialOrder X] {w w₁ w₂ : StdSimplex R X} {s t : Set X}
  {x y : X}

/-- The mass that `w` puts above `x` is the mass it puts on `x` plus the mass it puts strictly
above `x`. -/
lemma mass_Ici_eq_weights_add_mass_Ioi (w : StdSimplex R X) (x : X) :
    w.mass (Ici x) = w.weights x + w.mass (Ioi x) := by
  rw [← mass_singleton, ← mass_union_of_disjoint]
  · congr 1
    ext y
    simp [le_iff_lt_or_eq, or_comm]
  · simp

/-- If, on the support of `w`, lying in `s` is the same as lying above `x`, then the mass that `w`
puts on `s` is the mass it puts above `x`. -/
lemma mass_eq_mass_Ici (w : StdSimplex R X) (h : ∀ ⦃y⦄, w.weights y ≠ 0 → (y ∈ s ↔ x ≤ y)) :
    w.mass s = w.mass (Ici x) := by
  classical rw [mass_eq_sum, mass_eq_sum]; congr! 2 with y hy; exact h (mem_support_iff.1 hy)

variable [IsStrictOrderedRing R]

/-- `w` puts all of its mass above `x` exactly when its support lies above `x`. -/
lemma mass_Ici_eq_one_iff : w.mass (Ici x) = 1 ↔ ∀ y, w.weights y ≠ 0 → x ≤ y := mass_eq_one_iff

/-- `w` puts all of its mass below `x` exactly when its support lies below `x`. -/
lemma mass_Iic_eq_one_iff : w.mass (Iic x) = 1 ↔ ∀ y, w.weights y ≠ 0 → y ≤ x := mass_eq_one_iff

/-- The standard simplex indexed by a partial order is partially ordered by **stochastic
dominance**: `w₁ ≤ w₂` iff on each upper set the mass of `w₁` is at most that of `w₂`.

Equivalently, `w₁ ≤ w₂` iff `w₂` puts at most as much mass as `w₁` on each down-set
(`StdSimplex.le_iff_forall_isLowerSet`), which makes stochastic dominance self-dual. -/
noncomputable instance instPartialOrder : PartialOrder (StdSimplex R X) where
  le w₁ w₂ := ∀ ⦃s : Set X⦄, IsUpperSet s → w₁.mass s ≤ w₂.mass s
  le_refl w s _ := le_rfl
  le_trans w₁ w₂ w₃ h₁₂ h₂₃ s hs := (h₁₂ hs).trans (h₂₃ hs)
  le_antisymm w₁ w₂ h₁₂ h₂₁ := by
    have key {s : Set X} (hs : IsUpperSet s) : w₁.mass s = w₂.mass s := (h₁₂ hs).antisymm (h₂₁ hs)
    ext x
    have h := w₁.mass_Ici_eq_weights_add_mass_Ioi x
    rw [key (isUpperSet_Ici x), key (isUpperSet_Ioi x),
      w₂.mass_Ici_eq_weights_add_mass_Ioi x] at h
    exact (add_right_cancel h).symm

lemma le_iff_forall_isUpperSet :
    w₁ ≤ w₂ ↔ ∀ ⦃s : Set X⦄, IsUpperSet s → w₁.mass s ≤ w₂.mass s := .rfl

lemma le_iff_forall_isLowerSet :
    w₁ ≤ w₂ ↔ ∀ ⦃s : Set X⦄, IsLowerSet s → w₂.mass s ≤ w₁.mass s :=
  compl_surjective.forall.trans <| by simp

@[gcongr]
lemma mass_mono_of_isUpperSet (hw : w₁ ≤ w₂) (hst : s ⊆ t) (ht : IsUpperSet t) :
    w₁.mass s ≤ w₂.mass t := by grw [hst, le_iff_forall_isUpperSet.1 hw ht]

lemma mass_mono_of_isLowerSet (hw : w₁ ≤ w₂) (hst : s ⊆ t) (ht : IsLowerSet t) :
    w₂.mass s ≤ w₁.mass t := by grw [hst, le_iff_forall_isLowerSet.1 hw ht]

@[gcongr] lemma mass_Ici_mono (hw : w₁ ≤ w₂) : w₁.mass (Ici x) ≤ w₂.mass (Ici x) := by
  gcongr; exact isUpperSet_Ici _

@[gcongr] lemma mass_Iic_mono (hw : w₁ ≤ w₂) : w₂.mass (Iic x) ≤ w₁.mass (Iic x) :=
  mass_mono_of_isLowerSet hw .rfl <| isLowerSet_Iic _

lemma mass_strictMono :
    StrictMono fun (w : StdSimplex R X) (s : UpperSet X) ↦ w.mass (s : Set X) := by
  intro w₁ w₂ h
  refine lt_of_le_of_ne (fun s ↦ le_iff_forall_isUpperSet.1 h.le s.2) fun hmass ↦ h.ne ?_
  exact le_antisymm h.le <| le_iff_forall_isUpperSet.2 fun s hs ↦ (congrFun hmass ⟨s, hs⟩).ge

/-- If `w₁ ≤ w₂` and `w₁` puts all of its mass on an upper set `s`, then so does `w₂`. -/
lemma mass_eq_one_of_le (hs : IsUpperSet s) (h : w₁ ≤ w₂) (h₁ : w₁.mass s = 1) : w₂.mass s = 1 :=
  le_antisymm (mass_le_one ..) (h₁ ▸ le_iff_forall_isUpperSet.1 h hs)

/-- If `w₁ ≤ w₂` and `w₂` puts all of its mass on a down-set `s`, then so does `w₁`. -/
lemma mass_eq_one_of_ge (hs : IsLowerSet s) (h : w₁ ≤ w₂) (h₂ : w₂.mass s = 1) : w₁.mass s = 1 :=
  le_antisymm (mass_le_one ..) (h₂ ▸ le_iff_forall_isLowerSet.1 h hs)

lemma forall_le_of_le (h : w₁ ≤ w₂) (h₁ : ∀ ⦃y⦄, w₁.weights y ≠ 0 → x ≤ y) :
    ∀ ⦃y⦄, w₂.weights y ≠ 0 → x ≤ y := by
  rw [← mass_Ici_eq_one_iff] at h₁ ⊢
  exact mass_eq_one_of_le (isUpperSet_Ici x) h h₁

lemma forall_ge_of_le (h : w₁ ≤ w₂) (h₂ : ∀ ⦃y⦄, w₂.weights y ≠ 0 → y ≤ x) :
    ∀ ⦃y⦄, w₁.weights y ≠ 0 → y ≤ x := by
  rw [← mass_Iic_eq_one_iff] at h₂ ⊢
  exact mass_eq_one_of_ge (isLowerSet_Iic x) h h₂

lemma monotone_map {w : StdSimplex R I} : Monotone (w.map : (I → X) → StdSimplex R X) := by
  intro f g hfg s hs; rw [mass_map, mass_map]; gcongr; exact fun i hi ↦ hs (hfg i) hi

@[gcongr, to_dual self]
lemma map_le_map {w : StdSimplex R I} {f g : I → X} (hfg : f ≤ g) : w.map f ≤ w.map g :=
  monotone_map hfg

@[simp, to_dual self]
lemma single_le_single_iff : (single x : StdSimplex R X) ≤ single y ↔ x ≤ y := by
  classical
  simpa [le_iff_forall_isUpperSet, apply_ite, ite_apply, zero_lt_one.not_ge, not_imp_not]
    using ⟨fun h ↦ by simpa using h (isUpperSet_Ici x), fun hxy s hs ↦ hs hxy⟩

@[gcongr, to_dual self] alias ⟨_, single_mono⟩ := single_le_single_iff


end PartialOrder

section LinearOrder
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [LinearOrder X]
  {w₁ w₂ : StdSimplex R X}

/-- Over a linear order, stochastic dominance can be tested on the principal upper sets alone, ie by
comparing the (complementary) cumulative distribution functions. This is the usual definition of
stochastic dominance.

This fails over a general partial order: see the module docstring. -/
lemma le_iff_forall_Ici : w₁ ≤ w₂ ↔ ∀ x, w₁.mass (Ici x) ≤ w₂.mass (Ici x) := by
  classical
  refine ⟨fun h _ ↦ mass_Ici_mono h, fun h ↦ le_iff_forall_isUpperSet.2 fun s hs ↦ ?_⟩
  set F : Finset X := w₁.weights.support ∪ w₂.weights.support
  -- As an upper set of the finite linear order `F`, `s` is either empty or of the form `Ici x`.
  obtain hse | ⟨x, hsx⟩ := (hs.preimage (f := ((↑) : F → X)) fun _ _ h ↦ h).eq_empty_or_Ici
  -- If `s` misses `F`, then neither distribution charges `s`.
  · have key (w : StdSimplex R X) (hw : w.weights.support ⊆ F) : w.mass s = 0 :=
      mass_eq_zero_iff.2 fun y hy hys ↦
        Set.eq_empty_iff_forall_notMem.1 hse ⟨y, hw (mem_support_iff.2 hy)⟩ hys
    rw [key w₁ Finset.subset_union_left, key w₂ Finset.subset_union_right]
  -- Otherwise, on `F` the set `s` coincides with `Ici x`, so both masses are masses above `x`.
  · have key (w : StdSimplex R X) (hw : w.weights.support ⊆ F) : w.mass s = w.mass (Ici ↑x) :=
      mass_eq_mass_Ici _ fun y hy ↦ by
        simpa [← Subtype.coe_le_coe] using Set.ext_iff.1 hsx ⟨y, hw (mem_support_iff.2 hy)⟩
    rw [key w₁ Finset.subset_union_left, key w₂ Finset.subset_union_right]
    exact h _

end LinearOrder

section OrderDual
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [PartialOrder X]

@[simp] lemma ofDual_le_iff {w₁ w₂ : StdSimplex R Xᵒᵈ} :
    w₂ ≤ w₁ ↔ w₁.map OrderDual.ofDual ≤ w₂.map OrderDual.ofDual := by
  rw [le_iff_forall_isUpperSet, le_iff_forall_isLowerSet]
  simp [OrderDual.ofDual.setCongr.forall_congr_left, Equiv.image_eq_preimage_symm]

@[simp] lemma map_toDual_le_map_toDual_iff {w₁ w₂ : StdSimplex R X} :
    w₁.map OrderDual.toDual ≤ w₂.map OrderDual.toDual ↔ w₂ ≤ w₁ := by
  simp [ofDual_le_iff, map_map]

variable (R X) in
/-- The stochastic dominance order on the standard simplex is self-dual. -/
noncomputable def toDualOrderIso : (StdSimplex R X)ᵒᵈ ≃o StdSimplex R Xᵒᵈ where
  toFun w := w.ofDual.map .toDual
  invFun w := .toDual <| w.map OrderDual.ofDual
  left_inv w := by ext; simp
  right_inv w := by ext; simp
  map_rel_iff' := map_toDual_le_map_toDual_iff

end OrderDual
end StdSimplex

section IsOrderedConvexSpace
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [PartialOrder X] [ConvexSpace R X]

variable (R X) in
/-- A convex space over a partial order is *ordered* if taking convex combinations is monotone for
the stochastic dominance order on the standard simplex.

Equivalently, replacing the points of a convex combination by larger points, or moving weight from
smaller points to larger ones, can only increase the combination. -/
class IsOrderedConvexSpace : Prop where
  /-- Taking convex combinations is monotone for stochastic dominance. -/
  monotone_sConvexComb : Monotone (sConvexComb : StdSimplex R X → X)

export IsOrderedConvexSpace (monotone_sConvexComb)

variable [IsOrderedConvexSpace R X] {v : StdSimplex R I} {w₁ w₂ : StdSimplex R X} {f g : I → X}

@[gcongr, to_dual self]
lemma sConvexComb_le_sConvexComb (h : w₁ ≤ w₂) : w₁.sConvexComb ≤ w₂.sConvexComb :=
  monotone_sConvexComb h

lemma monotone_iConvexComb (v : StdSimplex R I) : Monotone (v.iConvexComb : (I → X) → X) :=
  fun _f _g hfg ↦ monotone_sConvexComb <| StdSimplex.monotone_map hfg

@[gcongr, to_dual self]
lemma iConvexComb_le_iConvexComb (hfg : f ≤ g) : v.iConvexComb f ≤ v.iConvexComb g :=
  monotone_iConvexComb _ hfg

@[gcongr, to_dual self (dont_translate := R)]
lemma convexCombPair_le_convexCombPair {a b : R} (ha hb hab) {x₁ x₂ y₁ y₂ : X} (hx : x₁ ≤ x₂)
    (hy : y₁ ≤ y₂) :
    convexCombPair a b ha hb hab x₁ y₁ ≤ convexCombPair a b ha hb hab x₂ y₂ := by
  simp only [convexCombPair_def]
  exact iConvexComb_le_iConvexComb (Fin.forall_fin_two.2 ⟨by simpa using hx, by simpa using hy⟩)

instance isOrderedConvexSpace_orderDual : IsOrderedConvexSpace R Xᵒᵈ where
  monotone_sConvexComb _w₁ _w₂ h := by
    rw [← OrderDual.ofDual_le_ofDual, ofDual_sConvexComb, ofDual_sConvexComb]
    exact sConvexComb_le_sConvexComb (StdSimplex.ofDual_le_iff.1 h)

end IsOrderedConvexSpace
end Convexity
