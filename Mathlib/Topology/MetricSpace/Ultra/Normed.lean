/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
## Ultrametric norms

This file describes behavior of norms in ultrametric spaces.

## Main results

* A normed additive group has an ultrametric iff the norm is nonarchimedean
* The (nn)norm of a sum of a list/multiset/finset/fintype/finsum is less than or equal to
  the maximum of the norm over the list/multiset/finset/fintype/finite set
* The supremum of the (nn)norm over a list/multiset/finset/fintype/finsum is a maximum when
  the "set" is nonempty

## Implementation details

Some results are proved first about `nnnorm : X → ℝ≥0` because the bottom element
in `NNReal` is 0, so easier to make statements about maxima of empty sets.

## Tags

ultrametric, nonarchimedean
-/
open Metric IsUltrametricDist NNReal

namespace IsUltrametricDist

section AddGroup

variable {S ι : Type*} [SeminormedAddGroup S] [IsUltrametricDist S]

lemma norm_add_le_max (x y : S) :
    ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [dist_eq_norm x (-y)] using dist_triangle_max x 0 (-y)

lemma isUltrametricDist_of_forall_norm_add_le_max_norm
    (h : ∀ x y : S, ‖x + y‖ ≤ max ‖x‖ ‖y‖) : IsUltrametricDist S := by
  constructor
  intro x y z
  simpa [dist_eq_norm] using h (x - y) (y - z)

lemma isUltrametricDist_of_isNonarchimedean_norm
    (h : IsNonarchimedean (norm : S → ℝ)) : IsUltrametricDist S :=
  isUltrametricDist_of_forall_norm_add_le_max_norm h

lemma nnnorm_add_le_max (x y : S) :
    ‖x + y‖₊ ≤ max ‖x‖₊ ‖y‖₊ :=
  norm_add_le_max _ _

lemma isUltrametricDist_of_forall_nnnorm_add_le_max_nnnorm
    (h : ∀ x y : S, ‖x + y‖₊ ≤ max ‖x‖₊ ‖y‖₊) : IsUltrametricDist S :=
  isUltrametricDist_of_forall_norm_add_le_max_norm h

lemma isUltrametricDist_of_isNonarchimedean_nnnorm
    (h : IsNonarchimedean ((↑) ∘ (nnnorm : S → ℝ≥0))) : IsUltrametricDist S :=
  isUltrametricDist_of_forall_nnnorm_add_le_max_nnnorm h

lemma _root_.List.nnnorm_sum_le_iSup_nnnorm (l : List S) :
    ‖l.sum‖₊ ≤ ⨆ x ∈ l, ‖x‖₊ := by
  rw [le_ciSup_iff']
  · intro b h
    induction l with
    | nil => simp
    | cons x xs IH =>
      rw [List.sum_cons]
      refine (nnnorm_add_le_max _ _).trans (max_le ((h x).trans' ?_) (IH fun y ↦ (h y).trans' ?_))
      · simp [le_ciSup_iff' (Set.finite_range _).bddAbove]
      · rw [le_ciSup_iff' (Set.finite_range _).bddAbove]
        intro c hy
        rw [ciSup_le_iff']
        · intro
          solve_by_elim
        · refine ⟨‖c‖₊, ?_⟩
          rintro z ⟨hz, rfl⟩
          solve_by_elim
  · exact (Set.finite_range_iSup_mem l.finite_toSet _).bddAbove

lemma _root_.List.norm_sum_le_iSup_norm (l : List S) :
    ‖l.sum‖ ≤ ⨆ x ∈ l, ‖x‖ := by
  have := l.nnnorm_sum_le_iSup_nnnorm
  rw [← Subtype.coe_le_coe] at this
  simpa using this

lemma _root_.List.iSup_nnnorm_mem_map_of_ne_nil {l : List S} (hl : l ≠ []) :
    ⨆ x ∈ l, ‖x‖₊ ∈ l.map (‖·‖₊) := by
  induction l with
  | nil => contradiction
  | cons y xs IH =>
    classical
    rcases eq_or_ne xs [] with rfl|hxs
    · simp only [List.mem_singleton, List.map_cons, List.map_nil]
      have : Nonempty S := ⟨y⟩
      refine le_antisymm (ciSup_le fun _ ↦ ?_) (le_ciSup_of_le ?_ y ?_)
      · simp only [ciSup_eq_ite, csSup_empty, bot_eq_zero', dite_eq_ite]
        split <;>
        simp_all
      · exact (Set.finite_range_iSup_mem (Set.finite_singleton y) _).bddAbove
      · simp
    · simp only [List.mem_cons, List.map_cons, ciSup_or']
      refine (le_total (⨆ x ∈ xs, ‖x‖₊) ‖y‖₊).imp (fun h ↦ ?_) (fun h ↦ ?_)
      · simp only [ciSup_eq_ite, csSup_empty, bot_eq_zero', dite_eq_ite]
        refine le_antisymm (ciSup_le fun x ↦ ?_) (le_ciSup_of_le ?_ y ?_)
        · split_ifs
          · simp_all
          · simp_all
          · refine h.trans' ?_
            simp only [zero_le, sup_of_le_right]
            rw [le_ciSup_iff']
            · intro b hb
              refine (hb x).trans' ?_
              simp_all
            · exact (Set.finite_range_iSup_mem xs.finite_toSet _).bddAbove
          · simp_all
        · refine ((((Set.finite_singleton ‖y‖₊).union (Set.finite_singleton 0)).union
            ((xs.map (‖·‖₊))).finite_toSet).subset ?_).bddAbove
          · intro b
            simp only [Set.mem_range, Set.union_singleton, List.mem_map, Set.mem_union,
              Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, forall_exists_index]
            intro
            split_ifs
            · simp_all
            · simp_all
            · simp only [zero_le, sup_of_le_right]
              rintro rfl
              exact Or.inr ⟨_, by assumption, rfl⟩
            · simp_all
        · simp
      · obtain ⟨a, hmem, ha⟩ := List.exists_of_mem_map (IH hxs)
        convert List.mem_map_of_mem _ hmem
        simp only [ha, sup_eq_right]
        refine le_antisymm (ciSup_le fun x ↦ ?_) (le_ciSup_of_le ?_ a ?_)
        · simp only [ciSup_eq_ite]
          split_ifs
          · simp_all [h, ciSup_eq_ite]
          · simp_all [h, ciSup_eq_ite]
          · simp_all only [ne_eq, not_false_eq_true, List.mem_map, true_implies, csSup_empty,
            bot_eq_zero', zero_le, sup_of_le_right]
            rw [le_ciSup_iff']
            · intro b hb
              refine (hb x).trans' ?_
              simp_all
            · convert (Set.finite_range_iSup_mem xs.finite_toSet (‖·‖₊)).bddAbove using 1
              simp [ciSup_eq_ite]
          · simp
        · refine ((((Set.finite_singleton ‖y‖₊).union (Set.finite_singleton 0)).union
            ((xs.map (‖·‖₊))).finite_toSet).subset ?_).bddAbove
          · intro b
            simp only [Set.mem_range, Set.union_singleton, List.mem_map, Set.mem_union,
              Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, forall_exists_index]
            intro
            simp only [ciSup_eq_ite]
            split_ifs
            · simp_all
            · simp_all
            · simp only [csSup_empty, bot_eq_zero', zero_le, sup_of_le_right]
              rintro rfl
              refine Or.inr ⟨_, by assumption, rfl⟩
            · simp_all
        · rw [← ha]
          simp [ciSup_eq_ite, hmem]

lemma _root_.List.iSup_norm_mem_map_of_ne_nil {l : List S} (hl : l ≠ []) :
    ⨆ x ∈ l, ‖x‖ ∈ l.map (‖·‖) := by
  obtain ⟨y, hmem, hy⟩ := List.exists_of_mem_map (l.iSup_nnnorm_mem_map_of_ne_nil hl)
  convert List.mem_map_of_mem _ hmem
  rw [Subtype.ext_iff] at hy
  simpa using hy.symm

/-- All triangles are isosceles in an ultrametric normed commutative additive group. -/
lemma norm_add_eq_max_of_norm_ne_norm
    {x y : S} (h : ‖x‖ ≠ ‖y‖) : ‖x + y‖ = max ‖x‖ ‖y‖ := by
  rcases le_total ‖x‖ ‖y‖ with hxy|hxy  -- instead of wlog, which would require add_comm
  · rw [max_eq_right hxy]
    refine le_antisymm ((norm_add_le_max x y).trans ?_) ?_
    · simp [h, hxy]
    · simpa [(lt_of_le_of_ne hxy h).not_le] using norm_add_le_max (-x) (x + y)
  · rw [max_eq_left hxy]
    refine le_antisymm ((norm_add_le_max x y).trans ?_) ?_
    · simp [h, hxy]
    · simpa [(lt_of_le_of_ne hxy (Ne.symm h)).not_le] using norm_add_le_max (x + y) (-y)

lemma norm_eq_of_add_norm_lt_max {x y : S} (h : ‖x + y‖ < max ‖x‖ ‖y‖) :
    ‖x‖ = ‖y‖ := by
  contrapose! h
  rw [norm_add_eq_max_of_norm_ne_norm h]

/-- All triangles are isosceles in an ultrametric normed commutative additive group. -/
lemma nnnorm_add_eq_max_of_nnnorm_ne_nnnorm
    {x y : S} (h : ‖x‖₊ ≠ ‖y‖₊) : ‖x + y‖₊ = max ‖x‖₊ ‖y‖₊ := by
  rw [ne_eq] at h
  rw [Subtype.ext_iff] at h ⊢
  simpa using norm_add_eq_max_of_norm_ne_norm h

lemma nnnorm_eq_of_add_nnnorm_lt_max {x y : S} (h : ‖x + y‖₊ < max ‖x‖₊ ‖y‖₊) :
    ‖x‖₊ = ‖y‖₊ := by
  contrapose! h
  rw [nnnorm_add_eq_max_of_nnnorm_ne_nnnorm h]

/-- All triangles are isosceles in an ultrametric normed commutative additive group. -/
lemma norm_sub_eq_max_of_norm_sub_ne_norm_sub (x y z : S) (h : ‖x - y‖ ≠ ‖y - z‖) :
    ‖x - z‖ = max ‖x - y‖ ‖y - z‖ := by
  simpa using norm_add_eq_max_of_norm_ne_norm h

/-- All triangles are isosceles in an ultrametric normed commutative additive group. -/
lemma dist_eq_max_of_dist_ne_dist (x y z : S) (h : dist x y ≠ dist y z) :
    dist x z = max (dist x y) (dist y z) := by
  simp only [dist_eq_norm] at h ⊢
  exact norm_sub_eq_max_of_norm_sub_ne_norm_sub _ _ _ h

/-- All triangles are isosceles in an ultrametric normed commutative additive group. -/
lemma nnnorm_sub_eq_max_of_nnnorm_sub_ne_nnnorm_sub (x y z : S) (h : ‖x - y‖₊ ≠ ‖y - z‖₊) :
    ‖x - z‖₊ = max ‖x - y‖₊ ‖y - z‖₊ := by
  rw [ne_eq] at h
  rw [Subtype.ext_iff] at h ⊢
  simpa using norm_add_eq_max_of_norm_ne_norm h

lemma nnnorm_nsmul_le (x : S) (n : ℕ) :
    ‖n • x‖₊ ≤ ‖x‖₊ := by
  induction n with
  | zero => simp
  | succ n hn => simpa [add_nsmul, hn] using nnnorm_add_le_max (n • x) x

lemma norm_nsmul_le (x : S) (n : ℕ) :
    ‖n • x‖ ≤ ‖x‖ :=
  nnnorm_nsmul_le x n

lemma nnnorm_zsmul_le (x : S) (z : ℤ) :
    ‖z • x‖₊ ≤ ‖x‖₊ := by
  induction z <;>
  simpa using nnnorm_nsmul_le _ _

lemma norm_zsmul_le (x : S) (z : ℤ) :
    ‖z • x‖ ≤ ‖x‖ :=
  nnnorm_zsmul_le x z

end AddGroup

section AddCommGroup

variable {M ι : Type*} [SeminormedAddCommGroup M] [IsUltrametricDist M]

lemma _root_.Multiset.nnnorm_sum_le_iSup_nnnorm (s : Multiset M) :
    ‖s.sum‖₊ ≤ ⨆ i ∈ s, ‖i‖₊ :=
  Quotient.inductionOn s (by simpa using List.nnnorm_sum_le_iSup_nnnorm)

lemma _root_.Multiset.norm_sum_le_iSup_norm (s : Multiset M) :
    ‖s.sum‖ ≤ ⨆ i ∈ s, ‖i‖ :=
  Quotient.inductionOn s (by simpa using List.norm_sum_le_iSup_norm)

lemma _root_.Multiset.iSup_nnnorm_mem_map_of_ne_nil {s : Multiset M} (hs : s ≠ ∅) :
    ⨆ x ∈ s, ‖x‖₊ ∈ s.map (‖·‖₊) := by
  induction s using Quotient.inductionOn
  simp only [Multiset.quot_mk_to_coe, Multiset.empty_eq_zero, ne_eq, Multiset.coe_eq_zero] at hs
  exact List.iSup_nnnorm_mem_map_of_ne_nil hs

lemma _root_.Multiset.iSup_norm_mem_map_of_ne_nil {s : Multiset M} (hs : s ≠ ∅) :
    ⨆ x ∈ s, ‖x‖ ∈ s.map (‖·‖) := by
  induction s using Quotient.inductionOn
  simp only [Multiset.quot_mk_to_coe, Multiset.empty_eq_zero, ne_eq, Multiset.coe_eq_zero] at hs
  exact List.iSup_norm_mem_map_of_ne_nil hs

/-- Nonarchimedean norm of a sum is less than or equal the norm of any term in the sum. -/
lemma _root_.Finset.nnnorm_sum_le_iSup_nnnorm (s : Finset ι) (f : ι → M) :
    ‖∑ i ∈ s, f i‖₊ ≤ ⨆ i ∈ s, ‖f i‖₊ := by
  refine ((s.1.map f).nnnorm_sum_le_iSup_nnnorm).trans_eq ?_
  rcases isEmpty_or_nonempty ι
  · simp
  rcases s.eq_empty_or_nonempty with rfl|hs
  · simp
  have : Set.Nonempty (s : Set ι) := hs
  have keyl (i : M) : ⨆ (_ : i ∈ Multiset.map f s.val), ‖i‖₊ = ⨆ (_ : i ∈ f '' s), ‖i‖₊ := by
    simp
  rw [iSup_congr keyl, ciSup_image this]
  · congr
  · simpa [bddAbove_def] using (s.image _).finite_toSet.bddAbove
  · simp

/-- Nonarchimedean norm of a sum is less than or equal the norm of any term in the sum. -/
lemma _root_.Finset.norm_sum_le_iSup_norm (s : Finset ι) (f : ι → M) :
    ‖∑ i ∈ s, f i‖ ≤ ⨆ i ∈ s, ‖f i‖ := by
  have := s.nnnorm_sum_le_iSup_nnnorm f
  rw [← Subtype.coe_le_coe] at this
  simpa using this

/-- Nonarchimedean norm of a sum is less than or equal the norm of any term in the sum. -/
lemma _root_.Finset.nnnorm_sum_le_sup_nnnorm (s : Finset ι) (f : ι → M) :
    ‖∑ i ∈ s, f i‖₊ ≤ s.sup (‖f ·‖₊) := by
  refine (s.nnnorm_sum_le_iSup_nnnorm _).trans ?_
  rw [ciSup_le_iff']
  · intro i
    classical
    rw [ciSup_eq_ite]
    split_ifs with hi
    · exact Finset.le_sup (f := (‖f ·‖₊)) hi
    · simp
  · exact (Set.finite_range_iSup_mem s.finite_toSet _).bddAbove

/-- Nonarchimedean norm of a sum is less than or equal the norm of any term in the sum.
This version is phrased using `Finset.sup'` and `Finset.Nonempty` due to `Finset.sup`
operating over an `OrderBot`, which `ℝ` is not.
-/
lemma _root_.Finset.Nonempty.norm_sum_le_sup'_norm {s : Finset ι} (hs : s.Nonempty) (f : ι → M) :
    ‖∑ i ∈ s, f i‖ ≤ s.sup' hs (‖f ·‖) := by
  refine (s.norm_sum_le_iSup_norm _).trans ?_
  classical
  simp_rw [ciSup_eq_ite]
  obtain ⟨i, -⟩ := id hs
  have : Nonempty ι := ⟨i⟩
  refine ciSup_le ?_
  intro i'
  split_ifs with hi
  · exact Finset.le_sup' (f := (‖f ·‖)) hi
  · simpa using hs

/-- A finset achieves its maximum under a nonarchimedean norm for some element. -/
lemma _root_.Finset.Nonempty.iSup_nnnorm_mem_image {s : Finset ι} (hs : s.Nonempty) (f : ι → M) :
    ⨆ x ∈ s, ‖f x‖₊ ∈ s.image (‖f ·‖₊) := by
  convert (s.1.map f).iSup_nnnorm_mem_map_of_ne_nil ?_
  · have : Nonempty ι := nonempty_of_exists hs
    have : Set.Nonempty (s : Set ι) := hs
    have keyl (i : M) : ⨆ (_ : i ∈ Multiset.map f s.val), ‖i‖₊ = ⨆ (_ : i ∈ f '' s), ‖i‖₊ := by
      simp
    rw [iSup_congr keyl, ciSup_image this]
    · simp
    · simpa [bddAbove_def] using (s.image _).finite_toSet.bddAbove
    · simp
  · simpa [Finset.nonempty_iff_ne_empty] using hs

/-- A finset achieves its maximum under a nonarchimedean norm for some element. -/
lemma _root_.Finset.Nonempty.iSup_norm_mem_image {s : Finset ι} (hs : s.Nonempty) (f : ι → M) :
    ⨆ x ∈ s, ‖f x‖ ∈ s.image (‖f ·‖) := by
  convert (s.1.map f).iSup_norm_mem_map_of_ne_nil ?_
  · have : Nonempty ι := nonempty_of_exists hs
    have : Set.Nonempty (s : Set ι) := hs
    have keyl (i : M) : ⨆ (_ : i ∈ Multiset.map f s.val), ‖i‖ = ⨆ (_ : i ∈ f '' s), ‖i‖ := by
      simp
    rw [iSup_congr keyl, ciSup_image this]
    · simp
    · simpa [bddAbove_def] using (s.image _).finite_toSet.bddAbove
    · simpa using Real.iSup_nonneg (by simp)
  · simpa [Finset.nonempty_iff_ne_empty] using hs

/-- Nonarchimedean norm of a sum is less than or equal the norm of any term in the sum. -/
lemma _root_.Fintype.nnnorm_sum_le_sup_norm (s : Finset ι) (f : ι → M) :
    ‖∑ i ∈ s, f i‖₊ ≤ s.sup (‖f ·‖₊) := by
  refine (s.nnnorm_sum_le_iSup_nnnorm _).trans ?_
  rw [ciSup_le_iff']
  · intro i
    classical
    rw [ciSup_eq_ite]
    split_ifs with hi
    · exact Finset.le_sup (f := (‖f ·‖₊)) hi
    · simp
  · exact (Set.finite_range_iSup_mem s.finite_toSet _).bddAbove

/-- Nonarchimedean norm of a sum is less than or equal the norm of any term in the sum. -/
lemma _root_.Fintype.nnnorm_sum_le_iSup_nnnorm [Fintype ι] (f : ι → M) :
    ‖∑ i, f i‖₊ ≤ ⨆ i, ‖f i‖₊ := by
  simpa using Finset.nnnorm_sum_le_iSup_nnnorm Finset.univ f

/-- Nonarchimedean norm of a sum is less than or equal the norm of any term in the sum. -/
lemma _root_.Fintype.norm_sum_le_iSup_norm [Fintype ι] (f : ι → M) :
    ‖∑ i, f i‖ ≤ ⨆ i, ‖f i‖ := by
  simpa using Finset.norm_sum_le_iSup_norm Finset.univ f

/-- Nonarchimedean norm of a sum is less than or equal the norm of any term in the sum. -/
lemma _root_.nnnorm_finsum_le_iSup_nnnorm (f : ι → M) :
    ‖∑ᶠ i, f i‖₊ ≤ ⨆ i, ‖f i‖₊ := by
  classical
  rw [finsum_def]
  split_ifs with h
  · refine (h.toFinset.nnnorm_sum_le_iSup_nnnorm f).trans ?_
    rw [ciSup_le_iff']
    · intro
      rw [ciSup_le_iff' (Set.finite_range _).bddAbove]
      intro
      refine le_ciSup (f := (‖f ·‖₊))
        (((h.image (‖f ·‖₊)).union (Set.finite_singleton 0)).subset ?_).bddAbove  _
      intro
      simp only [Set.mem_range, Set.union_singleton, Set.mem_insert_iff, Set.mem_image,
        Function.mem_support, ne_eq, forall_exists_index]
      rintro i rfl
      refine (eq_or_ne _ _).imp_right (fun hi ↦ ⟨i, mt ?_ hi, rfl⟩)
      simp (config := {contextual := true})
    · refine (Set.finite_range_iSup_mem (h.subset ?_) _).bddAbove
      intro _ ha -- needed becaues `(Function.support f).Finite` doesn't simplify as expected
      simpa using ha
  · simp

/-- Nonarchimedean norm of a sum is less than or equal the norm of any term in the sum. -/
lemma _root_.norm_finsum_le_iSup_norm (f : ι → M) :
    ‖∑ᶠ i, f i‖ ≤ ⨆ i, ‖f i‖ := by
  have := nnnorm_finsum_le_iSup_nnnorm f
  rw [← Subtype.coe_le_coe] at this
  simpa using this

end AddCommGroup

section DivisionRing

variable {K : Type*} [NormedDivisionRing K] [IsUltrametricDist K]

lemma norm_add_one_le_max_norm_one (x : K) :
    ‖x + 1‖ ≤ max ‖x‖ 1 := by
  simpa using norm_add_le_max x 1

lemma nnnorm_add_one_le_max_nnnorm_one (x : K) :
    ‖x + 1‖₊ ≤ max ‖x‖₊ 1 := by
  simpa using norm_add_le_max x 1

lemma nnnorm_natCast_le_one (n : ℕ) :
    ‖(n : K)‖₊ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n hn => simpa [hn] using nnnorm_add_one_le_max_nnnorm_one (n : K)

lemma norm_natCast_le_one (n : ℕ) :
    ‖(n : K)‖ ≤ 1 := by
  rw [← Real.toNNReal_le_toNNReal_iff zero_le_one]
  simpa using nnnorm_natCast_le_one n

lemma nnnorm_intCast_le_one (z : ℤ) :
    ‖(z : K)‖₊ ≤ 1 := by
  induction z
  · simpa using nnnorm_natCast_le_one _
  · simpa only [Int.cast_negSucc, Nat.cast_one, nnnorm_neg] using nnnorm_natCast_le_one _

lemma norm_intCast_le_one (z : ℤ) :
    ‖(z : K)‖ ≤ 1 := by
  rw [← Real.toNNReal_le_toNNReal_iff zero_le_one]
  simpa using nnnorm_intCast_le_one z

end DivisionRing

end IsUltrametricDist
