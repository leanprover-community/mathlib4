/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
import Mathlib.Topology.MetricSpace.Basic

#align_import topology.metric_space.infsep from "leanprover-community/mathlib"@"5316314b553dcf8c6716541851517c1a9715e22b"

/-!
# Infimum separation

This file defines the extended infimum separation of a set. This is approximately dual to the
diameter of a set, but where the extended diameter of a set is the supremum of the extended distance
between elements of the set, the extended infimum separation is the infimum of the (extended)
distance between *distinct* elements in the set.

We also define the infimum separation as the cast of the extended infimum separation to the reals.
This is the infimum of the distance between distinct elements of the set when in a pseudometric
space.

All lemmas and definitions are in the `Set` namespace to give access to dot notation.

## Main definitions
* `EMetric.infsep`: Extended infimum separation of a set.
* `Metric.infsep`: Infimum separation of a set (when in a pseudometric space).

-/


variable {α β : Type*}

namespace EMetric

open ENNReal Set

open Function

/-- The "extended infimum separation" of a set with an edist function. -/
noncomputable def infsep [EDist α] (s : Set α) : ℝ≥0∞ :=
  ⨅ (x ∈ s) (y ∈ s) (_ : x ≠ y), edist x y
#align set.einfsep EMetric.infsep

section EDist

variable [EDist α] {x y : α} {s t : Set α}

theorem le_infsep_iff {d} :
    d ≤ infsep s ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ edist x y := by
  simp_rw [infsep, le_iInf_iff]
#align set.le_einfsep_iff EMetric.le_infsep_iff

theorem infsep_zero : infsep s = 0 ↔ ∀ C > 0, ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y < C := by
  simp_rw [infsep, ← _root_.bot_eq_zero, iInf_eq_bot, iInf_lt_iff, exists_prop]
#align set.einfsep_zero EMetric.infsep_zero

theorem infsep_pos : 0 < infsep s ↔ ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ edist x y := by
  rw [pos_iff_ne_zero, Ne.def, infsep_zero]
  simp only [not_forall, not_exists, not_lt, exists_prop, not_and]
#align set.einfsep_pos EMetric.infsep_pos

theorem infsep_lt_iff {d} :
    infsep s < d ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y < d := by
  simp_rw [infsep, iInf_lt_iff, exists_prop]
#align set.einfsep_lt_iff EMetric.infsep_lt_iff

theorem infsep_ne_top_iff :
    infsep s ≠ ∞ ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y ≠ ∞ := by
  simp_rw [← lt_top_iff_ne_top, infsep_lt_iff]
#align set.einfsep_ne_top EMetric.infsep_ne_top_iff

theorem infsep_eq_top_iff :
    infsep s = ∞ ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → edist x y = ∞ := by
  rw [← not_iff_not]
  push_neg
  exact infsep_ne_top_iff
#align set.einfsep_top EMetric.infsep_eq_top_iff

theorem nontrivial_of_infsep_lt_top (hs : infsep s < ∞) : s.Nontrivial := by
  rcases infsep_lt_iff.1 hs with ⟨_, hx, _, hy, hxy, _⟩
  exact ⟨_, hx, _, hy, hxy⟩
#align set.nontrivial_of_einfsep_lt_top EMetric.nontrivial_of_infsep_lt_top

theorem nontrivial_of_infsep_ne_top (hs : infsep s ≠ ∞) : s.Nontrivial :=
  nontrivial_of_infsep_lt_top (lt_top_iff_ne_top.mpr hs)
#align set.nontrivial_of_infsep_ne_top EMetric.nontrivial_of_infsep_ne_top

theorem infsep_eq_top_of_subsingleton (hs : s.Subsingleton) : infsep s = ∞ := by
  rw [infsep_eq_top_iff]
  exact fun _ hx _ hy hxy => (hxy <| hs hx hy).elim
#align set.subsingleton.einfsep EMetric.infsep_eq_top_of_subsingleton

theorem le_infsep_image_iff {d} {f : β → α} {s : Set β} : d ≤ infsep (f '' s)
    ↔ ∀ x ∈ s, ∀ y ∈ s, f x ≠ f y → d ≤ edist (f x) (f y) := by
  simp_rw [le_infsep_iff, Set.ball_image_iff]
#align set.le_einfsep_image_iff EMetric.le_infsep_image_iff

theorem le_edist_of_le_infsep {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hd : d ≤ infsep s) : d ≤ edist x y :=
  le_infsep_iff.1 hd x hx y hy hxy
#align set.le_edist_of_le_einfsep EMetric.le_edist_of_le_infsep

theorem infsep_le_edist_of_mem {x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y) :
    infsep s ≤ edist x y :=
  le_edist_of_le_infsep hx hy hxy le_rfl
#align set.einfsep_le_edist_of_mem EMetric.infsep_le_edist_of_mem

theorem infsep_le_of_mem_of_edist_le {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hxy' : edist x y ≤ d) : infsep s ≤ d :=
  le_trans (infsep_le_edist_of_mem hx hy hxy) hxy'
#align set.einfsep_le_of_mem_of_edist_le EMetric.infsep_le_of_mem_of_edist_le

theorem le_infsep {d} (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ edist x y) : d ≤ infsep s :=
  le_infsep_iff.2 h
#align set.le_einfsep EMetric.le_infsep

@[simp]
theorem infsep_empty : infsep (∅ : Set α) = ∞ := infsep_eq_top_of_subsingleton subsingleton_empty
#align set.einfsep_empty EMetric.infsep_empty

@[simp]
theorem infsep_singleton : infsep ({x} : Set α) = ∞ :=
  infsep_eq_top_of_subsingleton subsingleton_singleton
#align set.einfsep_singleton EMetric.infsep_singleton

theorem infsep_iUnion_mem_option {ι : Type*} (o : Option ι) (s : ι → Set α) :
    infsep (⋃ i ∈ o, s i) = ⨅ i ∈ o, infsep (s i) := by cases o <;> simp
#align set.einfsep_Union_mem_option EMetric.infsep_iUnion_mem_option

theorem infsep_anti (hst : s ⊆ t) : infsep t ≤ infsep s :=
  le_infsep fun _x hx _y hy => infsep_le_edist_of_mem (hst hx) (hst hy)
#align set.einfsep_anti EMetric.infsep_anti

theorem infsep_insert_le : infsep (insert x s) ≤ ⨅ (y ∈ s) (_ : x ≠ y), edist x y := by
  simp_rw [le_iInf_iff]
  refine' fun _ hy hxy => infsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ hy) hxy
#align set.einfsep_insert_le EMetric.infsep_insert_le

theorem le_infsep_pair : edist x y ⊓ edist y x ≤ infsep ({x, y} : Set α) := by
  simp_rw [le_infsep_iff, inf_le_iff, mem_insert_iff, mem_singleton_iff]
  rintro a (rfl | rfl) b (rfl | rfl) hab <;> (try simp only [le_refl, true_or, or_true]) <;>
    contradiction
#align set.le_einfsep_pair EMetric.le_infsep_pair

theorem infsep_pair_le_left (hxy : x ≠ y) : infsep ({x, y} : Set α) ≤ edist x y :=
  infsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hxy
#align set.einfsep_pair_le_left EMetric.infsep_pair_le_left

theorem infsep_pair_le_right (hxy : x ≠ y) : infsep ({x, y} : Set α) ≤ edist y x := by
  rw [pair_comm]; exact infsep_pair_le_left hxy.symm
#align set.einfsep_pair_le_right EMetric.infsep_pair_le_right

theorem infsep_pair_eq_inf (hxy : x ≠ y) : infsep ({x, y} : Set α) = edist x y ⊓ edist y x :=
  le_antisymm (le_inf (infsep_pair_le_left hxy) (infsep_pair_le_right hxy)) le_infsep_pair
#align set.einfsep_pair_eq_inf EMetric.infsep_pair_eq_inf

theorem infsep_eq_iInf : infsep s = ⨅ d : s.offDiag, (uncurry edist) (d : α × α) := by
  refine' eq_of_forall_le_iff fun _ => _
  simp_rw [le_infsep_iff, le_iInf_iff, imp_forall_iff, SetCoe.forall, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]
#align set.einfsep_eq_infi EMetric.infsep_eq_iInf

theorem coe_finset_infsep_eq_inf [DecidableEq α] {s : Finset α} :
    infsep (s : Set α) = s.offDiag.inf (uncurry edist) := by
  refine' eq_of_forall_le_iff fun _ => _
  simp_rw [le_infsep_iff, Finset.mem_coe, imp_forall_iff, Finset.le_inf_iff, Finset.mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]
#align set.finset.coe_einfsep EMetric.coe_finset_infsep_eq_inf

theorem infsep_eq_inf_of_finite (hsf : s.Finite) :
    infsep s = hsf.offDiag.toFinset.inf (uncurry edist) := by
  rcases hsf.exists_finset_coe with ⟨s, rfl⟩
  classical
    rw [coe_finset_infsep_eq_inf, Finset.inf_congr _ (fun _ _ => rfl)]
    simp_rw [Finset.ext_iff, Finset.mem_offDiag, ne_eq, toFinite_toFinset, mem_toFinset,
      mem_offDiag, Finset.mem_coe, implies_true]
#align set.finite.einfsep EMetric.infsep_eq_inf_of_finite

theorem exists_coe_finset_infsep_eq_edist_of_nontrivial [DecidableEq α] {s : Finset α}
    (hs : s.Nontrivial) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ infsep (s : Set α) = edist x y := by
  rw [coe_finset_infsep_eq_inf]
  rcases Finset.exists_mem_eq_inf s.offDiag
    (match hs with | ⟨x, hx, y, hy, hxy⟩ => ⟨⟨x, y⟩, Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩⟩)
    (uncurry edist) with ⟨⟨x, y⟩, hxy, hed⟩
  rw [Finset.mem_offDiag] at hxy
  rcases hxy with ⟨hx, hy, hxy⟩
  exact ⟨x, hx, y, hy, hxy, hed⟩

theorem infsep_exists_of_finite_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ infsep s = edist x y := by
  rcases hsf.exists_finset_coe with ⟨s, rfl⟩
  classical exact exists_coe_finset_infsep_eq_edist_of_nontrivial hs
#align set.finite.einfsep_exists_of_nontrivial EMetric.infsep_exists_of_finite_of_nontrivial

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] {x y z : α} {s t : Set α}

theorem infsep_pair (hxy : x ≠ y) : infsep ({x, y} : Set α) = edist x y := by
  nth_rw 1 [← min_self (edist x y)]
  convert infsep_pair_eq_inf hxy using 2
  rw [edist_comm]
#align set.einfsep_pair EMetric.infsep_pair

theorem infsep_insert : infsep (insert x s) =
    (⨅ (y ∈ s) (_ : x ≠ y), edist x y) ⊓ infsep s := by
  refine' le_antisymm (le_min infsep_insert_le (infsep_anti (subset_insert _ _))) _
  simp_rw [le_infsep_iff, inf_le_iff, mem_insert_iff]
  rintro y (rfl | hy) z (rfl | hz) hyz
  · exact False.elim (hyz rfl)
  · exact Or.inl (iInf_le_of_le _ (iInf₂_le hz hyz))
  · rw [edist_comm]
    exact Or.inl (iInf_le_of_le _ (iInf₂_le hy hyz.symm))
  · exact Or.inr (infsep_le_edist_of_mem hy hz hyz)
#align set.einfsep_insert EMetric.infsep_insert

theorem infsep_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    infsep ({x, y, z} : Set α) = edist x y ⊓ edist x z ⊓ edist y z := by
  simp_rw [infsep_insert, iInf_insert, iInf_singleton, infsep_singleton, inf_top_eq,
    ciInf_pos hxy, ciInf_pos hyz, ciInf_pos hxz]
#align set.einfsep_triple EMetric.infsep_triple

theorem le_infsep_pi_of_le {π : β → Type*} [Fintype β] [∀ b, PseudoEMetricSpace (π b)]
    {s : ∀ b : β, Set (π b)} {c : ℝ≥0∞} (h : ∀ b, c ≤ infsep (s b)) :
    c ≤ infsep (pi univ s) := by
  refine' le_infsep fun x hx y hy hxy => _
  rw [mem_univ_pi] at hx hy
  rcases Function.ne_iff.mp hxy with ⟨i, hi⟩
  exact le_trans (le_infsep_iff.1 (h i) _ (hx _) _ (hy _) hi) (edist_le_pi_edist _ _ i)
#align set.le_einfsep_pi_of_le EMetric.le_infsep_pi_of_le

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] {s : Set α}

theorem infsep_ne_top_of_nontrivial : s.Nontrivial → infsep s ≠ ∞ :=
  fun ⟨x, hx, y, hy, hxy⟩ => infsep_ne_top_iff.mpr ⟨x, hx, y, hy, hxy, edist_ne_top x y⟩
#align set.nontrivial.einfsep_ne_top EMetric.infsep_ne_top_of_nontrivial

theorem infsep_ne_top_iff_nontrivial : infsep s ≠ ∞ ↔ s.Nontrivial :=
  ⟨nontrivial_of_infsep_ne_top, infsep_ne_top_of_nontrivial⟩
#align set.einfsep_ne_top_iff EMetric.infsep_ne_top_iff_nontrivial

theorem infsep_lt_top_of_nontrivial (hs : s.Nontrivial) : infsep s < ∞ := by
  rw [lt_top_iff_ne_top]
  exact infsep_ne_top_of_nontrivial hs
#align set.nontrivial.einfsep_lt_top EMetric.infsep_lt_top_of_nontrivial

theorem infsep_lt_top_iff_nontrivial : infsep s < ∞ ↔ s.Nontrivial :=
  ⟨nontrivial_of_infsep_lt_top, infsep_lt_top_of_nontrivial⟩
#align set.einfsep_lt_top_iff EMetric.infsep_lt_iff

theorem subsingleton_of_infsep_eq_top : infsep s = ∞ → s.Subsingleton :=
  (fun hs => infsep_ne_top_of_nontrivial (not_subsingleton_iff.mp hs)).mtr
#align set.subsingleton_of_einfsep_eq_top EMetric.subsingleton_of_infsep_eq_top

theorem infsep_eq_top_iff_subsingleton : infsep s = ∞ ↔ s.Subsingleton :=
  ⟨subsingleton_of_infsep_eq_top, infsep_eq_top_of_subsingleton⟩
#align set.einfsep_eq_top_iff EMetric.infsep_eq_top_iff_subsingleton

theorem ofReal_pos_le_infsep_iff {d} :
    ENNReal.ofReal d ≤ infsep s ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y := by
  rcases le_or_lt d 0 with (hd | hd)
  · simp_rw [ENNReal.ofReal_of_nonpos hd, zero_le, true_iff]
    exact fun _ _ _ _ _ => hd.trans dist_nonneg
  · simp_rw [le_infsep_iff, edist_dist, ENNReal.ofReal_le_ofReal_iff', hd.not_le, or_false]

end PseudoMetricSpace

section EMetricSpace

variable [EMetricSpace α] {x y z : α} {s t : Set α} {C : ℝ≥0∞} {sC : Set ℝ≥0∞}

theorem infsep_pos_of_finite (hsf : s.Finite) : 0 < infsep s := by
  by_cases hs : s.Nontrivial
  · rcases infsep_exists_of_finite_of_nontrivial hsf hs with ⟨x, _, y, _, hxy, hxy'⟩
    exact hxy'.symm ▸ edist_pos.2 hxy
  · rw [not_nontrivial_iff] at hs
    rw [infsep_eq_top_of_subsingleton hs]
    exact WithTop.zero_lt_top
#align set.finite.einfsep_pos EMetric.infsep_pos_of_finite

theorem relatively_discrete_of_finite (hsf : s.Finite) :
    ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ edist x y := by
  rw [← infsep_pos]
  exact infsep_pos_of_finite hsf
#align set.finite.relatively_discrete EMetric.relatively_discrete_of_finite

end EMetricSpace

end EMetric

namespace Metric

open ENNReal

open Set Function

/-- The "infimum separation" of a set with an edist function. -/
noncomputable def infsep [EDist α] (s : Set α) : ℝ :=
  ENNReal.toReal (EMetric.infsep s)
#align set.infsep Metric.infsep

section EDist

variable [EDist α] {x y : α} {s : Set α}

theorem infsep_zero : infsep s = 0 ↔ EMetric.infsep s = 0 ∨ EMetric.infsep s = ∞ := by
  rw [infsep, ENNReal.toReal_eq_zero_iff]
#align set.infsep_zero Metric.infsep_zero

theorem infsep_nonneg : 0 ≤ infsep s :=
  ENNReal.toReal_nonneg
#align set.infsep_nonneg Metric.infsep_nonneg

theorem infsep_pos : 0 < infsep s ↔ 0 < EMetric.infsep s ∧ EMetric.infsep s < ∞ := by
  simp_rw [infsep, ENNReal.toReal_pos_iff]
#align set.infsep_pos Metric.infsep_pos

theorem infsep_eq_zero_of_subsingleton (hs : s.Subsingleton) : infsep s = 0 :=
  Metric.infsep_zero.mpr <| Or.inr (EMetric.infsep_eq_top_of_subsingleton hs)
#align set.subsingleton.infsep_zero Metric.infsep_eq_zero_of_subsingleton

theorem nontrivial_of_infsep_pos (hs : 0 < infsep s) : s.Nontrivial := by
  contrapose hs
  rw [not_nontrivial_iff] at hs
  rw [infsep_eq_zero_of_subsingleton hs]
  exact lt_irrefl _
#align set.nontrivial_of_infsep_pos Metric.nontrivial_of_infsep_pos

theorem infsep_empty : infsep (∅ : Set α) = 0 :=
  infsep_eq_zero_of_subsingleton subsingleton_empty
#align set.infsep_empty Metric.infsep_empty

theorem infsep_singleton : infsep ({x} : Set α) = 0 :=
  infsep_eq_zero_of_subsingleton subsingleton_singleton
#align set.infsep_singleton Metric.infsep_singleton

theorem infsep_pair_le_toReal_inf (hxy : x ≠ y) :
    infsep ({x, y} : Set α) ≤ (edist x y ⊓ edist y x).toReal := by
  simp_rw [infsep, EMetric.infsep_pair_eq_inf hxy]
  exact le_rfl
#align set.infsep_pair_le_to_real_inf Metric.infsep_pair_le_toReal_inf

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] {x y : α} {s : Set α}

theorem infsep_pair_eq_toReal : infsep ({x, y} : Set α) = (edist x y).toReal := by
  by_cases hxy : x = y
  · rw [hxy]
    simp only [infsep_singleton, pair_eq_singleton, edist_self, ENNReal.zero_toReal]
  · rw [infsep, EMetric.infsep_pair hxy]
#align set.infsep_pair_eq_to_real Metric.infsep_pair_eq_toReal

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] {x y z : α} {s t : Set α}

theorem le_infsep_iff_of_nontrivial {d} (hs : s.Nontrivial) :
    d ≤ infsep s ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y := by
  simp_rw [infsep, ← ENNReal.ofReal_le_iff_le_toReal (EMetric.infsep_ne_top_of_nontrivial hs)]
  exact EMetric.ofReal_pos_le_infsep_iff
#align set.nontrivial.le_infsep_iff Metric.le_infsep_iff_of_nontrivial

theorem infsep_lt_iff_of_nontrivial {d} (hs : s.Nontrivial) :
    infsep s < d ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ dist x y < d := by
  rw [← not_iff_not]
  push_neg
  exact le_infsep_iff_of_nontrivial hs
#align set.nontrivial.infsep_lt_iff Metric.infsep_lt_iff_of_nontrivial

theorem le_infsep_of_nontrivial {d} (hs : s.Nontrivial)
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y) : d ≤ infsep s :=
  (le_infsep_iff_of_nontrivial hs).2 h
#align set.nontrivial.le_infsep Metric.le_infsep_of_nontrivial

theorem le_edist_of_le_infsep {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hd : d ≤ infsep s) : d ≤ dist x y := by
  by_cases hs : s.Nontrivial
  · exact (le_infsep_iff_of_nontrivial hs).1 hd x hx y hy hxy
  · rw [not_nontrivial_iff] at hs
    rw [infsep_eq_zero_of_subsingleton hs] at hd
    exact le_trans hd dist_nonneg
#align set.le_edist_of_le_infsep Metric.le_edist_of_le_infsep

theorem infsep_le_dist_of_mem (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : infsep s ≤ dist x y :=
  le_edist_of_le_infsep hx hy hxy le_rfl
#align set.infsep_le_dist_of_mem Metric.infsep_le_dist_of_mem

theorem infsep_le_of_mem_of_edist_le {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hxy' : dist x y ≤ d) : infsep s ≤ d :=
  le_trans (infsep_le_dist_of_mem hx hy hxy) hxy'
#align set.infsep_le_of_mem_of_edist_le Metric.infsep_le_of_mem_of_edist_le

theorem infsep_pair : infsep ({x, y} : Set α) = dist x y := by
  rw [infsep_pair_eq_toReal, edist_dist]
  exact ENNReal.toReal_ofReal dist_nonneg
#align set.infsep_pair Metric.infsep_pair

theorem infsep_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    infsep ({x, y, z} : Set α) = dist x y ⊓ dist x z ⊓ dist y z := by
  simp only [infsep, EMetric.infsep_triple hxy hyz hxz, ENNReal.toReal_inf, edist_ne_top x y,
    edist_ne_top x z, edist_ne_top y z, dist_edist, Ne.def, inf_eq_top_iff, and_self_iff,
    not_false_iff]
#align set.infsep_triple Metric.infsep_triple

theorem infsep_anti_of_nontrivial (hs : s.Nontrivial) (hst : s ⊆ t) : infsep t ≤ infsep s :=
  ENNReal.toReal_mono (EMetric.infsep_ne_top_of_nontrivial hs) (EMetric.infsep_anti hst)
#align set.nontrivial.infsep_anti Metric.infsep_anti_of_nontrivial

theorem infsep_eq_iInf : infsep s = ⨅ d : s.offDiag, (uncurry dist) (d : α × α) := by
  rw [infsep, EMetric.infsep_eq_iInf,
      ENNReal.toReal_iInf (Subtype.forall.mpr (fun ⟨x, y⟩ _ => edist_ne_top _ _)), iInf_congr]
  simp_rw [Subtype.forall, mem_offDiag, Prod.forall, uncurry_apply_pair, edist_dist,
      toReal_ofReal_eq_iff, dist_nonneg, implies_true]
#align set.nontrivial.infsep_eq_infi Metric.infsep_eq_iInf

theorem coe_finset_infsep_eq_of_nontrivial [DecidableEq α] {s : Finset α} (hs : s.Nontrivial) :
    infsep (s : Set α) = s.offDiag.inf'
    (match hs with | ⟨x, hx, y, hy, hxy⟩ => ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩⟩)
    (uncurry dist) := by
  refine' eq_of_forall_le_iff fun _ => _
  simp_rw [le_infsep_iff_of_nontrivial hs, Finset.le_inf'_iff, Finset.mem_offDiag, Prod.forall]
  exact ⟨fun H _ _ ⟨hx, hy, hxy⟩ => H _ hx _ hy hxy , fun H _ hx _ hy hxy => H _ _ ⟨hx, hy, hxy⟩⟩
#align finset.coe_infsep Metric.coe_finset_infsep_eq_of_nontrivial

theorem infsep_eq_of_finite_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial)  :
    infsep s = hsf.offDiag.toFinset.inf'
      ((hsf.offDiag.toFinset_nonempty.trans (offDiag_nonempty)).mpr hs) (uncurry dist) := by
  rcases hsf.exists_finset_coe with ⟨s, rfl⟩
  classical
    simp_rw [coe_finset_infsep_eq_of_nontrivial hs]
    congr
    simp_rw [Finset.ext_iff, Finset.mem_offDiag, ne_eq, toFinite_toFinset, mem_toFinset,
      mem_offDiag, Finset.mem_coe, implies_true]
#align set.finite.infsep_of_nontrivial Metric.infsep_eq_of_finite_of_nontrivial

theorem coe_finset_infsep_eq_zero_of_offDiag_empty [DecidableEq α] {s : Finset α}
    (hs : s.offDiag = ∅) : infsep (s : Set α) = 0 := by
  refine' infsep_eq_zero_of_subsingleton (fun x hx y hy => not_ne_iff.mp
    (fun hxy => Finset.not_mem_empty (x, y) (hs ▸ Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩)))
#align finset.coe_infsep_of_off_diag_empty Metric.coe_finset_infsep_eq_zero_of_offDiag_empty

theorem exists_coe_finset_infsep_eq_of_nontrivial [DecidableEq α] {s : Finset α}
    (hs : s.Nontrivial) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ infsep (s : Set α) = dist x y := by
  rw [coe_finset_infsep_eq_of_nontrivial hs]
  rcases Finset.exists_mem_eq_inf' (s := s.offDiag)
    (match hs with | ⟨x, hx, y, hy, hxy⟩ => ⟨⟨x, y⟩, Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩⟩)
    (uncurry dist) with ⟨⟨x, y⟩, hxy, hed⟩
  rw [Finset.mem_offDiag] at hxy
  rcases hxy with ⟨hx, hy, hxy⟩
  exact ⟨x, hx, y, hy, hxy, hed⟩

theorem infsep_exists_of_finite_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ infsep s = dist x y := by
  rcases hsf.exists_finset_coe with ⟨s, rfl⟩
  classical exact exists_coe_finset_infsep_eq_of_nontrivial hs
#align set.finite.infsep_exists_of_nontrivial Metric.infsep_exists_of_finite_of_nontrivial

end PseudoMetricSpace

section MetricSpace

variable [MetricSpace α] {s : Set α}

theorem infsep_zero_iff_subsingleton_of_finite (hs : s.Finite) : infsep s = 0 ↔ s.Subsingleton := by
  rw [infsep_zero, EMetric.infsep_eq_top_iff_subsingleton, or_iff_right_iff_imp]
  exact fun H => ((EMetric.infsep_pos_of_finite hs).ne' H).elim
#align set.finite.infsep_zero_iff_subsingleton Metric.infsep_zero_iff_subsingleton_of_finite

theorem infsep_pos_iff_nontrivial_of_finite (hs : s.Finite) : 0 < infsep s ↔ s.Nontrivial := by
  simp_rw [infsep_pos, EMetric.infsep_pos_of_finite hs,
  EMetric.infsep_lt_top_iff_nontrivial, true_and]
#align set.finite.infsep_pos_iff_nontrivial Metric.infsep_pos_iff_nontrivial_of_finite

theorem _root_.Finset.infsep_zero_iff_subsingleton (s : Finset α) :
    infsep (s : Set α) = 0 ↔ (s : Set α).Subsingleton :=
  infsep_zero_iff_subsingleton_of_finite s.finite_toSet
#align finset.infsep_zero_iff_subsingleton Finset.infsep_zero_iff_subsingleton

theorem _root_.Finset.infsep_pos_iff_nontrivial (s : Finset α) :
    0 < infsep (s : Set α) ↔ (s : Set α).Nontrivial :=
  infsep_pos_iff_nontrivial_of_finite s.finite_toSet
#align finset.infsep_pos_iff_nontrivial Finset.infsep_pos_iff_nontrivial

end MetricSpace

end Metric
