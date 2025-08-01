/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
import Mathlib.Topology.MetricSpace.Basic

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
* `Set.einfsep`: Extended infimum separation of a set.
* `Set.infsep`: Infimum separation of a set (when in a pseudometric space).

-/


variable {α β : Type*}

namespace Set

section Einfsep

open ENNReal

open Function

/-- The "extended infimum separation" of a set with an edist function. -/
noncomputable def einfsep [EDist α] (s : Set α) : ℝ≥0∞ :=
  ⨅ (x ∈ s) (y ∈ s) (_ : x ≠ y), edist x y

section EDist

variable [EDist α] {x y : α} {s t : Set α}

theorem le_einfsep_iff {d} :
    d ≤ s.einfsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ edist x y := by
  simp_rw [einfsep, le_iInf_iff]

theorem einfsep_zero : s.einfsep = 0 ↔ ∀ C > 0, ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y < C := by
  simp_rw [einfsep, ← _root_.bot_eq_zero, iInf_eq_bot, iInf_lt_iff, exists_prop]

theorem einfsep_pos : 0 < s.einfsep ↔ ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ edist x y := by
  rw [pos_iff_ne_zero, Ne, einfsep_zero]
  simp only [not_forall, not_exists, not_lt, exists_prop, not_and]

theorem einfsep_top :
    s.einfsep = ∞ ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → edist x y = ∞ := by
  simp_rw [einfsep, iInf_eq_top]

theorem einfsep_lt_top :
    s.einfsep < ∞ ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y < ∞ := by
  simp_rw [einfsep, iInf_lt_iff, exists_prop]

theorem einfsep_ne_top :
    s.einfsep ≠ ∞ ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y ≠ ∞ := by
  simp_rw [← lt_top_iff_ne_top, einfsep_lt_top]

theorem einfsep_lt_iff {d} :
    s.einfsep < d ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ edist x y < d := by
  simp_rw [einfsep, iInf_lt_iff, exists_prop]

theorem nontrivial_of_einfsep_lt_top (hs : s.einfsep < ∞) : s.Nontrivial := by
  rcases einfsep_lt_top.1 hs with ⟨_, hx, _, hy, hxy, _⟩
  exact ⟨_, hx, _, hy, hxy⟩

theorem nontrivial_of_einfsep_ne_top (hs : s.einfsep ≠ ∞) : s.Nontrivial :=
  nontrivial_of_einfsep_lt_top (lt_top_iff_ne_top.mpr hs)

theorem Subsingleton.einfsep (hs : s.Subsingleton) : s.einfsep = ∞ := by
  rw [einfsep_top]
  exact fun _ hx _ hy hxy => (hxy <| hs hx hy).elim

theorem le_einfsep_image_iff {d} {f : β → α} {s : Set β} : d ≤ einfsep (f '' s)
    ↔ ∀ x ∈ s, ∀ y ∈ s, f x ≠ f y → d ≤ edist (f x) (f y) := by
  simp_rw [le_einfsep_iff, forall_mem_image]

theorem le_edist_of_le_einfsep {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hd : d ≤ s.einfsep) : d ≤ edist x y :=
  le_einfsep_iff.1 hd x hx y hy hxy

theorem einfsep_le_edist_of_mem {x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y) :
    s.einfsep ≤ edist x y :=
  le_edist_of_le_einfsep hx hy hxy le_rfl

theorem einfsep_le_of_mem_of_edist_le {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hxy' : edist x y ≤ d) : s.einfsep ≤ d :=
  le_trans (einfsep_le_edist_of_mem hx hy hxy) hxy'

theorem le_einfsep {d} (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ edist x y) : d ≤ s.einfsep :=
  le_einfsep_iff.2 h

@[simp]
theorem einfsep_empty : (∅ : Set α).einfsep = ∞ :=
  subsingleton_empty.einfsep

@[simp]
theorem einfsep_singleton : ({x} : Set α).einfsep = ∞ :=
  subsingleton_singleton.einfsep

theorem einfsep_iUnion_mem_option {ι : Type*} (o : Option ι) (s : ι → Set α) :
    (⋃ i ∈ o, s i).einfsep = ⨅ i ∈ o, (s i).einfsep := by cases o <;> simp

theorem einfsep_anti (hst : s ⊆ t) : t.einfsep ≤ s.einfsep :=
  le_einfsep fun _x hx _y hy => einfsep_le_edist_of_mem (hst hx) (hst hy)

theorem einfsep_insert_le : (insert x s).einfsep ≤ ⨅ (y ∈ s) (_ : x ≠ y), edist x y := by
  simp_rw [le_iInf_iff]
  exact fun _ hy hxy => einfsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ hy) hxy

theorem le_einfsep_pair : edist x y ⊓ edist y x ≤ ({x, y} : Set α).einfsep := by
  simp_rw [le_einfsep_iff, inf_le_iff, mem_insert_iff, mem_singleton_iff]
  rintro a (rfl | rfl) b (rfl | rfl) hab <;> (try simp only [le_refl, true_or, or_true]) <;>
    contradiction

theorem einfsep_pair_le_left (hxy : x ≠ y) : ({x, y} : Set α).einfsep ≤ edist x y :=
  einfsep_le_edist_of_mem (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hxy

theorem einfsep_pair_le_right (hxy : x ≠ y) : ({x, y} : Set α).einfsep ≤ edist y x := by
  rw [pair_comm]; exact einfsep_pair_le_left hxy.symm

theorem einfsep_pair_eq_inf (hxy : x ≠ y) : ({x, y} : Set α).einfsep = edist x y ⊓ edist y x :=
  le_antisymm (le_inf (einfsep_pair_le_left hxy) (einfsep_pair_le_right hxy)) le_einfsep_pair

theorem einfsep_eq_iInf : s.einfsep = ⨅ d : s.offDiag, (uncurry edist) (d : α × α) := by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, le_iInf_iff, imp_forall_iff, SetCoe.forall, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

theorem einfsep_of_fintype [DecidableEq α] [Fintype s] :
    s.einfsep = s.offDiag.toFinset.inf (uncurry edist) := by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, imp_forall_iff, Finset.le_inf_iff, mem_toFinset, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

theorem Finite.einfsep (hs : s.Finite) : s.einfsep = hs.offDiag.toFinset.inf (uncurry edist) := by
  refine eq_of_forall_le_iff fun _ => ?_
  simp_rw [le_einfsep_iff, imp_forall_iff, Finset.le_inf_iff, Finite.mem_toFinset, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

theorem Finset.coe_einfsep [DecidableEq α] {s : Finset α} :
    (s : Set α).einfsep = s.offDiag.inf (uncurry edist) := by
  simp_rw [einfsep_of_fintype, ← Finset.coe_offDiag, Finset.toFinset_coe]

theorem Nontrivial.einfsep_exists_of_finite [Finite s] (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.einfsep = edist x y := by
  classical
    cases nonempty_fintype s
    simp_rw [einfsep_of_fintype]
    rcases Finset.exists_mem_eq_inf s.offDiag.toFinset (by simpa) (uncurry edist) with ⟨w, hxy, hed⟩
    simp_rw [mem_toFinset] at hxy
    exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩

theorem Finite.einfsep_exists_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.einfsep = edist x y :=
  letI := hsf.fintype
  hs.einfsep_exists_of_finite

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] {x y z : α} {s : Set α}

theorem einfsep_pair (hxy : x ≠ y) : ({x, y} : Set α).einfsep = edist x y := by
  nth_rw 1 [← min_self (edist x y)]
  convert einfsep_pair_eq_inf hxy using 2
  rw [edist_comm]

theorem einfsep_insert : einfsep (insert x s) =
    (⨅ (y ∈ s) (_ : x ≠ y), edist x y) ⊓ s.einfsep := by
  refine le_antisymm (le_min einfsep_insert_le (einfsep_anti (subset_insert _ _))) ?_
  simp_rw [le_einfsep_iff, inf_le_iff, mem_insert_iff]
  rintro y (rfl | hy) z (rfl | hz) hyz
  · exact False.elim (hyz rfl)
  · exact Or.inl (iInf_le_of_le _ (iInf₂_le hz hyz))
  · rw [edist_comm]
    exact Or.inl (iInf_le_of_le _ (iInf₂_le hy hyz.symm))
  · exact Or.inr (einfsep_le_edist_of_mem hy hz hyz)

theorem einfsep_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    einfsep ({x, y, z} : Set α) = edist x y ⊓ edist x z ⊓ edist y z := by
  simp_rw [einfsep_insert, iInf_insert, iInf_singleton, einfsep_singleton, inf_top_eq,
    ciInf_pos hxy, ciInf_pos hyz, ciInf_pos hxz]

theorem le_einfsep_pi_of_le {X : β → Type*} [Fintype β] [∀ b, PseudoEMetricSpace (X b)]
    {s : ∀ b : β, Set (X b)} {c : ℝ≥0∞} (h : ∀ b, c ≤ einfsep (s b)) :
    c ≤ einfsep (Set.pi univ s) := by
  refine le_einfsep fun x hx y hy hxy => ?_
  rw [mem_univ_pi] at hx hy
  rcases Function.ne_iff.mp hxy with ⟨i, hi⟩
  exact le_trans (le_einfsep_iff.1 (h i) _ (hx _) _ (hy _) hi) (edist_le_pi_edist _ _ i)

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] {s : Set α}

theorem subsingleton_of_einfsep_eq_top (hs : s.einfsep = ∞) : s.Subsingleton := by
  rw [einfsep_top] at hs
  exact fun _ hx _ hy => of_not_not fun hxy => edist_ne_top _ _ (hs _ hx _ hy hxy)

theorem einfsep_eq_top_iff : s.einfsep = ∞ ↔ s.Subsingleton :=
  ⟨subsingleton_of_einfsep_eq_top, Subsingleton.einfsep⟩

theorem Nontrivial.einfsep_ne_top (hs : s.Nontrivial) : s.einfsep ≠ ∞ := by
  contrapose! hs
  rw [not_nontrivial_iff]
  exact subsingleton_of_einfsep_eq_top hs

theorem Nontrivial.einfsep_lt_top (hs : s.Nontrivial) : s.einfsep < ∞ := by
  rw [lt_top_iff_ne_top]
  exact hs.einfsep_ne_top

theorem einfsep_lt_top_iff : s.einfsep < ∞ ↔ s.Nontrivial :=
  ⟨nontrivial_of_einfsep_lt_top, Nontrivial.einfsep_lt_top⟩

theorem einfsep_ne_top_iff : s.einfsep ≠ ∞ ↔ s.Nontrivial :=
  ⟨nontrivial_of_einfsep_ne_top, Nontrivial.einfsep_ne_top⟩

theorem le_einfsep_of_forall_dist_le {d} (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y) :
    ENNReal.ofReal d ≤ s.einfsep :=
  le_einfsep fun x hx y hy hxy => (edist_dist x y).symm ▸ ENNReal.ofReal_le_ofReal (h x hx y hy hxy)

end PseudoMetricSpace

section EMetricSpace

variable [EMetricSpace α] {s : Set α}

theorem einfsep_pos_of_finite [Finite s] : 0 < s.einfsep := by
  cases nonempty_fintype s
  by_cases hs : s.Nontrivial
  · rcases hs.einfsep_exists_of_finite with ⟨x, _hx, y, _hy, hxy, hxy'⟩
    exact hxy'.symm ▸ edist_pos.2 hxy
  · rw [not_nontrivial_iff] at hs
    exact hs.einfsep.symm ▸ WithTop.top_pos

theorem relatively_discrete_of_finite [Finite s] :
    ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ edist x y := by
  rw [← einfsep_pos]
  exact einfsep_pos_of_finite

theorem Finite.einfsep_pos (hs : s.Finite) : 0 < s.einfsep :=
  letI := hs.fintype
  einfsep_pos_of_finite

theorem Finite.relatively_discrete (hs : s.Finite) :
    ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ edist x y :=
  letI := hs.fintype
  relatively_discrete_of_finite

end EMetricSpace

end Einfsep

section Infsep

open ENNReal

open Set Function

/-- The "infimum separation" of a set with an edist function. -/
noncomputable def infsep [EDist α] (s : Set α) : ℝ :=
  ENNReal.toReal s.einfsep

section EDist

variable [EDist α] {x y : α} {s : Set α}

theorem infsep_zero : s.infsep = 0 ↔ s.einfsep = 0 ∨ s.einfsep = ∞ := by
  rw [infsep, ENNReal.toReal_eq_zero_iff]

theorem infsep_nonneg : 0 ≤ s.infsep :=
  ENNReal.toReal_nonneg

theorem infsep_pos : 0 < s.infsep ↔ 0 < s.einfsep ∧ s.einfsep < ∞ := by
  simp_rw [infsep, ENNReal.toReal_pos_iff]

theorem Subsingleton.infsep_zero (hs : s.Subsingleton) : s.infsep = 0 :=
  Set.infsep_zero.mpr <| Or.inr hs.einfsep

theorem nontrivial_of_infsep_pos (hs : 0 < s.infsep) : s.Nontrivial := by
  contrapose hs
  rw [not_nontrivial_iff] at hs
  exact hs.infsep_zero ▸ lt_irrefl _

theorem infsep_empty : (∅ : Set α).infsep = 0 :=
  subsingleton_empty.infsep_zero

theorem infsep_singleton : ({x} : Set α).infsep = 0 :=
  subsingleton_singleton.infsep_zero

theorem infsep_pair_le_toReal_inf (hxy : x ≠ y) :
    ({x, y} : Set α).infsep ≤ (edist x y ⊓ edist y x).toReal := by
  simp_rw [infsep, einfsep_pair_eq_inf hxy]
  simp

end EDist

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] {x y : α}

theorem infsep_pair_eq_toReal : ({x, y} : Set α).infsep = (edist x y).toReal := by
  by_cases hxy : x = y
  · rw [hxy]
    simp only [infsep_singleton, pair_eq_singleton, edist_self, ENNReal.toReal_zero]
  · rw [infsep, einfsep_pair hxy]

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] {x y z : α} {s t : Set α}

theorem Nontrivial.le_infsep_iff {d} (hs : s.Nontrivial) :
    d ≤ s.infsep ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y := by
  simp_rw [infsep, ← ENNReal.ofReal_le_iff_le_toReal hs.einfsep_ne_top, le_einfsep_iff, edist_dist,
    ENNReal.ofReal_le_ofReal_iff dist_nonneg]

theorem Nontrivial.infsep_lt_iff {d} (hs : s.Nontrivial) :
    s.infsep < d ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ dist x y < d := by
  rw [← not_iff_not]
  push_neg
  exact hs.le_infsep_iff

theorem Nontrivial.le_infsep {d} (hs : s.Nontrivial)
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ dist x y) : d ≤ s.infsep :=
  hs.le_infsep_iff.2 h

theorem le_edist_of_le_infsep {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hd : d ≤ s.infsep) : d ≤ dist x y := by
  by_cases hs : s.Nontrivial
  · exact hs.le_infsep_iff.1 hd x hx y hy hxy
  · rw [not_nontrivial_iff] at hs
    rw [hs.infsep_zero] at hd
    exact le_trans hd dist_nonneg

theorem infsep_le_dist_of_mem (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : s.infsep ≤ dist x y :=
  le_edist_of_le_infsep hx hy hxy le_rfl

theorem infsep_le_of_mem_of_edist_le {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hxy' : dist x y ≤ d) : s.infsep ≤ d :=
  le_trans (infsep_le_dist_of_mem hx hy hxy) hxy'

theorem infsep_pair : ({x, y} : Set α).infsep = dist x y := by
  rw [infsep_pair_eq_toReal, edist_dist]
  exact ENNReal.toReal_ofReal dist_nonneg

theorem infsep_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ({x, y, z} : Set α).infsep = dist x y ⊓ dist x z ⊓ dist y z := by
  simp only [infsep, einfsep_triple hxy hyz hxz, ENNReal.toReal_inf, edist_ne_top x y,
    edist_ne_top x z, edist_ne_top y z, dist_edist, Ne, inf_eq_top_iff, and_self_iff,
    not_false_iff]

theorem Nontrivial.infsep_anti (hs : s.Nontrivial) (hst : s ⊆ t) : t.infsep ≤ s.infsep :=
  ENNReal.toReal_mono hs.einfsep_ne_top (einfsep_anti hst)

theorem infsep_eq_iInf [Decidable s.Nontrivial] :
    s.infsep = if s.Nontrivial then ⨅ d : s.offDiag, (uncurry dist) (d : α × α) else 0 := by
  split_ifs with hs
  · have hb : BddBelow (uncurry dist '' s.offDiag) := by
      refine ⟨0, fun d h => ?_⟩
      simp_rw [mem_image, Prod.exists, uncurry_apply_pair] at h
      rcases h with ⟨_, _, _, rfl⟩
      exact dist_nonneg
    refine eq_of_forall_le_iff fun _ => ?_
    simp_rw [hs.le_infsep_iff, le_ciInf_set_iff (offDiag_nonempty.mpr hs) hb, imp_forall_iff,
      mem_offDiag, Prod.forall, uncurry_apply_pair, and_imp]
  · exact (not_nontrivial_iff.mp hs).infsep_zero

theorem Nontrivial.infsep_eq_iInf (hs : s.Nontrivial) :
    s.infsep = ⨅ d : s.offDiag, (uncurry dist) (d : α × α) := by
  classical rw [Set.infsep_eq_iInf, if_pos hs]

theorem infsep_of_fintype [Decidable s.Nontrivial] [DecidableEq α] [Fintype s] : s.infsep =
    if hs : s.Nontrivial then s.offDiag.toFinset.inf' (by simpa) (uncurry dist) else 0 := by
  split_ifs with hs
  · refine eq_of_forall_le_iff fun _ => ?_
    simp_rw [hs.le_infsep_iff, imp_forall_iff, Finset.le_inf'_iff, mem_toFinset, mem_offDiag,
      Prod.forall, uncurry_apply_pair, and_imp]
  · rw [not_nontrivial_iff] at hs
    exact hs.infsep_zero

theorem Nontrivial.infsep_of_fintype [DecidableEq α] [Fintype s] (hs : s.Nontrivial) :
    s.infsep = s.offDiag.toFinset.inf' (by simpa) (uncurry dist) := by
  classical rw [Set.infsep_of_fintype, dif_pos hs]

theorem Finite.infsep [Decidable s.Nontrivial] (hsf : s.Finite) :
    s.infsep =
      if hs : s.Nontrivial then hsf.offDiag.toFinset.inf' (by simpa) (uncurry dist) else 0 := by
  split_ifs with hs
  · refine eq_of_forall_le_iff fun _ => ?_
    simp_rw [hs.le_infsep_iff, imp_forall_iff, Finset.le_inf'_iff, Finite.mem_toFinset,
      mem_offDiag, Prod.forall, uncurry_apply_pair, and_imp]
  · rw [not_nontrivial_iff] at hs
    exact hs.infsep_zero

theorem Finite.infsep_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    s.infsep = hsf.offDiag.toFinset.inf' (by simpa) (uncurry dist) := by
  classical simp_rw [hsf.infsep, dif_pos hs]

theorem _root_.Finset.coe_infsep [DecidableEq α] (s : Finset α) : (s : Set α).infsep =
    if hs : s.offDiag.Nonempty then s.offDiag.inf' hs (uncurry dist) else 0 := by
  have H : (s : Set α).Nontrivial ↔ s.offDiag.Nonempty := by
    rw [← Set.offDiag_nonempty, ← Finset.coe_offDiag, Finset.coe_nonempty]
  split_ifs with hs
  · simp_rw [(H.mpr hs).infsep_of_fintype, ← Finset.coe_offDiag, Finset.toFinset_coe]
  · exact (not_nontrivial_iff.mp (H.mp.mt hs)).infsep_zero

theorem _root_.Finset.coe_infsep_of_offDiag_nonempty [DecidableEq α] {s : Finset α}
    (hs : s.offDiag.Nonempty) : (s : Set α).infsep = s.offDiag.inf' hs (uncurry dist) := by
  rw [Finset.coe_infsep, dif_pos hs]

theorem _root_.Finset.coe_infsep_of_offDiag_empty
    [DecidableEq α] {s : Finset α} (hs : s.offDiag = ∅) : (s : Set α).infsep = 0 := by
  rw [← Finset.not_nonempty_iff_eq_empty] at hs
  rw [Finset.coe_infsep, dif_neg hs]

theorem Nontrivial.infsep_exists_of_finite [Finite s] (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.infsep = dist x y := by
  classical
    cases nonempty_fintype s
    simp_rw [hs.infsep_of_fintype]
    rcases Finset.exists_mem_eq_inf' (s := s.offDiag.toFinset) (by simpa) (uncurry dist) with
      ⟨w, hxy, hed⟩
    simp_rw [mem_toFinset] at hxy
    exact ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩

theorem Finite.infsep_exists_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.infsep = dist x y :=
  letI := hsf.fintype
  hs.infsep_exists_of_finite

end PseudoMetricSpace

section MetricSpace

variable [MetricSpace α] {s : Set α}

theorem infsep_zero_iff_subsingleton_of_finite [Finite s] : s.infsep = 0 ↔ s.Subsingleton := by
  rw [infsep_zero, einfsep_eq_top_iff, or_iff_right_iff_imp]
  exact fun H => (einfsep_pos_of_finite.ne' H).elim

theorem infsep_pos_iff_nontrivial_of_finite [Finite s] : 0 < s.infsep ↔ s.Nontrivial := by
  rw [infsep_pos, einfsep_lt_top_iff, and_iff_right_iff_imp]
  exact fun _ => einfsep_pos_of_finite

theorem Finite.infsep_zero_iff_subsingleton (hs : s.Finite) : s.infsep = 0 ↔ s.Subsingleton :=
  letI := hs.fintype
  infsep_zero_iff_subsingleton_of_finite

theorem Finite.infsep_pos_iff_nontrivial (hs : s.Finite) : 0 < s.infsep ↔ s.Nontrivial :=
  letI := hs.fintype
  infsep_pos_iff_nontrivial_of_finite

theorem _root_.Finset.infsep_zero_iff_subsingleton (s : Finset α) :
    (s : Set α).infsep = 0 ↔ (s : Set α).Subsingleton :=
  infsep_zero_iff_subsingleton_of_finite

theorem _root_.Finset.infsep_pos_iff_nontrivial (s : Finset α) :
    0 < (s : Set α).infsep ↔ (s : Set α).Nontrivial :=
  infsep_pos_iff_nontrivial_of_finite

end MetricSpace

end Infsep

end Set
