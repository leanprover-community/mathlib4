/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Continuous
public import Mathlib.Topology.NhdsSet

/-!
# Separated neighbourhoods

This file defines the predicates `SeparatedNhds` and `HasSeparatingCover`, which are used in
formulating separation axioms for topological spaces.

## Main definitions

* `SeparatedNhds`: Two `Set`s are separated by neighbourhoods if they are contained in disjoint
  open sets.
* `HasSeparatingCover`: A set has a countable cover that can be used with
  `hasSeparatingCovers_iff_separatedNhds` to witness when two `Set`s have `SeparatedNhds`.

## References

* <https://en.wikipedia.org/wiki/Separation_axiom>
* [Willard's *General Topology*][zbMATH02107988]
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

/--
`SeparatedNhds` is a predicate on pairs of sub`Set`s of a topological space.  It holds if the two
sub`Set`s are contained in disjoint open sets.
-/
def SeparatedNhds : Set X → Set X → Prop := fun s t : Set X =>
  ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ s ⊆ U ∧ t ⊆ V ∧ Disjoint U V

theorem separatedNhds_iff_disjoint {s t : Set X} : SeparatedNhds s t ↔ Disjoint (𝓝ˢ s) (𝓝ˢ t) := by
  simp only [(hasBasis_nhdsSet s).disjoint_iff (hasBasis_nhdsSet t), SeparatedNhds, ←
    exists_and_left, and_assoc, and_comm, and_left_comm]

alias ⟨SeparatedNhds.disjoint_nhdsSet, _⟩ := separatedNhds_iff_disjoint

/-- `HasSeparatingCover`s can be useful witnesses for `SeparatedNhds`. -/
def HasSeparatingCover : Set X → Set X → Prop := fun s t ↦
  ∃ u : ℕ → Set X, s ⊆ ⋃ n, u n ∧ ∀ n, IsOpen (u n) ∧ Disjoint (closure (u n)) t

/-- Used to prove that a regular topological space with Lindelöf topology is a normal space,
and a perfectly normal space is a completely normal space. -/
theorem hasSeparatingCovers_iff_separatedNhds {s t : Set X} :
    HasSeparatingCover s t ∧ HasSeparatingCover t s ↔ SeparatedNhds s t := by
  constructor
  · rintro ⟨⟨u, u_cov, u_props⟩, ⟨v, v_cov, v_props⟩⟩
    have open_lemma : ∀ (u₀ a : ℕ → Set X), (∀ n, IsOpen (u₀ n)) →
      IsOpen (⋃ n, u₀ n \ closure (a n)) := fun _ _ u₀i_open ↦
        isOpen_iUnion fun i ↦ (u₀i_open i).sdiff isClosed_closure
    have cover_lemma : ∀ (h₀ : Set X) (u₀ v₀ : ℕ → Set X),
        (h₀ ⊆ ⋃ n, u₀ n) → (∀ n, Disjoint (closure (v₀ n)) h₀) →
        (h₀ ⊆ ⋃ n, u₀ n \ closure (⋃ m ≤ n, v₀ m)) :=
        fun h₀ u₀ v₀ h₀_cov dis x xinh ↦ by
      rcases h₀_cov xinh with ⟨un, ⟨n, rfl⟩, xinun⟩
      simp only [mem_iUnion]
      refine ⟨n, xinun, ?_⟩
      simp_all only [closure_iUnion₂_le_nat, disjoint_right, mem_iUnion,
        exists_false, not_false_eq_true]
    refine
      ⟨⋃ n : ℕ, u n \ (closure (⋃ m ≤ n, v m)),
       ⋃ n : ℕ, v n \ (closure (⋃ m ≤ n, u m)),
       open_lemma u (fun n ↦ ⋃ m ≤ n, v m) (fun n ↦ (u_props n).1),
       open_lemma v (fun n ↦ ⋃ m ≤ n, u m) (fun n ↦ (v_props n).1),
       cover_lemma s u v u_cov (fun n ↦ (v_props n).2),
       cover_lemma t v u v_cov (fun n ↦ (u_props n).2),
       ?_⟩
    rw [Set.disjoint_left]
    rintro x ⟨un, ⟨n, rfl⟩, xinun⟩
    suffices ∀ (m : ℕ), x ∈ v m → x ∈ closure (⋃ m' ∈ {m' | m' ≤ m}, u m') by simpa
    intro m xinvm
    have n_le_m : n ≤ m := by
      by_contra m_gt_n
      exact xinun.2 (subset_closure (mem_biUnion (le_of_lt (not_le.mp m_gt_n)) xinvm))
    exact subset_closure (mem_biUnion n_le_m xinun.1)
  · rintro ⟨U, V, U_open, V_open, h_sub_U, k_sub_V, UV_dis⟩
    exact
      ⟨⟨fun _ ↦ U,
        h_sub_U.trans (iUnion_const U).symm.subset,
        fun _ ↦
          ⟨U_open, disjoint_of_subset (fun ⦃a⦄ a ↦ a) k_sub_V (UV_dis.closure_left V_open)⟩⟩,
       ⟨fun _ ↦ V,
        k_sub_V.trans (iUnion_const V).symm.subset,
        fun _ ↦
          ⟨V_open, disjoint_of_subset (fun ⦃a⦄ a ↦ a) h_sub_U (UV_dis.closure_right U_open).symm⟩⟩⟩

theorem Set.hasSeparatingCover_empty_left (s : Set X) : HasSeparatingCover ∅ s :=
  ⟨fun _ ↦ ∅, empty_subset (⋃ _, ∅),
   fun _ ↦ ⟨isOpen_empty, by simp only [closure_empty, empty_disjoint]⟩⟩

theorem Set.hasSeparatingCover_empty_right (s : Set X) : HasSeparatingCover s ∅ :=
  ⟨fun _ ↦ univ, (subset_univ s).trans univ.iUnion_const.symm.subset,
   fun _ ↦ ⟨isOpen_univ, by apply disjoint_empty⟩⟩

theorem HasSeparatingCover.mono {s₁ s₂ t₁ t₂ : Set X} (sc_st : HasSeparatingCover s₂ t₂)
    (s_sub : s₁ ⊆ s₂) (t_sub : t₁ ⊆ t₂) : HasSeparatingCover s₁ t₁ := by
  obtain ⟨u, u_cov, u_props⟩ := sc_st
  exact
    ⟨u,
     s_sub.trans u_cov,
     fun n ↦
       ⟨(u_props n).1,
        disjoint_of_subset (fun ⦃_⦄ a ↦ a) t_sub (u_props n).2⟩⟩

namespace SeparatedNhds

variable {s s₁ s₂ t t₁ t₂ u : Set X}

@[symm]
theorem symm : SeparatedNhds s t → SeparatedNhds t s := fun ⟨U, V, oU, oV, aU, bV, UV⟩ =>
  ⟨V, U, oV, oU, bV, aU, Disjoint.symm UV⟩

theorem comm (s t : Set X) : SeparatedNhds s t ↔ SeparatedNhds t s :=
  ⟨symm, symm⟩

theorem preimage [TopologicalSpace Y] {f : X → Y} {s t : Set Y} (h : SeparatedNhds s t)
    (hf : Continuous f) : SeparatedNhds (f ⁻¹' s) (f ⁻¹' t) :=
  let ⟨U, V, oU, oV, sU, tV, UV⟩ := h
  ⟨f ⁻¹' U, f ⁻¹' V, oU.preimage hf, oV.preimage hf, preimage_mono sU, preimage_mono tV,
    UV.preimage f⟩

protected theorem disjoint (h : SeparatedNhds s t) : Disjoint s t :=
  let ⟨_, _, _, _, hsU, htV, hd⟩ := h; hd.mono hsU htV

theorem disjoint_closure_left (h : SeparatedNhds s t) : Disjoint (closure s) t :=
  let ⟨_U, _V, _, hV, hsU, htV, hd⟩ := h
  (hd.closure_left hV).mono (closure_mono hsU) htV

theorem disjoint_closure_right (h : SeparatedNhds s t) : Disjoint s (closure t) :=
  h.symm.disjoint_closure_left.symm

@[simp] theorem empty_right (s : Set X) : SeparatedNhds s ∅ :=
  ⟨_, _, isOpen_univ, isOpen_empty, fun a _ => mem_univ a, Subset.rfl, disjoint_empty _⟩

@[simp] theorem empty_left (s : Set X) : SeparatedNhds ∅ s :=
  (empty_right _).symm

theorem mono (h : SeparatedNhds s₂ t₂) (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : SeparatedNhds s₁ t₁ :=
  let ⟨U, V, hU, hV, hsU, htV, hd⟩ := h
  ⟨U, V, hU, hV, hs.trans hsU, ht.trans htV, hd⟩

theorem union_left : SeparatedNhds s u → SeparatedNhds t u → SeparatedNhds (s ∪ t) u := by
  simpa only [separatedNhds_iff_disjoint, nhdsSet_union, disjoint_sup_left] using And.intro

theorem union_right (ht : SeparatedNhds s t) (hu : SeparatedNhds s u) : SeparatedNhds s (t ∪ u) :=
  (ht.symm.union_left hu.symm).symm

lemma isOpen_left_of_isOpen_union (hst : SeparatedNhds s t) (hst' : IsOpen (s ∪ t)) : IsOpen s := by
  obtain ⟨u, v, hu, hv, hsu, htv, huv⟩ := hst
  suffices s = (s ∪ t) ∩ u from this ▸ hst'.inter hu
  rw [union_inter_distrib_right, (huv.symm.mono_left htv).inter_eq, union_empty,
    inter_eq_left.2 hsu]

lemma isOpen_right_of_isOpen_union (hst : SeparatedNhds s t) (hst' : IsOpen (s ∪ t)) : IsOpen t :=
  hst.symm.isOpen_left_of_isOpen_union (union_comm _ _ ▸ hst')

lemma isOpen_union_iff (hst : SeparatedNhds s t) : IsOpen (s ∪ t) ↔ IsOpen s ∧ IsOpen t :=
  ⟨fun h ↦ ⟨hst.isOpen_left_of_isOpen_union h, hst.isOpen_right_of_isOpen_union h⟩,
    fun ⟨h1, h2⟩ ↦ h1.union h2⟩

lemma isClosed_left_of_isClosed_union (hst : SeparatedNhds s t) (hst' : IsClosed (s ∪ t)) :
    IsClosed s := by
  obtain ⟨u, v, hu, hv, hsu, htv, huv⟩ := hst
  rw [← isOpen_compl_iff] at hst' ⊢
  suffices sᶜ = (s ∪ t)ᶜ ∪ v from this ▸ hst'.union hv
  rw [← compl_inj_iff, Set.compl_union, compl_compl, compl_compl, union_inter_distrib_right,
    (disjoint_compl_right.mono_left htv).inter_eq, union_empty, left_eq_inter, subset_compl_comm]
  exact (huv.mono_left hsu).subset_compl_left

lemma isClosed_right_of_isClosed_union (hst : SeparatedNhds s t) (hst' : IsClosed (s ∪ t)) :
    IsClosed t :=
  hst.symm.isClosed_left_of_isClosed_union (union_comm _ _ ▸ hst')

lemma isClosed_union_iff (hst : SeparatedNhds s t) : IsClosed (s ∪ t) ↔ IsClosed s ∧ IsClosed t :=
  ⟨fun h ↦ ⟨hst.isClosed_left_of_isClosed_union h, hst.isClosed_right_of_isClosed_union h⟩,
    fun ⟨h1, h2⟩ ↦ h1.union h2⟩

end SeparatedNhds

end Separation
