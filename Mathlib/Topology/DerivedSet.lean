/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.Topology.Separation

open Filter Topology

variable {X : Type*} [TopologicalSpace X]

def derivedSet (A : Set X) : Set X := {x | AccPt x (𝓟 A)}

lemma derivedSet_union (A B : Set X) : derivedSet (A ∪ B) = derivedSet A ∪ derivedSet B := by
  ext x
  simp only [derivedSet, ← sup_principal, accPt_sup]

lemma derivedSet_mono (A B : Set X) (h : A ⊆ B) : derivedSet A ⊆ derivedSet B := by
  intro x hx
  apply hx.mono
  simp [h]

lemma isClosed_iff_derivedSet_subset (A : Set X) : IsClosed A ↔ derivedSet A ⊆ A where
  mp h := by
    rw [isClosed_iff_clusterPt] at h
    intro x hx
    apply h
    apply hx.clusterPt
  mpr h := by
    rw [isClosed_iff_clusterPt]
    intro a ha
    by_contra! nh
    have : A = A \ {a} := by simp [nh]
    rw [this, ← acc_principal_iff_cluster] at ha
    exact nh (h ha)

theorem frequently_nhds_iff {x : X} {p : X → Prop} :
    (∃ᶠ (x : X) in 𝓝 x, p x) ↔ ∀ U, IsOpen U → x ∈ U → ∃ x ∈ U, p x := by
  simp only [frequently_iff, mem_nhds_iff, forall_exists_index, and_imp]
  constructor
  · intro a b c d
    exact a b subset_rfl c d
  · intro a _ c d e f
    obtain ⟨v, hv, hv2⟩ := a c e f
    exact ⟨v, d hv, hv2⟩

@[simp]
lemma isClosed_derivedSet [T1Space X] (A : Set X) : IsClosed (derivedSet A) := by
  rw [isClosed_iff_derivedSet_subset]
  intro x hx
  rw [derivedSet, Set.mem_setOf, accPt_iff_frequently, frequently_nhds_iff] at hx ⊢
  intro U hu1 hu2
  obtain ⟨y, hy, ⟨hy1, hy2⟩⟩ := hx U hu1 hu2
  rw [derivedSet, Set.mem_setOf, accPt_iff_frequently, frequently_nhds_iff] at hy2
  obtain ⟨z, hz⟩ := hy2 (U \ {x}) (IsOpen.sdiff hu1 isClosed_singleton) (by simp [hy1, hy])
  simp at hz
  use z
  simp [hz]

lemma connected_subset_derivedSet [T1Space X] (U : Set X) (hu : U.Nontrivial)
    (h : IsPreconnected U) : U ⊆ derivedSet U := by
  intro x hx
  rw [isPreconnected_closed_iff] at h
  replace h := h {x} (closure (U \ {x})) isClosed_singleton isClosed_closure (by
    trans {x} ∪ (U \ {x})
    · simp
    apply Set.union_subset_union_right
    exact subset_closure
  ) (Set.inter_singleton_nonempty.mpr hx) (by
    obtain ⟨y, hy⟩ := Set.Nontrivial.exists_ne hu x
    use y
    simp only [Set.mem_inter_iff, hy, true_and]
    apply subset_closure
    simp [hy]
  )
  apply Set.Nonempty.right at h
  rw [Set.singleton_inter_nonempty, mem_closure_iff_clusterPt, ← acc_principal_iff_cluster] at h
  exact h


lemma preconnected_shared_accPts [T1Space X] (U : Set X) (hs : IsPreconnected U) (a b : Set X)
    (h : U ⊆ a ∪ b) (ha : (U ∩ derivedSet a).Nonempty) (hb : (U ∩ derivedSet b).Nonempty) :
    (U ∩ (derivedSet a ∩ derivedSet b)).Nonempty := by
  by_cases hu : U.Nontrivial
  · apply isPreconnected_closed_iff.mp hs
    · simp
    · simp
    · trans derivedSet U
      · apply connected_subset_derivedSet U hu hs
      · rw [← derivedSet_union]
        exact derivedSet_mono _ _ h
    · exact ha
    · exact hb
  · obtain ⟨x, hx⟩ := ha.left.exists_eq_singleton_or_nontrivial.resolve_right hu
    simp_all
