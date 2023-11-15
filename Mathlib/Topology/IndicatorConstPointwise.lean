/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.Algebra.IndicatorFunction
import Mathlib.Topology.Separation

/-!
# Pointwise convergence of indicator functions

In this file, we prove the equivalence of three different ways to phrase that the indicator
functions of sets converge pointwise.
-/


open Filter Topology

variable {α : Type*} {A : Set α}
variable {β : Type*} [Zero β] [TopologicalSpace β]
variable {ι : Type*} (L : Filter ι) {As : ι → Set α}

lemma tendsto_ite {β : Type*} {p : ι → Prop} [DecidablePred p] {q : Prop} [Decidable q]
    {a b : β} {F G : Filter β}
    (haG : {a}ᶜ ∈ G) (hbF : {b}ᶜ ∈ F) (haF : principal {a} ≤ F) (hbG : principal {b} ≤ G) :
    Tendsto (fun i ↦ if p i then a else b) L (if q then F else G) ↔ ∀ᶠ i in L, p i ↔ q := by
  constructor <;> intro h
  · by_cases hq : q
    · simp only [hq, ite_true] at h
      filter_upwards [mem_map.mp (h hbF)] with i hi
      simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        ite_eq_right_iff, not_forall, exists_prop] at hi
      tauto
    · simp only [hq, ite_false] at h
      filter_upwards [mem_map.mp (h haG)] with i hi
      simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        ite_eq_left_iff, not_forall, exists_prop] at hi
      tauto
  · have obs : (fun _ ↦ if q then a else b) =ᶠ[L] (fun i ↦ if p i then a else b) := by
      filter_upwards [h] with i hi
      simp only [hi]
    apply Tendsto.congr' obs
    by_cases hq : q
    · simp only [hq, iff_true, ite_true]
      apply le_trans _ haF
      simp only [principal_singleton, le_pure_iff, mem_map, Set.mem_singleton_iff,
        Set.preimage_const_of_mem, univ_mem]
    · simp only [hq, ite_false]
      apply le_trans _ hbG
      simp only [principal_singleton, le_pure_iff, mem_map, Set.mem_singleton_iff,
        Set.preimage_const_of_mem, univ_mem]

lemma tendsto_indicator_const_iff_forall_eventually'
    (b : β) (nhd_b : {0}ᶜ ∈ 𝓝 b) (nhd_o : {b}ᶜ ∈ 𝓝 0) :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b)) L (𝓝 (A.indicator (fun (_ : α) ↦ b)))
      ↔ ∀ x, ∀ᶠ i in L, (x ∈ As i ↔ x ∈ A) := by
  simp_rw [tendsto_pi_nhds]
  apply forall_congr'
  intro x
  classical
  have heart := @tendsto_ite ι L β (fun i ↦ x ∈ As i) _ (x ∈ A) _ b 0 (𝓝 b) (𝓝 (0 : β))
                nhd_o nhd_b ?_ ?_
  convert heart
  · by_cases hxA : x ∈ A <;> simp [hxA]
  · simp only [principal_singleton, le_def, mem_pure]
    exact fun s s_nhd ↦ mem_of_mem_nhds s_nhd
  · simp only [principal_singleton, le_def, mem_pure]
    exact fun s s_nhd ↦ mem_of_mem_nhds s_nhd

@[simp] lemma tendsto_indicator_const_iff_forall_eventually [T1Space β] (b : β) [NeZero b] :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b)) L (𝓝 (A.indicator (fun (_ : α) ↦ b)))
      ↔ ∀ x, ∀ᶠ i in L, (x ∈ As i ↔ x ∈ A) := by
  apply tendsto_indicator_const_iff_forall_eventually' _ b
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, NeZero.ne]
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, (NeZero.ne b).symm]

lemma tendsto_indicator_const_iff_tendsto_pi_pure'
    (b : β) (nhd_b : {0}ᶜ ∈ 𝓝 b) (nhd_o : {b}ᶜ ∈ 𝓝 0) :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b)) L (𝓝 (A.indicator (fun (_ : α) ↦ b)))
      ↔ (Tendsto As L <| Filter.pi (pure <| · ∈ A)) := by
  rw [tendsto_indicator_const_iff_forall_eventually' _ b nhd_b nhd_o, tendsto_pi]
  simp_rw [tendsto_pure]
  aesop

lemma tendsto_indicator_const_iff_tendsto_pi_pure [T1Space β] (b : β) [NeZero b] :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b)) L (𝓝 (A.indicator (fun (_ : α) ↦ b)))
      ↔ (Tendsto As L <| Filter.pi (pure <| · ∈ A)) := by
  rw [tendsto_indicator_const_iff_forall_eventually _ b, tendsto_pi]
  simp_rw [tendsto_pure]
  aesop
