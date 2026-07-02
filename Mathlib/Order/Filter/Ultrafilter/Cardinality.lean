/-
Copyright (c) 2026 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
module

public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.SetTheory.Cardinal.Defs

import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinality of Ultrafilters

We prove there are `2 ^ 2 ^ #α` ultrafilters on an infinite type `α`.
-/

variable {α : Type*}
open Cardinal Filter Set

section Finite
variable [Finite α]

public theorem Cardinal.mk_ultrafilter_of_finite :
    #(Ultrafilter α) = #α := by
  refine Cardinal.mk_congr (Equiv.ofBijective pure ?_).symm
  exact ⟨Ultrafilter.pure_injective, Ultrafilter.pure_surjective⟩

public theorem Cardinal.mk_filter_of_finite :
    #(Filter α) = 2 ^ #α := by
  rw [← Cardinal.mk_set]
  refine Cardinal.mk_congr (Equiv.ofBijective Filter.principal ?_).symm
  exact ⟨Filter.principal_injective, Filter.principal_surjective⟩

end Finite

section Infinite

def interPair (s : Set α) : Set (Finset α × Finset (Finset α)) :=
  open scoped Classical in {p | p.1.filter (· ∈ s) ∈ p.2}

def interPairsFilter (s : Set (Set α)) : Filter (Finset α × Finset (Finset α)) :=
  open scoped Classical in ⨅ t, 𝓟 (if t ∈ s then interPair t else (interPair t)ᶜ)

instance interPairsFilter_neBot (s : Set (Set α)) : (interPairsFilter s).NeBot := by
  classical
  unfold interPairsFilter
  rw [← iInf_range, ← generate_eq_biInf, generate_neBot_iff]
  set f := fun t => if t ∈ s then interPair t else (interPair t)ᶜ
  suffices h : ∀ t, t.Finite → (⋂₀ (f '' t)).Nonempty by
    intro t hts ht
    choose c hc using hts
    refine Set.Nonempty.mono (sInter_mono ?_) <|
      h (⋃ (x) (hx : x ∈ t), {c hx}) (ht.biUnion' fun _ _ => finite_singleton _)
    intro x hx
    simp_rw [mem_image, mem_iUnion₂, mem_singleton_iff]
    exact ⟨_, ⟨x, hx, rfl⟩, hc hx⟩
  intro t ht
  rw [sInter_image, nonempty_def]
  have hne : Disjoint s sᶜ := disjoint_compl_right
  simp_rw [disjoint_iff_forall_ne, ← symmDiff_nonempty,
    nonempty_def, mem_symmDiff, ← xor_def] at hne
  choose c hc using hne
  let F := ⋃ (i) (hi : i ∈ t) (j) (hj : j ∈ t) (his : i ∈ s) (hjs : j ∉ s), {c his hjs}
  have hF : F.Finite := ht.biUnion' fun i hi => ht.biUnion' fun j hj =>
    finite_iUnion fun his => finite_iUnion fun hjs => finite_singleton (c his hjs)
  refine ⟨(hF.toFinset, (ht.toFinset.filter (· ∈ s)).image (fun i => hF.toFinset.filter (· ∈ i))),
    mem_biInter fun x hx => ?_⟩
  unfold f interPair
  split_ifs with hxs
  · refine Finset.mem_image_of_mem (fun i => hF.toFinset.filter (· ∈ i)) ?_
    simp [hx, hxs]
  · simp_rw [mem_compl_iff, mem_setOf, Finset.mem_image, Finset.mem_filter,
      not_exists, not_and, and_imp, ← SetLike.coe_injective.eq_iff, Finset.coe_filter,
      Set.Finite.mem_toFinset, ← symmDiff_nonempty, nonempty_def, mem_symmDiff, ← xor_def]
    intro y hy hys
    refine ⟨c hys hxs, ?_⟩
    have hxy : c hys hxs ∈ F := by
      simp_rw [F, mem_iUnion, mem_singleton_iff]
      exact ⟨y, hy, x, hx, hys, hxs, rfl⟩
    simpa [hxy] using hc hys hxs

theorem interPairsFilter_pairwiseDisjoint : Set.univ.Pairwise
    (fun s t : Set (Set α) => Disjoint (interPairsFilter s) (interPairsFilter t)) := by
  intro s _ t _ hst
  simp_rw [← symmDiff_nonempty, nonempty_def, mem_symmDiff] at hst
  rw [Filter.disjoint_iff]
  unfold interPairsFilter
  obtain ⟨x, hx | hx⟩ := hst
  · exact ⟨interPair x, Filter.mem_iInf_of_mem x
      (if_pos hx.1 ▸ Filter.mem_principal_self (interPair x)),
      (interPair x)ᶜ, Filter.mem_iInf_of_mem x
      (if_neg hx.2 ▸ Filter.mem_principal_self (interPair x)ᶜ),
      disjoint_compl_right⟩
  · exact ⟨(interPair x)ᶜ, Filter.mem_iInf_of_mem x
      (if_neg hx.2 ▸ Filter.mem_principal_self (interPair x)ᶜ),
      interPair x, Filter.mem_iInf_of_mem x
      (if_pos hx.1 ▸ Filter.mem_principal_self (interPair x)),
      disjoint_compl_left⟩

variable [Infinite α]

public theorem Cardinal.mk_ultrafilter_of_infinite :
    #(Ultrafilter α) = 2 ^ (2 ^ #α : Cardinal) := by
  rw [← Cardinal.mk_set, ← Cardinal.mk_set]
  apply le_antisymm
  · suffices h : Function.Injective Filter.sets from
      Cardinal.mk_le_of_injective (h.comp Ultrafilter.coe_injective)
    intro f g h
    ext s
    rw [← Filter.mem_sets, ← Filter.mem_sets, h]
  · obtain ⟨e⟩ : Nonempty (Finset α × Finset (Finset α) ≃ α) := Cardinal.eq.1 (by simp)
    let f (s : Set (Set α)) : Ultrafilter α := Ultrafilter.of ((interPairsFilter s).map e)
    suffices hf : f.Injective from Cardinal.mk_le_of_injective hf
    intro s t hst
    contrapose! hst
    have hdj : Disjoint ((interPairsFilter s).map e) ((interPairsFilter t).map e) := by
      rw [disjoint_map e.injective]
      exact interPairsFilter_pairwiseDisjoint (mem_univ s) (mem_univ t) hst
    unfold f
    rw [← Ultrafilter.coe_injective.ne_iff]
    exact (hdj.mono (Ultrafilter.of_le _) (Ultrafilter.of_le _)).ne (Ultrafilter.neBot _).ne

public theorem Cardinal.mk_filter_of_infinite :
    #(Filter α) = 2 ^ (2 ^ #α : Cardinal) := by
  apply le_antisymm
  · rw [← Cardinal.mk_set, ← Cardinal.mk_set]
    suffices h : Function.Injective Filter.sets from Cardinal.mk_le_of_injective h
    intro f g h
    ext s
    rw [← Filter.mem_sets, ← Filter.mem_sets, h]
  · rw [← Cardinal.mk_ultrafilter_of_infinite]
    exact Cardinal.mk_le_of_injective Ultrafilter.coe_injective

end Infinite
