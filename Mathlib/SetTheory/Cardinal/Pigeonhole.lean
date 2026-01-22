/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.SetTheory.Cardinal.Regular

/-!
# Infinite pigeonhole principle

This file proves variants of the infinite pigeonhole principle.

## TODO

Generalize universes of results.
-/

public section

open Order Ordinal Set

universe u v

namespace Cardinal

/-- The infinite pigeonhole principle -/
theorem infinite_pigeonhole {β α : Type u} (f : β → α) (h₁ : ℵ₀ ≤ #β) (h₂ : #α < (#β).ord.cof) :
    ∃ a : α, #(f ⁻¹' {a}) = #β := by
  have : ∃ a, #β ≤ #(f ⁻¹' {a}) := by
    by_contra! h
    apply mk_univ.not_lt
    rw [← preimage_univ, ← iUnion_of_singleton, preimage_iUnion]
    exact
      mk_iUnion_le_sum_mk.trans_lt <| (sum_le_mk_mul_iSup _).trans_lt <|
        mul_lt_of_lt h₁ (h₂.trans_le <| cof_ord_le _) (iSup_lt h₂ h)
  obtain ⟨x, h⟩ := this
  refine ⟨x, h.antisymm' ?_⟩
  rw [le_mk_iff_exists_set]
  exact ⟨_, rfl⟩

/-- Pigeonhole principle for a cardinality below the cardinality of the domain -/
theorem infinite_pigeonhole_card {β α : Type u} (f : β → α) (θ : Cardinal) (hθ : θ ≤ #β)
    (h₁ : ℵ₀ ≤ θ) (h₂ : #α < θ.ord.cof) : ∃ a : α, θ ≤ #(f ⁻¹' {a}) := by
  rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩
  obtain ⟨a, ha⟩ := infinite_pigeonhole (f ∘ Subtype.val : s → α) h₁ h₂
  use a; rw [← ha, @preimage_comp _ _ _ Subtype.val f]
  exact mk_preimage_of_injective _ _ Subtype.val_injective

theorem infinite_pigeonhole_set {β α : Type u} {s : Set β} (f : s → α) (θ : Cardinal)
    (hθ : θ ≤ #s) (h₁ : ℵ₀ ≤ θ) (h₂ : #α < θ.ord.cof) :
    ∃ (a : α) (t : Set β) (h : t ⊆ s), θ ≤ #t ∧ ∀ ⦃x⦄ (hx : x ∈ t), f ⟨x, h hx⟩ = a := by
  obtain ⟨a, ha⟩ := infinite_pigeonhole_card f θ hθ h₁ h₂
  refine ⟨a, { x | ∃ h, f ⟨x, h⟩ = a }, ?_, ?_, ?_⟩
  · rintro x ⟨hx, _⟩
    exact hx
  · refine
      ha.trans
        (ge_of_eq <|
          Quotient.sound ⟨Equiv.trans ?_ (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm⟩)
    simp only [coe_eq_subtype, mem_singleton_iff, mem_preimage, mem_setOf_eq]
    rfl
  rintro x ⟨_, hx'⟩; exact hx'

/-- A function whose domain's cardinality is infinite but strictly greater than its domain's
has a fiber with cardinality strictly great than the codomain. -/
theorem infinite_pigeonhole_card_lt {β α : Type u} (f : β → α) (h : #α < #β) (hβ : ℵ₀ ≤ #β) :
    ∃ a : α, #α < #(f ⁻¹' {a}) := by
  simp_rw [← succ_le_iff]
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card f ℵ₀ hβ le_rfl (by rwa [isRegular_aleph0.cof_eq])
    exact ⟨a, ha.trans' (succ_le_of_lt hα)⟩
  · exact infinite_pigeonhole_card f (succ #α) (succ_le_of_lt h) (hα.trans (le_succ _))
      ((lt_succ _).trans_le (isRegular_succ hα).2.ge)

/-- A function whose domain's cardinality is infinite but strictly greater than its domain's
has an infinite fiber. -/
theorem exists_infinite_fiber {β α : Type u} (f : β → α) (h : #α < #β) (hβ : Infinite β) :
    ∃ a : α, Infinite (f ⁻¹' {a}) := by
  simp_rw [Cardinal.infinite_iff] at hβ ⊢
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · exact infinite_pigeonhole_card f ℵ₀ hβ le_rfl (by rwa [isRegular_aleph0.cof_eq])
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card_lt f h hβ
    exact ⟨a, hα.trans ha.le⟩

/-- A weaker version of `exists_infinite_fiber` that requires codomain to be infinite. -/
theorem exists_infinite_fiber' {β α : Type u} (f : β → α) (h : #α < #β) (hα : Infinite α) :
    ∃ a : α, Infinite (f ⁻¹' {a}) :=
  exists_infinite_fiber f h (by
    rw [Cardinal.infinite_iff] at hα ⊢
    exact hα.trans h.le)

/-- A function whose domain's cardinality is uncountable but strictly greater than its domain's
has an uncountable fiber. -/
theorem exists_uncountable_fiber {β α : Type u} (f : β → α) (h : #α < #β) (hβ : Uncountable β) :
    ∃ a : α, Uncountable (f ⁻¹' {a}) := by
  simp_rw [← Cardinal.aleph0_lt_mk_iff, ← Order.succ_le_iff, succ_aleph0] at hβ ⊢
  rcases lt_or_ge #α ℵ₀ with hα | hα
  · exact infinite_pigeonhole_card f ℵ₁ hβ aleph0_lt_aleph_one.le
      (by rw [isRegular_aleph_one.cof_eq]; exact hα.trans aleph0_lt_aleph_one)
  · obtain ⟨a, ha⟩ := infinite_pigeonhole_card_lt f h (hβ.trans' aleph0_lt_aleph_one.le)
    rw [← Order.succ_le_succ_iff, succ_aleph0] at hα
    exact ⟨a, hα.trans (succ_le_of_lt ha)⟩

/-- If an infinite type `β` can be expressed as a union of finite sets,
then the cardinality of the collection of those finite sets
must be at least the cardinality of `β`. -/
theorem le_range_of_union_finset_eq_univ {α β : Type*} [Infinite β] (f : α → Finset β)
    (w : ⋃ a, (f a : Set β) = Set.univ) : #β ≤ #(range f) := by
  by_contra h
  simp only [not_le] at h
  let u : ∀ b, ∃ a, b ∈ f a := fun b => by simpa using (w.ge :) (Set.mem_univ b)
  let u' : β → range f := fun b => ⟨f (u b).choose, by simp⟩
  have v' : ∀ a, u' ⁻¹' {⟨f a, by simp⟩} ≤ f a := by
    rintro a p m
    have m : f (u p).choose = f a := by simpa [u'] using m
    rw [← m]
    apply fun b => (u b).choose_spec
  obtain ⟨⟨-, ⟨a, rfl⟩⟩, p⟩ := exists_infinite_fiber u' h (by infer_instance)
  exact (@Infinite.of_injective _ _ p (inclusion (v' a)) (inclusion_injective _)).false

@[deprecated (since := "2026-01-17")] alias le_range_of_union_finset_eq_top :=
  le_range_of_union_finset_eq_univ

end Cardinal

open Cardinal

/-- **Δ-system lemma**: every uncountable family of finite sets must contain an uncountable
Δ-system, i.e. an uncountable subfamily that share the same pairwise intersection. -/
theorem Uncountable.exists_uncountable_pairwise_inter_eq {α : Type u} {ι : Type v} [DecidableEq α]
    [Uncountable ι] (f : ι → Finset α) :
    ∃ (s : Set ι) (t : Finset α), Uncountable s ∧ s.Pairwise (f · ∩ f · = t) := by
  suffices ∀ (s : Set ι) (n : ℕ), (∀ i ∈ s, (f i).card = n) → Uncountable s →
      ∃ s' ⊆ s, ∃ (t : Finset α), Uncountable s' ∧ s'.Pairwise (f · ∩ f · = t) by
    rcases exists_uncountable_fiber (fun i => ULift.up (f i).card) (by simp) (by infer_instance)
      with ⟨⟨n⟩, h⟩
    rcases this _ n (by grind) h with ⟨s', -, t, hs, ht⟩
    exact ⟨s', t, hs, ht⟩
  intro s n hn hs
  induction n generalizing f s with
  | zero =>
    exact ⟨s, subset_rfl, ∅, hs, fun i hi j hj hij => by grind⟩
  | succ n ih =>
    by_cases h : ∃ a, Uncountable {i ∈ s | a ∈ f i}
    · rcases h with ⟨a, ha⟩
      rcases ih (fun i => f i \ {a}) _ (by grind) ha with ⟨s', hs', t, hs'', ht⟩
      exact ⟨s', hs'.trans (sep_subset _ _), t ∪ {a}, hs'', fun i hi j hj hij => by
        grind [Set.Pairwise]⟩
    simp only [coe_setOf, not_exists, not_uncountable_iff] at h
    let g : Ordinal.{v} → ι := WellFoundedLT.fix fun j ih =>
      Classical.epsilon fun i => i ∈ s ∧ ∀ k (hk : k < j), f i ∩ f (ih k hk) = ∅
    have hg : ∀ j < ω₁, g j ∈ s ∧ ∀ k < j, f (g j) ∩ f (g k) = ∅ := by
      intro j hj
      suffices {i ∈ s | ∀ k (hk : k < j), f i ∩ f (g k) = ∅}.Nonempty by
        simp only [nonempty_def, mem_setOf_eq] at this
        apply Classical.epsilon_spec at this
        unfold g
        rwa [WellFoundedLT.fix_eq]
      rw [setOf_and, setOf_mem_eq, ← diff_compl, ← diff_self_inter]
      refine (hs.to_set.diff ?_).nonempty
      simp_rw [compl_setOf, not_forall, setOf_exists, ← mem_Iio, inter_iUnion₂]
      refine .biUnion ?_ fun a ha => ?_
      · rwa [← le_aleph0_iff_set_countable, mk_Iio_ordinal, lift_le_aleph0, ← lt_succ_iff,
          succ_aleph0, ← lt_ord, ord_aleph]
      · simp_rw [Finset.eq_empty_iff_forall_notMem, Finset.mem_inter, not_and', not_forall,
          ← SetLike.mem_coe, setOf_exists, not_not, inter_iUnion₂]
        refine .biUnion (Finset.finite_toSet _).countable fun i hi => ?_
        simp_rw [SetLike.mem_coe, inter_setOf_eq_sep]
        exact h i
    have hg' : InjOn g (Iio ω₁) := by
      intro j hj k hk hjk
      by_contra hjk'
      wlog hjk'' : k < j generalizing j k
      · exact this hk hj hjk.symm (ne_comm.1 hjk') (lt_of_le_of_ne (le_of_not_gt hjk'') hjk')
      have := (hg j hj).2 k hjk''
      simp only [← hjk, Finset.inter_self] at this
      simpa [this] using hn _ (hg j hj).1
    refine ⟨g '' Iio ω₁, by grind, ∅, .to_subtype (.image ?_ hg'), Pairwise.image ?_⟩
    · rw [← uncountable_coe_iff, ← aleph0_lt_mk_iff, mk_Iio_ordinal, aleph0_lt_lift, card_omega]
      exact aleph0_lt_aleph_one
    intro j hj k hk hjk
    simp only [Function.onFun_apply]
    wlog hjk' : k < j generalizing j k
    · rw [Finset.inter_comm]
      exact this hk hj hjk.symm (lt_of_le_of_ne (le_of_not_gt hjk') hjk)
    exact (hg j hj).2 k hjk'
