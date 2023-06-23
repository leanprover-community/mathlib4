/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov

! This file was ported from Lean 3 source module order.filter.indicator_function
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.IndicatorFunction
import Mathlib.Order.Filter.AtTopBot

/-!
# Indicator function and filters

Properties of indicator functions involving `=ᶠ` and `≤ᶠ`.

## Tags
indicator, characteristic, filter
-/


variable {α β M E : Type _}

open Set Filter

section Zero

variable [Zero M] {s t : Set α} {f g : α → M} {a : α} {l : Filter α}

theorem indicator_eventuallyEq (hf : f =ᶠ[l ⊓ 𝓟 s] g) (hs : s =ᶠ[l] t) :
    indicator s f =ᶠ[l] indicator t g :=
  (eventually_inf_principal.1 hf).mp <|
    hs.mem_iff.mono fun x hst hfg =>
      by_cases (fun hxs : x ∈ s => by simp only [*, hst.1 hxs, indicator_of_mem]) fun hxs => by
        simp only [indicator_of_not_mem hxs, indicator_of_not_mem (mt hst.2 hxs)]
#align indicator_eventually_eq indicator_eventuallyEq

end Zero

section AddMonoid

variable [AddMonoid M] {s t : Set α} {f g : α → M} {a : α} {l : Filter α}

theorem indicator_union_eventuallyEq (h : ∀ᶠ a in l, a ∉ s ∩ t) :
    indicator (s ∪ t) f =ᶠ[l] indicator s f + indicator t f :=
  h.mono fun _a ha => indicator_union_of_not_mem_inter ha _
#align indicator_union_eventually_eq indicator_union_eventuallyEq

end AddMonoid

section Order

variable [Zero β] [Preorder β] {s t : Set α} {f g : α → β} {a : α} {l : Filter α}

theorem indicator_eventuallyLE_indicator (h : f ≤ᶠ[l ⊓ 𝓟 s] g) :
    indicator s f ≤ᶠ[l] indicator s g :=
  (eventually_inf_principal.1 h).mono fun _ => indicator_rel_indicator le_rfl
#align indicator_eventually_le_indicator indicator_eventuallyLE_indicator

end Order

theorem Monotone.tendsto_indicator {ι} [Preorder ι] [Zero β] (s : ι → Set α) (hs : Monotone s)
    (f : α → β) (a : α) :
    Tendsto (fun i => indicator (s i) f a) atTop (pure <| indicator (⋃ i, s i) f a) := by
  by_cases h : ∃ i, a ∈ s i
  · rcases h with ⟨i, hi⟩
    refine' tendsto_pure.2 ((eventually_ge_atTop i).mono fun n hn => _)
    rw [indicator_of_mem (hs hn hi) _, indicator_of_mem ((subset_iUnion _ _) hi) _]
  · have h' : a ∉ ⋃ i, s i := mt mem_iUnion.1 h
    rw [not_exists] at h
    simpa only [indicator_of_not_mem, *] using tendsto_const_pure
#align monotone.tendsto_indicator Monotone.tendsto_indicator

theorem Antitone.tendsto_indicator {ι} [Preorder ι] [Zero β] (s : ι → Set α) (hs : Antitone s)
    (f : α → β) (a : α) :
    Tendsto (fun i => indicator (s i) f a) atTop (pure <| indicator (⋂ i, s i) f a) := by
  by_cases h : ∃ i, a ∉ s i
  · rcases h with ⟨i, hi⟩
    refine' tendsto_pure.2 ((eventually_ge_atTop i).mono fun n hn => _)
    rw [indicator_of_not_mem _ _, indicator_of_not_mem _ _]
    · simp only [mem_iInter, not_forall]
      exact ⟨i, hi⟩
    · intro h
      have := hs hn h
      contradiction
  · push_neg at h
    simp only [indicator_of_mem, h, mem_iInter.2 h, tendsto_const_pure]
#align antitone.tendsto_indicator Antitone.tendsto_indicator

theorem tendsto_indicator_biUnion_finset {ι} [Zero β] (s : ι → Set α) (f : α → β) (a : α) :
    Tendsto (fun n : Finset ι => indicator (⋃ i ∈ n, s i) f a) atTop
      (pure <| indicator (iUnion s) f a) := by
  rw [iUnion_eq_iUnion_finset s]
  refine' Monotone.tendsto_indicator (fun n : Finset ι => ⋃ i ∈ n, s i) _ f a
  exact fun t₁ t₂ => biUnion_subset_biUnion_left
#align tendsto_indicator_bUnion_finset tendsto_indicator_biUnion_finset

theorem Filter.EventuallyEq.support [Zero β] {f g : α → β} {l : Filter α} (h : f =ᶠ[l] g) :
    Function.support f =ᶠ[l] Function.support g := by
  filter_upwards [h]with x hx
  rw [eq_iff_iff]
  change f x ≠ 0 ↔ g x ≠ 0
  rw [hx]
#align filter.eventually_eq.support Filter.EventuallyEq.support

theorem Filter.EventuallyEq.indicator [Zero β] {l : Filter α} {f g : α → β} {s : Set α}
    (hfg : f =ᶠ[l] g) : s.indicator f =ᶠ[l] s.indicator g :=
  indicator_eventuallyEq (hfg.filter_mono inf_le_left) EventuallyEq.rfl
#align filter.eventually_eq.indicator Filter.EventuallyEq.indicator

theorem Filter.EventuallyEq.indicator_zero [Zero β] {l : Filter α} {f : α → β} {s : Set α}
    (hf : f =ᶠ[l] 0) : s.indicator f =ᶠ[l] 0 := by
  refine' hf.indicator.trans _
  rw [indicator_zero']
#align filter.eventually_eq.indicator_zero Filter.EventuallyEq.indicator_zero
