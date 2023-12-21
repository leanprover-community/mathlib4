/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.IndicatorFunction
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.Archimedean
import Mathlib.Order.Filter.CountableInter
import Mathlib.Topology.Order.Basic

#align_import topology.algebra.order.liminf_limsup from "leanprover-community/mathlib"@"52932b3a083d4142e78a15dc928084a22fea9ba0"

/-!
# Lemmas about liminf and limsup in an order topology.
-/


open Filter TopologicalSpace

open Topology Classical

universe u v

variable {α : Type u} {β : Type v}

section LiminfLimsup

section OrderClosedTopology

variable [SemilatticeSup α] [TopologicalSpace α] [OrderTopology α]

theorem isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· ≤ ·) :=
  (isTop_or_exists_gt a).elim (fun h ↦ ⟨a, eventually_of_forall h⟩) fun ⟨b, hb⟩ ↦
    ⟨b, ge_mem_nhds hb⟩
#align is_bounded_le_nhds isBounded_le_nhds

theorem Filter.Tendsto.isBoundedUnder_le {f : Filter β} {u : β → α} {a : α}
    (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· ≤ ·) u :=
  (isBounded_le_nhds a).mono h
#align filter.tendsto.is_bounded_under_le Filter.Tendsto.isBoundedUnder_le

theorem Filter.Tendsto.bddAbove_range_of_cofinite {u : β → α} {a : α}
    (h : Tendsto u cofinite (𝓝 a)) : BddAbove (Set.range u) :=
  h.isBoundedUnder_le.bddAbove_range_of_cofinite
#align filter.tendsto.bdd_above_range_of_cofinite Filter.Tendsto.bddAbove_range_of_cofinite

theorem Filter.Tendsto.bddAbove_range {u : ℕ → α} {a : α} (h : Tendsto u atTop (𝓝 a)) :
    BddAbove (Set.range u) :=
  h.isBoundedUnder_le.bddAbove_range
#align filter.tendsto.bdd_above_range Filter.Tendsto.bddAbove_range

theorem isCobounded_ge_nhds (a : α) : (𝓝 a).IsCobounded (· ≥ ·) :=
  (isBounded_le_nhds a).isCobounded_flip
#align is_cobounded_ge_nhds isCobounded_ge_nhds

theorem Filter.Tendsto.isCoboundedUnder_ge {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : f.IsCoboundedUnder (· ≥ ·) u :=
  h.isBoundedUnder_le.isCobounded_flip
#align filter.tendsto.is_cobounded_under_ge Filter.Tendsto.isCoboundedUnder_ge

theorem isBounded_le_atBot (α : Type*) [hα : Nonempty α] [Preorder α] :
    (atBot : Filter α).IsBounded (· ≤ ·) :=
  isBounded_iff.2 ⟨Set.Iic hα.some, mem_atBot _, hα.some, fun _ hx ↦ hx⟩
#align is_bounded_le_at_bot isBounded_le_atBot

theorem Filter.Tendsto.isBoundedUnder_le_atBot {α : Type*} [Nonempty α] [Preorder α] {f : Filter β}
    {u : β → α} (h : Tendsto u f atBot) : f.IsBoundedUnder (· ≤ ·) u :=
  (isBounded_le_atBot α).mono h
#align filter.tendsto.is_bounded_under_le_at_bot Filter.Tendsto.isBoundedUnder_le_atBot

theorem bddAbove_range_of_tendsto_atTop_atBot {α : Type*} [Nonempty α] [SemilatticeSup α]
    {u : ℕ → α} (hx : Tendsto u atTop atBot) : BddAbove (Set.range u) :=
  (Filter.Tendsto.isBoundedUnder_le_atBot hx).bddAbove_range
#align bdd_above_range_of_tendsto_at_top_at_bot bddAbove_range_of_tendsto_atTop_atBot

end OrderClosedTopology

section OrderClosedTopology

variable [SemilatticeInf α] [TopologicalSpace α] [OrderTopology α]

theorem isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· ≥ ·) :=
  isBounded_le_nhds (α := αᵒᵈ) a
#align is_bounded_ge_nhds isBounded_ge_nhds

theorem Filter.Tendsto.isBoundedUnder_ge {f : Filter β} {u : β → α} {a : α}
    (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· ≥ ·) u :=
  (isBounded_ge_nhds a).mono h
#align filter.tendsto.is_bounded_under_ge Filter.Tendsto.isBoundedUnder_ge

theorem Filter.Tendsto.bddBelow_range_of_cofinite {u : β → α} {a : α}
    (h : Tendsto u cofinite (𝓝 a)) : BddBelow (Set.range u) :=
  h.isBoundedUnder_ge.bddBelow_range_of_cofinite
#align filter.tendsto.bdd_below_range_of_cofinite Filter.Tendsto.bddBelow_range_of_cofinite

theorem Filter.Tendsto.bddBelow_range {u : ℕ → α} {a : α} (h : Tendsto u atTop (𝓝 a)) :
    BddBelow (Set.range u) :=
  h.isBoundedUnder_ge.bddBelow_range
#align filter.tendsto.bdd_below_range Filter.Tendsto.bddBelow_range

theorem isCobounded_le_nhds (a : α) : (𝓝 a).IsCobounded (· ≤ ·) :=
  (isBounded_ge_nhds a).isCobounded_flip
#align is_cobounded_le_nhds isCobounded_le_nhds

theorem Filter.Tendsto.isCoboundedUnder_le {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : f.IsCoboundedUnder (· ≤ ·) u :=
  h.isBoundedUnder_ge.isCobounded_flip
#align filter.tendsto.is_cobounded_under_le Filter.Tendsto.isCoboundedUnder_le

theorem isBounded_ge_atTop (α : Type*) [Nonempty α] [Preorder α] :
    (atTop : Filter α).IsBounded (· ≥ ·) :=
  isBounded_le_atBot αᵒᵈ
#align is_bounded_ge_at_top isBounded_ge_atTop

theorem Filter.Tendsto.isBoundedUnder_ge_atTop {α : Type*} [Nonempty α] [Preorder α] {f : Filter β}
    {u : β → α} (h : Tendsto u f atTop) : f.IsBoundedUnder (· ≥ ·) u :=
  (isBounded_ge_atTop α).mono h
#align filter.tendsto.is_bounded_under_ge_at_top Filter.Tendsto.isBoundedUnder_ge_atTop

theorem bddBelow_range_of_tendsto_atTop_atTop {α : Type*} [Nonempty α] [SemilatticeInf α]
    {u : ℕ → α} (hx : Tendsto u atTop atTop) : BddBelow (Set.range u) :=
  (Filter.Tendsto.isBoundedUnder_ge_atTop hx).bddBelow_range
#align bdd_below_range_of_tendsto_at_top_at_top bddBelow_range_of_tendsto_atTop_atTop

end OrderClosedTopology

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α]

theorem lt_mem_sets_of_limsSup_lt {f : Filter α} {b} (h : f.IsBounded (· ≤ ·)) (l : f.limsSup < b) :
    ∀ᶠ a in f, a < b :=
  let ⟨_, (h : ∀ᶠ a in f, a ≤ _), hcb⟩ := exists_lt_of_csInf_lt h l
  mem_of_superset h fun _ hac ↦ lt_of_le_of_lt hac hcb
set_option linter.uppercaseLean3 false in
#align lt_mem_sets_of_Limsup_lt lt_mem_sets_of_limsSup_lt

theorem gt_mem_sets_of_limsInf_gt :
    ∀ {f : Filter α} {b}, f.IsBounded (· ≥ ·) → b < f.limsInf → ∀ᶠ a in f, b < a :=
  @lt_mem_sets_of_limsSup_lt αᵒᵈ _
set_option linter.uppercaseLean3 false in
#align gt_mem_sets_of_Liminf_gt gt_mem_sets_of_limsInf_gt

variable [TopologicalSpace α] [OrderTopology α]

/-- If the liminf and the limsup of a filter coincide, then this filter converges to
their common value, at least if the filter is eventually bounded above and below. -/
theorem le_nhds_of_limsSup_eq_limsInf {f : Filter α} {a : α} (hl : f.IsBounded (· ≤ ·))
    (hg : f.IsBounded (· ≥ ·)) (hs : f.limsSup = a) (hi : f.limsInf = a) : f ≤ 𝓝 a :=
  tendsto_order.2 ⟨fun _ hb ↦ gt_mem_sets_of_limsInf_gt hg <| hi.symm ▸ hb,
    fun _ hb ↦ lt_mem_sets_of_limsSup_lt hl <| hs.symm ▸ hb⟩
set_option linter.uppercaseLean3 false in
#align le_nhds_of_Limsup_eq_Liminf le_nhds_of_limsSup_eq_limsInf

theorem limsSup_nhds (a : α) : limsSup (𝓝 a) = a :=
  csInf_eq_of_forall_ge_of_forall_gt_exists_lt (isBounded_le_nhds a)
    (fun a' (h : { n : α | n ≤ a' } ∈ 𝓝 a) ↦ show a ≤ a' from @mem_of_mem_nhds α _ a _ h)
    fun b (hba : a < b) ↦
    show ∃ c, { n : α | n ≤ c } ∈ 𝓝 a ∧ c < b from
      match dense_or_discrete a b with
      | Or.inl ⟨c, hac, hcb⟩ => ⟨c, ge_mem_nhds hac, hcb⟩
      | Or.inr ⟨_, h⟩ => ⟨a, (𝓝 a).sets_of_superset (gt_mem_nhds hba) h, hba⟩
set_option linter.uppercaseLean3 false in
#align Limsup_nhds limsSup_nhds

theorem limsInf_nhds : ∀ a : α, limsInf (𝓝 a) = a :=
  limsSup_nhds (α := αᵒᵈ)
set_option linter.uppercaseLean3 false in
#align Liminf_nhds limsInf_nhds

/-- If a filter is converging, its limsup coincides with its limit. -/
theorem limsInf_eq_of_le_nhds {f : Filter α} {a : α} [NeBot f] (h : f ≤ 𝓝 a) : f.limsInf = a :=
  have hb_ge : IsBounded (· ≥ ·) f := (isBounded_ge_nhds a).mono h
  have hb_le : IsBounded (· ≤ ·) f := (isBounded_le_nhds a).mono h
  le_antisymm
    (calc
      f.limsInf ≤ f.limsSup := limsInf_le_limsSup hb_le hb_ge
      _ ≤ (𝓝 a).limsSup := limsSup_le_limsSup_of_le h hb_ge.isCobounded_flip (isBounded_le_nhds a)
      _ = a := limsSup_nhds a)
    (calc
      a = (𝓝 a).limsInf := (limsInf_nhds a).symm
      _ ≤ f.limsInf := limsInf_le_limsInf_of_le h (isBounded_ge_nhds a) hb_le.isCobounded_flip)
set_option linter.uppercaseLean3 false in
#align Liminf_eq_of_le_nhds limsInf_eq_of_le_nhds

/-- If a filter is converging, its liminf coincides with its limit. -/
theorem limsSup_eq_of_le_nhds : ∀ {f : Filter α} {a : α} [NeBot f], f ≤ 𝓝 a → f.limsSup = a :=
  limsInf_eq_of_le_nhds (α := αᵒᵈ)
set_option linter.uppercaseLean3 false in
#align Limsup_eq_of_le_nhds limsSup_eq_of_le_nhds

/-- If a function has a limit, then its limsup coincides with its limit. -/
theorem Filter.Tendsto.limsup_eq {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : limsup u f = a :=
  limsSup_eq_of_le_nhds h
#align filter.tendsto.limsup_eq Filter.Tendsto.limsup_eq

/-- If a function has a limit, then its liminf coincides with its limit. -/
theorem Filter.Tendsto.liminf_eq {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : liminf u f = a :=
  limsInf_eq_of_le_nhds h
#align filter.tendsto.liminf_eq Filter.Tendsto.liminf_eq

/-- If the liminf and the limsup of a function coincide, then the limit of the function
exists and has the same value. -/
theorem tendsto_of_liminf_eq_limsup {f : Filter β} {u : β → α} {a : α} (hinf : liminf u f = a)
    (hsup : limsup u f = a) (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) : Tendsto u f (𝓝 a) :=
  le_nhds_of_limsSup_eq_limsInf h h' hsup hinf
#align tendsto_of_liminf_eq_limsup tendsto_of_liminf_eq_limsup

/-- If a number `a` is less than or equal to the `liminf` of a function `f` at some filter
and is greater than or equal to the `limsup` of `f`, then `f` tends to `a` along this filter. -/
theorem tendsto_of_le_liminf_of_limsup_le {f : Filter β} {u : β → α} {a : α} (hinf : a ≤ liminf u f)
    (hsup : limsup u f ≤ a) (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) : Tendsto u f (𝓝 a) :=
  if hf : f = ⊥ then hf.symm ▸ tendsto_bot
  else
    haveI : NeBot f := ⟨hf⟩
    tendsto_of_liminf_eq_limsup (le_antisymm (le_trans (liminf_le_limsup h h') hsup) hinf)
      (le_antisymm hsup (le_trans hinf (liminf_le_limsup h h'))) h h'
#align tendsto_of_le_liminf_of_limsup_le tendsto_of_le_liminf_of_limsup_le

/-- Assume that, for any `a < b`, a sequence can not be infinitely many times below `a` and
above `b`. If it is also ultimately bounded above and below, then it has to converge. This even
works if `a` and `b` are restricted to a dense subset.
-/
theorem tendsto_of_no_upcrossings [DenselyOrdered α] {f : Filter β} {u : β → α} {s : Set α}
    (hs : Dense s) (H : ∀ a ∈ s, ∀ b ∈ s, a < b → ¬((∃ᶠ n in f, u n < a) ∧ ∃ᶠ n in f, b < u n))
    (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) :
    ∃ c : α, Tendsto u f (𝓝 c) := by
  rcases f.eq_or_neBot with rfl | hbot
  · exact ⟨sInf ∅, tendsto_bot⟩
  refine' ⟨limsup u f, _⟩
  apply tendsto_of_le_liminf_of_limsup_le _ le_rfl h h'
  by_contra' hlt
  obtain ⟨a, ⟨⟨la, au⟩, as⟩⟩ : ∃ a, (f.liminf u < a ∧ a < f.limsup u) ∧ a ∈ s :=
    dense_iff_inter_open.1 hs (Set.Ioo (f.liminf u) (f.limsup u)) isOpen_Ioo
      (Set.nonempty_Ioo.2 hlt)
  obtain ⟨b, ⟨⟨ab, bu⟩, bs⟩⟩ : ∃ b, (a < b ∧ b < f.limsup u) ∧ b ∈ s :=
    dense_iff_inter_open.1 hs (Set.Ioo a (f.limsup u)) isOpen_Ioo (Set.nonempty_Ioo.2 au)
  have A : ∃ᶠ n in f, u n < a := frequently_lt_of_liminf_lt (IsBounded.isCobounded_ge h) la
  have B : ∃ᶠ n in f, b < u n := frequently_lt_of_lt_limsup (IsBounded.isCobounded_le h') bu
  exact H a as b bs ab ⟨A, B⟩
#align tendsto_of_no_upcrossings tendsto_of_no_upcrossings

variable [FirstCountableTopology α] {f : Filter β} [CountableInterFilter f] {u : β → α}

theorem eventually_le_limsup (hf : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    ∀ᶠ b in f, u b ≤ f.limsup u := by
  obtain ha | ha := isTop_or_exists_gt (f.limsup u)
  · exact eventually_of_forall fun _ => ha _
  by_cases H : IsGLB (Set.Ioi (f.limsup u)) (f.limsup u)
  · obtain ⟨u, -, -, hua, hu⟩ := H.exists_seq_antitone_tendsto ha
    have := fun n => eventually_lt_of_limsup_lt (hu n) hf
    exact
      (eventually_countable_forall.2 this).mono fun b hb =>
        ge_of_tendsto hua <| eventually_of_forall fun n => (hb _).le
  · obtain ⟨x, hx, xa⟩ : ∃ x, (∀ ⦃b⦄, f.limsup u < b → x ≤ b) ∧ f.limsup u < x := by
      simp only [IsGLB, IsGreatest, lowerBounds, upperBounds, Set.mem_Ioi, Set.mem_setOf_eq,
        not_and, not_forall, not_le, exists_prop] at H
      exact H fun x => le_of_lt
    filter_upwards [eventually_lt_of_limsup_lt xa hf] with y hy
    contrapose! hy
    exact hx hy
#align eventually_le_limsup eventually_le_limsup

theorem eventually_liminf_le (hf : IsBoundedUnder (· ≥ ·) f u := by isBoundedDefault) :
    ∀ᶠ b in f, f.liminf u ≤ u b :=
  eventually_le_limsup (α := αᵒᵈ) hf
#align eventually_liminf_le eventually_liminf_le

end ConditionallyCompleteLinearOrder

section CompleteLinearOrder

variable [CompleteLinearOrder α] [TopologicalSpace α] [FirstCountableTopology α] [OrderTopology α]
  {f : Filter β} [CountableInterFilter f] {u : β → α}

@[simp]
theorem limsup_eq_bot : f.limsup u = ⊥ ↔ u =ᶠ[f] ⊥ :=
  ⟨fun h =>
    (EventuallyLE.trans eventually_le_limsup <| eventually_of_forall fun _ => h.le).mono fun x hx =>
      le_antisymm hx bot_le,
    fun h => by
    rw [limsup_congr h]
    exact limsup_const_bot⟩
#align limsup_eq_bot limsup_eq_bot

@[simp]
theorem liminf_eq_top : f.liminf u = ⊤ ↔ u =ᶠ[f] ⊤ :=
  limsup_eq_bot (α := αᵒᵈ)
#align liminf_eq_top liminf_eq_top

end CompleteLinearOrder

end LiminfLimsup

section Monotone

variable {ι R S : Type*} {F : Filter ι} [NeBot F]
  [ConditionallyCompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R]
  [ConditionallyCompleteLinearOrder S] [TopologicalSpace S] [OrderTopology S]

/-- An antitone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsSup` to the `Filter.liminf` of the image if the function is continuous at the `limsSup`
(and the filter is bounded from above and below). -/
theorem Antitone.map_limsSup_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_decr : Antitone f) (f_cont : ContinuousAt f F.limsSup)
    (bdd_above : F.IsBounded (· ≤ ·) := by isBoundedDefault)
    (bdd_below : F.IsBounded (· ≥ ·) := by isBoundedDefault) :
    f F.limsSup = F.liminf f := by
  have cobdd : F.IsCobounded (· ≤ ·) := bdd_below.isCobounded_flip
  apply le_antisymm
  · rw [limsSup, f_decr.map_sInf_of_continuousAt' f_cont bdd_above cobdd]
    apply le_of_forall_lt
    intro c hc
    simp only [liminf, limsInf, eventually_map] at hc ⊢
    obtain ⟨d, hd, h'd⟩ :=
      exists_lt_of_lt_csSup (bdd_above.recOn fun x hx ↦ ⟨f x, Set.mem_image_of_mem f hx⟩) hc
    apply lt_csSup_of_lt ?_ ?_ h'd
    · exact (Antitone.isBoundedUnder_le_comp f_decr bdd_below).isCoboundedUnder_flip
    · rcases hd with ⟨e, ⟨he, fe_eq_d⟩⟩
      filter_upwards [he] with x hx using (fe_eq_d.symm ▸ f_decr hx)
  · by_cases h' : ∃ c, c < F.limsSup ∧ Set.Ioo c F.limsSup = ∅
    · rcases h' with ⟨c, c_lt, hc⟩
      have B : ∃ᶠ n in F, F.limsSup ≤ n := by
        apply (frequently_lt_of_lt_limsSup cobdd c_lt).mono
        intro x hx
        by_contra'
        have : (Set.Ioo c F.limsSup).Nonempty := ⟨x, ⟨hx, this⟩⟩
        simp only [hc, Set.not_nonempty_empty] at this
      apply liminf_le_of_frequently_le _ (bdd_above.isBoundedUnder f_decr)
      exact (B.mono fun x hx ↦ f_decr hx)
    push_neg at h'
    by_contra' H
    have not_bot : ¬ IsBot F.limsSup := fun maybe_bot ↦
      lt_irrefl (F.liminf f) <| lt_of_le_of_lt
        (liminf_le_of_frequently_le (frequently_of_forall (fun r ↦ f_decr (maybe_bot r)))
          (bdd_above.isBoundedUnder f_decr)) H
    obtain ⟨l, l_lt, h'l⟩ : ∃ l < F.limsSup, Set.Ioc l F.limsSup ⊆ { x : R | f x < F.liminf f }
    · apply exists_Ioc_subset_of_mem_nhds ((tendsto_order.1 f_cont.tendsto).2 _ H)
      simpa [IsBot] using not_bot
    obtain ⟨m, l_m, m_lt⟩ : (Set.Ioo l F.limsSup).Nonempty := by
      contrapose! h'
      refine' ⟨l, l_lt, by rwa [Set.not_nonempty_iff_eq_empty] at h'⟩
    have B : F.liminf f ≤ f m := by
      apply liminf_le_of_frequently_le _ _
      · apply (frequently_lt_of_lt_limsSup cobdd m_lt).mono
        exact fun x hx ↦ f_decr hx.le
      · exact IsBounded.isBoundedUnder f_decr bdd_above
    have I : f m < F.liminf f := h'l ⟨l_m, m_lt.le⟩
    exact lt_irrefl _ (B.trans_lt I)
set_option linter.uppercaseLean3 false in
#align antitone.map_Limsup_of_continuous_at Antitone.map_limsSup_of_continuousAt

/-- A continuous antitone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsup` to the `Filter.liminf` of the images (if the filter is bounded from above and
below). -/
theorem Antitone.map_limsup_of_continuousAt {f : R → S} (f_decr : Antitone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.limsup a))
    (bdd_above : F.IsBoundedUnder (· ≤ ·) a := by isBoundedDefault)
    (bdd_below : F.IsBoundedUnder (· ≥ ·) a := by isBoundedDefault) :
    f (F.limsup a) = F.liminf (f ∘ a) :=
  f_decr.map_limsSup_of_continuousAt f_cont bdd_above bdd_below
#align antitone.map_limsup_of_continuous_at Antitone.map_limsup_of_continuousAt

/-- An antitone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsInf` to the `Filter.limsup` of the image if the function is continuous at the `limsInf`
(and the filter is bounded from above and below). -/
theorem Antitone.map_limsInf_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_decr : Antitone f) (f_cont : ContinuousAt f F.limsInf)
    (bdd_above : F.IsBounded (· ≤ ·) := by isBoundedDefault)
    (bdd_below : F.IsBounded (· ≥ ·) := by isBoundedDefault) : f F.limsInf = F.limsup f :=
  Antitone.map_limsSup_of_continuousAt (R := Rᵒᵈ) (S := Sᵒᵈ) f_decr.dual f_cont bdd_below bdd_above
set_option linter.uppercaseLean3 false in
#align antitone.map_Liminf_of_continuous_at Antitone.map_limsInf_of_continuousAt

/-- A continuous antitone function between (conditionally) complete linear ordered spaces sends a
`Filter.liminf` to the `Filter.limsup` of the images (if the filter is bounded from above and
below). -/
theorem Antitone.map_liminf_of_continuousAt {f : R → S} (f_decr : Antitone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.liminf a))
    (bdd_above : F.IsBoundedUnder (· ≤ ·) a := by isBoundedDefault)
    (bdd_below : F.IsBoundedUnder (· ≥ ·) a := by isBoundedDefault) :
    f (F.liminf a) = F.limsup (f ∘ a) :=
  f_decr.map_limsInf_of_continuousAt f_cont bdd_above bdd_below
#align antitone.map_liminf_of_continuous_at Antitone.map_liminf_of_continuousAt

/-- A monotone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsSup` to the `Filter.limsup` of the image if the function is continuous at the `limsSup`
(and the filter is bounded from above and below). -/
theorem Monotone.map_limsSup_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_incr : Monotone f) (f_cont : ContinuousAt f F.limsSup)
    (bdd_above : F.IsBounded (· ≤ ·) := by isBoundedDefault)
    (bdd_below : F.IsBounded (· ≥ ·) := by isBoundedDefault) : f F.limsSup = F.limsup f :=
  Antitone.map_limsSup_of_continuousAt (S := Sᵒᵈ) f_incr f_cont bdd_above bdd_below
set_option linter.uppercaseLean3 false in
#align monotone.map_Limsup_of_continuous_at Monotone.map_limsSup_of_continuousAt

/-- A continuous monotone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsup` to the `Filter.limsup` of the images (if the filter is bounded from above and
below). -/
theorem Monotone.map_limsup_of_continuousAt {f : R → S} (f_incr : Monotone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.limsup a))
    (bdd_above : F.IsBoundedUnder (· ≤ ·) a := by isBoundedDefault)
    (bdd_below : F.IsBoundedUnder (· ≥ ·) a := by isBoundedDefault) :
    f (F.limsup a) = F.limsup (f ∘ a) :=
  f_incr.map_limsSup_of_continuousAt f_cont bdd_above bdd_below
#align monotone.map_limsup_of_continuous_at Monotone.map_limsup_of_continuousAt

/-- A monotone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsInf` to the `Filter.liminf` of the image if the function is continuous at the `limsInf`
(and the filter is bounded from above and below). -/
theorem Monotone.map_limsInf_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_incr : Monotone f) (f_cont : ContinuousAt f F.limsInf)
    (bdd_above : F.IsBounded (· ≤ ·) := by isBoundedDefault)
    (bdd_below : F.IsBounded (· ≥ ·) := by isBoundedDefault) : f F.limsInf = F.liminf f :=
  Antitone.map_limsSup_of_continuousAt (R := Rᵒᵈ) f_incr.dual f_cont bdd_below bdd_above
set_option linter.uppercaseLean3 false in
#align monotone.map_Liminf_of_continuous_at Monotone.map_limsInf_of_continuousAt

/-- A continuous monotone function between (conditionally) complete linear ordered spaces sends a
`Filter.liminf` to the `Filter.liminf` of the images (if the filter is bounded from above and
below). -/
theorem Monotone.map_liminf_of_continuousAt {f : R → S} (f_incr : Monotone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.liminf a))
    (bdd_above : F.IsBoundedUnder (· ≤ ·) a := by isBoundedDefault)
    (bdd_below : F.IsBoundedUnder (· ≥ ·) a := by isBoundedDefault) :
    f (F.liminf a) = F.liminf (f ∘ a) :=
  f_incr.map_limsInf_of_continuousAt f_cont bdd_above bdd_below
#align monotone.map_liminf_of_continuous_at Monotone.map_liminf_of_continuousAt

end Monotone

section InfiAndSupr

open Topology

open Filter Set

variable {ι : Type*} {R : Type*} [CompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R]

theorem iInf_eq_of_forall_le_of_tendsto {x : R} {as : ι → R} (x_le : ∀ i, x ≤ as i) {F : Filter ι}
    [Filter.NeBot F] (as_lim : Filter.Tendsto as F (𝓝 x)) : ⨅ i, as i = x := by
  refine' iInf_eq_of_forall_ge_of_forall_gt_exists_lt (fun i ↦ x_le i) _
  apply fun w x_lt_w ↦ ‹Filter.NeBot F›.nonempty_of_mem (eventually_lt_of_tendsto_lt x_lt_w as_lim)
#align infi_eq_of_forall_le_of_tendsto iInf_eq_of_forall_le_of_tendsto

theorem iSup_eq_of_forall_le_of_tendsto {x : R} {as : ι → R} (le_x : ∀ i, as i ≤ x) {F : Filter ι}
    [Filter.NeBot F] (as_lim : Filter.Tendsto as F (𝓝 x)) : ⨆ i, as i = x :=
  iInf_eq_of_forall_le_of_tendsto (R := Rᵒᵈ) le_x as_lim
#align supr_eq_of_forall_le_of_tendsto iSup_eq_of_forall_le_of_tendsto

theorem iUnion_Ici_eq_Ioi_of_lt_of_tendsto {ι : Type*} (x : R) {as : ι → R} (x_lt : ∀ i, x < as i)
    {F : Filter ι} [Filter.NeBot F] (as_lim : Filter.Tendsto as F (𝓝 x)) :
    ⋃ i : ι, Ici (as i) = Ioi x := by
  have obs : x ∉ range as := by
    intro maybe_x_is
    rcases mem_range.mp maybe_x_is with ⟨i, hi⟩
    simpa only [hi, lt_self_iff_false] using x_lt i
  -- Porting note: `rw at *` was too destructive. Let's only rewrite `obs` and the goal.
  have := iInf_eq_of_forall_le_of_tendsto (fun i ↦ (x_lt i).le) as_lim
  rw [← this] at obs
  rw [← this]
  exact iUnion_Ici_eq_Ioi_iInf obs
#align Union_Ici_eq_Ioi_of_lt_of_tendsto iUnion_Ici_eq_Ioi_of_lt_of_tendsto

theorem iUnion_Iic_eq_Iio_of_lt_of_tendsto {ι : Type*} (x : R) {as : ι → R} (lt_x : ∀ i, as i < x)
    {F : Filter ι} [Filter.NeBot F] (as_lim : Filter.Tendsto as F (𝓝 x)) :
    ⋃ i : ι, Iic (as i) = Iio x :=
  iUnion_Ici_eq_Ioi_of_lt_of_tendsto (R := Rᵒᵈ) x lt_x as_lim
#align Union_Iic_eq_Iio_of_lt_of_tendsto iUnion_Iic_eq_Iio_of_lt_of_tendsto

end InfiAndSupr

section Indicator

open BigOperators

theorem limsup_eq_tendsto_sum_indicator_nat_atTop (s : ℕ → Set α) :
    limsup s atTop = { ω | Tendsto
      (fun n ↦ ∑ k in Finset.range n, (s (k + 1)).indicator (1 : α → ℕ) ω) atTop atTop } := by
  ext ω
  simp only [limsup_eq_iInf_iSup_of_nat, ge_iff_le, Set.iSup_eq_iUnion, Set.iInf_eq_iInter,
    Set.mem_iInter, Set.mem_iUnion, exists_prop]
  constructor
  · intro hω
    refine' tendsto_atTop_atTop_of_monotone' (fun n m hnm ↦ Finset.sum_mono_set_of_nonneg
      (fun i ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _) (Finset.range_mono hnm)) _
    rintro ⟨i, h⟩
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff'] at h
    induction' i with k hk
    · obtain ⟨j, hj₁, hj₂⟩ := hω 1
      refine' not_lt.2 (h <| j + 1)
        (lt_of_le_of_lt (Finset.sum_const_zero.symm : 0 = ∑ k in Finset.range (j + 1), 0).le _)
      refine' Finset.sum_lt_sum (fun m _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
        ⟨j - 1, Finset.mem_range.2 (lt_of_le_of_lt (Nat.sub_le _ _) j.lt_succ_self), _⟩
      rw [Nat.sub_add_cancel hj₁, Set.indicator_of_mem hj₂]
      exact zero_lt_one
    · rw [imp_false] at hk
      push_neg at hk
      obtain ⟨i, hi⟩ := hk
      obtain ⟨j, hj₁, hj₂⟩ := hω (i + 1)
      replace hi : (∑ k in Finset.range i, (s (k + 1)).indicator 1 ω) = k + 1 :=
        le_antisymm (h i) hi
      refine' not_lt.2 (h <| j + 1) _
      rw [← Finset.sum_range_add_sum_Ico _ (i.le_succ.trans (hj₁.trans j.le_succ)), hi]
      refine' lt_add_of_pos_right _ _
      rw [(Finset.sum_const_zero.symm : 0 = ∑ k in Finset.Ico i (j + 1), 0)]
      refine' Finset.sum_lt_sum (fun m _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
        ⟨j - 1, Finset.mem_Ico.2 ⟨(Nat.le_sub_iff_add_le (le_trans ((le_add_iff_nonneg_left _).2
          zero_le') hj₁)).2 hj₁, lt_of_le_of_lt (Nat.sub_le _ _) j.lt_succ_self⟩, _⟩
      rw [Nat.sub_add_cancel (le_trans ((le_add_iff_nonneg_left _).2 zero_le') hj₁),
        Set.indicator_of_mem hj₂]
      exact zero_lt_one
  · rintro hω i
    rw [Set.mem_setOf_eq, tendsto_atTop_atTop] at hω
    by_contra hcon
    push_neg at hcon
    obtain ⟨j, h⟩ := hω (i + 1)
    have : (∑ k in Finset.range j, (s (k + 1)).indicator 1 ω) ≤ i := by
      have hle : ∀ j ≤ i, (∑ k in Finset.range j, (s (k + 1)).indicator 1 ω) ≤ i := by
        refine' fun j hij ↦
          (Finset.sum_le_card_nsmul _ _ _ _ : _ ≤ (Finset.range j).card • 1).trans _
        · exact fun m _ ↦ Set.indicator_apply_le' (fun _ ↦ le_rfl) fun _ ↦ zero_le_one
        · simpa only [Finset.card_range, smul_eq_mul, mul_one]
      by_cases hij : j < i
      · exact hle _ hij.le
      · rw [← Finset.sum_range_add_sum_Ico _ (not_lt.1 hij)]
        suffices (∑ k in Finset.Ico i j, (s (k + 1)).indicator 1 ω) = 0 by
          rw [this, add_zero]
          exact hle _ le_rfl
        refine' Finset.sum_eq_zero fun m hm ↦ _
        exact Set.indicator_of_not_mem (hcon _ <| (Finset.mem_Ico.1 hm).1.trans m.le_succ) _
    exact not_le.2 (lt_of_lt_of_le i.lt_succ_self <| h _ le_rfl) this
#align limsup_eq_tendsto_sum_indicator_nat_at_top limsup_eq_tendsto_sum_indicator_nat_atTop

theorem limsup_eq_tendsto_sum_indicator_atTop (R : Type*) [StrictOrderedSemiring R] [Archimedean R]
    (s : ℕ → Set α) : limsup s atTop = { ω | Tendsto
      (fun n ↦ ∑ k in Finset.range n, (s (k + 1)).indicator (1 : α → R) ω) atTop atTop } := by
  rw [limsup_eq_tendsto_sum_indicator_nat_atTop s]
  ext ω
  simp only [Set.mem_setOf_eq]
  rw [(_ : (fun n ↦ ∑ k in Finset.range n, (s (k + 1)).indicator (1 : α → R) ω) = fun n ↦
    ↑(∑ k in Finset.range n, (s (k + 1)).indicator (1 : α → ℕ) ω))]
  · exact tendsto_nat_cast_atTop_iff.symm
  · ext n
    simp only [Set.indicator, Pi.one_apply, Finset.sum_boole, Nat.cast_id]
#align limsup_eq_tendsto_sum_indicator_at_top limsup_eq_tendsto_sum_indicator_atTop

end Indicator

section LiminfLimsupAddSub

variable {R : Type*} [ConditionallyCompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R]

/-- `liminf (c + xᵢ) = c + liminf xᵢ`. -/
lemma limsup_const_add (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [CovariantClass R R (fun x y ↦ x + y) fun x y ↦ x ≤ y] (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.limsup (fun i ↦ c + f i) F = c + Filter.limsup f F :=
  (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ c + x)
    (fun _ _ h ↦ add_le_add_left h c) (continuous_add_left c).continuousAt bdd_above bdd_below).symm

/-- `limsup (xᵢ + c) = (limsup xᵢ) + c`. -/
lemma limsup_add_const (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [CovariantClass R R (Function.swap fun x y ↦ x + y) fun x y ↦ x ≤ y] (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.limsup (fun i ↦ f i + c) F = Filter.limsup f F + c :=
  (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ x + c)
    (fun _ _ h ↦ add_le_add_right h c)
    (continuous_add_right c).continuousAt bdd_above bdd_below).symm

/-- `liminf (c + xᵢ) = c + limsup xᵢ`. -/
lemma liminf_const_add (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [CovariantClass R R (fun x y ↦ x + y) fun x y ↦ x ≤ y]  (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ c + f i) F = c + Filter.liminf f F :=
  (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ c + x)
    (fun _ _ h ↦ add_le_add_left h c) (continuous_add_left c).continuousAt bdd_above bdd_below).symm

/-- `liminf (xᵢ + c) = (liminf xᵢ) + c`. -/
lemma liminf_add_const (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [CovariantClass R R (Function.swap fun x y ↦ x + y) fun x y ↦ x ≤ y] (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ f i + c) F = Filter.liminf f F + c :=
  (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ x + c)
    (fun _ _ h ↦ add_le_add_right h c)
    (continuous_add_right c).continuousAt bdd_above bdd_below).symm

/-- `limsup (c - xᵢ) = c - liminf xᵢ`. -/
lemma limsup_const_sub (F : Filter ι) [NeBot F] [AddCommSemigroup R] [Sub R] [ContinuousSub R]
    [OrderedSub R] [CovariantClass R R (fun x y ↦ x + y) fun x y ↦ x ≤ y] (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.limsup (fun i ↦ c - f i) F = c - Filter.liminf f F :=
  (Antitone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ c - x)
    (fun _ _ h ↦ tsub_le_tsub_left h c)
    (continuous_sub_left c).continuousAt bdd_above bdd_below).symm

/-- `limsup (xᵢ - c) = (limsup xᵢ) - c`. -/
lemma limsup_sub_const (F : Filter ι) [NeBot F] [AddCommSemigroup R] [Sub R] [ContinuousSub R]
    [OrderedSub R] (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.limsup (fun i ↦ f i - c) F = Filter.limsup f F - c :=
  (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ x - c)
    (fun _ _ h ↦ tsub_le_tsub_right h c)
    (continuous_sub_right c).continuousAt bdd_above bdd_below).symm

/-- `liminf (c - xᵢ) = c - limsup xᵢ`. -/
lemma liminf_const_sub (F : Filter ι) [NeBot F] [AddCommSemigroup R] [Sub R] [ContinuousSub R]
    [OrderedSub R] [CovariantClass R R (fun x y ↦ x + y) fun x y ↦ x ≤ y] (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ c - f i) F = c - Filter.limsup f F :=
  (Antitone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ c - x)
    (fun _ _ h ↦ tsub_le_tsub_left h c)
    (continuous_sub_left c).continuousAt bdd_above bdd_below).symm

/-- `liminf (xᵢ - c) = (liminf xᵢ) - c`. -/
lemma liminf_sub_const (F : Filter ι) [NeBot F] [AddCommSemigroup R] [Sub R] [ContinuousSub R]
    [OrderedSub R] (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ f i - c) F = Filter.liminf f F - c :=
  (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ x - c)
    (fun _ _ h ↦ tsub_le_tsub_right h c)
    (continuous_sub_right c).continuousAt bdd_above bdd_below).symm

end LiminfLimsupAddSub -- section
