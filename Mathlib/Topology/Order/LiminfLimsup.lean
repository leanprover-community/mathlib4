/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Order.Filter.CountableInter
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Order.Monotone

/-!
# Lemmas about liminf and limsup in an order topology.

## Main declarations

* `BoundedLENhdsClass`: Typeclass stating that neighborhoods are eventually bounded above.
* `BoundedGENhdsClass`: Typeclass stating that neighborhoods are eventually bounded below.

## Implementation notes

The same lemmas are true in `ℝ`, `ℝ × ℝ`, `ι → ℝ`, `EuclideanSpace ι ℝ`. To avoid code
duplication, we provide an ad hoc axiomatisation of the properties we need.
-/

@[expose] public section

open Filter TopologicalSpace
open scoped Topology

universe u v

variable {ι α β R S : Type*} {π : ι → Type*}

/-- Ad hoc typeclass stating that neighborhoods are eventually bounded above. -/
class BoundedLENhdsClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· ≤ ·)

/-- Ad hoc typeclass stating that neighborhoods are eventually bounded below. -/
class BoundedGENhdsClass (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· ≥ ·)

section Preorder
variable [Preorder α] [Preorder β] [TopologicalSpace α] [TopologicalSpace β]

section BoundedLENhdsClass
variable [BoundedLENhdsClass α] [BoundedLENhdsClass β] {f : Filter ι} {u : ι → α} {a : α}

theorem isBounded_le_nhds (a : α) : (𝓝 a).IsBounded (· ≤ ·) :=
  BoundedLENhdsClass.isBounded_le_nhds _

theorem Filter.Tendsto.isBoundedUnder_le (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· ≤ ·) u :=
  (isBounded_le_nhds a).mono h

theorem Filter.Tendsto.bddAbove_range_of_cofinite [IsDirected α (· ≤ ·)]
    (h : Tendsto u cofinite (𝓝 a)) : BddAbove (Set.range u) :=
  h.isBoundedUnder_le.bddAbove_range_of_cofinite

theorem Filter.Tendsto.bddAbove_range [IsDirected α (· ≤ ·)] {u : ℕ → α}
    (h : Tendsto u atTop (𝓝 a)) : BddAbove (Set.range u) :=
  h.isBoundedUnder_le.bddAbove_range

theorem isCobounded_ge_nhds (a : α) : (𝓝 a).IsCobounded (· ≥ ·) :=
  (isBounded_le_nhds a).isCobounded_flip

theorem Filter.Tendsto.isCoboundedUnder_ge [NeBot f] (h : Tendsto u f (𝓝 a)) :
    f.IsCoboundedUnder (· ≥ ·) u :=
  h.isBoundedUnder_le.isCobounded_flip

instance : BoundedGENhdsClass αᵒᵈ := ⟨@isBounded_le_nhds α _ _ _⟩

instance Prod.instBoundedLENhdsClass : BoundedLENhdsClass (α × β) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨a, ha⟩ := isBounded_le_nhds x.1
  obtain ⟨b, hb⟩ := isBounded_le_nhds x.2
  rw [← @Prod.mk.eta _ _ x, nhds_prod_eq]
  exact ⟨(a, b), ha.prod_mk hb⟩

instance Pi.instBoundedLENhdsClass [Finite ι] [∀ i, Preorder (π i)] [∀ i, TopologicalSpace (π i)]
    [∀ i, BoundedLENhdsClass (π i)] : BoundedLENhdsClass (∀ i, π i) := by
  refine ⟨fun x ↦ ?_⟩
  rw [nhds_pi]
  choose f hf using fun i ↦ isBounded_le_nhds (x i)
  exact ⟨f, eventually_pi hf⟩

end BoundedLENhdsClass

section BoundedGENhdsClass
variable [BoundedGENhdsClass α] [BoundedGENhdsClass β] {f : Filter ι} {u : ι → α} {a : α}

theorem isBounded_ge_nhds (a : α) : (𝓝 a).IsBounded (· ≥ ·) :=
  BoundedGENhdsClass.isBounded_ge_nhds _

theorem Filter.Tendsto.isBoundedUnder_ge (h : Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· ≥ ·) u :=
  (isBounded_ge_nhds a).mono h

theorem Filter.Tendsto.bddBelow_range_of_cofinite [IsDirected α (· ≥ ·)]
    (h : Tendsto u cofinite (𝓝 a)) : BddBelow (Set.range u) :=
  h.isBoundedUnder_ge.bddBelow_range_of_cofinite

theorem Filter.Tendsto.bddBelow_range [IsDirected α (· ≥ ·)] {u : ℕ → α}
    (h : Tendsto u atTop (𝓝 a)) : BddBelow (Set.range u) :=
  h.isBoundedUnder_ge.bddBelow_range

theorem isCobounded_le_nhds (a : α) : (𝓝 a).IsCobounded (· ≤ ·) :=
  (isBounded_ge_nhds a).isCobounded_flip

theorem Filter.Tendsto.isCoboundedUnder_le [NeBot f] (h : Tendsto u f (𝓝 a)) :
    f.IsCoboundedUnder (· ≤ ·) u :=
  h.isBoundedUnder_ge.isCobounded_flip

instance : BoundedLENhdsClass αᵒᵈ := ⟨@isBounded_ge_nhds α _ _ _⟩

instance Prod.instBoundedGENhdsClass : BoundedGENhdsClass (α × β) :=
  ⟨(Prod.instBoundedLENhdsClass (α := αᵒᵈ) (β := βᵒᵈ)).isBounded_le_nhds⟩

instance Pi.instBoundedGENhdsClass [Finite ι] [∀ i, Preorder (π i)] [∀ i, TopologicalSpace (π i)]
    [∀ i, BoundedGENhdsClass (π i)] : BoundedGENhdsClass (∀ i, π i) :=
  ⟨(Pi.instBoundedLENhdsClass (π := fun i ↦ (π i)ᵒᵈ)).isBounded_le_nhds⟩

end BoundedGENhdsClass

-- See note [lower instance priority]
instance (priority := 100) OrderTop.to_BoundedLENhdsClass [OrderTop α] : BoundedLENhdsClass α :=
  ⟨fun _a ↦ isBounded_le_of_top⟩

-- See note [lower instance priority]
instance (priority := 100) OrderBot.to_BoundedGENhdsClass [OrderBot α] : BoundedGENhdsClass α :=
  ⟨fun _a ↦ isBounded_ge_of_bot⟩

end Preorder

-- See note [lower instance priority]
instance (priority := 100) BoundedLENhdsClass.of_closedIciTopology [LinearOrder α]
    [TopologicalSpace α] [ClosedIciTopology α] : BoundedLENhdsClass α :=
  ⟨fun a ↦ ((isTop_or_exists_gt a).elim fun h ↦ ⟨a, Eventually.of_forall h⟩) <|
    Exists.imp fun _b ↦ eventually_le_nhds⟩

-- See note [lower instance priority]
instance (priority := 100) BoundedGENhdsClass.of_closedIicTopology [LinearOrder α]
    [TopologicalSpace α] [ClosedIicTopology α] : BoundedGENhdsClass α :=
  inferInstanceAs <| BoundedGENhdsClass αᵒᵈᵒᵈ

section LiminfLimsup

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]

/-- If the liminf and the limsup of a filter coincide, then this filter converges to
their common value, at least if the filter is eventually bounded above and below. -/
theorem le_nhds_of_limsSup_eq_limsInf {f : Filter α} {a : α} (hl : f.IsBounded (· ≤ ·))
    (hg : f.IsBounded (· ≥ ·)) (hs : f.limsSup = a) (hi : f.limsInf = a) : f ≤ 𝓝 a :=
  tendsto_order.2 ⟨fun _ hb ↦ gt_mem_sets_of_limsInf_gt hg <| hi.symm ▸ hb,
    fun _ hb ↦ lt_mem_sets_of_limsSup_lt hl <| hs.symm ▸ hb⟩

theorem limsSup_nhds (a : α) : limsSup (𝓝 a) = a :=
  csInf_eq_of_forall_ge_of_forall_gt_exists_lt (isBounded_le_nhds a)
    (fun a' (h : { n : α | n ≤ a' } ∈ 𝓝 a) ↦ show a ≤ a' from @mem_of_mem_nhds _ _ a _ h)
    fun b (hba : a < b) ↦
    show ∃ c, { n : α | n ≤ c } ∈ 𝓝 a ∧ c < b from
      match dense_or_discrete a b with
      | Or.inl ⟨c, hac, hcb⟩ => ⟨c, ge_mem_nhds hac, hcb⟩
      | Or.inr ⟨_, h⟩ => ⟨a, (𝓝 a).sets_of_superset (gt_mem_nhds hba) h, hba⟩

theorem limsInf_nhds (a : α) : limsInf (𝓝 a) = a :=
  limsSup_nhds (α := αᵒᵈ) a

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

/-- If a filter is converging, its liminf coincides with its limit. -/
theorem limsSup_eq_of_le_nhds {f : Filter α} {a : α} [NeBot f] (h : f ≤ 𝓝 a) : f.limsSup = a :=
  limsInf_eq_of_le_nhds (α := αᵒᵈ) h

/-- If a function has a limit, then its limsup coincides with its limit. -/
theorem Filter.Tendsto.limsup_eq {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : limsup u f = a :=
  limsSup_eq_of_le_nhds h

/-- If a function has a limit, then its liminf coincides with its limit. -/
theorem Filter.Tendsto.liminf_eq {f : Filter β} {u : β → α} {a : α} [NeBot f]
    (h : Tendsto u f (𝓝 a)) : liminf u f = a :=
  limsInf_eq_of_le_nhds h

/-- If the liminf and the limsup of a function coincide, then the limit of the function
exists and has the same value. -/
theorem tendsto_of_liminf_eq_limsup {f : Filter β} {u : β → α} {a : α} (hinf : liminf u f = a)
    (hsup : limsup u f = a) (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) : Tendsto u f (𝓝 a) :=
  le_nhds_of_limsSup_eq_limsInf h h' hsup hinf

/-- If a number `a` is less than or equal to the `liminf` of a function `f` at some filter
and is greater than or equal to the `limsup` of `f`, then `f` tends to `a` along this filter. -/
theorem tendsto_of_le_liminf_of_limsup_le {f : Filter β} {u : β → α} {a : α} (hinf : a ≤ liminf u f)
    (hsup : limsup u f ≤ a) (h : f.IsBoundedUnder (· ≤ ·) u := by isBoundedDefault)
    (h' : f.IsBoundedUnder (· ≥ ·) u := by isBoundedDefault) : Tendsto u f (𝓝 a) := by
  rcases f.eq_or_neBot with rfl | _
  · exact tendsto_bot
  · exact tendsto_of_liminf_eq_limsup (le_antisymm (le_trans (liminf_le_limsup h h') hsup) hinf)
      (le_antisymm hsup (le_trans hinf (liminf_le_limsup h h'))) h h'

/-- Assume that, for any `a < b`, a sequence cannot be infinitely many times below `a` and
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
  refine ⟨limsup u f, ?_⟩
  apply tendsto_of_le_liminf_of_limsup_le _ le_rfl h h'
  by_contra! hlt
  obtain ⟨a, ⟨⟨la, au⟩, as⟩⟩ : ∃ a, (f.liminf u < a ∧ a < f.limsup u) ∧ a ∈ s :=
    dense_iff_inter_open.1 hs (Set.Ioo (f.liminf u) (f.limsup u)) isOpen_Ioo
      (Set.nonempty_Ioo.2 hlt)
  obtain ⟨b, ⟨⟨ab, bu⟩, bs⟩⟩ : ∃ b, (a < b ∧ b < f.limsup u) ∧ b ∈ s :=
    dense_iff_inter_open.1 hs (Set.Ioo a (f.limsup u)) isOpen_Ioo (Set.nonempty_Ioo.2 au)
  have A : ∃ᶠ n in f, u n < a := frequently_lt_of_liminf_lt (IsBounded.isCobounded_ge h) la
  have B : ∃ᶠ n in f, b < u n := frequently_lt_of_lt_limsup (IsBounded.isCobounded_le h') bu
  exact H a as b bs ab ⟨A, B⟩

variable [FirstCountableTopology α] {f : Filter β} [CountableInterFilter f] {u : β → α}

theorem eventually_le_limsup (hf : IsBoundedUnder (· ≤ ·) f u := by isBoundedDefault) :
    ∀ᶠ b in f, u b ≤ f.limsup u := by
  obtain ha | ha := isTop_or_exists_gt (f.limsup u)
  · exact Eventually.of_forall fun _ => ha _
  by_cases H : IsGLB (Set.Ioi (f.limsup u)) (f.limsup u)
  · obtain ⟨u, -, -, hua, hu⟩ := H.exists_seq_antitone_tendsto ha
    have := fun n => eventually_lt_of_limsup_lt (hu n) hf
    exact
      (eventually_countable_forall.2 this).mono fun b hb =>
        ge_of_tendsto hua <| Eventually.of_forall fun n => (hb _).le
  · obtain ⟨x, hx, xa⟩ : ∃ x, (∀ ⦃b⦄, f.limsup u < b → x ≤ b) ∧ f.limsup u < x := by
      simp only [IsGLB, IsGreatest, lowerBounds, upperBounds, Set.mem_Ioi, Set.mem_setOf_eq,
        not_and, not_forall, not_le, exists_prop] at H
      exact H fun x => le_of_lt
    filter_upwards [eventually_lt_of_limsup_lt xa hf] with y hy
    contrapose! hy
    exact hx hy

theorem eventually_liminf_le (hf : IsBoundedUnder (· ≥ ·) f u := by isBoundedDefault) :
    ∀ᶠ b in f, f.liminf u ≤ u b :=
  eventually_le_limsup (α := αᵒᵈ) hf

end ConditionallyCompleteLinearOrder

section CompleteLinearOrder

variable [CompleteLinearOrder α] [TopologicalSpace α] [FirstCountableTopology α] [OrderTopology α]
  {f : Filter β} [CountableInterFilter f] {u : β → α}

@[simp]
theorem limsup_eq_bot : f.limsup u = ⊥ ↔ u =ᶠ[f] ⊥ :=
  ⟨fun h =>
    (EventuallyLE.trans eventually_le_limsup <| Eventually.of_forall fun _ => h.le).mono fun _ hx =>
      le_antisymm hx bot_le,
    fun h => by
    rw [limsup_congr h]
    exact limsup_const_bot⟩

@[simp]
theorem liminf_eq_top : f.liminf u = ⊤ ↔ u =ᶠ[f] ⊤ :=
  limsup_eq_bot (α := αᵒᵈ)

end CompleteLinearOrder

end LiminfLimsup

section Monotone

variable {F : Filter ι} [NeBot F]
  [ConditionallyCompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R]
  [ConditionallyCompleteLinearOrder S] [TopologicalSpace S] [OrderTopology S]

/-- An antitone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsSup` to the `Filter.liminf` of the image if the function is continuous at the `limsSup`
(and the filter is bounded from above and frequently bounded from below). -/
theorem Antitone.map_limsSup_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_decr : Antitone f) (f_cont : ContinuousAt f F.limsSup)
    (bdd_above : F.IsBounded (· ≤ ·) := by isBoundedDefault)
    (cobdd : F.IsCobounded (· ≤ ·) := by isBoundedDefault) :
    f F.limsSup = F.liminf f := by
  apply le_antisymm
  · rw [limsSup, f_decr.map_csInf_of_continuousAt f_cont bdd_above cobdd]
    apply le_of_forall_lt
    intro c hc
    simp only [liminf, limsInf, eventually_map] at hc ⊢
    obtain ⟨d, hd, h'd⟩ :=
      exists_lt_of_lt_csSup (bdd_above.recOn fun x hx ↦ ⟨f x, Set.mem_image_of_mem f hx⟩) hc
    apply lt_csSup_of_lt ?_ ?_ h'd
    · simpa only [BddAbove, upperBounds]
        using Antitone.isCoboundedUnder_ge_of_isCobounded f_decr cobdd
    · rcases hd with ⟨e, ⟨he, fe_eq_d⟩⟩
      filter_upwards [he] with x hx using (fe_eq_d.symm ▸ f_decr hx)
  · by_cases! h' : ∃ c, c < F.limsSup ∧ Set.Ioo c F.limsSup = ∅
    · rcases h' with ⟨c, c_lt, hc⟩
      have B : ∃ᶠ n in F, F.limsSup ≤ n := by
        apply (frequently_lt_of_lt_limsSup cobdd c_lt).mono
        intro x hx
        by_contra!
        have : (Set.Ioo c F.limsSup).Nonempty := ⟨x, ⟨hx, this⟩⟩
        simp only [hc, Set.not_nonempty_empty] at this
      apply liminf_le_of_frequently_le _ (bdd_above.isBoundedUnder f_decr)
      exact B.mono fun x hx ↦ f_decr hx
    by_contra! H
    have not_bot : ¬ IsBot F.limsSup := fun maybe_bot ↦
      lt_irrefl (F.liminf f) <| lt_of_le_of_lt
        (liminf_le_of_frequently_le (Frequently.of_forall (fun r ↦ f_decr (maybe_bot r)))
          (bdd_above.isBoundedUnder f_decr)) H
    obtain ⟨l, l_lt, h'l⟩ :
        ∃ l < F.limsSup, Set.Ioc l F.limsSup ⊆ { x : R | f x < F.liminf f } := by
      apply exists_Ioc_subset_of_mem_nhds ((tendsto_order.1 f_cont.tendsto).2 _ H)
      simpa [IsBot] using not_bot
    obtain ⟨m, l_m, m_lt⟩ : (Set.Ioo l F.limsSup).Nonempty := by
      contrapose! h'
      exact ⟨l, l_lt, h'⟩
    have B : F.liminf f ≤ f m := by
      apply liminf_le_of_frequently_le _ _
      · apply (frequently_lt_of_lt_limsSup cobdd m_lt).mono
        exact fun x hx ↦ f_decr hx.le
      · exact IsBounded.isBoundedUnder f_decr bdd_above
    have I : f m < F.liminf f := h'l ⟨l_m, m_lt.le⟩
    exact lt_irrefl _ (B.trans_lt I)

/-- A continuous antitone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsup` to the `Filter.liminf` of the images (if the filter is bounded from above and
frequently bounded from below). -/
theorem Antitone.map_limsup_of_continuousAt {f : R → S} (f_decr : Antitone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.limsup a))
    (bdd_above : F.IsBoundedUnder (· ≤ ·) a := by isBoundedDefault)
    (cobdd : F.IsCoboundedUnder (· ≤ ·) a := by isBoundedDefault) :
    f (F.limsup a) = F.liminf (f ∘ a) :=
  f_decr.map_limsSup_of_continuousAt f_cont bdd_above cobdd

/-- An antitone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsInf` to the `Filter.limsup` of the image if the function is continuous at the `limsInf`
(and the filter is bounded from below and frequently bounded from above). -/
theorem Antitone.map_limsInf_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_decr : Antitone f) (f_cont : ContinuousAt f F.limsInf)
    (cobdd : F.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (bdd_below : F.IsBounded (· ≥ ·) := by isBoundedDefault) : f F.limsInf = F.limsup f :=
  Antitone.map_limsSup_of_continuousAt (R := Rᵒᵈ) (S := Sᵒᵈ) f_decr.dual f_cont bdd_below cobdd

/-- A continuous antitone function between (conditionally) complete linear ordered spaces sends a
`Filter.liminf` to the `Filter.limsup` of the images (if the filter is bounded from below and
frequently bounded from above). -/
theorem Antitone.map_liminf_of_continuousAt {f : R → S} (f_decr : Antitone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.liminf a))
    (cobdd : F.IsCoboundedUnder (· ≥ ·) a := by isBoundedDefault)
    (bdd_below : F.IsBoundedUnder (· ≥ ·) a := by isBoundedDefault) :
    f (F.liminf a) = F.limsup (f ∘ a) :=
  f_decr.map_limsInf_of_continuousAt f_cont cobdd bdd_below

/-- A monotone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsSup` to the `Filter.limsup` of the image if the function is continuous at the `limsSup`
(and the filter is bounded from above and frequently bounded from below). -/
theorem Monotone.map_limsSup_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_incr : Monotone f) (f_cont : ContinuousAt f F.limsSup)
    (bdd_above : F.IsBounded (· ≤ ·) := by isBoundedDefault)
    (cobdd : F.IsCobounded (· ≤ ·) := by isBoundedDefault) : f F.limsSup = F.limsup f :=
  Antitone.map_limsSup_of_continuousAt (S := Sᵒᵈ) f_incr f_cont bdd_above cobdd

/-- A continuous monotone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsup` to the `Filter.limsup` of the images (if the filter is bounded from above and
frequently bounded from below). -/
theorem Monotone.map_limsup_of_continuousAt {f : R → S} (f_incr : Monotone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.limsup a))
    (bdd_above : F.IsBoundedUnder (· ≤ ·) a := by isBoundedDefault)
    (cobdd : F.IsCoboundedUnder (· ≤ ·) a := by isBoundedDefault) :
    f (F.limsup a) = F.limsup (f ∘ a) :=
  f_incr.map_limsSup_of_continuousAt f_cont bdd_above cobdd

/-- A monotone function between (conditionally) complete linear ordered spaces sends a
`Filter.limsInf` to the `Filter.liminf` of the image if the function is continuous at the `limsInf`
(and the filter is bounded from below and frequently bounded from above). -/
theorem Monotone.map_limsInf_of_continuousAt {F : Filter R} [NeBot F] {f : R → S}
    (f_incr : Monotone f) (f_cont : ContinuousAt f F.limsInf)
    (cobdd : F.IsCobounded (· ≥ ·) := by isBoundedDefault)
    (bdd_below : F.IsBounded (· ≥ ·) := by isBoundedDefault) : f F.limsInf = F.liminf f :=
  Antitone.map_limsSup_of_continuousAt (R := Rᵒᵈ) f_incr.dual f_cont bdd_below cobdd

/-- A continuous monotone function between (conditionally) complete linear ordered spaces sends a
`Filter.liminf` to the `Filter.liminf` of the images (if the filter is bounded from below and
frequently bounded from above). -/
theorem Monotone.map_liminf_of_continuousAt {f : R → S} (f_incr : Monotone f) (a : ι → R)
    (f_cont : ContinuousAt f (F.liminf a))
    (cobdd : F.IsCoboundedUnder (· ≥ ·) a := by isBoundedDefault)
    (bdd_below : F.IsBoundedUnder (· ≥ ·) a := by isBoundedDefault) :
    f (F.liminf a) = F.liminf (f ∘ a) :=
  f_incr.map_limsInf_of_continuousAt f_cont cobdd bdd_below

end Monotone

section

variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
  [CompleteLattice β] {f : α → β}

lemma Antitone.liminf_nhdsGT_eq_iSup₂_of_exists_gt (hf : Antitone f) (a : α) (hb : ∃ b, a < b) :
    (𝓝[>] a).liminf f = ⨆ r > a, f r := by
  rw [(nhdsGT_basis_of_exists_gt hb).liminf_eq_iSup_iInf]
  refine le_antisymm (iSup₂_mono' fun r hr ↦ ?_) (iSup₂_mono' fun r hr ↦ ?_)
  · obtain ⟨b, hb⟩ := exists_between hr
    use b, hb.1
    exact iInf₂_le b hb
  · use r, hr
    apply le_iInf
    simp only [Set.mem_Ioo, le_iInf_iff, and_imp]
    intro i hi0 hir
    exact hf hir.le

lemma liminf_nhdsGT_eq_iSup₂ [NoMaxOrder α] (hf : Antitone f) (a : α) :
    (𝓝[>] a).liminf f = ⨆ r > a, f r :=
  hf.liminf_nhdsGT_eq_iSup₂_of_exists_gt a (exists_gt a)

end
