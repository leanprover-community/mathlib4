/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/

import Mathlib.Topology.Order.LeftRightNhds

/-!
# Properties of LUB and GLB in an order topology
-/

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α γ : Type*}

section OrderTopology

variable [TopologicalSpace α] [LinearOrder α] [OrderTopology α]

theorem IsLUB.frequently_mem {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty) :
    ∃ᶠ x in 𝓝[≤] a, x ∈ s := by
  rcases hs with ⟨a', ha'⟩
  intro h
  rcases (ha.1 ha').eq_or_lt with (rfl | ha'a)
  · exact h.self_of_nhdsWithin le_rfl ha'
  · rcases (mem_nhdsLE_iff_exists_Ioc_subset' ha'a).1 h with ⟨b, hba, hb⟩
    rcases ha.exists_between hba with ⟨b', hb's, hb'⟩
    exact hb hb' hb's

theorem IsLUB.frequently_nhds_mem {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty) :
    ∃ᶠ x in 𝓝 a, x ∈ s :=
  (ha.frequently_mem hs).filter_mono inf_le_left

theorem IsGLB.frequently_mem {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty) :
    ∃ᶠ x in 𝓝[≥] a, x ∈ s :=
  IsLUB.frequently_mem (α := αᵒᵈ) ha hs

theorem IsGLB.frequently_nhds_mem {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty) :
    ∃ᶠ x in 𝓝 a, x ∈ s :=
  (ha.frequently_mem hs).filter_mono inf_le_left

theorem IsLUB.mem_closure {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty) : a ∈ closure s :=
  (ha.frequently_nhds_mem hs).mem_closure

theorem IsGLB.mem_closure {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty) : a ∈ closure s :=
  (ha.frequently_nhds_mem hs).mem_closure

theorem IsLUB.nhdsWithin_neBot {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty) :
    NeBot (𝓝[s] a) :=
  mem_closure_iff_nhdsWithin_neBot.1 (ha.mem_closure hs)

theorem IsGLB.nhdsWithin_neBot {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty) :
    NeBot (𝓝[s] a) :=
  IsLUB.nhdsWithin_neBot (α := αᵒᵈ) ha hs

theorem isLUB_of_mem_nhds {s : Set α} {a : α} {f : Filter α} (hsa : a ∈ upperBounds s) (hsf : s ∈ f)
    [NeBot (f ⊓ 𝓝 a)] : IsLUB s a :=
  ⟨hsa, fun b hb =>
    not_lt.1 fun hba =>
      have : s ∩ { a | b < a } ∈ f ⊓ 𝓝 a := inter_mem_inf hsf (IsOpen.mem_nhds (isOpen_lt' _) hba)
      let ⟨_x, ⟨hxs, hxb⟩⟩ := Filter.nonempty_of_mem this
      have : b < b := lt_of_lt_of_le hxb <| hb hxs
      lt_irrefl b this⟩

theorem isLUB_of_mem_closure {s : Set α} {a : α} (hsa : a ∈ upperBounds s) (hsf : a ∈ closure s) :
    IsLUB s a := by
  rw [mem_closure_iff_clusterPt, ClusterPt, inf_comm] at hsf
  exact isLUB_of_mem_nhds hsa (mem_principal_self s)

theorem isGLB_of_mem_nhds {s : Set α} {a : α} {f : Filter α} (hsa : a ∈ lowerBounds s) (hsf : s ∈ f)
    [NeBot (f ⊓ 𝓝 a)] :
    IsGLB s a :=
  isLUB_of_mem_nhds (α := αᵒᵈ) hsa hsf

theorem isGLB_of_mem_closure {s : Set α} {a : α} (hsa : a ∈ lowerBounds s) (hsf : a ∈ closure s) :
    IsGLB s a :=
  isLUB_of_mem_closure (α := αᵒᵈ) hsa hsf

theorem IsLUB.mem_upperBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
    {f : α → γ} {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) (ha : IsLUB s a)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b ∈ upperBounds (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  replace ha := ha.inter_Ici_of_mem hx
  haveI := ha.nhdsWithin_neBot ⟨x, hx, le_rfl⟩
  refine ge_of_tendsto (hb.mono_left (nhdsWithin_mono a (inter_subset_left (t := Ici x)))) ?_
  exact mem_of_superset self_mem_nhdsWithin fun y hy => hf hx hy.1 hy.2

-- For a version of this theorem in which the convergence considered on the domain `α` is as `x : α`
-- tends to infinity, rather than tending to a point `x` in `α`, see `isLUB_of_tendsto_atTop`
theorem IsLUB.isLUB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α → γ}
    {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) (ha : IsLUB s a) (hs : s.Nonempty)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : IsLUB (f '' s) b :=
  haveI := ha.nhdsWithin_neBot hs
  ⟨ha.mem_upperBounds_of_tendsto hf hb, fun _b' hb' =>
    le_of_tendsto hb (mem_of_superset self_mem_nhdsWithin fun _ hx => hb' <| mem_image_of_mem _ hx)⟩

theorem IsGLB.mem_lowerBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
    {f : α → γ} {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) (ha : IsGLB s a)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b ∈ lowerBounds (f '' s) :=
  IsLUB.mem_upperBounds_of_tendsto (α := αᵒᵈ) (γ := γᵒᵈ) hf.dual ha hb

-- For a version of this theorem in which the convergence considered on the domain `α` is as
-- `x : α` tends to negative infinity, rather than tending to a point `x` in `α`, see
-- `isGLB_of_tendsto_atBot`
theorem IsGLB.isGLB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α → γ}
    {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) :
    IsGLB s a → s.Nonempty → Tendsto f (𝓝[s] a) (𝓝 b) → IsGLB (f '' s) b :=
  IsLUB.isLUB_of_tendsto (α := αᵒᵈ) (γ := γᵒᵈ) hf.dual

theorem IsLUB.mem_lowerBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
    {f : α → γ} {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) (ha : IsLUB s a)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b ∈ lowerBounds (f '' s) :=
  IsLUB.mem_upperBounds_of_tendsto (γ := γᵒᵈ) hf ha hb

theorem IsLUB.isGLB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α → γ}
    {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) (ha : IsLUB s a) (hs : s.Nonempty)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : IsGLB (f '' s) b :=
  IsLUB.isLUB_of_tendsto (γ := γᵒᵈ) hf ha hs hb

theorem IsGLB.mem_upperBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
    {f : α → γ} {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) (ha : IsGLB s a)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b ∈ upperBounds (f '' s) :=
  IsGLB.mem_lowerBounds_of_tendsto (γ := γᵒᵈ) hf ha hb

theorem IsGLB.isLUB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α → γ}
    {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) (ha : IsGLB s a) (hs : s.Nonempty)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : IsLUB (f '' s) b :=
  IsGLB.isGLB_of_tendsto (γ := γᵒᵈ) hf ha hs hb

theorem IsLUB.mem_of_isClosed {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty)
    (sc : IsClosed s) : a ∈ s :=
  sc.closure_subset <| ha.mem_closure hs

alias IsClosed.isLUB_mem := IsLUB.mem_of_isClosed

theorem IsGLB.mem_of_isClosed {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty)
    (sc : IsClosed s) : a ∈ s :=
  sc.closure_subset <| ha.mem_closure hs

alias IsClosed.isGLB_mem := IsGLB.mem_of_isClosed

theorem isLUB_iff_of_subset_of_subset_closure {α : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIicTopology α] {s t : Set α} (hst : s ⊆ t) (hts : t ⊆ closure s) {x : α} :
    IsLUB s x ↔ IsLUB t x :=
  isLUB_congr <| (upperBounds_closure (s := s) ▸ upperBounds_mono_set hts).antisymm <|
    upperBounds_mono_set hst

theorem isGLB_iff_of_subset_of_subset_closure {α : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIciTopology α] {s t : Set α} (hst : s ⊆ t) (hts : t ⊆ closure s) {x : α} :
    IsGLB s x ↔ IsGLB t x :=
  isLUB_iff_of_subset_of_subset_closure (α := αᵒᵈ) hst hts

theorem Dense.isLUB_inter_iff {α : Type*} [TopologicalSpace α] [Preorder α] [ClosedIicTopology α]
    {s t : Set α} (hs : Dense s) (ht : IsOpen t) {x : α} :
    IsLUB (t ∩ s) x ↔ IsLUB t x :=
  isLUB_iff_of_subset_of_subset_closure (by simp) <| hs.open_subset_closure_inter ht

theorem Dense.isGLB_inter_iff {α : Type*} [TopologicalSpace α] [Preorder α] [ClosedIciTopology α]
    {s t : Set α} (hs : Dense s) (ht : IsOpen t) {x : α} :
    IsGLB (t ∩ s) x ↔ IsGLB t x :=
  hs.isLUB_inter_iff (α := αᵒᵈ) ht

/-!
### Existence of sequences tending to `sInf` or `sSup` of a given set
-/

theorem IsLUB.exists_seq_strictMono_tendsto_of_notMem {t : Set α} {x : α}
    [IsCountablyGenerated (𝓝 x)] (htx : IsLUB t x) (notMem : x ∉ t) (ht : t.Nonempty) :
    ∃ u : ℕ → α, StrictMono u ∧ (∀ n, u n < x) ∧ Tendsto u atTop (𝓝 x) ∧ ∀ n, u n ∈ t := by
  obtain ⟨v, hvx, hvt⟩ := exists_seq_forall_of_frequently (htx.frequently_mem ht)
  replace hvx := hvx.mono_right nhdsWithin_le_nhds
  have hvx' : ∀ {n}, v n < x := (htx.1 (hvt _)).lt_of_ne (ne_of_mem_of_not_mem (hvt _) notMem)
  have : ∀ k, ∀ᶠ l in atTop, v k < v l := fun k => hvx.eventually (lt_mem_nhds hvx')
  choose N hN hvN using fun k => ((eventually_gt_atTop k).and (this k)).exists
  refine ⟨fun k => v (N^[k] 0), strictMono_nat_of_lt_succ fun _ => ?_, fun _ => hvx',
    hvx.comp (strictMono_nat_of_lt_succ fun _ => ?_).tendsto_atTop, fun _ => hvt _⟩
  · rw [iterate_succ_apply']; exact hvN _
  · rw [iterate_succ_apply']; exact hN _

@[deprecated (since := "2025-05-23")]
alias IsLUB.exists_seq_strictMono_tendsto_of_not_mem :=
  IsLUB.exists_seq_strictMono_tendsto_of_notMem

theorem IsLUB.exists_seq_monotone_tendsto {t : Set α} {x : α} [IsCountablyGenerated (𝓝 x)]
    (htx : IsLUB t x) (ht : t.Nonempty) :
    ∃ u : ℕ → α, Monotone u ∧ (∀ n, u n ≤ x) ∧ Tendsto u atTop (𝓝 x) ∧ ∀ n, u n ∈ t := by
  by_cases h : x ∈ t
  · exact ⟨fun _ => x, monotone_const, fun n => le_rfl, tendsto_const_nhds, fun _ => h⟩
  · rcases htx.exists_seq_strictMono_tendsto_of_notMem h ht with ⟨u, hu⟩
    exact ⟨u, hu.1.monotone, fun n => (hu.2.1 n).le, hu.2.2⟩

theorem exists_seq_strictMono_tendsto' {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [DenselyOrdered α] [OrderTopology α] [FirstCountableTopology α] {x y : α} (hy : y < x) :
    ∃ u : ℕ → α, StrictMono u ∧ (∀ n, u n ∈ Ioo y x) ∧ Tendsto u atTop (𝓝 x) := by
  have hx : x ∉ Ioo y x := fun h => (lt_irrefl x h.2).elim
  have ht : Set.Nonempty (Ioo y x) := nonempty_Ioo.2 hy
  rcases (isLUB_Ioo hy).exists_seq_strictMono_tendsto_of_notMem hx ht with ⟨u, hu⟩
  exact ⟨u, hu.1, hu.2.2.symm⟩

theorem exists_seq_strictMono_tendsto [DenselyOrdered α] [NoMinOrder α] [FirstCountableTopology α]
    (x : α) : ∃ u : ℕ → α, StrictMono u ∧ (∀ n, u n < x) ∧ Tendsto u atTop (𝓝 x) := by
  obtain ⟨y, hy⟩ : ∃ y, y < x := exists_lt x
  rcases exists_seq_strictMono_tendsto' hy with ⟨u, hu_mono, hu_mem, hux⟩
  exact ⟨u, hu_mono, fun n => (hu_mem n).2, hux⟩

theorem exists_seq_strictMono_tendsto_nhdsWithin [DenselyOrdered α] [NoMinOrder α]
    [FirstCountableTopology α] (x : α) :
    ∃ u : ℕ → α, StrictMono u ∧ (∀ n, u n < x) ∧ Tendsto u atTop (𝓝[<] x) :=
  let ⟨u, hu, hx, h⟩ := exists_seq_strictMono_tendsto x
  ⟨u, hu, hx, tendsto_nhdsWithin_mono_right (range_subset_iff.2 hx) <| tendsto_nhdsWithin_range.2 h⟩

theorem exists_seq_tendsto_sSup {α : Type*} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [FirstCountableTopology α] {S : Set α} (hS : S.Nonempty)
    (hS' : BddAbove S) : ∃ u : ℕ → α, Monotone u ∧ Tendsto u atTop (𝓝 (sSup S)) ∧ ∀ n, u n ∈ S := by
  rcases (isLUB_csSup hS hS').exists_seq_monotone_tendsto hS with ⟨u, hu⟩
  exact ⟨u, hu.1, hu.2.2⟩

theorem Dense.exists_seq_strictMono_tendsto_of_lt [DenselyOrdered α] [FirstCountableTopology α]
    {s : Set α} (hs : Dense s) {x y : α} (hy : y < x) :
    ∃ u : ℕ → α, StrictMono u ∧ (∀ n, u n ∈ (Ioo y x ∩ s)) ∧ Tendsto u atTop (𝓝 x) := by
  have hnonempty : (Ioo y x ∩ s).Nonempty := by
    obtain ⟨z, hyz, hzx⟩ := hs.exists_between hy
    exact ⟨z, mem_inter hzx hyz⟩
  have hx : IsLUB (Ioo y x ∩ s) x := hs.isLUB_inter_iff isOpen_Ioo |>.mpr <| isLUB_Ioo hy
  apply hx.exists_seq_strictMono_tendsto_of_notMem (by simp) hnonempty |>.imp
  simp_all

theorem Dense.exists_seq_strictMono_tendsto [DenselyOrdered α] [NoMinOrder α]
    [FirstCountableTopology α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ u : ℕ → α, StrictMono u ∧ (∀ n, u n ∈ (Iio x ∩ s)) ∧ Tendsto u atTop (𝓝 x) := by
  obtain ⟨y, hy⟩ := exists_lt x
  apply hs.exists_seq_strictMono_tendsto_of_lt (exists_lt x).choose_spec |>.imp
  simp_all

theorem DenseRange.exists_seq_strictMono_tendsto_of_lt {β : Type*} [LinearOrder β]
    [DenselyOrdered α] [FirstCountableTopology α] {f : β → α} {x y : α} (hf : DenseRange f)
    (hmono : Monotone f) (hlt : y < x) :
    ∃ u : ℕ → β, StrictMono u ∧ (∀ n, f (u n) ∈ Ioo y x) ∧ Tendsto (f ∘ u) atTop (𝓝 x) := by
  rcases Dense.exists_seq_strictMono_tendsto_of_lt hf hlt with ⟨u, hu, huyxf, hlim⟩
  have huyx (n : ℕ) : u n ∈ Ioo y x := (huyxf n).1
  have huf (n : ℕ) : u n ∈ range f := (huyxf n).2
  choose v hv using huf
  obtain rfl : f ∘ v = u := funext hv
  exact ⟨v, fun a b hlt ↦ hmono.reflect_lt <| hu hlt, huyx, hlim⟩

theorem DenseRange.exists_seq_strictMono_tendsto {β : Type*} [LinearOrder β] [DenselyOrdered α]
    [NoMinOrder α] [FirstCountableTopology α] {f : β → α} (hf : DenseRange f) (hmono : Monotone f)
    (x : α) :
    ∃ u : ℕ → β, StrictMono u ∧ (∀ n, f (u n) ∈ Iio x) ∧ Tendsto (f ∘ u) atTop (𝓝 x) := by
  rcases Dense.exists_seq_strictMono_tendsto hf x with ⟨u, hu, huxf, hlim⟩
  have hux (n : ℕ) : u n ∈ Iio x := (huxf n).1
  have huf (n : ℕ) : u n ∈ range f := (huxf n).2
  choose v hv using huf
  obtain rfl : f ∘ v = u := funext hv
  exact ⟨v, fun a b hlt ↦ hmono.reflect_lt <| hu hlt, hux, hlim⟩

theorem IsGLB.exists_seq_strictAnti_tendsto_of_notMem {t : Set α} {x : α}
    [IsCountablyGenerated (𝓝 x)] (htx : IsGLB t x) (notMem : x ∉ t) (ht : t.Nonempty) :
    ∃ u : ℕ → α, StrictAnti u ∧ (∀ n, x < u n) ∧ Tendsto u atTop (𝓝 x) ∧ ∀ n, u n ∈ t :=
  IsLUB.exists_seq_strictMono_tendsto_of_notMem (α := αᵒᵈ) htx notMem ht

@[deprecated (since := "2025-05-23")]
alias IsGLB.exists_seq_strictAnti_tendsto_of_not_mem :=
  IsGLB.exists_seq_strictAnti_tendsto_of_notMem

theorem IsGLB.exists_seq_antitone_tendsto {t : Set α} {x : α} [IsCountablyGenerated (𝓝 x)]
    (htx : IsGLB t x) (ht : t.Nonempty) :
    ∃ u : ℕ → α, Antitone u ∧ (∀ n, x ≤ u n) ∧ Tendsto u atTop (𝓝 x) ∧ ∀ n, u n ∈ t :=
  IsLUB.exists_seq_monotone_tendsto (α := αᵒᵈ) htx ht

theorem exists_seq_strictAnti_tendsto' [DenselyOrdered α] [FirstCountableTopology α] {x y : α}
    (hy : x < y) : ∃ u : ℕ → α, StrictAnti u ∧ (∀ n, u n ∈ Ioo x y) ∧ Tendsto u atTop (𝓝 x) := by
  simpa using exists_seq_strictMono_tendsto' (α := αᵒᵈ) (OrderDual.toDual_lt_toDual.2 hy)

theorem exists_seq_strictAnti_tendsto [DenselyOrdered α] [NoMaxOrder α] [FirstCountableTopology α]
    (x : α) : ∃ u : ℕ → α, StrictAnti u ∧ (∀ n, x < u n) ∧ Tendsto u atTop (𝓝 x) :=
  exists_seq_strictMono_tendsto (α := αᵒᵈ) x

theorem exists_seq_strictAnti_tendsto_nhdsWithin [DenselyOrdered α] [NoMaxOrder α]
    [FirstCountableTopology α] (x : α) :
    ∃ u : ℕ → α, StrictAnti u ∧ (∀ n, x < u n) ∧ Tendsto u atTop (𝓝[>] x) :=
  exists_seq_strictMono_tendsto_nhdsWithin (α := αᵒᵈ) _

theorem exists_seq_strictAnti_strictMono_tendsto [DenselyOrdered α] [FirstCountableTopology α]
    {x y : α} (h : x < y) :
    ∃ u v : ℕ → α, StrictAnti u ∧ StrictMono v ∧ (∀ k, u k ∈ Ioo x y) ∧ (∀ l, v l ∈ Ioo x y) ∧
      (∀ k l, u k < v l) ∧ Tendsto u atTop (𝓝 x) ∧ Tendsto v atTop (𝓝 y) := by
  rcases exists_seq_strictAnti_tendsto' h with ⟨u, hu_anti, hu_mem, hux⟩
  rcases exists_seq_strictMono_tendsto' (hu_mem 0).2 with ⟨v, hv_mono, hv_mem, hvy⟩
  exact
    ⟨u, v, hu_anti, hv_mono, hu_mem, fun l => ⟨(hu_mem 0).1.trans (hv_mem l).1, (hv_mem l).2⟩,
      fun k l => (hu_anti.antitone (zero_le k)).trans_lt (hv_mem l).1, hux, hvy⟩

theorem exists_seq_tendsto_sInf {α : Type*} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [FirstCountableTopology α] {S : Set α} (hS : S.Nonempty)
    (hS' : BddBelow S) : ∃ u : ℕ → α, Antitone u ∧ Tendsto u atTop (𝓝 (sInf S)) ∧ ∀ n, u n ∈ S :=
  exists_seq_tendsto_sSup (α := αᵒᵈ) hS hS'

theorem Dense.exists_seq_strictAnti_tendsto_of_lt [DenselyOrdered α] [FirstCountableTopology α]
    {s : Set α} (hs : Dense s) {x y : α} (hy : x < y) :
    ∃ u : ℕ → α, StrictAnti u ∧ (∀ n, u n ∈ (Ioo x y ∩ s)) ∧ Tendsto u atTop (𝓝 x) := by
  simpa using hs.exists_seq_strictMono_tendsto_of_lt (α := αᵒᵈ) (OrderDual.toDual_lt_toDual.2 hy)

theorem Dense.exists_seq_strictAnti_tendsto [DenselyOrdered α] [NoMaxOrder α]
    [FirstCountableTopology α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ u : ℕ → α, StrictAnti u ∧ (∀ n, u n ∈ (Ioi x ∩ s)) ∧ Tendsto u atTop (𝓝 x) :=
  hs.exists_seq_strictMono_tendsto (α := αᵒᵈ) x

theorem DenseRange.exists_seq_strictAnti_tendsto_of_lt {β : Type*} [LinearOrder β]
    [DenselyOrdered α] [FirstCountableTopology α] {f : β → α} {x y : α} (hf : DenseRange f)
    (hmono : Monotone f) (hlt : x < y) :
    ∃ u : ℕ → β, StrictAnti u ∧ (∀ n, f (u n) ∈ Ioo x y) ∧ Tendsto (f ∘ u) atTop (𝓝 x) := by
  simpa using hf.exists_seq_strictMono_tendsto_of_lt (α := αᵒᵈ) (β := βᵒᵈ) hmono.dual
    (OrderDual.toDual_lt_toDual.2 hlt)

theorem DenseRange.exists_seq_strictAnti_tendsto {β : Type*} [LinearOrder β] [DenselyOrdered α]
    [NoMaxOrder α] [FirstCountableTopology α] {f : β → α} (hf : DenseRange f) (hmono : Monotone f)
    (x : α) :
    ∃ u : ℕ → β, StrictAnti u ∧ (∀ n, f (u n) ∈ Ioi x) ∧ Tendsto (f ∘ u) atTop (𝓝 x) :=
  hf.exists_seq_strictMono_tendsto (α := αᵒᵈ) (β := βᵒᵈ) hmono.dual x

end OrderTopology
