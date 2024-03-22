/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.UniformGroup

/-!
# Infinite sums in topological groups

Lemmas on topological sums in groups (as opposed to monoids).
-/

noncomputable section

open Filter Finset Function

open scoped BigOperators Topology

variable {α β γ δ : Type*}

section TopologicalGroup

variable [AddCommGroup α] [TopologicalSpace α] [TopologicalAddGroup α]
variable {f g : β → α} {a a₁ a₂ : α}

-- `by simpa using` speeds up elaboration. Why?
theorem HasSum.neg (h : HasSum f a) : HasSum (fun b ↦ -f b) (-a) := by
  simpa only using h.map (-AddMonoidHom.id α) continuous_neg
#align has_sum.neg HasSum.neg

theorem Summable.neg (hf : Summable f) : Summable fun b ↦ -f b :=
  hf.hasSum.neg.summable
#align summable.neg Summable.neg

theorem Summable.of_neg (hf : Summable fun b ↦ -f b) : Summable f := by
  simpa only [neg_neg] using hf.neg
#align summable.of_neg Summable.of_neg

theorem summable_neg_iff : (Summable fun b ↦ -f b) ↔ Summable f :=
  ⟨Summable.of_neg, Summable.neg⟩
#align summable_neg_iff summable_neg_iff

theorem HasSum.sub (hf : HasSum f a₁) (hg : HasSum g a₂) :
    HasSum (fun b ↦ f b - g b) (a₁ - a₂) := by
  simp only [sub_eq_add_neg]
  exact hf.add hg.neg
#align has_sum.sub HasSum.sub

theorem Summable.sub (hf : Summable f) (hg : Summable g) : Summable fun b ↦ f b - g b :=
  (hf.hasSum.sub hg.hasSum).summable
#align summable.sub Summable.sub

theorem Summable.trans_sub (hg : Summable g) (hfg : Summable fun b ↦ f b - g b) : Summable f := by
  simpa only [sub_add_cancel] using hfg.add hg
#align summable.trans_sub Summable.trans_sub

theorem summable_iff_of_summable_sub (hfg : Summable fun b ↦ f b - g b) :
    Summable f ↔ Summable g :=
  ⟨fun hf ↦ hf.trans_sub <| by simpa only [neg_sub] using hfg.neg, fun hg ↦ hg.trans_sub hfg⟩
#align summable_iff_of_summable_sub summable_iff_of_summable_sub

theorem HasSum.update (hf : HasSum f a₁) (b : β) [DecidableEq β] (a : α) :
    HasSum (update f b a) (a - f b + a₁) := by
  convert (hasSum_ite_eq b (a - f b)).add hf with b'
  by_cases h : b' = b
  · rw [h, update_same]
    simp [eq_self_iff_true, if_true, sub_add_cancel]
  · simp only [h, update_noteq, if_false, Ne.def, zero_add, not_false_iff]
#align has_sum.update HasSum.update

theorem Summable.update (hf : Summable f) (b : β) [DecidableEq β] (a : α) :
    Summable (update f b a) :=
  (hf.hasSum.update b a).summable
#align summable.update Summable.update

theorem HasSum.hasSum_compl_iff {s : Set β} (hf : HasSum (f ∘ (↑) : s → α) a₁) :
    HasSum (f ∘ (↑) : ↑sᶜ → α) a₂ ↔ HasSum f (a₁ + a₂) := by
  refine' ⟨fun h ↦ hf.add_compl h, fun h ↦ _⟩
  rw [hasSum_subtype_iff_indicator] at hf ⊢
  rw [Set.indicator_compl]
  simpa only [add_sub_cancel_left] using h.sub hf
#align has_sum.has_sum_compl_iff HasSum.hasSum_compl_iff

theorem HasSum.hasSum_iff_compl {s : Set β} (hf : HasSum (f ∘ (↑) : s → α) a₁) :
    HasSum f a₂ ↔ HasSum (f ∘ (↑) : ↑sᶜ → α) (a₂ - a₁) :=
  Iff.symm <| hf.hasSum_compl_iff.trans <| by rw [add_sub_cancel]
#align has_sum.has_sum_iff_compl HasSum.hasSum_iff_compl

theorem Summable.summable_compl_iff {s : Set β} (hf : Summable (f ∘ (↑) : s → α)) :
    Summable (f ∘ (↑) : ↑sᶜ → α) ↔ Summable f :=
  ⟨fun ⟨_, ha⟩ ↦ (hf.hasSum.hasSum_compl_iff.1 ha).summable, fun ⟨_, ha⟩ ↦
    (hf.hasSum.hasSum_iff_compl.1 ha).summable⟩
#align summable.summable_compl_iff Summable.summable_compl_iff

protected theorem Finset.hasSum_compl_iff (s : Finset β) :
    HasSum (fun x : { x // x ∉ s } ↦ f x) a ↔ HasSum f (a + ∑ i in s, f i) :=
  (s.hasSum f).hasSum_compl_iff.trans <| by rw [add_comm]
#align finset.has_sum_compl_iff Finset.hasSum_compl_iff

protected theorem Finset.hasSum_iff_compl (s : Finset β) :
    HasSum f a ↔ HasSum (fun x : { x // x ∉ s } ↦ f x) (a - ∑ i in s, f i) :=
  (s.hasSum f).hasSum_iff_compl
#align finset.has_sum_iff_compl Finset.hasSum_iff_compl

protected theorem Finset.summable_compl_iff (s : Finset β) :
    (Summable fun x : { x // x ∉ s } ↦ f x) ↔ Summable f :=
  (s.summable f).summable_compl_iff
#align finset.summable_compl_iff Finset.summable_compl_iff

theorem Set.Finite.summable_compl_iff {s : Set β} (hs : s.Finite) :
    Summable (f ∘ (↑) : ↑sᶜ → α) ↔ Summable f :=
  (hs.summable f).summable_compl_iff
#align set.finite.summable_compl_iff Set.Finite.summable_compl_iff

theorem hasSum_ite_sub_hasSum [DecidableEq β] (hf : HasSum f a) (b : β) :
    HasSum (fun n ↦ ite (n = b) 0 (f n)) (a - f b) := by
  convert hf.update b 0 using 1
  · ext n
    rw [Function.update_apply]
  · rw [sub_add_eq_add_sub, zero_add]
#align has_sum_ite_sub_has_sum hasSum_ite_sub_hasSum

section tsum

variable [T2Space α]

theorem tsum_neg : ∑' b, -f b = -∑' b, f b := by
  by_cases hf : Summable f
  · exact hf.hasSum.neg.tsum_eq
  · simp [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable (mt Summable.of_neg hf)]
#align tsum_neg tsum_neg

theorem tsum_sub (hf : Summable f) (hg : Summable g) :
    ∑' b, (f b - g b) = ∑' b, f b - ∑' b, g b :=
  (hf.hasSum.sub hg.hasSum).tsum_eq
#align tsum_sub tsum_sub

theorem sum_add_tsum_compl {s : Finset β} (hf : Summable f) :
    ((∑ x in s, f x) + ∑' x : ↑(s : Set β)ᶜ, f x) = ∑' x, f x :=
  ((s.hasSum f).add_compl (s.summable_compl_iff.2 hf).hasSum).tsum_eq.symm
#align sum_add_tsum_compl sum_add_tsum_compl

/-- Let `f : β → α` be a sequence with summable series and let `b ∈ β` be an index.
Lemma `tsum_eq_add_tsum_ite` writes `Σ f n` as the sum of `f b` plus the series of the
remaining terms. -/
theorem tsum_eq_add_tsum_ite [DecidableEq β] (hf : Summable f) (b : β) :
    ∑' n, f n = f b + ∑' n, ite (n = b) 0 (f n) := by
  rw [(hasSum_ite_sub_hasSum hf.hasSum b).tsum_eq]
  exact (add_sub_cancel _ _).symm
#align tsum_eq_add_tsum_ite tsum_eq_add_tsum_ite

end tsum

end TopologicalGroup

section UniformGroup

variable [AddCommGroup α] [UniformSpace α]

/-- The **Cauchy criterion** for infinite sums, also known as the **Cauchy convergence test** -/
theorem summable_iff_cauchySeq_finset [CompleteSpace α] {f : β → α} :
    Summable f ↔ CauchySeq fun s : Finset β ↦ ∑ b in s, f b := by
  classical exact cauchy_map_iff_exists_tendsto.symm
#align summable_iff_cauchy_seq_finset summable_iff_cauchySeq_finset

variable [UniformAddGroup α] {f g : β → α} {a a₁ a₂ : α}

theorem cauchySeq_finset_iff_vanishing :
    (CauchySeq fun s : Finset β ↦ ∑ b in s, f b) ↔
      ∀ e ∈ 𝓝 (0 : α), ∃ s : Finset β, ∀ t, Disjoint t s → (∑ b in t, f b) ∈ e := by
  classical
  simp only [CauchySeq, cauchy_map_iff, and_iff_right atTop_neBot, prod_atTop_atTop_eq,
    uniformity_eq_comap_nhds_zero α, tendsto_comap_iff, (· ∘ ·), atTop_neBot, true_and]
  rw [tendsto_atTop']
  constructor
  · intro h e he
    obtain ⟨⟨s₁, s₂⟩, h⟩ := h e he
    use s₁ ∪ s₂
    intro t ht
    specialize h (s₁ ∪ s₂, s₁ ∪ s₂ ∪ t) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩
    simpa only [Finset.sum_union ht.symm, add_sub_cancel_left] using h
  · rintro h e he
    rcases exists_nhds_half_neg he with ⟨d, hd, hde⟩
    rcases h d hd with ⟨s, h⟩
    use (s, s)
    rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩
    have : ((∑ b in t₂, f b) - ∑ b in t₁, f b) = (∑ b in t₂ \ s, f b) - ∑ b in t₁ \ s, f b := by
      rw [← Finset.sum_sdiff ht₁, ← Finset.sum_sdiff ht₂, add_sub_add_right_eq_sub]
    simp only [this]
    exact hde _ (h _ Finset.sdiff_disjoint) _ (h _ Finset.sdiff_disjoint)
#align cauchy_seq_finset_iff_vanishing cauchySeq_finset_iff_vanishing

theorem cauchySeq_finset_iff_tsum_vanishing :
    (CauchySeq fun s : Finset β ↦ ∑ b in s, f b) ↔
      ∀ e ∈ 𝓝 (0 : α), ∃ s : Finset β, ∀ t : Set β, Disjoint t s → (∑' b : t, f b) ∈ e := by
  simp_rw [cauchySeq_finset_iff_vanishing, Set.disjoint_left, disjoint_left]
  refine ⟨fun vanish e he ↦ ?_, fun vanish e he ↦ ?_⟩
  · obtain ⟨o, ho, o_closed, oe⟩ := exists_mem_nhds_isClosed_subset he
    obtain ⟨s, hs⟩ := vanish o ho
    refine ⟨s, fun t hts ↦ oe ?_⟩
    by_cases ht : Summable fun a : t ↦ f a
    · classical
      refine o_closed.mem_of_tendsto ht.hasSum (eventually_of_forall fun t' ↦ ?_)
      rw [← sum_subtype_map_embedding fun _ _ ↦ by rfl]
      apply hs
      simp_rw [Finset.mem_map]
      rintro _ ⟨b, -, rfl⟩
      exact hts b.prop
    · exact tsum_eq_zero_of_not_summable ht ▸ mem_of_mem_nhds ho
  · obtain ⟨s, hs⟩ := vanish _ he
    exact ⟨s, fun t hts ↦ (t.tsum_subtype f).symm ▸ hs _ hts⟩

variable [CompleteSpace α]

theorem summable_iff_vanishing :
    Summable f ↔ ∀ e ∈ 𝓝 (0 : α), ∃ s : Finset β, ∀ t, Disjoint t s → (∑ b in t, f b) ∈ e := by
  rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_vanishing]
#align summable_iff_vanishing summable_iff_vanishing

theorem summable_iff_tsum_vanishing : Summable f ↔
    ∀ e ∈ 𝓝 (0 : α), ∃ s : Finset β, ∀ t : Set β, Disjoint t s → (∑' b : t, f b) ∈ e := by
  rw [summable_iff_cauchySeq_finset, cauchySeq_finset_iff_tsum_vanishing]

-- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a`
theorem Summable.summable_of_eq_zero_or_self (hf : Summable f) (h : ∀ b, g b = 0 ∨ g b = f b) :
    Summable g := by
  classical
  exact summable_iff_vanishing.2 fun e he ↦
    let ⟨s, hs⟩ := summable_iff_vanishing.1 hf e he
    ⟨s, fun t ht ↦
      have eq : ∑ b in t.filter fun b ↦ g b = f b, f b = ∑ b in t, g b :=
        calc
          ∑ b in t.filter fun b ↦ g b = f b, f b = ∑ b in t.filter fun b ↦ g b = f b, g b :=
            Finset.sum_congr rfl fun b hb ↦ (Finset.mem_filter.1 hb).2.symm
          _ = ∑ b in t, g b := by
           {refine' Finset.sum_subset (Finset.filter_subset _ _) _
            intro b hbt hb
            simp only [Finset.mem_filter, and_iff_right hbt] at hb
            exact (h b).resolve_right hb}
      eq ▸ hs _ <| Finset.disjoint_of_subset_left (Finset.filter_subset _ _) ht⟩
#align summable.summable_of_eq_zero_or_self Summable.summable_of_eq_zero_or_self

protected theorem Summable.indicator (hf : Summable f) (s : Set β) : Summable (s.indicator f) :=
  hf.summable_of_eq_zero_or_self <| Set.indicator_eq_zero_or_self _ _
#align summable.indicator Summable.indicator

theorem Summable.comp_injective {i : γ → β} (hf : Summable f) (hi : Injective i) :
    Summable (f ∘ i) := by
  simpa only [Set.indicator_range_comp] using
    (hi.summable_iff (fun x hx ↦ Set.indicator_of_not_mem hx _)).2 (hf.indicator (Set.range i))
#align summable.comp_injective Summable.comp_injective

theorem Summable.subtype (hf : Summable f) (s : Set β) : Summable (f ∘ (↑) : s → α) :=
  hf.comp_injective Subtype.coe_injective
#align summable.subtype Summable.subtype

theorem summable_subtype_and_compl {s : Set β} :
    ((Summable fun x : s ↦ f x) ∧ Summable fun x : ↑sᶜ ↦ f x) ↔ Summable f :=
  ⟨and_imp.2 Summable.add_compl, fun h ↦ ⟨h.subtype s, h.subtype sᶜ⟩⟩
#align summable_subtype_and_compl summable_subtype_and_compl

theorem tsum_subtype_add_tsum_subtype_compl [T2Space α] {f : β → α} (hf : Summable f) (s : Set β) :
    ∑' x : s, f x + ∑' x : ↑sᶜ, f x = ∑' x, f x :=
  ((hf.subtype s).hasSum.add_compl (hf.subtype { x | x ∉ s }).hasSum).unique hf.hasSum
#align tsum_subtype_add_tsum_subtype_compl tsum_subtype_add_tsum_subtype_compl

theorem sum_add_tsum_subtype_compl [T2Space α] {f : β → α} (hf : Summable f) (s : Finset β) :
    ∑ x in s, f x + ∑' x : { x // x ∉ s }, f x = ∑' x, f x := by
  rw [← tsum_subtype_add_tsum_subtype_compl hf s]
  simp only [Finset.tsum_subtype', add_right_inj]
  rfl
#align sum_add_tsum_subtype_compl sum_add_tsum_subtype_compl

end UniformGroup

section TopologicalGroup

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [TopologicalAddGroup G] {f : α → G}

theorem Summable.vanishing (hf : Summable f) ⦃e : Set G⦄ (he : e ∈ 𝓝 (0 : G)) :
    ∃ s : Finset α, ∀ t, Disjoint t s → (∑ k in t, f k) ∈ e := by
  classical
  letI : UniformSpace G := TopologicalAddGroup.toUniformSpace G
  have : UniformAddGroup G := comm_topologicalAddGroup_is_uniform
  exact cauchySeq_finset_iff_vanishing.1 hf.hasSum.cauchySeq e he
#align summable.vanishing Summable.vanishing

theorem Summable.tsum_vanishing (hf : Summable f) ⦃e : Set G⦄ (he : e ∈ 𝓝 0) :
    ∃ s : Finset α, ∀ t : Set α, Disjoint t s → (∑' b : t, f b) ∈ e := by
  classical
  letI : UniformSpace G := TopologicalAddGroup.toUniformSpace G
  have : UniformAddGroup G := comm_topologicalAddGroup_is_uniform
  exact cauchySeq_finset_iff_tsum_vanishing.1 hf.hasSum.cauchySeq e he

/-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
space. This does not need a summability assumption, as otherwise all sums are zero. -/
theorem tendsto_tsum_compl_atTop_zero (f : α → G) :
    Tendsto (fun s : Finset α ↦ ∑' a : { x // x ∉ s }, f a) atTop (𝓝 0) := by
  classical
  by_cases H : Summable f
  · intro e he
    obtain ⟨s, hs⟩ := H.tsum_vanishing he
    rw [Filter.mem_map, mem_atTop_sets]
    exact ⟨s, fun t hts ↦ hs _ <| Set.disjoint_left.mpr fun a ha has ↦ ha (hts has)⟩
  · refine tendsto_const_nhds.congr fun _ ↦ (tsum_eq_zero_of_not_summable ?_).symm
    rwa [Finset.summable_compl_iff]
#align tendsto_tsum_compl_at_top_zero tendsto_tsum_compl_atTop_zero

/-- Series divergence test: if `f` is a convergent series, then `f x` tends to zero along
`cofinite`. -/
theorem Summable.tendsto_cofinite_zero (hf : Summable f) : Tendsto f cofinite (𝓝 0) := by
  intro e he
  rw [Filter.mem_map]
  rcases hf.vanishing he with ⟨s, hs⟩
  refine' s.eventually_cofinite_nmem.mono fun x hx ↦ _
  · simpa using hs {x} (disjoint_singleton_left.2 hx)
#align summable.tendsto_cofinite_zero Summable.tendsto_cofinite_zero

theorem Summable.countable_support [FirstCountableTopology G] [T1Space G]
    (hf : Summable f) : f.support.Countable := by
  simpa only [ker_nhds] using hf.tendsto_cofinite_zero.countable_compl_preimage_ker

theorem summable_const_iff [Infinite β] [T2Space G] (a : G) :
    Summable (fun _ : β ↦ a) ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_contra ha
    have : {a}ᶜ ∈ 𝓝 0 := compl_singleton_mem_nhds (Ne.symm ha)
    have : Finite β := by
      simpa [← Set.finite_univ_iff] using h.tendsto_cofinite_zero this
    exact not_finite β
  · rintro rfl
    exact summable_zero

@[simp]
theorem tsum_const [T2Space G] (a : G) : ∑' _ : β, a = Nat.card β • a := by
  rcases finite_or_infinite β with hβ|hβ
  · letI : Fintype β := Fintype.ofFinite β
    rw [tsum_eq_sum (s := univ) (fun x hx ↦ (hx (mem_univ x)).elim)]
    simp only [sum_const, Nat.card_eq_fintype_card, Fintype.card]
  · simp only [Nat.card_eq_zero_of_infinite, zero_smul]
    rcases eq_or_ne a 0 with rfl|ha
    · simp
    · apply tsum_eq_zero_of_not_summable
      simpa [summable_const_iff] using ha

end TopologicalGroup
