/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Infinite sums and products in topological groups

Lemmas on topological sums in groups (as opposed to monoids).
-/

public section

noncomputable section

open Filter Finset Function

open scoped Topology

variable {α β γ : Type*} {L : SummationFilter β}

section IsTopologicalGroup

variable [CommGroup α] [TopologicalSpace α] [IsTopologicalGroup α]
variable {f g : β → α} {a a₁ a₂ : α}

-- `by simpa using` speeds up elaboration. Why?
@[to_additive]
theorem HasProd.inv (h : HasProd f a L) : HasProd (fun b ↦ (f b)⁻¹) a⁻¹ L := by
  simpa only using h.map (MonoidHom.id α)⁻¹ continuous_inv

@[to_additive]
theorem Multipliable.inv (hf : Multipliable f L) : Multipliable (fun b ↦ (f b)⁻¹) L :=
  hf.hasProd.inv.multipliable

@[to_additive]
theorem Multipliable.of_inv (hf : Multipliable (fun b ↦ (f b)⁻¹) L) : Multipliable f L := by
  simpa only [inv_inv] using hf.inv

@[to_additive]
theorem multipliable_inv_iff : (Multipliable (fun b ↦ (f b)⁻¹) L) ↔ Multipliable f L :=
  ⟨Multipliable.of_inv, Multipliable.inv⟩

@[to_additive]
theorem HasProd.div (hf : HasProd f a₁ L) (hg : HasProd g a₂ L) :
    HasProd (fun b ↦ f b / g b) (a₁ / a₂) L := by
  simp only [div_eq_mul_inv]
  exact hf.mul hg.inv

@[to_additive]
theorem Multipliable.div (hf : Multipliable f L) (hg : Multipliable g L) :
    Multipliable (fun b ↦ f b / g b) L :=
  (hf.hasProd.div hg.hasProd).multipliable

@[to_additive]
theorem Multipliable.trans_div (hg : Multipliable g L) (hfg : Multipliable (fun b ↦ f b / g b) L) :
    Multipliable f L := by
  simpa only [div_mul_cancel] using hfg.mul hg

@[to_additive]
theorem multipliable_iff_of_multipliable_div (hfg : Multipliable (fun b ↦ f b / g b) L) :
    Multipliable f L ↔ Multipliable g L :=
  ⟨fun hf ↦ hf.trans_div <| by simpa only [inv_div] using hfg.inv, fun hg ↦ hg.trans_div hfg⟩

@[to_additive]
theorem HasProd.update [L.LeAtTop] (hf : HasProd f a₁ L) (b : β) [DecidableEq β] (a : α) :
    HasProd (update f b a) (a / f b * a₁) L := by
  convert (hasProd_ite_eq b (a / f b) (L := L)).mul hf with b'
  by_cases h : b' = b
  · rw [h, update_self]
    simp
  · simp only [h, update_of_ne, if_false, Ne, one_mul, not_false_iff]

@[to_additive]
theorem Multipliable.update [L.LeAtTop] (hf : Multipliable f L) (b : β) [DecidableEq β] (a : α) :
    Multipliable (update f b a) L :=
  (hf.hasProd.update b a).multipliable

@[to_additive]
theorem HasProd.hasProd_compl_iff {s : Set β} (hf : HasProd (f ∘ (↑) : s → α) a₁) :
    HasProd (f ∘ (↑) : ↑sᶜ → α) a₂ ↔ HasProd f (a₁ * a₂) := by
  refine ⟨fun h ↦ hf.mul_compl h, fun h ↦ ?_⟩
  rw [hasProd_subtype_iff_mulIndicator] at hf ⊢
  rw [Set.mulIndicator_compl]
  simpa only [div_eq_mul_inv, mul_inv_cancel_comm] using h.div hf

@[to_additive]
theorem HasProd.hasProd_iff_compl {s : Set β} (hf : HasProd (f ∘ (↑) : s → α) a₁) :
    HasProd f a₂ ↔ HasProd (f ∘ (↑) : ↑sᶜ → α) (a₂ / a₁) :=
  Iff.symm <| hf.hasProd_compl_iff.trans <| by rw [mul_div_cancel]

@[to_additive]
theorem Multipliable.multipliable_compl_iff {s : Set β} (hf : Multipliable (f ∘ (↑) : s → α)) :
    Multipliable (f ∘ (↑) : ↑sᶜ → α) ↔ Multipliable f where
  mp := fun ⟨_, ha⟩ ↦ (hf.hasProd.hasProd_compl_iff.1 ha).multipliable
  mpr := fun ⟨_, ha⟩ ↦ (hf.hasProd.hasProd_iff_compl.1 ha).multipliable

@[to_additive]
protected theorem Finset.hasProd_compl_iff (s : Finset β) :
    HasProd (fun x : { x // x ∉ s } ↦ f x) a ↔ HasProd f (a * ∏ i ∈ s, f i) :=
  (s.hasProd f).hasProd_compl_iff.trans <| by rw [mul_comm]

@[to_additive]
protected theorem Finset.hasProd_iff_compl (s : Finset β) :
    HasProd f a ↔ HasProd (fun x : { x // x ∉ s } ↦ f x) (a / ∏ i ∈ s, f i) :=
  (s.hasProd f).hasProd_iff_compl

@[to_additive]
protected theorem Finset.multipliable_compl_iff (s : Finset β) :
    (Multipliable fun x : { x // x ∉ s } ↦ f x) ↔ Multipliable f :=
  (s.multipliable f).multipliable_compl_iff

@[to_additive]
theorem Set.Finite.multipliable_compl_iff {s : Set β} (hs : s.Finite) :
    Multipliable (f ∘ (↑) : ↑sᶜ → α) ↔ Multipliable f :=
  (hs.multipliable f).multipliable_compl_iff

@[to_additive]
theorem hasProd_ite_div_hasProd [L.LeAtTop] [DecidableEq β] (hf : HasProd f a L) (b : β) :
    HasProd (fun n ↦ ite (n = b) 1 (f n)) (a / f b) L := by
  convert hf.update b 1 using 1
  · ext n
    rw [Function.update_apply]
  · rw [div_mul_eq_mul_div, one_mul]

/-- A more general version of `Multipliable.congr`, allowing the functions to
disagree on a finite set.

Note that this requires the target to be a group, and hence fails for products valued
in a ring. See `Multipliable.congr_cofinite₀` for a version applying in this case,
with an additional non-vanishing hypothesis.
-/
@[to_additive /-- A more general version of `Summable.congr`, allowing the functions to
disagree on a finite set. -/]
theorem Multipliable.congr_cofinite (hf : Multipliable f) (hfg : f =ᶠ[cofinite] g) :
    Multipliable g :=
  hfg.multipliable_compl_iff.mp <| (hfg.multipliable_compl_iff.mpr hf).congr (by simp)

/-- A more general version of `multipliable_congr`, allowing the functions to
disagree on a finite set. -/
@[to_additive /-- A more general version of `summable_congr`, allowing the functions to
disagree on a finite set. -/]
theorem multipliable_congr_cofinite (hfg : f =ᶠ[cofinite] g) :
    Multipliable f ↔ Multipliable g :=
  ⟨fun h ↦ h.congr_cofinite hfg, fun h ↦ h.congr_cofinite (hfg.mono fun _ h' ↦ h'.symm)⟩

@[to_additive]
theorem Multipliable.congr_atTop {f₁ g₁ : ℕ → α} (hf : Multipliable f₁) (hfg : f₁ =ᶠ[atTop] g₁) :
    Multipliable g₁ := hf.congr_cofinite (Nat.cofinite_eq_atTop ▸ hfg)

@[to_additive]
theorem multipliable_congr_atTop {f₁ g₁ : ℕ → α} (hfg : f₁ =ᶠ[atTop] g₁) :
    Multipliable f₁ ↔ Multipliable g₁ := multipliable_congr_cofinite (Nat.cofinite_eq_atTop ▸ hfg)

section tprod

variable [T2Space α]

@[to_additive]
theorem tprod_inv : ∏'[L] b, (f b)⁻¹ = (∏'[L] b, f b)⁻¹ :=
  ((Homeomorph.inv α).isClosedEmbedding.map_tprod f (g := MulEquiv.inv α)).symm

@[to_additive]
protected theorem Multipliable.tprod_div [L.NeBot] (hf : Multipliable f L) (hg : Multipliable g L) :
    ∏'[L] b, (f b / g b) = (∏'[L] b, f b) / ∏'[L] b, g b :=
  (hf.hasProd.div hg.hasProd).tprod_eq

@[to_additive]
protected theorem Multipliable.prod_mul_tprod_compl {s : Finset β} (hf : Multipliable f) :
    (∏ x ∈ s, f x) * ∏' x : ↑(s : Set β)ᶜ, f x = ∏' x, f x :=
  ((s.hasProd f).mul_compl (s.multipliable_compl_iff.2 hf).hasProd).tprod_eq.symm

/-- Let `f : β → α` be a multipliable function and let `b ∈ β` be an index.
Lemma `tprod_eq_mul_tprod_ite` writes `∏ n, f n` as `f b` times the product of the
remaining terms. -/
@[to_additive /-- Let `f : β → α` be a summable function and let `b ∈ β` be an index.
Lemma `tsum_eq_add_tsum_ite` writes `Σ' n, f n` as `f b` plus the sum of the
remaining terms. -/]
protected theorem Multipliable.tprod_eq_mul_tprod_ite [DecidableEq β] (hf : Multipliable f)
    (b : β) : ∏' n, f n = f b * ∏' n, ite (n = b) 1 (f n) := by
  rw [(hasProd_ite_div_hasProd hf.hasProd b).tprod_eq]
  exact (mul_div_cancel _ _).symm

end tprod

end IsTopologicalGroup

section IsUniformGroup

variable [UniformSpace α]

/-- The **Cauchy criterion** for infinite products, also known as the **Cauchy convergence test** -/
@[to_additive /-- The **Cauchy criterion** for infinite sums, also known as the
**Cauchy convergence test** -/]
theorem multipliable_iff_cauchySeq_finset [CommMonoid α] [CompleteSpace α] {f : β → α} :
    Multipliable f ↔ CauchySeq fun s : Finset β ↦ ∏ b ∈ s, f b := by
  classical exact cauchy_map_iff_exists_tendsto.symm

variable [CommGroup α] [IsUniformGroup α] {f g : β → α}

@[to_additive]
theorem cauchySeq_finset_iff_prod_vanishing :
    (CauchySeq fun s : Finset β ↦ ∏ b ∈ s, f b) ↔
      ∀ e ∈ 𝓝 (1 : α), ∃ s : Finset β, ∀ t, Disjoint t s → (∏ b ∈ t, f b) ∈ e := by
  classical
  simp only [CauchySeq, cauchy_map_iff, prod_atTop_atTop_eq,
    uniformity_eq_comap_nhds_one α, tendsto_comap_iff, Function.comp_def, atTop_neBot, true_and]
  rw [tendsto_atTop']
  constructor
  · intro h e he
    obtain ⟨⟨s₁, s₂⟩, h⟩ := h e he
    use s₁ ∪ s₂
    intro t ht
    specialize h (s₁ ∪ s₂, s₁ ∪ s₂ ∪ t) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩
    simpa only [Finset.prod_union ht.symm, mul_div_cancel_left] using h
  · rintro h e he
    rcases exists_nhds_split_inv he with ⟨d, hd, hde⟩
    rcases h d hd with ⟨s, h⟩
    use (s, s)
    rintro ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩
    have : ((∏ b ∈ t₂, f b) / ∏ b ∈ t₁, f b) = (∏ b ∈ t₂ \ s, f b) / ∏ b ∈ t₁ \ s, f b := by
      rw [← Finset.prod_sdiff ht₁, ← Finset.prod_sdiff ht₂, mul_div_mul_right_eq_div]
    simp only [this]
    exact hde _ (h _ Finset.sdiff_disjoint) _ (h _ Finset.sdiff_disjoint)

@[to_additive]
theorem cauchySeq_finset_iff_tprod_vanishing :
    (CauchySeq fun s : Finset β ↦ ∏ b ∈ s, f b) ↔
      ∀ e ∈ 𝓝 (1 : α), ∃ s : Finset β, ∀ t : Set β, Disjoint t s → (∏' b : t, f b) ∈ e := by
  simp_rw [cauchySeq_finset_iff_prod_vanishing, Set.disjoint_left, disjoint_left]
  refine ⟨fun vanish e he ↦ ?_, fun vanish e he ↦ ?_⟩
  · obtain ⟨o, ho, o_closed, oe⟩ := exists_mem_nhds_isClosed_subset he
    obtain ⟨s, hs⟩ := vanish o ho
    refine ⟨s, fun t hts ↦ oe ?_⟩
    by_cases ht : Multipliable fun a : t ↦ f a
    · classical
      refine o_closed.mem_of_tendsto ht.hasProd (Eventually.of_forall fun t' ↦ ?_)
      rw [← prod_subtype_map_embedding fun _ _ ↦ by rfl]
      apply hs
      simp_rw [Finset.mem_map]
      rintro _ ⟨b, -, rfl⟩
      exact hts b.prop
    · exact tprod_eq_one_of_not_multipliable ht ▸ mem_of_mem_nhds ho
  · obtain ⟨s, hs⟩ := vanish _ he
    exact ⟨s, fun t hts ↦ (t.tprod_subtype f).symm ▸ hs _ hts⟩

variable [CompleteSpace α]

@[to_additive]
theorem multipliable_iff_vanishing :
    Multipliable f ↔
    ∀ e ∈ 𝓝 (1 : α), ∃ s : Finset β, ∀ t, Disjoint t s → (∏ b ∈ t, f b) ∈ e := by
  rw [multipliable_iff_cauchySeq_finset, cauchySeq_finset_iff_prod_vanishing]

@[to_additive]
theorem multipliable_iff_tprod_vanishing : Multipliable f ↔
    ∀ e ∈ 𝓝 (1 : α), ∃ s : Finset β, ∀ t : Set β, Disjoint t s → (∏' b : t, f b) ∈ e := by
  rw [multipliable_iff_cauchySeq_finset, cauchySeq_finset_iff_tprod_vanishing]

-- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a`
@[to_additive]
theorem Multipliable.multipliable_of_eq_one_or_self (hf : Multipliable f)
    (h : ∀ b, g b = 1 ∨ g b = f b) : Multipliable g := by
  classical
  exact multipliable_iff_vanishing.2 fun e he ↦
    let ⟨s, hs⟩ := multipliable_iff_vanishing.1 hf e he
    ⟨s, fun t ht ↦
      have eq : ∏ b ∈ t with g b = f b, f b = ∏ b ∈ t, g b :=
        calc
          ∏ b ∈ t with g b = f b, f b = ∏ b ∈ t with g b = f b, g b :=
            Finset.prod_congr rfl fun b hb ↦ (Finset.mem_filter.1 hb).2.symm
          _ = ∏ b ∈ t, g b := by
           {refine Finset.prod_subset (Finset.filter_subset _ _) ?_
            intro b hbt hb
            simp only [Finset.mem_filter, and_iff_right hbt] at hb
            exact (h b).resolve_right hb}
      eq ▸ hs _ <| Finset.disjoint_of_subset_left (Finset.filter_subset _ _) ht⟩

@[to_additive]
protected theorem Multipliable.mulIndicator (hf : Multipliable f) (s : Set β) :
    Multipliable (s.mulIndicator f) :=
  hf.multipliable_of_eq_one_or_self <| Set.mulIndicator_eq_one_or_self _ _

@[to_additive]
theorem Multipliable.comp_injective {i : γ → β} (hf : Multipliable f) (hi : Injective i) :
    Multipliable (f ∘ i) := by
  simpa only [Set.mulIndicator_range_comp] using
    (hi.multipliable_iff (fun x hx ↦ Set.mulIndicator_of_notMem hx _)).2
    (hf.mulIndicator (Set.range i))

@[to_additive]
theorem Multipliable.subtype (hf : Multipliable f) (s : Set β) : Multipliable (f ∘ (↑) : s → α) :=
  hf.comp_injective Subtype.coe_injective

@[to_additive]
theorem multipliable_subtype_and_compl {s : Set β} :
    ((Multipliable fun x : s ↦ f x) ∧ Multipliable fun x : ↑sᶜ ↦ f x) ↔ Multipliable f :=
  ⟨and_imp.2 Multipliable.mul_compl, fun h ↦ ⟨h.subtype s, h.subtype sᶜ⟩⟩

@[to_additive]
protected theorem Multipliable.tprod_subtype_mul_tprod_subtype_compl [T2Space α] {f : β → α}
    (hf : Multipliable f) (s : Set β) : (∏' x : s, f x) * ∏' x : ↑sᶜ, f x = ∏' x, f x :=
  ((hf.subtype s).hasProd.mul_compl (hf.subtype { x | x ∉ s }).hasProd).unique hf.hasProd

@[to_additive]
protected theorem Multipliable.prod_mul_tprod_subtype_compl [T2Space α] {f : β → α}
    (hf : Multipliable f) (s : Finset β) :
    (∏ x ∈ s, f x) * ∏' x : { x // x ∉ s }, f x = ∏' x, f x := by
  rw [← hf.tprod_subtype_mul_tprod_subtype_compl s]
  simp only [Finset.tprod_subtype', mul_right_inj]
  rfl

end IsUniformGroup

section IsTopologicalGroup

variable {G : Type*} [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G] {f : α → G}

@[to_additive]
theorem Multipliable.vanishing (hf : Multipliable f) ⦃e : Set G⦄ (he : e ∈ 𝓝 (1 : G)) :
    ∃ s : Finset α, ∀ t, Disjoint t s → (∏ k ∈ t, f k) ∈ e := by
  classical
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  exact cauchySeq_finset_iff_prod_vanishing.1 hf.hasProd.cauchySeq e he

@[to_additive]
theorem Multipliable.tprod_vanishing (hf : Multipliable f) ⦃e : Set G⦄ (he : e ∈ 𝓝 1) :
    ∃ s : Finset α, ∀ t : Set α, Disjoint t s → (∏' b : t, f b) ∈ e := by
  classical
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  exact cauchySeq_finset_iff_tprod_vanishing.1 hf.hasProd.cauchySeq e he

/-- The product over the complement of a finset tends to `1` when the finset grows to cover the
whole space. This does not need a multipliability assumption, as otherwise all such products are
one. -/
@[to_additive /-- The sum over the complement of a finset tends to `0` when the finset grows to
cover the whole space. This does not need a summability assumption, as otherwise all such sums are
zero. -/]
theorem tendsto_tprod_compl_atTop_one (f : α → G) :
    Tendsto (fun s : Finset α ↦ ∏' a : { x // x ∉ s }, f a) atTop (𝓝 1) := by
  classical
  by_cases H : Multipliable f
  · intro e he
    obtain ⟨s, hs⟩ := H.tprod_vanishing he
    rw [Filter.mem_map, mem_atTop_sets]
    exact ⟨s, fun t hts ↦ hs _ <| Set.disjoint_left.mpr fun a ha has ↦ ha (hts has)⟩
  · refine tendsto_const_nhds.congr fun _ ↦ (tprod_eq_one_of_not_multipliable ?_).symm
    rwa [Finset.multipliable_compl_iff]

/-- Product divergence test: if `f` is unconditionally multipliable, then `f x` tends to one along
`cofinite`. -/
@[to_additive /-- Series divergence test: if `f` is unconditionally summable, then `f x` tends to
zero along `cofinite`. -/]
theorem Multipliable.tendsto_cofinite_one (hf : Multipliable f) : Tendsto f cofinite (𝓝 1) := by
  intro e he
  rw [Filter.mem_map]
  rcases hf.vanishing he with ⟨s, hs⟩
  refine s.eventually_cofinite_notMem.mono fun x hx ↦ ?_
  · simpa using hs {x} (disjoint_singleton_left.2 hx)

@[to_additive]
theorem Multipliable.hasFiniteMulSupport_of_discreteTopology
    {α : Type*} [CommGroup α] [TopologicalSpace α] [DiscreteTopology α]
    {β : Type*} (f : β → α) (h : Multipliable f) : HasFiniteMulSupport f :=
  haveI : IsTopologicalGroup α := ⟨⟩
  h.tendsto_cofinite_one (discreteTopology_iff_singleton_mem_nhds.mp ‹_› 1)

@[deprecated (since := "2026-03-03")] alias
  Multipliable.finite_mulSupport_of_discreteTopology :=
    Multipliable.hasFiniteMulSupport_of_discreteTopology

@[deprecated (since := "2026-03-03")] alias
  Summable.finite_support_of_discreteTopology :=
    Summable.hasFiniteSupport_of_discreteTopology

@[to_additive]
theorem Multipliable.countable_mulSupport [FirstCountableTopology G] [T1Space G]
    (hf : Multipliable f) : f.mulSupport.Countable := by
  simpa only [ker_nhds] using hf.tendsto_cofinite_one.countable_compl_preimage_ker

@[to_additive]
theorem multipliable_const_iff [Infinite β] [T2Space G] (a : G) :
    Multipliable (fun _ : β ↦ a) ↔ a = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_contra ha
    have : {a}ᶜ ∈ 𝓝 1 := compl_singleton_mem_nhds (Ne.symm ha)
    have : Finite β := by
      simpa [← Set.finite_univ_iff] using h.tendsto_cofinite_one this
    exact not_finite β
  · rintro rfl
    exact multipliable_one

@[to_additive (attr := simp)]
theorem tprod_const [T2Space G] (a : G) : ∏' _ : β, a = a ^ (Nat.card β) := by
  rcases finite_or_infinite β with hβ | hβ
  · letI : Fintype β := Fintype.ofFinite β
    rw [tprod_eq_prod (s := univ) (fun x hx ↦ (hx (mem_univ x)).elim)]
    simp only [prod_const, Nat.card_eq_fintype_card, Fintype.card]
  · simp only [Nat.card_eq_zero_of_infinite, pow_zero]
    rcases eq_or_ne a 1 with rfl | ha
    · simp
    · apply tprod_eq_one_of_not_multipliable
      simpa [multipliable_const_iff] using ha

end IsTopologicalGroup

section CommGroupWithZero
variable {K : Type*} [CommGroupWithZero K] [TopologicalSpace K] [ContinuousMul K] {f g : α → K}
/-!
## Groups with a zero

These lemmas apply to a `CommGroupWithZero`; the most familiar case is when `K` is a field. These
are specific to the product setting and do not have a sensible additive analogue.
-/

open Finset in
lemma HasProd.congr_cofinite₀ {c : K} (hc : HasProd f c) {s : Finset α}
    (hs : ∀ a ∈ s, f a ≠ 0) (hs' : ∀ a ∉ s, f a = g a) :
    HasProd g (c * ((∏ i ∈ s, g i) / ∏ i ∈ s, f i)) := by
  classical
  refine (Tendsto.mul_const ((∏ i ∈ s, g i) / ∏ i ∈ s, f i) hc).congr' ?_
  filter_upwards [eventually_ge_atTop s] with t ht
  calc (∏ i ∈ t, f i) * ((∏ i ∈ s, g i) / ∏ i ∈ s, f i)
  _ = ((∏ i ∈ s, f i) * ∏ i ∈ t \ s, g i) * _ := by
    conv_lhs => rw [← union_sdiff_of_subset ht, prod_union disjoint_sdiff,
      prod_congr rfl fun i hi ↦ hs' i (mem_sdiff.mp hi).2]
  _ = (∏ i ∈ s, g i) * ∏ i ∈ t \ s, g i := by
    rw [← mul_div_assoc, ← div_mul_eq_mul_div, ← div_mul_eq_mul_div, div_self, one_mul, mul_comm]
    exact prod_ne_zero_iff.mpr hs
  _ = ∏ i ∈ t, g i := by
    rw [← prod_union disjoint_sdiff, union_sdiff_of_subset ht]

protected lemma Multipliable.tsum_congr_cofinite₀ [T2Space K] (hc : Multipliable f) {s : Finset α}
    (hs : ∀ a ∈ s, f a ≠ 0) (hs' : ∀ a ∉ s, f a = g a) :
    ∏' i, g i = ((∏' i, f i) * ((∏ i ∈ s, g i) / ∏ i ∈ s, f i)) :=
  (hc.hasProd.congr_cofinite₀ hs hs').tprod_eq

/--
See also `Multipliable.congr_cofinite`, which does not have a non-vanishing condition, but instead
requires the target to be a group under multiplication (and hence fails for infinite products in a
ring).
-/
lemma Multipliable.congr_cofinite₀ (hf : Multipliable f) (hf' : ∀ a, f a ≠ 0)
    (hfg : ∀ᶠ a in cofinite, f a = g a) :
    Multipliable g := by
  classical
  obtain ⟨c, hc⟩ := hf
  obtain ⟨s, hs⟩ : ∃ s : Finset α, ∀ i ∉ s, f i = g i := ⟨hfg.toFinset, by simp⟩
  exact (hc.congr_cofinite₀ (fun a _ ↦ hf' a) hs).multipliable

end CommGroupWithZero
