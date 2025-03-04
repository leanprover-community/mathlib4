/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Order.Filter.Bases.Defs
import Mathlib.Order.Filter.Map
import Mathlib.Data.Set.Sigma

/-!
# Basic results on filter bases

A filter basis `B : FilterBasis α` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element of
the collection.

## Main statements

* `Filter.basis_sets` : all sets of a filter form a basis;

* `Filter.HasBasis.inf`, `Filter.HasBasis.inf_principal`, `Filter.HasBasis.prod`,
  `Filter.HasBasis.prod_self`, `Filter.HasBasis.map`, `Filter.HasBasis.comap` : combinators to
  construct filters of `l ⊓ l'`, `l ⊓ 𝓟 t`, `l ×ˢ l'`, `l ×ˢ l`, `l.map f`, `l.comap f`
  respectively;

* `Filter.HasBasis.tendsto_right_iff`, `Filter.HasBasis.tendsto_left_iff`,
  `Filter.HasBasis.tendsto_iff` : restate `Tendsto f l l'` in terms of bases.
-/

assert_not_exists Finset

open Set Filter

variable {α β γ : Type*} {ι ι' : Sort*}

namespace FilterBasis

theorem eq_iInf_principal (B : FilterBasis α) : B.filter = ⨅ s : B.sets, 𝓟 s := by
  have : Directed (· ≥ ·) fun s : B.sets => 𝓟 (s : Set α) := by
    rintro ⟨U, U_in⟩ ⟨V, V_in⟩
    rcases B.inter_sets U_in V_in with ⟨W, W_in, W_sub⟩
    use ⟨W, W_in⟩
    simp only [le_principal_iff, mem_principal, Subtype.coe_mk]
    exact subset_inter_iff.mp W_sub
  ext U
  simp [mem_filter_iff, mem_iInf_of_directed this]

protected theorem generate (B : FilterBasis α) : generate B.sets = B.filter := by
  apply le_antisymm
  · intro U U_in
    rcases B.mem_filter_iff.mp U_in with ⟨V, V_in, h⟩
    exact GenerateSets.superset (GenerateSets.basic V_in) h
  · rw [le_generate_iff]
    apply mem_filter_of_mem

end FilterBasis

namespace Filter

namespace IsBasis

variable {p : ι → Prop} {s : ι → Set α}

theorem filter_eq_generate (h : IsBasis p s) : h.filter = generate { U | ∃ i, p i ∧ s i = U } := by
  rw [IsBasis.filter, ← h.filterBasis.generate, IsBasis.filterBasis]

end IsBasis

section SameType

variable {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {t : Set α} {i : ι} {p' : ι' → Prop}
  {s' : ι' → Set α} {i' : ι'}

theorem HasBasis.eq_generate (h : l.HasBasis p s) : l = generate { U | ∃ i, p i ∧ s i = U } := by
  rw [← h.isBasis.filter_eq_generate, h.filter_eq]

protected theorem HasBasis.neBot_iff (hl : l.HasBasis p s) :
    NeBot l ↔ ∀ {i}, p i → (s i).Nonempty :=
  forall_mem_nonempty_iff_neBot.symm.trans <| hl.forall_iff fun _ _ => Nonempty.mono

theorem HasBasis.eq_bot_iff (hl : l.HasBasis p s) : l = ⊥ ↔ ∃ i, p i ∧ s i = ∅ :=
  not_iff_not.1 <| neBot_iff.symm.trans <|
    hl.neBot_iff.trans <| by simp only [not_exists, not_and, nonempty_iff_ne_empty]

theorem basis_sets (l : Filter α) : l.HasBasis (fun s : Set α => s ∈ l) id :=
  ⟨fun _ => exists_mem_subset_iff.symm⟩

theorem asBasis_filter (f : Filter α) : f.asBasis.filter = f :=
  Filter.ext fun _ => exists_mem_subset_iff

theorem HasBasis.inf' (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊓ l').HasBasis (fun i : PProd ι ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∩ s' i.2 :=
  ⟨by
    intro t
    constructor
    · simp only [mem_inf_iff, hl.mem_iff, hl'.mem_iff]
      rintro ⟨t, ⟨i, hi, ht⟩, t', ⟨i', hi', ht'⟩, rfl⟩
      exact ⟨⟨i, i'⟩, ⟨hi, hi'⟩, inter_subset_inter ht ht'⟩
    · rintro ⟨⟨i, i'⟩, ⟨hi, hi'⟩, H⟩
      exact mem_inf_of_inter (hl.mem_of_mem hi) (hl'.mem_of_mem hi') H⟩

theorem HasBasis.inf {ι ι' : Type*} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}
    {s' : ι' → Set α} (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊓ l').HasBasis (fun i : ι × ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∩ s' i.2 :=
  (hl.inf' hl').comp_equiv Equiv.pprodEquivProd.symm

theorem hasBasis_iInf_of_directed' {ι : Type*} {ι' : ι → Sort _} [Nonempty ι] {l : ι → Filter α}
    (s : ∀ i, ι' i → Set α) (p : ∀ i, ι' i → Prop) (hl : ∀ i, (l i).HasBasis (p i) (s i))
    (h : Directed (· ≥ ·) l) :
    (⨅ i, l i).HasBasis (fun ii' : Σi, ι' i => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_iInf_of_directed h, Sigma.exists]
  exact exists_congr fun i => (hl i).mem_iff

theorem hasBasis_iInf_of_directed {ι : Type*} {ι' : Sort _} [Nonempty ι] {l : ι → Filter α}
    (s : ι → ι' → Set α) (p : ι → ι' → Prop) (hl : ∀ i, (l i).HasBasis (p i) (s i))
    (h : Directed (· ≥ ·) l) :
    (⨅ i, l i).HasBasis (fun ii' : ι × ι' => p ii'.1 ii'.2) fun ii' => s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_iInf_of_directed h, Prod.exists]
  exact exists_congr fun i => (hl i).mem_iff

theorem hasBasis_biInf_of_directed' {ι : Type*} {ι' : ι → Sort _} {dom : Set ι}
    (hdom : dom.Nonempty) {l : ι → Filter α} (s : ∀ i, ι' i → Set α) (p : ∀ i, ι' i → Prop)
    (hl : ∀ i ∈ dom, (l i).HasBasis (p i) (s i)) (h : DirectedOn (l ⁻¹'o GE.ge) dom) :
    (⨅ i ∈ dom, l i).HasBasis (fun ii' : Σi, ι' i => ii'.1 ∈ dom ∧ p ii'.1 ii'.2) fun ii' =>
      s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_biInf_of_directed h hdom, Sigma.exists]
  refine exists_congr fun i => ⟨?_, ?_⟩
  · rintro ⟨hi, hti⟩
    rcases (hl i hi).mem_iff.mp hti with ⟨b, hb, hbt⟩
    exact ⟨b, ⟨hi, hb⟩, hbt⟩
  · rintro ⟨b, ⟨hi, hb⟩, hibt⟩
    exact ⟨hi, (hl i hi).mem_iff.mpr ⟨b, hb, hibt⟩⟩

theorem hasBasis_biInf_of_directed {ι : Type*} {ι' : Sort _} {dom : Set ι} (hdom : dom.Nonempty)
    {l : ι → Filter α} (s : ι → ι' → Set α) (p : ι → ι' → Prop)
    (hl : ∀ i ∈ dom, (l i).HasBasis (p i) (s i)) (h : DirectedOn (l ⁻¹'o GE.ge) dom) :
    (⨅ i ∈ dom, l i).HasBasis (fun ii' : ι × ι' => ii'.1 ∈ dom ∧ p ii'.1 ii'.2) fun ii' =>
      s ii'.1 ii'.2 := by
  refine ⟨fun t => ?_⟩
  rw [mem_biInf_of_directed h hdom, Prod.exists]
  refine exists_congr fun i => ⟨?_, ?_⟩
  · rintro ⟨hi, hti⟩
    rcases (hl i hi).mem_iff.mp hti with ⟨b, hb, hbt⟩
    exact ⟨b, ⟨hi, hb⟩, hbt⟩
  · rintro ⟨b, ⟨hi, hb⟩, hibt⟩
    exact ⟨hi, (hl i hi).mem_iff.mpr ⟨b, hb, hibt⟩⟩

theorem hasBasis_pure (x : α) :
    (pure x : Filter α).HasBasis (fun _ : Unit => True) fun _ => {x} := by
  simp only [← principal_singleton, hasBasis_principal]

theorem HasBasis.sup' (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊔ l').HasBasis (fun i : PProd ι ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∪ s' i.2 :=
  ⟨by
    intro t
    simp_rw [mem_sup, hl.mem_iff, hl'.mem_iff, PProd.exists, union_subset_iff,
       ← exists_and_right, ← exists_and_left]
    simp only [and_assoc, and_left_comm]⟩

theorem HasBasis.sup {ι ι' : Type*} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}
    {s' : ι' → Set α} (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    (l ⊔ l').HasBasis (fun i : ι × ι' => p i.1 ∧ p' i.2) fun i => s i.1 ∪ s' i.2 :=
  (hl.sup' hl').comp_equiv Equiv.pprodEquivProd.symm

theorem hasBasis_iSup {ι : Sort*} {ι' : ι → Type*} {l : ι → Filter α} {p : ∀ i, ι' i → Prop}
    {s : ∀ i, ι' i → Set α} (hl : ∀ i, (l i).HasBasis (p i) (s i)) :
    (⨆ i, l i).HasBasis (fun f : ∀ i, ι' i => ∀ i, p i (f i)) fun f : ∀ i, ι' i => ⋃ i, s i (f i) :=
  hasBasis_iff.mpr fun t => by
    simp only [hasBasis_iff, (hl _).mem_iff, Classical.skolem, forall_and, iUnion_subset_iff,
      mem_iSup]

theorem HasBasis.sup_principal (hl : l.HasBasis p s) (t : Set α) :
    (l ⊔ 𝓟 t).HasBasis p fun i => s i ∪ t :=
  ⟨fun u => by
    simp only [(hl.sup' (hasBasis_principal t)).mem_iff, PProd.exists, exists_prop, and_true,
      Unique.exists_iff]⟩

theorem HasBasis.sup_pure (hl : l.HasBasis p s) (x : α) :
    (l ⊔ pure x).HasBasis p fun i => s i ∪ {x} := by
  simp only [← principal_singleton, hl.sup_principal]

theorem HasBasis.inf_principal (hl : l.HasBasis p s) (s' : Set α) :
    (l ⊓ 𝓟 s').HasBasis p fun i => s i ∩ s' :=
  ⟨fun t => by
    simp only [mem_inf_principal, hl.mem_iff, subset_def, mem_setOf_eq, mem_inter_iff, and_imp]⟩

theorem HasBasis.principal_inf (hl : l.HasBasis p s) (s' : Set α) :
    (𝓟 s' ⊓ l).HasBasis p fun i => s' ∩ s i := by
  simpa only [inf_comm, inter_comm] using hl.inf_principal s'

theorem HasBasis.inf_basis_neBot_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    NeBot (l ⊓ l') ↔ ∀ ⦃i⦄, p i → ∀ ⦃i'⦄, p' i' → (s i ∩ s' i').Nonempty :=
  (hl.inf' hl').neBot_iff.trans <| by simp [@forall_swap _ ι']

theorem HasBasis.inf_neBot_iff (hl : l.HasBasis p s) :
    NeBot (l ⊓ l') ↔ ∀ ⦃i⦄, p i → ∀ ⦃s'⦄, s' ∈ l' → (s i ∩ s').Nonempty :=
  hl.inf_basis_neBot_iff l'.basis_sets

theorem HasBasis.inf_principal_neBot_iff (hl : l.HasBasis p s) {t : Set α} :
    NeBot (l ⊓ 𝓟 t) ↔ ∀ ⦃i⦄, p i → (s i ∩ t).Nonempty :=
  (hl.inf_principal t).neBot_iff

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.disjoint_iff (hl : l.HasBasis p s) (hl' : l'.HasBasis p' s') :
    Disjoint l l' ↔ ∃ i, p i ∧ ∃ i', p' i' ∧ Disjoint (s i) (s' i') :=
  not_iff_not.mp <| by simp only [_root_.disjoint_iff, ← Ne.eq_def, ← neBot_iff, inf_eq_inter,
    hl.inf_basis_neBot_iff hl', not_exists, not_and, bot_eq_empty, ← nonempty_iff_ne_empty]

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem _root_.Disjoint.exists_mem_filter_basis (h : Disjoint l l') (hl : l.HasBasis p s)
    (hl' : l'.HasBasis p' s') : ∃ i, p i ∧ ∃ i', p' i' ∧ Disjoint (s i) (s' i') :=
  (hl.disjoint_iff hl').1 h

theorem inf_neBot_iff :
    NeBot (l ⊓ l') ↔ ∀ ⦃s : Set α⦄, s ∈ l → ∀ ⦃s'⦄, s' ∈ l' → (s ∩ s').Nonempty :=
  l.basis_sets.inf_neBot_iff

theorem inf_principal_neBot_iff {s : Set α} : NeBot (l ⊓ 𝓟 s) ↔ ∀ U ∈ l, (U ∩ s).Nonempty :=
  l.basis_sets.inf_principal_neBot_iff

theorem mem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s ∈ f ↔ f ⊓ 𝓟 sᶜ = ⊥ := by
  refine not_iff_not.1 ((inf_principal_neBot_iff.trans ?_).symm.trans neBot_iff)
  exact
    ⟨fun h hs => by simpa [Set.not_nonempty_empty] using h s hs, fun hs t ht =>
      inter_compl_nonempty_iff.2 fun hts => hs <| mem_of_superset ht hts⟩

theorem not_mem_iff_inf_principal_compl {f : Filter α} {s : Set α} : s ∉ f ↔ NeBot (f ⊓ 𝓟 sᶜ) :=
  (not_congr mem_iff_inf_principal_compl).trans neBot_iff.symm

@[simp]
theorem disjoint_principal_right {f : Filter α} {s : Set α} : Disjoint f (𝓟 s) ↔ sᶜ ∈ f := by
  rw [mem_iff_inf_principal_compl, compl_compl, disjoint_iff]

@[simp]
theorem disjoint_principal_left {f : Filter α} {s : Set α} : Disjoint (𝓟 s) f ↔ sᶜ ∈ f := by
  rw [disjoint_comm, disjoint_principal_right]

@[simp 1100] -- Porting note: higher priority for linter
theorem disjoint_principal_principal {s t : Set α} : Disjoint (𝓟 s) (𝓟 t) ↔ Disjoint s t := by
  rw [← subset_compl_iff_disjoint_left, disjoint_principal_left, mem_principal]

alias ⟨_, _root_.Disjoint.filter_principal⟩ := disjoint_principal_principal

@[simp]
theorem disjoint_pure_pure {x y : α} : Disjoint (pure x : Filter α) (pure y) ↔ x ≠ y := by
  simp only [← principal_singleton, disjoint_principal_principal, disjoint_singleton]

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.disjoint_iff_left (h : l.HasBasis p s) :
    Disjoint l l' ↔ ∃ i, p i ∧ (s i)ᶜ ∈ l' := by
  simp only [h.disjoint_iff l'.basis_sets, id, ← disjoint_principal_left,
    (hasBasis_principal _).disjoint_iff l'.basis_sets, true_and, Unique.exists_iff]

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.disjoint_iff_right (h : l.HasBasis p s) :
    Disjoint l' l ↔ ∃ i, p i ∧ (s i)ᶜ ∈ l' :=
  disjoint_comm.trans h.disjoint_iff_left

theorem le_iff_forall_inf_principal_compl {f g : Filter α} : f ≤ g ↔ ∀ V ∈ g, f ⊓ 𝓟 Vᶜ = ⊥ :=
  forall₂_congr fun _ _ => mem_iff_inf_principal_compl

theorem inf_neBot_iff_frequently_left {f g : Filter α} :
    NeBot (f ⊓ g) ↔ ∀ {p : α → Prop}, (∀ᶠ x in f, p x) → ∃ᶠ x in g, p x := by
  simp only [inf_neBot_iff, frequently_iff, and_comm]; rfl

theorem inf_neBot_iff_frequently_right {f g : Filter α} :
    NeBot (f ⊓ g) ↔ ∀ {p : α → Prop}, (∀ᶠ x in g, p x) → ∃ᶠ x in f, p x := by
  rw [inf_comm]
  exact inf_neBot_iff_frequently_left

theorem HasBasis.eq_biInf (h : l.HasBasis p s) : l = ⨅ (i) (_ : p i), 𝓟 (s i) :=
  eq_biInf_of_mem_iff_exists_mem fun {_} => by simp only [h.mem_iff, mem_principal, exists_prop]

theorem HasBasis.eq_iInf (h : l.HasBasis (fun _ => True) s) : l = ⨅ i, 𝓟 (s i) := by
  simpa only [iInf_true] using h.eq_biInf

theorem hasBasis_iInf_principal {s : ι → Set α} (h : Directed (· ≥ ·) s) [Nonempty ι] :
    (⨅ i, 𝓟 (s i)).HasBasis (fun _ => True) s :=
  ⟨fun t => by
    simpa only [true_and] using mem_iInf_of_directed (h.mono_comp _ monotone_principal.dual) t⟩

theorem hasBasis_biInf_principal {s : β → Set α} {S : Set β} (h : DirectedOn (s ⁻¹'o (· ≥ ·)) S)
    (ne : S.Nonempty) : (⨅ i ∈ S, 𝓟 (s i)).HasBasis (fun i => i ∈ S) s :=
  ⟨fun t => by
    refine mem_biInf_of_directed ?_ ne
    rw [directedOn_iff_directed, ← directed_comp] at h ⊢
    refine h.mono_comp _ ?_
    exact fun _ _ => principal_mono.2⟩

theorem hasBasis_biInf_principal' {ι : Type*} {p : ι → Prop} {s : ι → Set α}
    (h : ∀ i, p i → ∀ j, p j → ∃ k, p k ∧ s k ⊆ s i ∧ s k ⊆ s j) (ne : ∃ i, p i) :
    (⨅ (i) (_ : p i), 𝓟 (s i)).HasBasis p s :=
  Filter.hasBasis_biInf_principal h ne

theorem HasBasis.map (f : α → β) (hl : l.HasBasis p s) : (l.map f).HasBasis p fun i => f '' s i :=
  ⟨fun t => by simp only [mem_map, image_subset_iff, hl.mem_iff, preimage]⟩

theorem HasBasis.comap (f : β → α) (hl : l.HasBasis p s) :
    (l.comap f).HasBasis p fun i => f ⁻¹' s i :=
  ⟨fun t => by
    simp only [mem_comap', hl.mem_iff]
    refine exists_congr (fun i => Iff.rfl.and ?_)
    exact ⟨fun h x hx => h hx rfl, fun h y hy x hx => h <| by rwa [mem_preimage, hx]⟩⟩

theorem comap_hasBasis (f : α → β) (l : Filter β) :
    HasBasis (comap f l) (fun s : Set β => s ∈ l) fun s => f ⁻¹' s :=
  ⟨fun _ => mem_comap⟩

protected theorem HasBasis.biInf_mem [CompleteLattice β] {f : Set α → β} (h : HasBasis l p s)
    (hf : Monotone f) : ⨅ t ∈ l, f t = ⨅ (i) (_ : p i), f (s i) :=
  le_antisymm (le_iInf₂ fun i hi => iInf₂_le (s i) (h.mem_of_mem hi)) <|
    le_iInf₂ fun _t ht =>
      let ⟨i, hpi, hi⟩ := h.mem_iff.1 ht
      iInf₂_le_of_le i hpi (hf hi)

protected theorem HasBasis.biInter_mem {f : Set α → Set β} (h : HasBasis l p s) (hf : Monotone f) :
    ⋂ t ∈ l, f t = ⋂ (i) (_ : p i), f (s i) :=
  h.biInf_mem hf

protected theorem HasBasis.ker (h : HasBasis l p s) : l.ker = ⋂ (i) (_ : p i), s i :=
  sInter_eq_biInter.trans <| h.biInter_mem monotone_id

variable {ι'' : Type*} [Preorder ι''] (l) (s'' : ι'' → Set α)

protected theorem HasAntitoneBasis.map {l : Filter α} {s : ι'' → Set α}
    (hf : HasAntitoneBasis l s) (m : α → β) : HasAntitoneBasis (map m l) (m '' s ·) :=
  ⟨HasBasis.map _ hf.toHasBasis, fun _ _ h => image_subset _ <| hf.2 h⟩

protected theorem HasAntitoneBasis.comap {l : Filter α} {s : ι'' → Set α}
    (hf : HasAntitoneBasis l s) (m : β → α) : HasAntitoneBasis (comap m l) (m ⁻¹' s ·) :=
  ⟨hf.1.comap _, fun _ _ h ↦ preimage_mono (hf.2 h)⟩

lemma HasAntitoneBasis.iInf_principal {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {s : ι → Set α} (hs : Antitone s) : (⨅ i, 𝓟 (s i)).HasAntitoneBasis s :=
  ⟨hasBasis_iInf_principal hs.directed_ge, hs⟩

end SameType

section TwoTypes

variable {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β} {pb : ι' → Prop}
  {sb : ι' → Set β} {f : α → β}

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.tendsto_left_iff (hla : la.HasBasis pa sa) :
    Tendsto f la lb ↔ ∀ t ∈ lb, ∃ i, pa i ∧ MapsTo f (sa i) t := by
  simp only [Tendsto, (hla.map f).le_iff, image_subset_iff]
  rfl

theorem HasBasis.tendsto_right_iff (hlb : lb.HasBasis pb sb) :
    Tendsto f la lb ↔ ∀ i, pb i → ∀ᶠ x in la, f x ∈ sb i := by
  simp only [Tendsto, hlb.ge_iff, mem_map', Filter.Eventually]

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem HasBasis.tendsto_iff (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    Tendsto f la lb ↔ ∀ ib, pb ib → ∃ ia, pa ia ∧ ∀ x ∈ sa ia, f x ∈ sb ib := by
  simp [hlb.tendsto_right_iff, hla.eventually_iff]

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem Tendsto.basis_left (H : Tendsto f la lb) (hla : la.HasBasis pa sa) :
    ∀ t ∈ lb, ∃ i, pa i ∧ MapsTo f (sa i) t :=
  hla.tendsto_left_iff.1 H

theorem Tendsto.basis_right (H : Tendsto f la lb) (hlb : lb.HasBasis pb sb) :
    ∀ i, pb i → ∀ᶠ x in la, f x ∈ sb i :=
  hlb.tendsto_right_iff.1 H

-- Porting note: use `∃ i, p i ∧ _` instead of `∃ i (hi : p i), _`.
theorem Tendsto.basis_both (H : Tendsto f la lb) (hla : la.HasBasis pa sa)
    (hlb : lb.HasBasis pb sb) :
    ∀ ib, pb ib → ∃ ia, pa ia ∧ MapsTo f (sa ia) (sb ib) :=
  (hla.tendsto_iff hlb).1 H

theorem HasBasis.prod_pprod (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la ×ˢ lb).HasBasis (fun i : PProd ι ι' => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  (hla.comap Prod.fst).inf' (hlb.comap Prod.snd)

theorem HasBasis.prod {ι ι' : Type*} {pa : ι → Prop} {sa : ι → Set α} {pb : ι' → Prop}
    {sb : ι' → Set β} (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la ×ˢ lb).HasBasis (fun i : ι × ι' => pa i.1 ∧ pb i.2) fun i => sa i.1 ×ˢ sb i.2 :=
  (hla.comap Prod.fst).inf (hlb.comap Prod.snd)

theorem HasBasis.prod_same_index {p : ι → Prop} {sb : ι → Set β} (hla : la.HasBasis p sa)
    (hlb : lb.HasBasis p sb) (h_dir : ∀ {i j}, p i → p j → ∃ k, p k ∧ sa k ⊆ sa i ∧ sb k ⊆ sb j) :
    (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i := by
  simp only [hasBasis_iff, (hla.prod_pprod hlb).mem_iff]
  refine fun t => ⟨?_, ?_⟩
  · rintro ⟨⟨i, j⟩, ⟨hi, hj⟩, hsub : sa i ×ˢ sb j ⊆ t⟩
    rcases h_dir hi hj with ⟨k, hk, ki, kj⟩
    exact ⟨k, hk, (Set.prod_mono ki kj).trans hsub⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, i⟩, ⟨hi, hi⟩, h⟩

theorem HasBasis.prod_same_index_mono {ι : Type*} [LinearOrder ι] {p : ι → Prop} {sa : ι → Set α}
    {sb : ι → Set β} (hla : la.HasBasis p sa) (hlb : lb.HasBasis p sb)
    (hsa : MonotoneOn sa { i | p i }) (hsb : MonotoneOn sb { i | p i }) :
    (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  hla.prod_same_index hlb fun {i j} hi hj =>
    have : p (min i j) := min_rec' _ hi hj
    ⟨min i j, this, hsa this hi <| min_le_left _ _, hsb this hj <| min_le_right _ _⟩

theorem HasBasis.prod_same_index_anti {ι : Type*} [LinearOrder ι] {p : ι → Prop} {sa : ι → Set α}
    {sb : ι → Set β} (hla : la.HasBasis p sa) (hlb : lb.HasBasis p sb)
    (hsa : AntitoneOn sa { i | p i }) (hsb : AntitoneOn sb { i | p i }) :
    (la ×ˢ lb).HasBasis p fun i => sa i ×ˢ sb i :=
  @HasBasis.prod_same_index_mono _ _ _ _ ιᵒᵈ _ _ _ _ hla hlb hsa.dual_left hsb.dual_left

theorem HasBasis.prod_self (hl : la.HasBasis pa sa) :
    (la ×ˢ la).HasBasis pa fun i => sa i ×ˢ sa i :=
  hl.prod_same_index hl fun {i j} hi hj => by
    simpa only [exists_prop, subset_inter_iff] using
      hl.mem_iff.1 (inter_mem (hl.mem_of_mem hi) (hl.mem_of_mem hj))

theorem mem_prod_self_iff {s} : s ∈ la ×ˢ la ↔ ∃ t ∈ la, t ×ˢ t ⊆ s :=
  la.basis_sets.prod_self.mem_iff

lemma eventually_prod_self_iff {r : α → α → Prop} :
    (∀ᶠ x in la ×ˢ la, r x.1 x.2) ↔ ∃ t ∈ la, ∀ x ∈ t, ∀ y ∈ t, r x y :=
  mem_prod_self_iff.trans <| by simp only [prod_subset_iff, mem_setOf_eq]

/-- A version of `eventually_prod_self_iff` that is more suitable for forward rewriting. -/
lemma eventually_prod_self_iff' {r : α × α → Prop} :
    (∀ᶠ x in la ×ˢ la, r x) ↔ ∃ t ∈ la, ∀ x ∈ t, ∀ y ∈ t, r (x, y) :=
  Iff.symm eventually_prod_self_iff.symm

theorem HasAntitoneBasis.prod {ι : Type*} [LinearOrder ι] {f : Filter α} {g : Filter β}
    {s : ι → Set α} {t : ι → Set β} (hf : HasAntitoneBasis f s) (hg : HasAntitoneBasis g t) :
    HasAntitoneBasis (f ×ˢ g) fun n => s n ×ˢ t n :=
  ⟨hf.1.prod_same_index_anti hg.1 (hf.2.antitoneOn _) (hg.2.antitoneOn _), hf.2.set_prod hg.2⟩

theorem HasBasis.coprod {ι ι' : Type*} {pa : ι → Prop} {sa : ι → Set α} {pb : ι' → Prop}
    {sb : ι' → Set β} (hla : la.HasBasis pa sa) (hlb : lb.HasBasis pb sb) :
    (la.coprod lb).HasBasis (fun i : ι × ι' => pa i.1 ∧ pb i.2) fun i =>
      Prod.fst ⁻¹' sa i.1 ∪ Prod.snd ⁻¹' sb i.2 :=
  (hla.comap Prod.fst).sup (hlb.comap Prod.snd)

end TwoTypes

theorem map_sigma_mk_comap {π : α → Type*} {π' : β → Type*} {f : α → β}
    (hf : Function.Injective f) (g : ∀ a, π a → π' (f a)) (a : α) (l : Filter (π' (f a))) :
    map (Sigma.mk a) (comap (g a) l) = comap (Sigma.map f g) (map (Sigma.mk (f a)) l) := by
  refine (((basis_sets _).comap _).map _).eq_of_same_basis ?_
  convert ((basis_sets l).map (Sigma.mk (f a))).comap (Sigma.map f g)
  apply image_sigmaMk_preimage_sigmaMap hf

end Filter
