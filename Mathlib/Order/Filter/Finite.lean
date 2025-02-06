/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Filter.Basic

/-!
# Results filters related to finiteness.

-/



open Function Set Order
open scoped symmDiff

universe u v w x y

namespace Filter

variable {α : Type u} {f g : Filter α} {s t : Set α}

@[simp]
theorem biInter_mem {β : Type v} {s : β → Set α} {is : Set β} (hf : is.Finite) :
    (⋂ i ∈ is, s i) ∈ f ↔ ∀ i ∈ is, s i ∈ f := by
  induction is, hf using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hs => simp [hs]

@[simp]
theorem biInter_finset_mem {β : Type v} {s : β → Set α} (is : Finset β) :
    (⋂ i ∈ is, s i) ∈ f ↔ ∀ i ∈ is, s i ∈ f :=
  biInter_mem is.finite_toSet

alias _root_.Finset.iInter_mem_sets := biInter_finset_mem

-- attribute [protected] Finset.iInter_mem_sets porting note: doesn't work

@[simp]
theorem sInter_mem {s : Set (Set α)} (hfin : s.Finite) : ⋂₀ s ∈ f ↔ ∀ U ∈ s, U ∈ f := by
  rw [sInter_eq_biInter, biInter_mem hfin]

@[simp]
theorem iInter_mem {β : Sort v} {s : β → Set α} [Finite β] : (⋂ i, s i) ∈ f ↔ ∀ i, s i ∈ f :=
  (sInter_mem (finite_range _)).trans forall_mem_range

end Filter


namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {ι : Sort x}

section Lattice

variable {f g : Filter α} {s t : Set α}

theorem mem_generate_iff {s : Set <| Set α} {U : Set α} :
    U ∈ generate s ↔ ∃ t ⊆ s, Set.Finite t ∧ ⋂₀ t ⊆ U := by
  constructor <;> intro h
  · induction h with
    | @basic V V_in =>
      exact ⟨{V}, singleton_subset_iff.2 V_in, finite_singleton _, (sInter_singleton _).subset⟩
    | univ => exact ⟨∅, empty_subset _, finite_empty, subset_univ _⟩
    | superset _ hVW hV =>
      rcases hV with ⟨t, hts, ht, htV⟩
      exact ⟨t, hts, ht, htV.trans hVW⟩
    | inter _ _ hV hW =>
      rcases hV, hW with ⟨⟨t, hts, ht, htV⟩, u, hus, hu, huW⟩
      exact
        ⟨t ∪ u, union_subset hts hus, ht.union hu,
          (sInter_union _ _).subset.trans <| inter_subset_inter htV huW⟩
  · rcases h with ⟨t, hts, tfin, h⟩
    exact mem_of_superset ((sInter_mem tfin).2 fun V hV => GenerateSets.basic <| hts hV) h

theorem mem_iInf_of_iInter {ι} {s : ι → Filter α} {U : Set α} {I : Set ι} (I_fin : I.Finite)
    {V : I → Set α} (hV : ∀ (i : I), V i ∈ s i) (hU : ⋂ i, V i ⊆ U) : U ∈ ⨅ i, s i := by
  haveI := I_fin.fintype
  refine mem_of_superset (iInter_mem.2 fun i => ?_) hU
  exact mem_iInf_of_mem (i : ι) (hV _)

theorem mem_iInf {ι} {s : ι → Filter α} {U : Set α} :
    (U ∈ ⨅ i, s i) ↔
      ∃ I : Set ι, I.Finite ∧ ∃ V : I → Set α, (∀ (i : I), V i ∈ s i) ∧ U = ⋂ i, V i := by
  constructor
  · rw [iInf_eq_generate, mem_generate_iff]
    rintro ⟨t, tsub, tfin, tinter⟩
    rcases eq_finite_iUnion_of_finite_subset_iUnion tfin tsub with ⟨I, Ifin, σ, σfin, σsub, rfl⟩
    rw [sInter_iUnion] at tinter
    set V := fun i => U ∪ ⋂₀ σ i with hV
    have V_in : ∀ (i : I), V i ∈ s i := by
      rintro i
      have : ⋂₀ σ i ∈ s i := by
        rw [sInter_mem (σfin _)]
        apply σsub
      exact mem_of_superset this subset_union_right
    refine ⟨I, Ifin, V, V_in, ?_⟩
    rwa [hV, ← union_iInter, union_eq_self_of_subset_right]
  · rintro ⟨I, Ifin, V, V_in, rfl⟩
    exact mem_iInf_of_iInter Ifin V_in Subset.rfl

theorem mem_iInf' {ι} {s : ι → Filter α} {U : Set α} :
    (U ∈ ⨅ i, s i) ↔
      ∃ I : Set ι, I.Finite ∧ ∃ V : ι → Set α, (∀ i, V i ∈ s i) ∧
        (∀ i ∉ I, V i = univ) ∧ (U = ⋂ i ∈ I, V i) ∧ U = ⋂ i, V i := by
  classical
  simp only [mem_iInf, SetCoe.forall', biInter_eq_iInter]
  refine ⟨?_, fun ⟨I, If, V, hVs, _, hVU, _⟩ => ⟨I, If, fun i => V i, fun i => hVs i, hVU⟩⟩
  rintro ⟨I, If, V, hV, rfl⟩
  refine ⟨I, If, fun i => if hi : i ∈ I then V ⟨i, hi⟩ else univ, fun i => ?_, fun i hi => ?_, ?_⟩
  · dsimp only
    split_ifs
    exacts [hV ⟨i,_⟩, univ_mem]
  · exact dif_neg hi
  · simp only [iInter_dite, biInter_eq_iInter, dif_pos (Subtype.coe_prop _), Subtype.coe_eta,
      iInter_univ, inter_univ, eq_self_iff_true, true_and]

theorem exists_iInter_of_mem_iInf {ι : Type*} {α : Type*} {f : ι → Filter α} {s}
    (hs : s ∈ ⨅ i, f i) : ∃ t : ι → Set α, (∀ i, t i ∈ f i) ∧ s = ⋂ i, t i :=
  let ⟨_, _, V, hVs, _, _, hVU'⟩ := mem_iInf'.1 hs; ⟨V, hVs, hVU'⟩

theorem mem_iInf_of_finite {ι : Type*} [Finite ι] {α : Type*} {f : ι → Filter α} (s) :
    (s ∈ ⨅ i, f i) ↔ ∃ t : ι → Set α, (∀ i, t i ∈ f i) ∧ s = ⋂ i, t i := by
  refine ⟨exists_iInter_of_mem_iInf, ?_⟩
  rintro ⟨t, ht, rfl⟩
  exact iInter_mem.2 fun i => mem_iInf_of_mem i (ht i)

/-! ### Lattice equations -/

theorem _root_.Pairwise.exists_mem_filter_of_disjoint {ι : Type*} [Finite ι] {l : ι → Filter α}
    (hd : Pairwise (Disjoint on l)) :
    ∃ s : ι → Set α, (∀ i, s i ∈ l i) ∧ Pairwise (Disjoint on s) := by
  have : Pairwise fun i j => ∃ (s : {s // s ∈ l i}) (t : {t // t ∈ l j}), Disjoint s.1 t.1 := by
    simpa only [Pairwise, Function.onFun, Filter.disjoint_iff, exists_prop, Subtype.exists] using hd
  choose! s t hst using this
  refine ⟨fun i => ⋂ j, @s i j ∩ @t j i, fun i => ?_, fun i j hij => ?_⟩
  exacts [iInter_mem.2 fun j => inter_mem (@s i j).2 (@t j i).2,
    (hst hij).mono ((iInter_subset _ j).trans inter_subset_left)
      ((iInter_subset _ i).trans inter_subset_right)]

theorem _root_.Set.PairwiseDisjoint.exists_mem_filter {ι : Type*} {l : ι → Filter α} {t : Set ι}
    (hd : t.PairwiseDisjoint l) (ht : t.Finite) :
    ∃ s : ι → Set α, (∀ i, s i ∈ l i) ∧ t.PairwiseDisjoint s := by
  haveI := ht.to_subtype
  rcases (hd.subtype _ _).exists_mem_filter_of_disjoint with ⟨s, hsl, hsd⟩
  lift s to (i : t) → {s // s ∈ l i} using hsl
  rcases @Subtype.exists_pi_extension ι (fun i => { s // s ∈ l i }) _ _ s with ⟨s, rfl⟩
  exact ⟨fun i => s i, fun i => (s i).2, hsd.set_of_subtype _ _⟩


theorem iInf_sets_eq_finite {ι : Type*} (f : ι → Filter α) :
    (⨅ i, f i).sets = ⋃ t : Finset ι, (⨅ i ∈ t, f i).sets := by
  rw [iInf_eq_iInf_finset, iInf_sets_eq]
  exact directed_of_isDirected_le fun _ _ => biInf_mono

theorem iInf_sets_eq_finite' (f : ι → Filter α) :
    (⨅ i, f i).sets = ⋃ t : Finset (PLift ι), (⨅ i ∈ t, f (PLift.down i)).sets := by
  rw [← iInf_sets_eq_finite, ← Equiv.plift.surjective.iInf_comp, Equiv.plift_apply]

theorem mem_iInf_finite {ι : Type*} {f : ι → Filter α} (s) :
    s ∈ iInf f ↔ ∃ t : Finset ι, s ∈ ⨅ i ∈ t, f i :=
  (Set.ext_iff.1 (iInf_sets_eq_finite f) s).trans mem_iUnion

theorem mem_iInf_finite' {f : ι → Filter α} (s) :
    s ∈ iInf f ↔ ∃ t : Finset (PLift ι), s ∈ ⨅ i ∈ t, f (PLift.down i) :=
  (Set.ext_iff.1 (iInf_sets_eq_finite' f) s).trans mem_iUnion

/-- The dual version does not hold! `Filter α` is not a `CompleteDistribLattice`. -/
-- See note [reducible non-instances]
abbrev coframeMinimalAxioms : Coframe.MinimalAxioms (Filter α) :=
  { Filter.instCompleteLatticeFilter with
    iInf_sup_le_sup_sInf := fun f s t ⟨h₁, h₂⟩ => by
      classical
      rw [iInf_subtype']
      rw [sInf_eq_iInf', ← Filter.mem_sets, iInf_sets_eq_finite, mem_iUnion] at h₂
      obtain ⟨u, hu⟩ := h₂
      rw [← Finset.inf_eq_iInf] at hu
      suffices ⨅ i : s, f ⊔ ↑i ≤ f ⊔ u.inf fun i => ↑i from this ⟨h₁, hu⟩
      refine Finset.induction_on u (le_sup_of_le_right le_top) ?_
      rintro ⟨i⟩ u _ ih
      rw [Finset.inf_insert, sup_inf_left]
      exact le_inf (iInf_le _ _) ih }

instance instCoframe : Coframe (Filter α) := .ofMinimalAxioms coframeMinimalAxioms

theorem mem_iInf_finset {s : Finset α} {f : α → Filter β} {t : Set β} :
    (t ∈ ⨅ a ∈ s, f a) ↔ ∃ p : α → Set β, (∀ a ∈ s, p a ∈ f a) ∧ t = ⋂ a ∈ s, p a := by
  classical
  simp only [← Finset.set_biInter_coe, biInter_eq_iInter, iInf_subtype']
  refine ⟨fun h => ?_, ?_⟩
  · rcases (mem_iInf_of_finite _).1 h with ⟨p, hp, rfl⟩
    refine ⟨fun a => if h : a ∈ s then p ⟨a, h⟩ else univ,
            fun a ha => by simpa [ha] using hp ⟨a, ha⟩, ?_⟩
    refine iInter_congr_of_surjective id surjective_id ?_
    rintro ⟨a, ha⟩
    simp [ha]
  · rintro ⟨p, hpf, rfl⟩
    exact iInter_mem.2 fun a => mem_iInf_of_mem a (hpf a a.2)


@[elab_as_elim]
theorem iInf_sets_induct {f : ι → Filter α} {s : Set α} (hs : s ∈ iInf f) {p : Set α → Prop}
    (uni : p univ) (ins : ∀ {i s₁ s₂}, s₁ ∈ f i → p s₂ → p (s₁ ∩ s₂)) : p s := by
  classical
  rw [mem_iInf_finite'] at hs
  simp only [← Finset.inf_eq_iInf] at hs
  rcases hs with ⟨is, his⟩
  induction is using Finset.induction_on generalizing s with
  | empty => rwa [mem_top.1 his]
  | insert _ ih =>
    rw [Finset.inf_insert, mem_inf_iff] at his
    rcases his with ⟨s₁, hs₁, s₂, hs₂, rfl⟩
    exact ins hs₁ (ih hs₂)

/-! #### `principal` equations -/

@[simp]
theorem iInf_principal_finset {ι : Type w} (s : Finset ι) (f : ι → Set α) :
    ⨅ i ∈ s, 𝓟 (f i) = 𝓟 (⋂ i ∈ s, f i) := by
  classical
  induction' s using Finset.induction_on with i s _ hs
  · simp
  · rw [Finset.iInf_insert, Finset.set_biInter_insert, hs, inf_principal]

theorem iInf_principal {ι : Sort w} [Finite ι] (f : ι → Set α) : ⨅ i, 𝓟 (f i) = 𝓟 (⋂ i, f i) := by
  cases nonempty_fintype (PLift ι)
  rw [← iInf_plift_down, ← iInter_plift_down]
  simpa using iInf_principal_finset Finset.univ (f <| PLift.down ·)

/-- A special case of `iInf_principal` that is safe to mark `simp`. -/
@[simp]
theorem iInf_principal' {ι : Type w} [Finite ι] (f : ι → Set α) : ⨅ i, 𝓟 (f i) = 𝓟 (⋂ i, f i) :=
  iInf_principal _

theorem iInf_principal_finite {ι : Type w} {s : Set ι} (hs : s.Finite) (f : ι → Set α) :
    ⨅ i ∈ s, 𝓟 (f i) = 𝓟 (⋂ i ∈ s, f i) := by
  lift s to Finset ι using hs
  exact mod_cast iInf_principal_finset s f

end Lattice

/-! ### Eventually -/

@[simp]
theorem eventually_all {ι : Sort*} [Finite ι] {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀ i, p i x) ↔ ∀ i, ∀ᶠ x in l, p i x := by
  simpa only [Filter.Eventually, setOf_forall] using iInter_mem

@[simp]
theorem eventually_all_finite {ι} {I : Set ι} (hI : I.Finite) {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀ i ∈ I, p i x) ↔ ∀ i ∈ I, ∀ᶠ x in l, p i x := by
  simpa only [Filter.Eventually, setOf_forall] using biInter_mem hI

alias _root_.Set.Finite.eventually_all := eventually_all_finite

-- attribute [protected] Set.Finite.eventually_all

@[simp] theorem eventually_all_finset {ι} (I : Finset ι) {l} {p : ι → α → Prop} :
    (∀ᶠ x in l, ∀ i ∈ I, p i x) ↔ ∀ i ∈ I, ∀ᶠ x in l, p i x :=
  I.finite_toSet.eventually_all

alias _root_.Finset.eventually_all := eventually_all_finset

-- attribute [protected] Finset.eventually_all

/-!
### Relation “eventually equal”
-/

section EventuallyEq
variable {l : Filter α} {f g : α → β}

variable {l : Filter α}

protected lemma EventuallyLE.iUnion [Finite ι] {s t : ι → Set α}
    (h : ∀ i, s i ≤ᶠ[l] t i) : (⋃ i, s i) ≤ᶠ[l] ⋃ i, t i :=
  (eventually_all.2 h).mono fun _x hx hx' ↦
    let ⟨i, hi⟩ := mem_iUnion.1 hx'; mem_iUnion.2 ⟨i, hx i hi⟩

protected lemma EventuallyEq.iUnion [Finite ι] {s t : ι → Set α}
    (h : ∀ i, s i =ᶠ[l] t i) : (⋃ i, s i) =ᶠ[l] ⋃ i, t i :=
  (EventuallyLE.iUnion fun i ↦ (h i).le).antisymm <| .iUnion fun i ↦ (h i).symm.le

protected lemma EventuallyLE.iInter [Finite ι] {s t : ι → Set α}
    (h : ∀ i, s i ≤ᶠ[l] t i) : (⋂ i, s i) ≤ᶠ[l] ⋂ i, t i :=
  (eventually_all.2 h).mono fun _x hx hx' ↦ mem_iInter.2 fun i ↦ hx i (mem_iInter.1 hx' i)

protected lemma EventuallyEq.iInter [Finite ι] {s t : ι → Set α}
    (h : ∀ i, s i =ᶠ[l] t i) : (⋂ i, s i) =ᶠ[l] ⋂ i, t i :=
  (EventuallyLE.iInter fun i ↦ (h i).le).antisymm <| .iInter fun i ↦ (h i).symm.le

lemma _root_.Set.Finite.eventuallyLE_iUnion {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι → Set α} (hle : ∀ i ∈ s, f i ≤ᶠ[l] g i) : (⋃ i ∈ s, f i) ≤ᶠ[l] (⋃ i ∈ s, g i) := by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion, biUnion_eq_iUnion]
  exact .iUnion fun i ↦ hle i.1 i.2

alias EventuallyLE.biUnion := Set.Finite.eventuallyLE_iUnion

lemma _root_.Set.Finite.eventuallyEq_iUnion {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι → Set α} (heq : ∀ i ∈ s, f i =ᶠ[l] g i) : (⋃ i ∈ s, f i) =ᶠ[l] (⋃ i ∈ s, g i) :=
  (EventuallyLE.biUnion hs fun i hi ↦ (heq i hi).le).antisymm <|
    .biUnion hs fun i hi ↦ (heq i hi).symm.le

alias EventuallyEq.biUnion := Set.Finite.eventuallyEq_iUnion

lemma _root_.Set.Finite.eventuallyLE_iInter {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι → Set α} (hle : ∀ i ∈ s, f i ≤ᶠ[l] g i) : (⋂ i ∈ s, f i) ≤ᶠ[l] (⋂ i ∈ s, g i) := by
  have := hs.to_subtype
  rw [biInter_eq_iInter, biInter_eq_iInter]
  exact .iInter fun i ↦ hle i.1 i.2

alias EventuallyLE.biInter := Set.Finite.eventuallyLE_iInter

lemma _root_.Set.Finite.eventuallyEq_iInter {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι → Set α} (heq : ∀ i ∈ s, f i =ᶠ[l] g i) : (⋂ i ∈ s, f i) =ᶠ[l] (⋂ i ∈ s, g i) :=
  (EventuallyLE.biInter hs fun i hi ↦ (heq i hi).le).antisymm <|
    .biInter hs fun i hi ↦ (heq i hi).symm.le

alias EventuallyEq.biInter := Set.Finite.eventuallyEq_iInter

lemma _root_.Finset.eventuallyLE_iUnion {ι : Type*} (s : Finset ι) {f g : ι → Set α}
    (hle : ∀ i ∈ s, f i ≤ᶠ[l] g i) : (⋃ i ∈ s, f i) ≤ᶠ[l] (⋃ i ∈ s, g i) :=
  .biUnion s.finite_toSet hle

lemma _root_.Finset.eventuallyEq_iUnion {ι : Type*} (s : Finset ι) {f g : ι → Set α}
    (heq : ∀ i ∈ s, f i =ᶠ[l] g i) : (⋃ i ∈ s, f i) =ᶠ[l] (⋃ i ∈ s, g i) :=
  .biUnion s.finite_toSet heq

lemma _root_.Finset.eventuallyLE_iInter {ι : Type*} (s : Finset ι) {f g : ι → Set α}
    (hle : ∀ i ∈ s, f i ≤ᶠ[l] g i) : (⋂ i ∈ s, f i) ≤ᶠ[l] (⋂ i ∈ s, g i) :=
  .biInter s.finite_toSet hle

lemma _root_.Finset.eventuallyEq_iInter {ι : Type*} (s : Finset ι) {f g : ι → Set α}
    (heq : ∀ i ∈ s, f i =ᶠ[l] g i) : (⋂ i ∈ s, f i) =ᶠ[l] (⋂ i ∈ s, g i) :=
  .biInter s.finite_toSet heq

end EventuallyEq

end Filter

open Filter
