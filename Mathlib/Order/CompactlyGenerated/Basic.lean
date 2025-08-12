/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Order.Atoms
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.RelIso.Set
import Mathlib.Order.SupClosed
import Mathlib.Order.SupIndep
import Mathlib.Order.Zorn
import Mathlib.Data.Finset.Order
import Mathlib.Order.Interval.Set.OrderIso
import Mathlib.Data.Finite.Set
import Mathlib.Tactic.TFAE

/-!
# Compactness properties for complete lattices

For complete lattices, there are numerous equivalent ways to express the fact that the relation `>`
is well-founded. In this file we define three especially-useful characterisations and provide
proofs that they are indeed equivalent to well-foundedness.

## Main definitions
* `CompleteLattice.IsSupClosedCompact`
* `CompleteLattice.IsSupFiniteCompact`
* `CompleteLattice.IsCompactElement`
* `IsCompactlyGenerated`

## Main results
The main result is that the following four conditions are equivalent for a complete lattice:
* `well_founded (>)`
* `CompleteLattice.IsSupClosedCompact`
* `CompleteLattice.IsSupFiniteCompact`
* `∀ k, CompleteLattice.IsCompactElement k`

This is demonstrated by means of the following four lemmas:
* `CompleteLattice.WellFounded.isSupFiniteCompact`
* `CompleteLattice.IsSupFiniteCompact.isSupClosedCompact`
* `CompleteLattice.IsSupClosedCompact.wellFounded`
* `CompleteLattice.isSupFiniteCompact_iff_all_elements_compact`

We also show well-founded lattices are compactly generated
(`CompleteLattice.isCompactlyGenerated_of_wellFounded`).

## References
- [G. Călugăreanu, *Lattice Concepts of Module Theory*][calugareanu]

## Tags

complete lattice, well-founded, compact
-/

open Set

variable {ι : Sort*} {α : Type*} [CompleteLattice α] {f : ι → α}

namespace CompleteLattice

variable (α)

/-- A compactness property for a complete lattice is that any `sup`-closed non-empty subset
contains its `sSup`. -/
def IsSupClosedCompact : Prop :=
  ∀ (s : Set α) (_ : s.Nonempty), SupClosed s → sSup s ∈ s

/-- A compactness property for a complete lattice is that any subset has a finite subset with the
same `sSup`. -/
def IsSupFiniteCompact : Prop :=
  ∀ s : Set α, ∃ t : Finset α, ↑t ⊆ s ∧ sSup s = t.sup id

/-- An element `k` of a complete lattice is said to be compact if any set with `sSup`
above `k` has a finite subset with `sSup` above `k`.  Such an element is also called
"finite" or "S-compact". -/
def IsCompactElement {α : Type*} [CompleteLattice α] (k : α) :=
  ∀ s : Set α, k ≤ sSup s → ∃ t : Finset α, ↑t ⊆ s ∧ k ≤ t.sup id

theorem isCompactElement_iff.{u} {α : Type u} [CompleteLattice α] (k : α) :
    CompleteLattice.IsCompactElement k ↔
      ∀ (ι : Type u) (s : ι → α), k ≤ iSup s → ∃ t : Finset ι, k ≤ t.sup s := by
  classical
    constructor
    · intro H ι s hs
      obtain ⟨t, ht, ht'⟩ := H (Set.range s) hs
      have : ∀ x : t, ∃ i, s i = x := fun x => ht x.prop
      choose f hf using this
      refine ⟨Finset.univ.image f, ht'.trans ?_⟩
      rw [Finset.sup_le_iff]
      intro b hb
      rw [← show s (f ⟨b, hb⟩) = id b from hf _]
      exact Finset.le_sup (Finset.mem_image_of_mem f <| Finset.mem_univ (Subtype.mk b hb))
    · intro H s hs
      obtain ⟨t, ht⟩ :=
        H s Subtype.val
          (by
            delta iSup
            rwa [Subtype.range_coe])
      refine ⟨t.image Subtype.val, by simp, ht.trans ?_⟩
      rw [Finset.sup_le_iff]
      exact fun x hx => @Finset.le_sup _ _ _ _ _ id _ (Finset.mem_image_of_mem Subtype.val hx)

/-- An element `k` is compact if and only if any directed set with `sSup` above
`k` already got above `k` at some point in the set. -/
theorem isCompactElement_iff_le_of_directed_sSup_le (k : α) :
    IsCompactElement k ↔
      ∀ s : Set α, s.Nonempty → DirectedOn (· ≤ ·) s → k ≤ sSup s → ∃ x : α, x ∈ s ∧ k ≤ x := by
  classical
    constructor
    · intro hk s hne hdir hsup
      obtain ⟨t, ht⟩ := hk s hsup
      -- certainly every element of t is below something in s, since ↑t ⊆ s.
      have t_below_s : ∀ x ∈ t, ∃ y ∈ s, x ≤ y := fun x hxt => ⟨x, ht.left hxt, le_rfl⟩
      obtain ⟨x, ⟨hxs, hsupx⟩⟩ := Finset.sup_le_of_le_directed s hne hdir t t_below_s
      exact ⟨x, ⟨hxs, le_trans ht.right hsupx⟩⟩
    · intro hk s hsup
      -- Consider the set of finite joins of elements of the (plain) set s.
      let S : Set α := { x | ∃ t : Finset α, ↑t ⊆ s ∧ x = t.sup id }
      -- S is directed, nonempty, and still has sup above k.
      have dir_US : DirectedOn (· ≤ ·) S := by
        rintro x ⟨c, hc⟩ y ⟨d, hd⟩
        use x ⊔ y
        constructor
        · use c ∪ d
          constructor
          · simp only [hc.left, hd.left, Set.union_subset_iff, Finset.coe_union, and_self_iff]
          · simp only [hc.right, hd.right, Finset.sup_union]
        simp only [and_self_iff, le_sup_left, le_sup_right]
      have sup_S : sSup s ≤ sSup S := by
        apply sSup_le_sSup
        intro x hx
        use {x}
        simpa only [and_true, id, Finset.coe_singleton, eq_self_iff_true,
          Finset.sup_singleton, Set.singleton_subset_iff]
      have Sne : S.Nonempty := by
        suffices ⊥ ∈ S from Set.nonempty_of_mem this
        use ∅
        simp only [Set.empty_subset, Finset.coe_empty, Finset.sup_empty,
          and_self_iff]
      -- Now apply the defn of compact and finish.
      obtain ⟨j, ⟨hjS, hjk⟩⟩ := hk S Sne dir_US (le_trans hsup sup_S)
      obtain ⟨t, ⟨htS, htsup⟩⟩ := hjS
      use t
      exact ⟨htS, by rwa [← htsup]⟩

theorem IsCompactElement.exists_finset_of_le_iSup {k : α} (hk : IsCompactElement k) {ι : Type*}
    (f : ι → α) (h : k ≤ ⨆ i, f i) : ∃ s : Finset ι, k ≤ ⨆ i ∈ s, f i := by
  classical
    let g : Finset ι → α := fun s => ⨆ i ∈ s, f i
    have h1 : DirectedOn (· ≤ ·) (Set.range g) := by
      rintro - ⟨s, rfl⟩ - ⟨t, rfl⟩
      exact
        ⟨g (s ∪ t), ⟨s ∪ t, rfl⟩, iSup_le_iSup_of_subset Finset.subset_union_left,
          iSup_le_iSup_of_subset Finset.subset_union_right⟩
    have h2 : k ≤ sSup (Set.range g) :=
      h.trans
        (iSup_le fun i =>
          le_sSup_of_le ⟨{i}, rfl⟩
            (le_iSup_of_le i (le_iSup_of_le (Finset.mem_singleton_self i) le_rfl)))
    obtain ⟨-, ⟨s, rfl⟩, hs⟩ :=
      (isCompactElement_iff_le_of_directed_sSup_le α k).mp hk (Set.range g) (Set.range_nonempty g)
        h1 h2
    exact ⟨s, hs⟩

/-- A compact element `k` has the property that any directed set lying strictly below `k` has
its `sSup` strictly below `k`. -/
theorem IsCompactElement.directed_sSup_lt_of_lt {α : Type*} [CompleteLattice α] {k : α}
    (hk : IsCompactElement k) {s : Set α} (hemp : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hbelow : ∀ x ∈ s, x < k) : sSup s < k := by
  rw [isCompactElement_iff_le_of_directed_sSup_le] at hk
  by_contra h
  have sSup' : sSup s ≤ k := sSup_le s k fun s hs => (hbelow s hs).le
  replace sSup : sSup s = k := eq_iff_le_not_lt.mpr ⟨sSup', h⟩
  obtain ⟨x, hxs, hkx⟩ := hk s hemp hdir sSup.symm.le
  obtain hxk := hbelow x hxs
  exact hxk.ne (hxk.le.antisymm hkx)

theorem isCompactElement_finsetSup {α β : Type*} [CompleteLattice α] {f : β → α} (s : Finset β)
    (h : ∀ x ∈ s, IsCompactElement (f x)) : IsCompactElement (s.sup f) := by
  classical
    rw [isCompactElement_iff_le_of_directed_sSup_le]
    intro d hemp hdir hsup
    rw [← Function.id_comp f]
    rw [← Finset.sup_image]
    apply Finset.sup_le_of_le_directed d hemp hdir
    rintro x hx
    obtain ⟨p, ⟨hps, rfl⟩⟩ := Finset.mem_image.mp hx
    specialize h p hps
    rw [isCompactElement_iff_le_of_directed_sSup_le] at h
    specialize h d hemp hdir (le_trans (Finset.le_sup hps) hsup)
    simpa only [exists_prop]

theorem WellFoundedGT.isSupFiniteCompact [WellFoundedGT α] :
    IsSupFiniteCompact α := fun s => by
  let S := { x | ∃ t : Finset α, ↑t ⊆ s ∧ t.sup id = x }
  obtain ⟨m, ⟨t, ⟨ht₁, rfl⟩⟩, hm⟩ := wellFounded_gt.has_min S ⟨⊥, ∅, by simp⟩
  refine ⟨t, ht₁, (sSup_le _ _ fun y hy => ?_).antisymm ?_⟩
  · classical
    rw [eq_of_le_of_not_lt (Finset.sup_mono (t.subset_insert y))
        (hm _ ⟨insert y t, by simp [Set.insert_subset_iff, hy, ht₁]⟩)]
    simp
  · rw [Finset.sup_id_eq_sSup]
    exact sSup_le_sSup ht₁

theorem IsSupFiniteCompact.isSupClosedCompact (h : IsSupFiniteCompact α) :
    IsSupClosedCompact α := by
  intro s hne hsc; obtain ⟨t, ht₁, ht₂⟩ := h s; clear h
  rcases t.eq_empty_or_nonempty with h | h
  · subst h
    rw [Finset.sup_empty] at ht₂
    rw [ht₂]
    simp [eq_singleton_bot_of_sSup_eq_bot_of_nonempty ht₂ hne]
  · rw [ht₂]
    exact hsc.finsetSup_mem h ht₁

theorem IsSupClosedCompact.wellFoundedGT (h : IsSupClosedCompact α) :
    WellFoundedGT α where
  wf := by
    refine RelEmbedding.wellFounded_iff_no_descending_seq.mpr ⟨fun a => ?_⟩
    suffices sSup (Set.range a) ∈ Set.range a by
      obtain ⟨n, hn⟩ := Set.mem_range.mp this
      have h' : sSup (Set.range a) < a (n + 1) := by
        change _ > _
        simp [← hn, a.map_rel_iff]
      apply lt_irrefl (a (n + 1))
      apply lt_of_le_of_lt _ h'
      apply le_sSup
      apply Set.mem_range_self
    apply h (Set.range a)
    · use a 37
      apply Set.mem_range_self
    · rintro x ⟨m, hm⟩ y ⟨n, hn⟩
      use m ⊔ n
      rw [← hm, ← hn]
      apply RelHomClass.map_sup a

theorem isSupFiniteCompact_iff_all_elements_compact :
    IsSupFiniteCompact α ↔ ∀ k : α, IsCompactElement k := by
  refine ⟨fun h k s hs => ?_, fun h s => ?_⟩
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h s
    use t, hts
    rwa [← htsup]
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h (sSup s) s (by rfl)
    have : sSup s = t.sup id := by
      suffices t.sup id ≤ sSup s by apply le_antisymm <;> assumption
      simp only [id, Finset.sup_le_iff]
      intro x hx
      exact le_sSup _ _ (hts hx)
    exact ⟨t, hts, this⟩

open List in
theorem wellFoundedGT_characterisations : List.TFAE
    [WellFoundedGT α, IsSupFiniteCompact α, IsSupClosedCompact α, ∀ k : α, IsCompactElement k] := by
  tfae_have 1 → 2 := @WellFoundedGT.isSupFiniteCompact α _
  tfae_have 2 → 3 := IsSupFiniteCompact.isSupClosedCompact α
  tfae_have 3 → 1 := IsSupClosedCompact.wellFoundedGT α
  tfae_have 2 ↔ 4 := isSupFiniteCompact_iff_all_elements_compact α
  tfae_finish

theorem wellFoundedGT_iff_isSupFiniteCompact :
    WellFoundedGT α ↔ IsSupFiniteCompact α :=
  (wellFoundedGT_characterisations α).out 0 1

theorem isSupFiniteCompact_iff_isSupClosedCompact : IsSupFiniteCompact α ↔ IsSupClosedCompact α :=
  (wellFoundedGT_characterisations α).out 1 2

theorem isSupClosedCompact_iff_wellFoundedGT :
    IsSupClosedCompact α ↔ WellFoundedGT α :=
  (wellFoundedGT_characterisations α).out 2 0

alias ⟨_, IsSupFiniteCompact.wellFoundedGT⟩ := wellFoundedGT_iff_isSupFiniteCompact

alias ⟨_, IsSupClosedCompact.isSupFiniteCompact⟩ := isSupFiniteCompact_iff_isSupClosedCompact

alias ⟨_, WellFoundedGT.isSupClosedCompact⟩ := isSupClosedCompact_iff_wellFoundedGT

end CompleteLattice


theorem WellFoundedGT.finite_of_sSupIndep [WellFoundedGT α] {s : Set α}
    (hs : sSupIndep s) : s.Finite := by
  classical
    refine Set.not_infinite.mp fun contra => ?_
    obtain ⟨t, ht₁, ht₂⟩ := CompleteLattice.WellFoundedGT.isSupFiniteCompact α s
    replace contra : ∃ x : α, x ∈ s ∧ x ≠ ⊥ ∧ x ∉ t := by
      have : (s \ (insert ⊥ t : Finset α)).Infinite := contra.diff (Finset.finite_toSet _)
      obtain ⟨x, hx₁, hx₂⟩ := this.nonempty
      exact ⟨x, hx₁, by simpa [not_or] using hx₂⟩
    obtain ⟨x, hx₀, hx₁, hx₂⟩ := contra
    replace hs : x ⊓ sSup s = ⊥ := by
      have := hs.mono (by simp [ht₁, hx₀, -Set.union_singleton] : ↑t ∪ {x} ≤ s) (by simp : x ∈ _)
      simpa [Disjoint, hx₂, ← t.sup_id_eq_sSup, ← ht₂] using this.eq_bot
    apply hx₁
    rw [← hs, eq_comm, inf_eq_left]
    exact le_sSup hx₀

theorem WellFoundedGT.finite_ne_bot_of_iSupIndep [WellFoundedGT α]
    {ι : Type*} {t : ι → α} (ht : iSupIndep t) : Set.Finite {i | t i ≠ ⊥} := by
  refine Finite.of_finite_image (Finite.subset ?_ (image_subset_range t _)) ht.injOn
  exact WellFoundedGT.finite_of_sSupIndep ht.sSupIndep_range

theorem WellFoundedGT.finite_of_iSupIndep [WellFoundedGT α] {ι : Type*}
    {t : ι → α} (ht : iSupIndep t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Finite ι :=
  haveI := (WellFoundedGT.finite_of_sSupIndep ht.sSupIndep_range).to_subtype
  Finite.of_injective_finite_range (ht.injective h_ne_bot)

theorem WellFoundedLT.finite_of_sSupIndep [WellFoundedLT α] {s : Set α}
    (hs : sSupIndep s) : s.Finite := by
  by_contra inf
  let e := (Infinite.diff inf <| finite_singleton ⊥).to_subtype.natEmbedding
  let a n := ⨆ i ≥ n, (e i).1
  have sup_le n : (e n).1 ⊔ a (n + 1) ≤ a n := sup_le_iff.mpr ⟨le_iSup₂_of_le n le_rfl le_rfl,
    iSup₂_le fun i hi ↦ le_iSup₂_of_le i (n.le_succ.trans hi) le_rfl⟩
  have lt n : a (n + 1) < a n := (Disjoint.right_lt_sup_of_left_ne_bot
    ((hs (e n).2.1).mono_right <| iSup₂_le fun i hi ↦ le_sSup ?_) (e n).2.2).trans_le (sup_le n)
  · exact (RelEmbedding.natGT a lt).not_wellFounded_of_decreasing_seq wellFounded_lt
  exact ⟨(e i).2.1, fun h ↦ n.lt_succ_self.not_ge <| hi.trans_eq <| e.2 <| Subtype.val_injective h⟩

theorem WellFoundedLT.finite_ne_bot_of_iSupIndep [WellFoundedLT α]
    {ι : Type*} {t : ι → α} (ht : iSupIndep t) : Set.Finite {i | t i ≠ ⊥} := by
  refine Finite.of_finite_image (Finite.subset ?_ (image_subset_range t _)) ht.injOn
  exact WellFoundedLT.finite_of_sSupIndep ht.sSupIndep_range

theorem WellFoundedLT.finite_of_iSupIndep [WellFoundedLT α] {ι : Type*}
    {t : ι → α} (ht : iSupIndep t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Finite ι :=
  haveI := (WellFoundedLT.finite_of_sSupIndep ht.sSupIndep_range).to_subtype
  Finite.of_injective_finite_range (ht.injective h_ne_bot)

/-- A complete lattice is said to be compactly generated if any
element is the `sSup` of compact elements. -/
class IsCompactlyGenerated (α : Type*) [CompleteLattice α] : Prop where
  /-- In a compactly generated complete lattice,
  every element is the `sSup` of some set of compact elements. -/
  exists_sSup_eq : ∀ x : α, ∃ s : Set α, (∀ x ∈ s, CompleteLattice.IsCompactElement x) ∧ sSup s = x

section

variable [IsCompactlyGenerated α] {a : α} {s : Set α}

@[simp]
theorem sSup_compact_le_eq (b) :
    sSup { c : α | CompleteLattice.IsCompactElement c ∧ c ≤ b } = b := by
  rcases IsCompactlyGenerated.exists_sSup_eq b with ⟨s, hs, rfl⟩
  exact le_antisymm (sSup_le fun c hc => hc.2) (sSup_le_sSup fun c cs => ⟨hs c cs, le_sSup cs⟩)

@[simp]
theorem sSup_compact_eq_top : sSup { a : α | CompleteLattice.IsCompactElement a } = ⊤ := by
  refine Eq.trans (congr rfl (Set.ext fun x => ?_)) (sSup_compact_le_eq ⊤)
  exact (and_iff_left le_top).symm

theorem le_iff_compact_le_imp {a b : α} :
    a ≤ b ↔ ∀ c : α, CompleteLattice.IsCompactElement c → c ≤ a → c ≤ b :=
  ⟨fun ab _ _ ca => le_trans ca ab, fun h => by
    rw [← sSup_compact_le_eq a, ← sSup_compact_le_eq b]
    exact sSup_le_sSup fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩

/-- This property is sometimes referred to as `α` being upper continuous. -/
theorem DirectedOn.inf_sSup_eq (h : DirectedOn (· ≤ ·) s) : a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
  le_antisymm
    (by
      rw [le_iff_compact_le_imp]
      by_cases hs : s.Nonempty
      · intro c hc hcinf
        rw [le_inf_iff] at hcinf
        rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le] at hc
        rcases hc s hs h hcinf.2 with ⟨d, ds, cd⟩
        refine (le_inf hcinf.1 cd).trans (le_trans ?_ (le_iSup₂ d ds))
        rfl
      · rw [Set.not_nonempty_iff_eq_empty] at hs
        simp [hs])
    iSup_inf_le_inf_sSup

/-- This property is sometimes referred to as `α` being upper continuous. -/
protected theorem DirectedOn.sSup_inf_eq (h : DirectedOn (· ≤ ·) s) :
    sSup s ⊓ a = ⨆ b ∈ s, b ⊓ a := by
  simp_rw [inf_comm _ a, h.inf_sSup_eq]

protected theorem Directed.inf_iSup_eq (h : Directed (· ≤ ·) f) :
    (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i := by
  rw [iSup, h.directedOn_range.inf_sSup_eq, iSup_range]

protected theorem Directed.iSup_inf_eq (h : Directed (· ≤ ·) f) :
    (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a := by
  rw [iSup, h.directedOn_range.sSup_inf_eq, iSup_range]

protected theorem DirectedOn.disjoint_sSup_right (h : DirectedOn (· ≤ ·) s) :
    Disjoint a (sSup s) ↔ ∀ ⦃b⦄, b ∈ s → Disjoint a b := by
  simp_rw [disjoint_iff, h.inf_sSup_eq, iSup_eq_bot]

protected theorem DirectedOn.disjoint_sSup_left (h : DirectedOn (· ≤ ·) s) :
    Disjoint (sSup s) a ↔ ∀ ⦃b⦄, b ∈ s → Disjoint b a := by
  simp_rw [disjoint_iff, h.sSup_inf_eq, iSup_eq_bot]

protected theorem Directed.disjoint_iSup_right (h : Directed (· ≤ ·) f) :
    Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simp_rw [disjoint_iff, h.inf_iSup_eq, iSup_eq_bot]

protected theorem Directed.disjoint_iSup_left (h : Directed (· ≤ ·) f) :
    Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp_rw [disjoint_iff, h.iSup_inf_eq, iSup_eq_bot]

/-- This property is equivalent to `α` being upper continuous. -/
theorem inf_sSup_eq_iSup_inf_sup_finset :
    a ⊓ sSup s = ⨆ (t : Finset α) (_ : ↑t ⊆ s), a ⊓ t.sup id :=
  le_antisymm
    (by
      rw [le_iff_compact_le_imp]
      intro c hc hcinf
      rw [le_inf_iff] at hcinf
      rcases hc s hcinf.2 with ⟨t, ht1, ht2⟩
      refine (le_inf hcinf.1 ht2).trans (le_trans ?_ (le_iSup₂ t ht1))
      rfl)
    (iSup_le fun t =>
      iSup_le fun h => inf_le_inf_left _ ((Finset.sup_id_eq_sSup t).symm ▸ sSup_le_sSup h))

theorem sSupIndep_iff_finite {s : Set α} :
    sSupIndep s ↔
      ∀ t : Finset α, ↑t ⊆ s → sSupIndep (↑t : Set α) :=
  ⟨fun hs _ ht => hs.mono ht, fun h a ha => by
    rw [disjoint_iff, inf_sSup_eq_iSup_inf_sup_finset, iSup_eq_bot]
    intro t
    rw [iSup_eq_bot, Finset.sup_id_eq_sSup]
    intro ht
    classical
      have h' := (h (insert a t) ?_ (t.mem_insert_self a)).eq_bot
      · rwa [Finset.coe_insert, Set.insert_diff_self_of_notMem] at h'
        exact fun con => ((Set.mem_diff a).1 (ht con)).2 (Set.mem_singleton a)
      · rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨ha, Set.Subset.trans ht diff_subset⟩⟩

lemma iSupIndep_iff_supIndep_of_injOn {ι : Type*} {f : ι → α}
    (hf : InjOn f {i | f i ≠ ⊥}) :
    iSupIndep f ↔ ∀ (s : Finset ι), s.SupIndep f := by
  refine ⟨fun h ↦ h.supIndep', fun h ↦ iSupIndep_def'.mpr fun i ↦ ?_⟩
  simp_rw [disjoint_iff, inf_sSup_eq_iSup_inf_sup_finset, iSup_eq_bot, ← disjoint_iff]
  intro s hs
  classical
  rw [← Finset.sup_erase_bot]
  set t := s.erase ⊥
  replace hf : InjOn f (f ⁻¹' t) := fun i hi j _ hij ↦ by
    refine hf ?_ ?_ hij <;> aesop (add norm simp [t])
  have : (Finset.erase (insert i (t.preimage _ hf)) i).image f = t := by
    ext a
    simp only [Finset.mem_preimage, Finset.mem_erase, ne_eq,
      Finset.erase_insert_eq_erase, Finset.mem_image, t]
    refine ⟨by aesop, fun ⟨ha, has⟩ ↦ ?_⟩
    obtain ⟨j, hj, rfl⟩ := hs has
    exact ⟨j, ⟨hj, ha, has⟩, rfl⟩
  rw [← this, Finset.sup_image]
  specialize h (insert i (t.preimage _ hf))
  rw [Finset.supIndep_iff_disjoint_erase] at h
  exact h i (Finset.mem_insert_self i _)

theorem sSupIndep_iUnion_of_directed {η : Type*} {s : η → Set α}
    (hs : Directed (· ⊆ ·) s) (h : ∀ i, sSupIndep (s i)) :
    sSupIndep (⋃ i, s i) := by
  by_cases hη : Nonempty η
  · rw [sSupIndep_iff_finite]
    intro t ht
    obtain ⟨I, fi, hI⟩ := Set.finite_subset_iUnion t.finite_toSet ht
    obtain ⟨i, hi⟩ := hs.finset_le fi.toFinset
    exact (h i).mono
        (Set.Subset.trans hI <| Set.iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
  · rintro a ⟨_, ⟨i, _⟩, _⟩
    exfalso
    exact hη ⟨i⟩

theorem iSupIndep_sUnion_of_directed {s : Set (Set α)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ a ∈ s, sSupIndep a) : sSupIndep (⋃₀ s) := by
  rw [Set.sUnion_eq_iUnion]
  exact sSupIndep_iUnion_of_directed hs.directed_val (by simpa using h)

end

namespace CompleteLattice

theorem isCompactlyGenerated_of_wellFoundedGT [h : WellFoundedGT α] :
    IsCompactlyGenerated α := by
  rw [wellFoundedGT_iff_isSupFiniteCompact, isSupFiniteCompact_iff_all_elements_compact] at h
  -- x is the join of the set of compact elements {x}
  exact ⟨fun x => ⟨{x}, ⟨fun x _ => h x, sSup_singleton⟩⟩⟩

/-- A compact element `k` has the property that any `b < k` lies below a "maximal element below
`k`", which is to say `[⊥, k]` is coatomic. -/
theorem Iic_coatomic_of_compact_element {k : α} (h : IsCompactElement k) :
    IsCoatomic (Set.Iic k) := by
  constructor
  rintro ⟨b, hbk⟩
  obtain rfl | H := eq_or_ne b k
  · left; ext; simp only [Set.Iic.coe_top]
  right
  have ⟨a, ba, h⟩ := zorn_le_nonempty₀ (Set.Iio k) ?_ b (lt_of_le_of_ne hbk H)
  · refine ⟨⟨a, le_of_lt h.prop⟩, ⟨ne_of_lt h.prop, fun c hck => by_contradiction fun c₀ => ?_⟩, ba⟩
    cases h.eq_of_le (y := c.1) (lt_of_le_of_ne c.2 fun con ↦ c₀ (Subtype.ext con)) hck.le
    exact lt_irrefl _ hck
  · intro S SC cC I _
    by_cases hS : S.Nonempty
    · refine ⟨sSup S, h.directed_sSup_lt_of_lt hS cC.directedOn SC, ?_⟩
      intro; apply le_sSup
    exact
      ⟨b, lt_of_le_of_ne hbk H, by
        simp only [Set.not_nonempty_iff_eq_empty.mp hS, Set.mem_empty_iff_false, forall_const,
          forall_prop_of_false, not_false_iff]⟩

theorem coatomic_of_top_compact (h : IsCompactElement (⊤ : α)) : IsCoatomic α :=
  (@OrderIso.IicTop α _ _).isCoatomic_iff.mp (Iic_coatomic_of_compact_element h)

end CompleteLattice

section

variable [IsModularLattice α] [IsCompactlyGenerated α]

instance (priority := 100) isAtomic_of_complementedLattice [ComplementedLattice α] : IsAtomic α :=
  ⟨fun b => by
    by_cases h : { c : α | CompleteLattice.IsCompactElement c ∧ c ≤ b } ⊆ {⊥}
    · left
      rw [← sSup_compact_le_eq b, sSup_eq_bot]
      exact h
    · rcases Set.not_subset.1 h with ⟨c, ⟨hc, hcb⟩, hcbot⟩
      right
      have hc' := CompleteLattice.Iic_coatomic_of_compact_element hc
      rw [← isAtomic_iff_isCoatomic] at hc'
      obtain con | ⟨a, ha, hac⟩ := eq_bot_or_exists_atom_le (⟨c, le_refl c⟩ : Set.Iic c)
      · exfalso
        apply hcbot
        simp only [Subtype.ext_iff, Set.Iic.coe_bot] at con
        exact con
      rw [← Subtype.coe_le_coe, Subtype.coe_mk] at hac
      exact ⟨a, ha.of_isAtom_coe_Iic, hac.trans hcb⟩⟩

/-- See [Lemma 5.1][calugareanu]. -/
instance (priority := 100) isAtomistic_of_complementedLattice [ComplementedLattice α] :
    IsAtomistic α :=
  CompleteLattice.isAtomistic_iff.2 fun b =>
    ⟨{ a | IsAtom a ∧ a ≤ b }, by
      symm
      have hle : sSup { a : α | IsAtom a ∧ a ≤ b } ≤ b := sSup_le fun _ => And.right
      apply (lt_or_eq_of_le hle).resolve_left _
      intro con
      obtain ⟨c, hc⟩ := exists_isCompl (⟨sSup { a : α | IsAtom a ∧ a ≤ b }, hle⟩ : Set.Iic b)
      obtain rfl | ⟨a, ha, hac⟩ := eq_bot_or_exists_atom_le c
      · exact ne_of_lt con (Subtype.ext_iff.1 (eq_top_of_isCompl_bot hc))
      · apply ha.1
        rw [eq_bot_iff]
        apply le_trans (le_inf _ hac) hc.disjoint.le_bot
        rw [← Subtype.coe_le_coe, Subtype.coe_mk]
        exact le_sSup ⟨ha.of_isAtom_coe_Iic, a.2⟩, fun _ => And.left⟩

/-!
Now we will prove that a compactly generated modular atomistic lattice is a complemented lattice.
Most explicitly, every element is the complement of a supremum of indepedendent atoms.
-/

/-- In an atomic lattice, every element `b` has a complement of the form `sSup s` relative to a
given element `c`, where each element of `s` is an atom.
See also `complementedLattice_of_sSup_atoms_eq_top`. -/
theorem exists_sSupIndep_disjoint_sSup_atoms (b c : α) (hbc : b ≤ c)
    (h : sSup {a ≤ c | IsAtom a} = c) :
    ∃ s : Set α, sSupIndep s ∧ Disjoint b (sSup s) ∧ b ⊔ sSup s = c ∧ ∀ ⦃a⦄, a ∈ s → IsAtom a := by
  -- porting note(https://github.com/leanprover-community/mathlib4/issues/5732):
  -- `obtain` chokes on the placeholder.
  have zorn := zorn_subset
    (S := {s : Set α | sSupIndep s ∧ Disjoint b (sSup s) ∧ ∀ a ∈ s, IsAtom a ∧ a ≤ c})
    fun c hc1 hc2 =>
      ⟨⋃₀ c,
        ⟨iSupIndep_sUnion_of_directed hc2.directedOn fun s hs => (hc1 hs).1, ?_,
          fun a ⟨s, sc, as⟩ => (hc1 sc).2.2 a as⟩,
        fun _ => Set.subset_sUnion_of_mem⟩
  swap
  · rw [sSup_sUnion, ← sSup_image, DirectedOn.disjoint_sSup_right]
    · rintro _ ⟨s, hs, rfl⟩
      exact (hc1 hs).2.1
    · rw [directedOn_image]
      exact hc2.directedOn.mono @fun s t => sSup_le_sSup
  simp_rw [maximal_subset_iff] at zorn
  obtain ⟨s, ⟨s_ind, b_inf_Sup_s, s_atoms⟩, s_max⟩ := zorn
  refine ⟨s, s_ind, b_inf_Sup_s, le_antisymm ?_ ?_, fun a ha ↦ (s_atoms a ha).1⟩
  · aesop
  rw [← h, sSup_le_iff]
  intro a ha
  rw [← inf_eq_left]
  refine (ha.2.le_iff.mp inf_le_left).resolve_left fun con => ha.2.1 ?_
  rw [← con, eq_comm, inf_eq_left]
  refine (le_sSup ?_).trans le_sup_right
  rw [← disjoint_iff] at con
  have a_dis_Sup_s : Disjoint a (sSup s) := con.mono_right le_sup_right
  rw [s_max ⟨fun x hx => ?_, ?_, fun x hx => ?_⟩ Set.subset_union_left]
  · exact Set.mem_union_right _ (Set.mem_singleton _)
  · rw [sSup_union, sSup_singleton]
    exact b_inf_Sup_s.disjoint_sup_right_of_disjoint_sup_left con.symm
  · rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain rfl | xa := eq_or_ne x a
    · simp only [Set.mem_singleton, Set.insert_diff_of_mem, Set.union_singleton]
      exact con.mono_right ((sSup_le_sSup Set.diff_subset).trans le_sup_right)
    · have h : (s ∪ {a}) \ {x} = s \ {x} ∪ {a} := by
        simp only [Set.union_singleton]
        rw [Set.insert_diff_of_notMem]
        rw [Set.mem_singleton_iff]
        exact Ne.symm xa
      rw [h, sSup_union, sSup_singleton]
      apply
        (s_ind (hx.resolve_right xa)).disjoint_sup_right_of_disjoint_sup_left
          (a_dis_Sup_s.mono_right _).symm
      rw [← sSup_insert, Set.insert_diff_singleton, Set.insert_eq_of_mem (hx.resolve_right xa)]
  · rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain hx | rfl := hx
    · exact s_atoms x hx
    · exact ha.symm

/-- In an atomic lattice, every element `b` has a complement of the form `sSup s`, where each
element of `s` is an atom. See also `complementedLattice_of_sSup_atoms_eq_top`. -/
theorem exists_sSupIndep_isCompl_sSup_atoms (h : sSup { a : α | IsAtom a } = ⊤) (b : α) :
    ∃ s : Set α, sSupIndep s ∧ IsCompl b (sSup s) ∧ ∀ ⦃a⦄, a ∈ s → IsAtom a := by
  simpa [isCompl_iff, codisjoint_iff, and_assoc]
    using exists_sSupIndep_disjoint_sSup_atoms b ⊤ le_top <| by simpa using h

theorem exists_sSupIndep_of_sSup_atoms (b : α) (h : sSup {a ≤ b | IsAtom a} = b) :
    ∃ s : Set α, sSupIndep s ∧ sSup s = b ∧ ∀ ⦃a⦄, a ∈ s → IsAtom a :=
  let ⟨s, s_ind, _, s_atoms⟩ := exists_sSupIndep_disjoint_sSup_atoms ⊥ b bot_le h
  ⟨s, s_ind, by simpa using s_atoms⟩

theorem exists_sSupIndep_of_sSup_atoms_eq_top (h : sSup {a : α | IsAtom a} = ⊤) :
    ∃ s : Set α, sSupIndep s ∧ sSup s = ⊤ ∧ ∀ ⦃a⦄, a ∈ s → IsAtom a :=
  exists_sSupIndep_of_sSup_atoms ⊤ (by simpa)

/-- See [Theorem 6.6][calugareanu]. -/
theorem complementedLattice_of_sSup_atoms_eq_top (h : sSup { a : α | IsAtom a } = ⊤) :
    ComplementedLattice α where
  exists_isCompl b :=
    let ⟨s, _, hcompl, _⟩ := exists_sSupIndep_isCompl_sSup_atoms (by simpa) b
    ⟨sSup s, hcompl⟩

/-- See [Theorem 6.6][calugareanu]. -/
theorem complementedLattice_of_isAtomistic [IsAtomistic α] : ComplementedLattice α :=
  complementedLattice_of_sSup_atoms_eq_top sSup_atoms_eq_top

theorem complementedLattice_iff_isAtomistic : ComplementedLattice α ↔ IsAtomistic α := by
  constructor <;> intros
  · exact isAtomistic_of_complementedLattice
  · exact complementedLattice_of_isAtomistic

end
