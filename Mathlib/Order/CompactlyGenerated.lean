/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Order.Atoms
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.RelIso.Set
import Mathlib.Order.SupIndep
import Mathlib.Order.Zorn
import Mathlib.Data.Finset.Order
import Mathlib.Data.Set.Intervals.OrderIso
import Mathlib.Data.Finite.Set
import Mathlib.Tactic.TFAE

#align_import order.compactly_generated from "leanprover-community/mathlib"@"c813ed7de0f5115f956239124e9b30f3a621966f"

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

variable {ι : Sort*} {α : Type*} [CompleteLattice α] {f : ι → α}

namespace CompleteLattice

variable (α)

/-- A compactness property for a complete lattice is that any `sup`-closed non-empty subset
contains its `sSup`. -/
def IsSupClosedCompact : Prop :=
  ∀ (s : Set α) (_ : s.Nonempty), (∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), a ⊔ b ∈ s) → sSup s ∈ s
#align complete_lattice.is_sup_closed_compact CompleteLattice.IsSupClosedCompact

/-- A compactness property for a complete lattice is that any subset has a finite subset with the
same `sSup`. -/
def IsSupFiniteCompact : Prop :=
  ∀ s : Set α, ∃ t : Finset α, ↑t ⊆ s ∧ sSup s = t.sup id
#align complete_lattice.is_Sup_finite_compact CompleteLattice.IsSupFiniteCompact

/-- An element `k` of a complete lattice is said to be compact if any set with `sSup`
above `k` has a finite subset with `sSup` above `k`.  Such an element is also called
"finite" or "S-compact". -/
def IsCompactElement {α : Type*} [CompleteLattice α] (k : α) :=
  ∀ s : Set α, k ≤ sSup s → ∃ t : Finset α, ↑t ⊆ s ∧ k ≤ t.sup id
#align complete_lattice.is_compact_element CompleteLattice.IsCompactElement

theorem isCompactElement_iff.{u} {α : Type u} [CompleteLattice α] (k : α) :
    CompleteLattice.IsCompactElement k ↔
      ∀ (ι : Type u) (s : ι → α), k ≤ iSup s → ∃ t : Finset ι, k ≤ t.sup s := by
  classical
    constructor
    · intro H ι s hs
      obtain ⟨t, ht, ht'⟩ := H (Set.range s) hs
      have : ∀ x : t, ∃ i, s i = x := fun x => ht x.prop
      choose f hf using this
      refine' ⟨Finset.univ.image f, ht'.trans _⟩
      · rw [Finset.sup_le_iff]
        intro b hb
        rw [← show s (f ⟨b, hb⟩) = id b from hf _]
        exact Finset.le_sup (Finset.mem_image_of_mem f <| Finset.mem_univ (Subtype.mk b hb))
    · intro H s hs
      obtain ⟨t, ht⟩ :=
        H s Subtype.val
          (by
            delta iSup
            rwa [Subtype.range_coe])
      refine' ⟨t.image Subtype.val, by simp, ht.trans _⟩
      rw [Finset.sup_le_iff]
      exact fun x hx => @Finset.le_sup _ _ _ _ _ id _ (Finset.mem_image_of_mem Subtype.val hx)
#align complete_lattice.is_compact_element_iff CompleteLattice.isCompactElement_iff

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
        simpa only [and_true_iff, id.def, Finset.coe_singleton, eq_self_iff_true,
          Finset.sup_singleton, Set.singleton_subset_iff]
      have Sne : S.Nonempty := by
        suffices : ⊥ ∈ S
        exact Set.nonempty_of_mem this
        use ∅
        simp only [Set.empty_subset, Finset.coe_empty, Finset.sup_empty, eq_self_iff_true,
          and_self_iff]
      -- Now apply the defn of compact and finish.
      obtain ⟨j, ⟨hjS, hjk⟩⟩ := hk S Sne dir_US (le_trans hsup sup_S)
      obtain ⟨t, ⟨htS, htsup⟩⟩ := hjS
      use t
      exact ⟨htS, by rwa [← htsup]⟩
#align complete_lattice.is_compact_element_iff_le_of_directed_Sup_le CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le

theorem IsCompactElement.exists_finset_of_le_iSup {k : α} (hk : IsCompactElement k) {ι : Type*}
    (f : ι → α) (h : k ≤ ⨆ i, f i) : ∃ s : Finset ι, k ≤ ⨆ i ∈ s, f i := by
  classical
    let g : Finset ι → α := fun s => ⨆ i ∈ s, f i
    have h1 : DirectedOn (· ≤ ·) (Set.range g) := by
      rintro - ⟨s, rfl⟩ - ⟨t, rfl⟩
      exact
        ⟨g (s ∪ t), ⟨s ∪ t, rfl⟩, iSup_le_iSup_of_subset (Finset.subset_union_left s t),
          iSup_le_iSup_of_subset (Finset.subset_union_right s t)⟩
    have h2 : k ≤ sSup (Set.range g) :=
      h.trans
        (iSup_le fun i =>
          le_sSup_of_le ⟨{i}, rfl⟩
            (le_iSup_of_le i (le_iSup_of_le (Finset.mem_singleton_self i) le_rfl)))
    obtain ⟨-, ⟨s, rfl⟩, hs⟩ :=
      (isCompactElement_iff_le_of_directed_sSup_le α k).mp hk (Set.range g) (Set.range_nonempty g)
        h1 h2
    exact ⟨s, hs⟩
#align complete_lattice.is_compact_element.exists_finset_of_le_supr CompleteLattice.IsCompactElement.exists_finset_of_le_iSup

/-- A compact element `k` has the property that any directed set lying strictly below `k` has
its `sSup` strictly below `k`. -/
theorem IsCompactElement.directed_sSup_lt_of_lt {α : Type*} [CompleteLattice α] {k : α}
    (hk : IsCompactElement k) {s : Set α} (hemp : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hbelow : ∀ x ∈ s, x < k) : sSup s < k := by
  rw [isCompactElement_iff_le_of_directed_sSup_le] at hk
  -- ⊢ sSup s < k
  by_contra h
  -- ⊢ False
  have sSup' : sSup s ≤ k := sSup_le s k fun s hs => (hbelow s hs).le
  -- ⊢ False
  replace sSup : sSup s = k := eq_iff_le_not_lt.mpr ⟨sSup', h⟩
  -- ⊢ False
  obtain ⟨x, hxs, hkx⟩ := hk s hemp hdir sSup.symm.le
  -- ⊢ False
  obtain hxk := hbelow x hxs
  -- ⊢ False
  exact hxk.ne (hxk.le.antisymm hkx)
  -- 🎉 no goals
#align complete_lattice.is_compact_element.directed_Sup_lt_of_lt CompleteLattice.IsCompactElement.directed_sSup_lt_of_lt

theorem finset_sup_compact_of_compact {α β : Type*} [CompleteLattice α] {f : β → α} (s : Finset β)
    (h : ∀ x ∈ s, IsCompactElement (f x)) : IsCompactElement (s.sup f) := by
  classical
    rw [isCompactElement_iff_le_of_directed_sSup_le]
    intro d hemp hdir hsup
    rw [← Function.comp.left_id f]
    rw [← Finset.sup_image]
    apply Finset.sup_le_of_le_directed d hemp hdir
    rintro x hx
    obtain ⟨p, ⟨hps, rfl⟩⟩ := Finset.mem_image.mp hx
    specialize h p hps
    rw [isCompactElement_iff_le_of_directed_sSup_le] at h
    specialize h d hemp hdir (le_trans (Finset.le_sup hps) hsup)
    simpa only [exists_prop]
#align complete_lattice.finset_sup_compact_of_compact CompleteLattice.finset_sup_compact_of_compact

theorem WellFounded.isSupFiniteCompact (h : WellFounded ((· > ·) : α → α → Prop)) :
    IsSupFiniteCompact α := fun s => by
  let S := { x | ∃ t : Finset α, ↑t ⊆ s ∧ t.sup id = x }
  -- ⊢ ∃ t, ↑t ⊆ s ∧ sSup s = Finset.sup t id
  obtain ⟨m, ⟨t, ⟨ht₁, rfl⟩⟩, hm⟩ := h.has_min S ⟨⊥, ∅, by simp⟩
  -- ⊢ ∃ t, ↑t ⊆ s ∧ sSup s = Finset.sup t id
  refine' ⟨t, ht₁, (sSup_le _ _ fun y hy => _).antisymm _⟩
  -- ⊢ y ≤ Finset.sup t id
  · classical
    rw [eq_of_le_of_not_lt (Finset.sup_mono (t.subset_insert y))
        (hm _ ⟨insert y t, by simp [Set.insert_subset_iff, hy, ht₁]⟩)]
    simp
  · rw [Finset.sup_id_eq_sSup]
    -- ⊢ sSup ↑t ≤ sSup s
    exact sSup_le_sSup ht₁
    -- 🎉 no goals
#align complete_lattice.well_founded.is_Sup_finite_compact CompleteLattice.WellFounded.isSupFiniteCompact

theorem IsSupFiniteCompact.isSupClosedCompact (h : IsSupFiniteCompact α) :
    IsSupClosedCompact α := by
  intro s hne hsc; obtain ⟨t, ht₁, ht₂⟩ := h s; clear h
  -- ⊢ sSup s ∈ s
                   -- ⊢ sSup s ∈ s
                                                -- ⊢ sSup s ∈ s
  cases' t.eq_empty_or_nonempty with h h
  -- ⊢ sSup s ∈ s
  · subst h
    -- ⊢ sSup s ∈ s
    rw [Finset.sup_empty] at ht₂
    -- ⊢ sSup s ∈ s
    rw [ht₂]
    -- ⊢ ⊥ ∈ s
    simp [eq_singleton_bot_of_sSup_eq_bot_of_nonempty ht₂ hne]
    -- 🎉 no goals
  · rw [ht₂]
    -- ⊢ Finset.sup t id ∈ s
    exact t.sup_closed_of_sup_closed h ht₁ hsc
    -- 🎉 no goals
#align complete_lattice.is_Sup_finite_compact.is_sup_closed_compact CompleteLattice.IsSupFiniteCompact.isSupClosedCompact

theorem IsSupClosedCompact.wellFounded (h : IsSupClosedCompact α) :
    WellFounded ((· > ·) : α → α → Prop) := by
  refine' RelEmbedding.wellFounded_iff_no_descending_seq.mpr ⟨fun a => _⟩
  -- ⊢ False
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
  -- ⊢ Set.Nonempty (Set.range ↑a)
  · use a 37
    -- ⊢ ↑a 37 ∈ Set.range ↑a
    apply Set.mem_range_self
    -- 🎉 no goals
  · rintro x ⟨m, hm⟩ y ⟨n, hn⟩
    -- ⊢ x ⊔ y ∈ Set.range ↑a
    use m ⊔ n
    -- ⊢ ↑a (m ⊔ n) = x ⊔ y
    rw [← hm, ← hn]
    -- ⊢ ↑a (m ⊔ n) = ↑a m ⊔ ↑a n
    apply RelHomClass.map_sup a
    -- 🎉 no goals
#align complete_lattice.is_sup_closed_compact.well_founded CompleteLattice.IsSupClosedCompact.wellFounded

theorem isSupFiniteCompact_iff_all_elements_compact :
    IsSupFiniteCompact α ↔ ∀ k : α, IsCompactElement k := by
  refine' ⟨fun h k s hs => _, fun h s => _⟩
  -- ⊢ ∃ t, ↑t ⊆ s ∧ k ≤ Finset.sup t id
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h s
    -- ⊢ ∃ t, ↑t ⊆ s ∧ k ≤ Finset.sup t id
    use t, hts
    -- ⊢ k ≤ Finset.sup t id
    rwa [← htsup]
    -- 🎉 no goals
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h (sSup s) s (by rfl)
    -- ⊢ ∃ t, ↑t ⊆ s ∧ sSup s = Finset.sup t id
    have : sSup s = t.sup id := by
      suffices t.sup id ≤ sSup s by apply le_antisymm <;> assumption
      simp only [id.def, Finset.sup_le_iff]
      intro x hx
      exact le_sSup _ _ (hts hx)
    exact ⟨t, hts, this⟩
    -- 🎉 no goals
#align complete_lattice.is_Sup_finite_compact_iff_all_elements_compact CompleteLattice.isSupFiniteCompact_iff_all_elements_compact

open List in
theorem wellFounded_characterisations : List.TFAE
    [WellFounded (( · > · ) : α → α → Prop),
      IsSupFiniteCompact α, IsSupClosedCompact α, ∀ k : α, IsCompactElement k] := by
  tfae_have 1 → 2
  -- ⊢ (WellFounded fun x x_1 => x > x_1) → IsSupFiniteCompact α
  · exact WellFounded.isSupFiniteCompact α
    -- 🎉 no goals
  tfae_have 2 → 3
  -- ⊢ IsSupFiniteCompact α → IsSupClosedCompact α
  · exact IsSupFiniteCompact.isSupClosedCompact α
    -- 🎉 no goals
  tfae_have 3 → 1
  -- ⊢ IsSupClosedCompact α → WellFounded fun x x_1 => x > x_1
  · exact IsSupClosedCompact.wellFounded α
    -- 🎉 no goals
  tfae_have 2 ↔ 4
  -- ⊢ IsSupFiniteCompact α ↔ ∀ (k : α), IsCompactElement k
  · exact isSupFiniteCompact_iff_all_elements_compact α
    -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals
#align complete_lattice.well_founded_characterisations CompleteLattice.wellFounded_characterisations

theorem wellFounded_iff_isSupFiniteCompact :
    WellFounded ((· > ·) : α → α → Prop) ↔ IsSupFiniteCompact α :=
  (wellFounded_characterisations α).out 0 1
#align complete_lattice.well_founded_iff_is_Sup_finite_compact CompleteLattice.wellFounded_iff_isSupFiniteCompact

theorem isSupFiniteCompact_iff_isSupClosedCompact : IsSupFiniteCompact α ↔ IsSupClosedCompact α :=
  (wellFounded_characterisations α).out 1 2
#align complete_lattice.is_Sup_finite_compact_iff_is_sup_closed_compact CompleteLattice.isSupFiniteCompact_iff_isSupClosedCompact

theorem isSupClosedCompact_iff_wellFounded :
    IsSupClosedCompact α ↔ WellFounded ((· > ·) : α → α → Prop) :=
  (wellFounded_characterisations α).out 2 0
#align complete_lattice.is_sup_closed_compact_iff_well_founded CompleteLattice.isSupClosedCompact_iff_wellFounded

alias ⟨_, IsSupFiniteCompact.wellFounded⟩ := wellFounded_iff_isSupFiniteCompact
#align complete_lattice.is_Sup_finite_compact.well_founded CompleteLattice.IsSupFiniteCompact.wellFounded

alias ⟨_, IsSupClosedCompact.isSupFiniteCompact⟩ := isSupFiniteCompact_iff_isSupClosedCompact
#align complete_lattice.is_sup_closed_compact.is_Sup_finite_compact CompleteLattice.IsSupClosedCompact.isSupFiniteCompact

alias ⟨_, _root_.WellFounded.isSupClosedCompact⟩ := isSupClosedCompact_iff_wellFounded
#align well_founded.is_sup_closed_compact WellFounded.isSupClosedCompact

variable {α}

theorem WellFounded.finite_of_setIndependent (h : WellFounded ((· > ·) : α → α → Prop)) {s : Set α}
    (hs : SetIndependent s) : s.Finite := by
  classical
    refine' Set.not_infinite.mp fun contra => _
    obtain ⟨t, ht₁, ht₂⟩ := WellFounded.isSupFiniteCompact α h s
    replace contra : ∃ x : α, x ∈ s ∧ x ≠ ⊥ ∧ x ∉ t
    · have : (s \ (insert ⊥ t : Finset α)).Infinite := contra.diff (Finset.finite_toSet _)
      obtain ⟨x, hx₁, hx₂⟩ := this.nonempty
      exact ⟨x, hx₁, by simpa [not_or] using hx₂⟩
    obtain ⟨x, hx₀, hx₁, hx₂⟩ := contra
    replace hs : x ⊓ sSup s = ⊥
    · have := hs.mono (by simp [ht₁, hx₀, -Set.union_singleton] : ↑t ∪ {x} ≤ s) (by simp : x ∈ _)
      simpa [Disjoint, hx₂, ← t.sup_id_eq_sSup, ← ht₂] using this.eq_bot
    apply hx₁
    rw [← hs, eq_comm, inf_eq_left]
    exact le_sSup _ _ hx₀
#align complete_lattice.well_founded.finite_of_set_independent CompleteLattice.WellFounded.finite_of_setIndependent

theorem WellFounded.finite_of_independent (hwf : WellFounded ((· > ·) : α → α → Prop)) {ι : Type*}
    {t : ι → α} (ht : Independent t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Finite ι :=
  haveI := (WellFounded.finite_of_setIndependent hwf ht.setIndependent_range).to_subtype
  Finite.of_injective_finite_range (ht.injective h_ne_bot)
#align complete_lattice.well_founded.finite_of_independent CompleteLattice.WellFounded.finite_of_independent

end CompleteLattice

/-- A complete lattice is said to be compactly generated if any
element is the `sSup` of compact elements. -/
class IsCompactlyGenerated (α : Type*) [CompleteLattice α] : Prop where
  /-- In a compactly generated complete lattice,
    every element is the `sSup` of some set of compact elements. -/
  exists_sSup_eq : ∀ x : α, ∃ s : Set α, (∀ x ∈ s, CompleteLattice.IsCompactElement x) ∧ sSup s = x
#align is_compactly_generated IsCompactlyGenerated

section

variable [CompleteLattice α] [IsCompactlyGenerated α] {a b : α} {s : Set α}

@[simp]
theorem sSup_compact_le_eq (b) :
    sSup { c : α | CompleteLattice.IsCompactElement c ∧ c ≤ b } = b := by
  rcases IsCompactlyGenerated.exists_sSup_eq b with ⟨s, hs, rfl⟩
  -- ⊢ sSup {c | CompleteLattice.IsCompactElement c ∧ c ≤ sSup s} = sSup s
  exact le_antisymm (sSup_le fun c hc => hc.2) (sSup_le_sSup fun c cs => ⟨hs c cs, le_sSup cs⟩)
  -- 🎉 no goals
#align Sup_compact_le_eq sSup_compact_le_eq

@[simp]
theorem sSup_compact_eq_top : sSup { a : α | CompleteLattice.IsCompactElement a } = ⊤ := by
  refine' Eq.trans (congr rfl (Set.ext fun x => _)) (sSup_compact_le_eq ⊤)
  -- ⊢ x ∈ {a | CompleteLattice.IsCompactElement a} ↔ x ∈ {c | CompleteLattice.IsCo …
  exact (and_iff_left le_top).symm
  -- 🎉 no goals
#align Sup_compact_eq_top sSup_compact_eq_top

theorem le_iff_compact_le_imp {a b : α} :
    a ≤ b ↔ ∀ c : α, CompleteLattice.IsCompactElement c → c ≤ a → c ≤ b :=
  ⟨fun ab c _ ca => le_trans ca ab, fun h => by
    rw [← sSup_compact_le_eq a, ← sSup_compact_le_eq b]
    -- ⊢ sSup {c | CompleteLattice.IsCompactElement c ∧ c ≤ a} ≤ sSup {c | CompleteLa …
    exact sSup_le_sSup fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩
    -- 🎉 no goals
#align le_iff_compact_le_imp le_iff_compact_le_imp

/-- This property is sometimes referred to as `α` being upper continuous. -/
theorem DirectedOn.inf_sSup_eq (h : DirectedOn (· ≤ ·) s) : a ⊓ sSup s = ⨆ b ∈ s, a ⊓ b :=
  le_antisymm
    (by
      rw [le_iff_compact_le_imp]
      -- ⊢ ∀ (c : α), CompleteLattice.IsCompactElement c → c ≤ a ⊓ sSup s → c ≤ ⨆ (b :  …
      by_cases hs : s.Nonempty
      -- ⊢ ∀ (c : α), CompleteLattice.IsCompactElement c → c ≤ a ⊓ sSup s → c ≤ ⨆ (b :  …
      · intro c hc hcinf
        -- ⊢ c ≤ ⨆ (b : α) (_ : b ∈ s), a ⊓ b
        rw [le_inf_iff] at hcinf
        -- ⊢ c ≤ ⨆ (b : α) (_ : b ∈ s), a ⊓ b
        rw [CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le] at hc
        -- ⊢ c ≤ ⨆ (b : α) (_ : b ∈ s), a ⊓ b
        rcases hc s hs h hcinf.2 with ⟨d, ds, cd⟩
        -- ⊢ c ≤ ⨆ (b : α) (_ : b ∈ s), a ⊓ b
        refine' (le_inf hcinf.1 cd).trans (le_trans _ (le_iSup₂ d ds))
        -- ⊢ a ⊓ d ≤ a ⊓ d
        rfl
        -- 🎉 no goals
      · rw [Set.not_nonempty_iff_eq_empty] at hs
        -- ⊢ ∀ (c : α), CompleteLattice.IsCompactElement c → c ≤ a ⊓ sSup s → c ≤ ⨆ (b :  …
        simp [hs])
        -- 🎉 no goals
    iSup_inf_le_inf_sSup
#align directed_on.inf_Sup_eq DirectedOn.inf_sSup_eq

/-- This property is sometimes referred to as `α` being upper continuous. -/
protected theorem DirectedOn.sSup_inf_eq (h : DirectedOn (· ≤ ·) s) : sSup s ⊓ a = ⨆ b ∈ s, b ⊓ a :=
  by simp_rw [@inf_comm _ _ _ a, h.inf_sSup_eq]
     -- 🎉 no goals
#align directed_on.Sup_inf_eq DirectedOn.sSup_inf_eq

protected theorem Directed.inf_iSup_eq (h : Directed (· ≤ ·) f) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i :=
  by rw [iSup, h.directedOn_range.inf_sSup_eq, iSup_range]
     -- 🎉 no goals
#align directed.inf_supr_eq Directed.inf_iSup_eq

protected theorem Directed.iSup_inf_eq (h : Directed (· ≤ ·) f) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a :=
  by rw [iSup, h.directedOn_range.sSup_inf_eq, iSup_range]
     -- 🎉 no goals
#align directed.supr_inf_eq Directed.iSup_inf_eq

protected theorem DirectedOn.disjoint_sSup_right (h : DirectedOn (· ≤ ·) s) :
    Disjoint a (sSup s) ↔ ∀ ⦃b⦄, b ∈ s → Disjoint a b := by
  simp_rw [disjoint_iff, h.inf_sSup_eq, iSup_eq_bot]
  -- 🎉 no goals
#align directed_on.disjoint_Sup_right DirectedOn.disjoint_sSup_right

protected theorem DirectedOn.disjoint_sSup_left (h : DirectedOn (· ≤ ·) s) :
    Disjoint (sSup s) a ↔ ∀ ⦃b⦄, b ∈ s → Disjoint b a := by
  simp_rw [disjoint_iff, h.sSup_inf_eq, iSup_eq_bot]
  -- 🎉 no goals
#align directed_on.disjoint_Sup_left DirectedOn.disjoint_sSup_left

protected theorem Directed.disjoint_iSup_right (h : Directed (· ≤ ·) f) :
    Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simp_rw [disjoint_iff, h.inf_iSup_eq, iSup_eq_bot]
  -- 🎉 no goals
#align directed.disjoint_supr_right Directed.disjoint_iSup_right

protected theorem Directed.disjoint_iSup_left (h : Directed (· ≤ ·) f) :
    Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp_rw [disjoint_iff, h.iSup_inf_eq, iSup_eq_bot]
  -- 🎉 no goals
#align directed.disjoint_supr_left Directed.disjoint_iSup_left

/-- This property is equivalent to `α` being upper continuous. -/
theorem inf_sSup_eq_iSup_inf_sup_finset :
    a ⊓ sSup s = ⨆ (t : Finset α) (_ : ↑t ⊆ s), a ⊓ t.sup id :=
  le_antisymm
    (by
      rw [le_iff_compact_le_imp]
      -- ⊢ ∀ (c : α), CompleteLattice.IsCompactElement c → c ≤ a ⊓ sSup s → c ≤ ⨆ (t :  …
      intro c hc hcinf
      -- ⊢ c ≤ ⨆ (t : Finset α) (_ : ↑t ⊆ s), a ⊓ Finset.sup t id
      rw [le_inf_iff] at hcinf
      -- ⊢ c ≤ ⨆ (t : Finset α) (_ : ↑t ⊆ s), a ⊓ Finset.sup t id
      rcases hc s hcinf.2 with ⟨t, ht1, ht2⟩
      -- ⊢ c ≤ ⨆ (t : Finset α) (_ : ↑t ⊆ s), a ⊓ Finset.sup t id
      refine' (le_inf hcinf.1 ht2).trans (le_trans _ (le_iSup₂ t ht1))
      -- ⊢ a ⊓ Finset.sup t id ≤ a ⊓ Finset.sup t id
      rfl)
      -- 🎉 no goals
    (iSup_le fun t =>
      iSup_le fun h => inf_le_inf_left _ ((Finset.sup_id_eq_sSup t).symm ▸ sSup_le_sSup h))
#align inf_Sup_eq_supr_inf_sup_finset inf_sSup_eq_iSup_inf_sup_finset

theorem CompleteLattice.setIndependent_iff_finite {s : Set α} :
    CompleteLattice.SetIndependent s ↔
      ∀ t : Finset α, ↑t ⊆ s → CompleteLattice.SetIndependent (↑t : Set α) :=
  ⟨fun hs t ht => hs.mono ht, fun h a ha => by
    rw [disjoint_iff, inf_sSup_eq_iSup_inf_sup_finset, iSup_eq_bot]
    -- ⊢ ∀ (i : Finset α), ⨆ (_ : ↑i ⊆ s \ {a}), a ⊓ Finset.sup i id = ⊥
    intro t
    -- ⊢ ⨆ (_ : ↑t ⊆ s \ {a}), a ⊓ Finset.sup t id = ⊥
    rw [iSup_eq_bot, Finset.sup_id_eq_sSup]
    -- ⊢ ↑t ⊆ s \ {a} → a ⊓ sSup ↑t = ⊥
    intro ht
    -- ⊢ a ⊓ sSup ↑t = ⊥
    classical
      have h' := (h (insert a t) ?_ (t.mem_insert_self a)).eq_bot
      · rwa [Finset.coe_insert, Set.insert_diff_self_of_not_mem] at h'
        exact fun con => ((Set.mem_diff a).1 (ht con)).2 (Set.mem_singleton a)
      · rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨ha, Set.Subset.trans ht (Set.diff_subset _ _)⟩⟩
#align complete_lattice.set_independent_iff_finite CompleteLattice.setIndependent_iff_finite

theorem CompleteLattice.setIndependent_iUnion_of_directed {η : Type*} {s : η → Set α}
    (hs : Directed (· ⊆ ·) s) (h : ∀ i, CompleteLattice.SetIndependent (s i)) :
    CompleteLattice.SetIndependent (⋃ i, s i) := by
  by_cases hη : Nonempty η
  -- ⊢ SetIndependent (⋃ (i : η), s i)
  · rw [CompleteLattice.setIndependent_iff_finite]
    -- ⊢ ∀ (t : Finset α), ↑t ⊆ ⋃ (i : η), s i → SetIndependent ↑t
    intro t ht
    -- ⊢ SetIndependent ↑t
    obtain ⟨I, fi, hI⟩ := Set.finite_subset_iUnion t.finite_toSet ht
    -- ⊢ SetIndependent ↑t
    obtain ⟨i, hi⟩ := hs.finset_le fi.toFinset
    -- ⊢ SetIndependent ↑t
    exact (h i).mono
        (Set.Subset.trans hI <| Set.iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
  · rintro a ⟨_, ⟨i, _⟩, _⟩
    -- ⊢ Disjoint a (sSup ((⋃ (i : η), s i) \ {a}))
    exfalso
    -- ⊢ False
    exact hη ⟨i⟩
    -- 🎉 no goals
#align complete_lattice.set_independent_Union_of_directed CompleteLattice.setIndependent_iUnion_of_directed

theorem CompleteLattice.independent_sUnion_of_directed {s : Set (Set α)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ a ∈ s, CompleteLattice.SetIndependent a) : CompleteLattice.SetIndependent (⋃₀ s) := by
  rw [Set.sUnion_eq_iUnion]
  -- ⊢ SetIndependent (⋃ (i : ↑s), ↑i)
  exact CompleteLattice.setIndependent_iUnion_of_directed hs.directed_val (by simpa using h)
  -- 🎉 no goals
#align complete_lattice.independent_sUnion_of_directed CompleteLattice.independent_sUnion_of_directed

end

namespace CompleteLattice

theorem isCompactlyGenerated_of_wellFounded (h : WellFounded ((· > ·) : α → α → Prop)) :
    IsCompactlyGenerated α := by
  rw [wellFounded_iff_isSupFiniteCompact, isSupFiniteCompact_iff_all_elements_compact] at h
  -- ⊢ IsCompactlyGenerated α
  -- x is the join of the set of compact elements {x}
  exact ⟨fun x => ⟨{x}, ⟨fun x _ => h x, sSup_singleton⟩⟩⟩
  -- 🎉 no goals
#align complete_lattice.compactly_generated_of_well_founded CompleteLattice.isCompactlyGenerated_of_wellFounded

/-- A compact element `k` has the property that any `b < k` lies below a "maximal element below
`k`", which is to say `[⊥, k]` is coatomic. -/
theorem Iic_coatomic_of_compact_element {k : α} (h : IsCompactElement k) :
    IsCoatomic (Set.Iic k) := by
  constructor
  -- ⊢ ∀ (b : ↑(Set.Iic k)), b = ⊤ ∨ ∃ a, IsCoatom a ∧ b ≤ a
  rintro ⟨b, hbk⟩
  -- ⊢ { val := b, property := hbk } = ⊤ ∨ ∃ a, IsCoatom a ∧ { val := b, property : …
  obtain rfl | H := eq_or_ne b k
  -- ⊢ { val := b, property := hbk } = ⊤ ∨ ∃ a, IsCoatom a ∧ { val := b, property : …
  · left; ext; simp only [Set.Iic.coe_top, Subtype.coe_mk]
    -- ⊢ { val := b, property := hbk } = ⊤
          -- ⊢ ↑{ val := b, property := hbk } = ↑⊤
               -- 🎉 no goals
  right
  -- ⊢ ∃ a, IsCoatom a ∧ { val := b, property := hbk } ≤ a
  have ⟨a, a₀, ba, h⟩ := zorn_nonempty_partialOrder₀ (Set.Iio k) ?_ b (lt_of_le_of_ne hbk H)
  -- ⊢ ∃ a, IsCoatom a ∧ { val := b, property := hbk } ≤ a
  · refine' ⟨⟨a, le_of_lt a₀⟩, ⟨ne_of_lt a₀, fun c hck => by_contradiction fun c₀ => _⟩, ba⟩
    -- ⊢ False
    cases h c.1 (lt_of_le_of_ne c.2 fun con => c₀ (Subtype.ext con)) hck.le
    -- ⊢ False
    exact lt_irrefl _ hck
    -- 🎉 no goals
  · intro S SC cC I _
    -- ⊢ ∃ ub, ub ∈ Set.Iio k ∧ ∀ (z : α), z ∈ S → z ≤ ub
    by_cases hS : S.Nonempty
    -- ⊢ ∃ ub, ub ∈ Set.Iio k ∧ ∀ (z : α), z ∈ S → z ≤ ub
    · refine' ⟨sSup S, h.directed_sSup_lt_of_lt hS cC.directedOn SC, _⟩
      -- ⊢ ∀ (z : α), z ∈ S → z ≤ sSup S
      intro; apply le_sSup
      -- ⊢ z✝ ∈ S → z✝ ≤ sSup S
             -- 🎉 no goals
    exact
      ⟨b, lt_of_le_of_ne hbk H, by
        simp only [Set.not_nonempty_iff_eq_empty.mp hS, Set.mem_empty_iff_false, forall_const,
          forall_prop_of_false, not_false_iff]⟩
#align complete_lattice.Iic_coatomic_of_compact_element CompleteLattice.Iic_coatomic_of_compact_element

theorem coatomic_of_top_compact (h : IsCompactElement (⊤ : α)) : IsCoatomic α :=
  (@OrderIso.IicTop α _ _).isCoatomic_iff.mp (Iic_coatomic_of_compact_element h)
#align complete_lattice.coatomic_of_top_compact CompleteLattice.coatomic_of_top_compact

end CompleteLattice

section

variable [IsModularLattice α] [IsCompactlyGenerated α]

instance (priority := 100) isAtomic_of_complementedLattice [ComplementedLattice α] : IsAtomic α :=
  ⟨fun b => by
    by_cases h : { c : α | CompleteLattice.IsCompactElement c ∧ c ≤ b } ⊆ {⊥}
    -- ⊢ b = ⊥ ∨ ∃ a, IsAtom a ∧ a ≤ b
    · left
      -- ⊢ b = ⊥
      rw [← sSup_compact_le_eq b, sSup_eq_bot]
      -- ⊢ ∀ (a : α), a ∈ {c | CompleteLattice.IsCompactElement c ∧ c ≤ b} → a = ⊥
      exact h
      -- 🎉 no goals
    · rcases Set.not_subset.1 h with ⟨c, ⟨hc, hcb⟩, hcbot⟩
      -- ⊢ b = ⊥ ∨ ∃ a, IsAtom a ∧ a ≤ b
      right
      -- ⊢ ∃ a, IsAtom a ∧ a ≤ b
      have hc' := CompleteLattice.Iic_coatomic_of_compact_element hc
      -- ⊢ ∃ a, IsAtom a ∧ a ≤ b
      rw [← isAtomic_iff_isCoatomic] at hc'
      -- ⊢ ∃ a, IsAtom a ∧ a ≤ b
      haveI := hc'
      -- ⊢ ∃ a, IsAtom a ∧ a ≤ b
      obtain con | ⟨a, ha, hac⟩ := eq_bot_or_exists_atom_le (⟨c, le_refl c⟩ : Set.Iic c)
      -- ⊢ ∃ a, IsAtom a ∧ a ≤ b
      · exfalso
        -- ⊢ False
        apply hcbot
        -- ⊢ c ∈ {⊥}
        simp only [Subtype.ext_iff, Set.Iic.coe_bot, Subtype.coe_mk] at con
        -- ⊢ c ∈ {⊥}
        exact con
        -- 🎉 no goals
      rw [← Subtype.coe_le_coe, Subtype.coe_mk] at hac
      -- ⊢ ∃ a, IsAtom a ∧ a ≤ b
      exact ⟨a, ha.of_isAtom_coe_Iic, hac.trans hcb⟩⟩
      -- 🎉 no goals
#align is_atomic_of_complemented_lattice isAtomic_of_complementedLattice

/-- See [Lemma 5.1][calugareanu]. -/
instance (priority := 100) isAtomistic_of_complementedLattice [ComplementedLattice α] :
    IsAtomistic α :=
  ⟨fun b =>
    ⟨{ a | IsAtom a ∧ a ≤ b }, by
      symm
      -- ⊢ sSup {a | IsAtom a ∧ a ≤ b} = b
      have hle : sSup { a : α | IsAtom a ∧ a ≤ b } ≤ b := sSup_le fun _ => And.right
      -- ⊢ sSup {a | IsAtom a ∧ a ≤ b} = b
      apply (lt_or_eq_of_le hle).resolve_left _
      -- ⊢ ¬sSup {a | IsAtom a ∧ a ≤ b} < b
      intro con
      -- ⊢ False
      obtain ⟨c, hc⟩ := exists_isCompl (⟨sSup { a : α | IsAtom a ∧ a ≤ b }, hle⟩ : Set.Iic b)
      -- ⊢ False
      obtain rfl | ⟨a, ha, hac⟩ := eq_bot_or_exists_atom_le c
      -- ⊢ False
      · exact ne_of_lt con (Subtype.ext_iff.1 (eq_top_of_isCompl_bot hc))
        -- 🎉 no goals
      · apply ha.1
        -- ⊢ a = ⊥
        rw [eq_bot_iff]
        -- ⊢ a ≤ ⊥
        apply le_trans (le_inf _ hac) hc.disjoint.le_bot
        -- ⊢ a ≤ { val := sSup {a | IsAtom a ∧ a ≤ b}, property := hle }
        rw [← Subtype.coe_le_coe, Subtype.coe_mk]
        -- ⊢ ↑a ≤ ↑{ val := sSup {a | IsAtom a ∧ a ≤ b}, property := hle }
        exact le_sSup ⟨ha.of_isAtom_coe_Iic, a.2⟩, fun _ => And.left⟩⟩
        -- 🎉 no goals
#align is_atomistic_of_complemented_lattice isAtomistic_of_complementedLattice

/-!
Now we will prove that a compactly generated modular atomistic lattice is a complemented lattice.
Most explicitly, every element is the complement of a supremum of indepedendent atoms.
-/

/-- In an atomic lattice, every element `b` has a complement of the form `sSup s`, where each
element of `s` is an atom. See also `complementedLattice_of_sSup_atoms_eq_top`. -/
theorem exists_setIndependent_isCompl_sSup_atoms (h : sSup { a : α | IsAtom a } = ⊤) (b : α) :
    ∃ s : Set α, CompleteLattice.SetIndependent s ∧
    IsCompl b (sSup s) ∧ ∀ ⦃a⦄, a ∈ s → IsAtom a := by
  -- porting note(https://github.com/leanprover-community/mathlib4/issues/5732):
  -- `obtain` chokes on the placeholder.
  have := zorn_subset
    {s : Set α | CompleteLattice.SetIndependent s ∧ Disjoint b (sSup s) ∧ ∀ a ∈ s, IsAtom a}
    fun c hc1 hc2 =>
      ⟨⋃₀ c,
        ⟨CompleteLattice.independent_sUnion_of_directed hc2.directedOn fun s hs => (hc1 hs).1, ?_,
          fun a ⟨s, sc, as⟩ => (hc1 sc).2.2 a as⟩,
        fun _ => Set.subset_sUnion_of_mem⟩
  obtain ⟨s, ⟨s_ind, b_inf_Sup_s, s_atoms⟩, s_max⟩ := this
  -- ⊢ ∃ s, CompleteLattice.SetIndependent s ∧ IsCompl b (sSup s) ∧ ∀ ⦃a : α⦄, a ∈  …
  swap
  -- ⊢ Disjoint b (sSup (⋃₀ c))
  · rw [sSup_sUnion, ← sSup_image, DirectedOn.disjoint_sSup_right]
    -- ⊢ ∀ ⦃b_1 : α⦄, b_1 ∈ (fun t => sSup t) '' c → Disjoint b b_1
    · rintro _ ⟨s, hs, rfl⟩
      -- ⊢ Disjoint b ((fun t => sSup t) s)
      exact (hc1 hs).2.1
      -- 🎉 no goals
    · rw [directedOn_image]
      -- ⊢ DirectedOn ((fun t => sSup t) ⁻¹'o fun x x_1 => x ≤ x_1) c
      exact hc2.directedOn.mono @fun s t => sSup_le_sSup
      -- 🎉 no goals
  refine' ⟨s, s_ind, ⟨b_inf_Sup_s, _⟩, s_atoms⟩
  -- ⊢ Codisjoint b (sSup s)
  rw [codisjoint_iff_le_sup, ← h, sSup_le_iff]
  -- ⊢ ∀ (b_1 : α), b_1 ∈ {a | IsAtom a} → b_1 ≤ b ⊔ sSup s
  intro a ha
  -- ⊢ a ≤ b ⊔ sSup s
  rw [← inf_eq_left]
  -- ⊢ a ⊓ (b ⊔ sSup s) = a
  refine' (ha.le_iff.mp inf_le_left).resolve_left fun con => ha.1 _
  -- ⊢ a = ⊥
  rw [← con, eq_comm, inf_eq_left]
  -- ⊢ a ≤ b ⊔ sSup s
  refine' (le_sSup _).trans le_sup_right
  -- ⊢ a ∈ s
  rw [← disjoint_iff] at con
  -- ⊢ a ∈ s
  have a_dis_Sup_s : Disjoint a (sSup s) := con.mono_right le_sup_right
  -- ⊢ a ∈ s
  -- porting note: The two following `fun x hx => _` are no-op
  rw [← s_max (s ∪ {a}) ⟨fun x hx => _, _, fun x hx => _⟩ (Set.subset_union_left _ _)]
  · exact Set.mem_union_right _ (Set.mem_singleton _)
    -- 🎉 no goals
  · intro x hx
    -- ⊢ Disjoint x (sSup ((s ∪ {a}) \ {x}))
    rw [Set.mem_union, Set.mem_singleton_iff] at hx
    -- ⊢ Disjoint x (sSup ((s ∪ {a}) \ {x}))
    obtain rfl | xa := eq_or_ne x a
    -- ⊢ Disjoint x (sSup ((s ∪ {x}) \ {x}))
    · simp only [Set.mem_singleton, Set.insert_diff_of_mem, Set.union_singleton]
      -- ⊢ Disjoint x (sSup (s \ {x}))
      exact con.mono_right ((sSup_le_sSup <| Set.diff_subset _ _).trans le_sup_right)
      -- 🎉 no goals
    · have h : (s ∪ {a}) \ {x} = s \ {x} ∪ {a} := by
        simp only [Set.union_singleton]
        rw [Set.insert_diff_of_not_mem]
        rw [Set.mem_singleton_iff]
        exact Ne.symm xa
      rw [h, sSup_union, sSup_singleton]
      -- ⊢ Disjoint x (sSup (s \ {x}) ⊔ a)
      apply
        (s_ind (hx.resolve_right xa)).disjoint_sup_right_of_disjoint_sup_left
          (a_dis_Sup_s.mono_right _).symm
      rw [← sSup_insert, Set.insert_diff_singleton, Set.insert_eq_of_mem (hx.resolve_right xa)]
      -- 🎉 no goals
  · rw [sSup_union, sSup_singleton]
    -- ⊢ Disjoint b (sSup s ⊔ a)
    exact b_inf_Sup_s.disjoint_sup_right_of_disjoint_sup_left con.symm
    -- 🎉 no goals
  · intro x hx
    -- ⊢ IsAtom x
    rw [Set.mem_union, Set.mem_singleton_iff] at hx
    -- ⊢ IsAtom x
    obtain hx | rfl := hx
    -- ⊢ IsAtom x
    · exact s_atoms x hx
      -- 🎉 no goals
    · exact ha
      -- 🎉 no goals
#align exists_set_independent_is_compl_Sup_atoms exists_setIndependent_isCompl_sSup_atoms

theorem exists_setIndependent_of_sSup_atoms_eq_top (h : sSup { a : α | IsAtom a } = ⊤) :
    ∃ s : Set α, CompleteLattice.SetIndependent s ∧ sSup s = ⊤ ∧ ∀ ⦃a⦄, a ∈ s → IsAtom a :=
  let ⟨s, s_ind, s_top, s_atoms⟩ := exists_setIndependent_isCompl_sSup_atoms h ⊥
  ⟨s, s_ind, eq_top_of_isCompl_bot s_top.symm, s_atoms⟩
#align exists_set_independent_of_Sup_atoms_eq_top exists_setIndependent_of_sSup_atoms_eq_top

/-- See [Theorem 6.6][calugareanu]. -/
theorem complementedLattice_of_sSup_atoms_eq_top (h : sSup { a : α | IsAtom a } = ⊤) :
    ComplementedLattice α :=
  ⟨fun b =>
    let ⟨s, _, s_top, _⟩ := exists_setIndependent_isCompl_sSup_atoms h b
    ⟨sSup s, s_top⟩⟩
#align complemented_lattice_of_Sup_atoms_eq_top complementedLattice_of_sSup_atoms_eq_top

/-- See [Theorem 6.6][calugareanu]. -/
theorem complementedLattice_of_isAtomistic [IsAtomistic α] : ComplementedLattice α :=
  complementedLattice_of_sSup_atoms_eq_top sSup_atoms_eq_top
#align complemented_lattice_of_is_atomistic complementedLattice_of_isAtomistic

theorem complementedLattice_iff_isAtomistic : ComplementedLattice α ↔ IsAtomistic α := by
  constructor <;> intros
  -- ⊢ ComplementedLattice α → IsAtomistic α
                  -- ⊢ IsAtomistic α
                  -- ⊢ ComplementedLattice α
  · exact isAtomistic_of_complementedLattice
    -- 🎉 no goals
  · exact complementedLattice_of_isAtomistic
    -- 🎉 no goals
#align complemented_lattice_iff_is_atomistic complementedLattice_iff_isAtomistic

end
