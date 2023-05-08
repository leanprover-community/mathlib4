/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module order.compactly_generated
! leanprover-community/mathlib commit c813ed7de0f5115f956239124e9b30f3a621966f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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

variable {ι : Sort _} {α : Type _} [CompleteLattice α] {f : ι → α}

namespace CompleteLattice

variable (α)

/-- A compactness property for a complete lattice is that any `sup`-closed non-empty subset
contains its `supₛ`. -/
def IsSupClosedCompact : Prop :=
  ∀ (s : Set α) (_ : s.Nonempty), (∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), a ⊔ b ∈ s) → supₛ s ∈ s
#align complete_lattice.is_sup_closed_compact CompleteLattice.IsSupClosedCompact

/-- A compactness property for a complete lattice is that any subset has a finite subset with the
same `supₛ`. -/
def IsSupFiniteCompact : Prop :=
  ∀ s : Set α, ∃ t : Finset α, ↑t ⊆ s ∧ supₛ s = t.sup id
#align complete_lattice.is_Sup_finite_compact CompleteLattice.IsSupFiniteCompact

/-- An element `k` of a complete lattice is said to be compact if any set with `supₛ`
above `k` has a finite subset with `supₛ` above `k`.  Such an element is also called
"finite" or "S-compact". -/
def IsCompactElement {α : Type _} [CompleteLattice α] (k : α) :=
  ∀ s : Set α, k ≤ supₛ s → ∃ t : Finset α, ↑t ⊆ s ∧ k ≤ t.sup id
#align complete_lattice.is_compact_element CompleteLattice.IsCompactElement

theorem isCompactElement_iff.{u} {α : Type u} [CompleteLattice α] (k : α) :
    CompleteLattice.IsCompactElement k ↔
      ∀ (ι : Type u) (s : ι → α), k ≤ supᵢ s → ∃ t : Finset ι, k ≤ t.sup s := by
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
            delta supᵢ
            rwa [Subtype.range_coe])
      refine' ⟨t.image Subtype.val, by simp, ht.trans _⟩
      rw [Finset.sup_le_iff]
      exact fun x hx => @Finset.le_sup _ _ _ _ _ id _ (Finset.mem_image_of_mem Subtype.val hx)
#align complete_lattice.is_compact_element_iff CompleteLattice.isCompactElement_iff

/-- An element `k` is compact if and only if any directed set with `supₛ` above
`k` already got above `k` at some point in the set. -/
theorem isCompactElement_iff_le_of_directed_supₛ_le (k : α) :
    IsCompactElement k ↔
      ∀ s : Set α, s.Nonempty → DirectedOn (· ≤ ·) s → k ≤ supₛ s → ∃ x : α, x ∈ s ∧ k ≤ x := by
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
      have sup_S : supₛ s ≤ supₛ S := by
        apply supₛ_le_supₛ
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
#align complete_lattice.is_compact_element_iff_le_of_directed_Sup_le CompleteLattice.isCompactElement_iff_le_of_directed_supₛ_le

theorem IsCompactElement.exists_finset_of_le_supᵢ {k : α} (hk : IsCompactElement k) {ι : Type _}
    (f : ι → α) (h : k ≤ ⨆ i, f i) : ∃ s : Finset ι, k ≤ ⨆ i ∈ s, f i := by
  classical
    let g : Finset ι → α := fun s => ⨆ i ∈ s, f i
    have h1 : DirectedOn (· ≤ ·) (Set.range g) := by
      rintro - ⟨s, rfl⟩ - ⟨t, rfl⟩
      exact
        ⟨g (s ∪ t), ⟨s ∪ t, rfl⟩, supᵢ_le_supᵢ_of_subset (Finset.subset_union_left s t),
          supᵢ_le_supᵢ_of_subset (Finset.subset_union_right s t)⟩
    have h2 : k ≤ supₛ (Set.range g) :=
      h.trans
        (supᵢ_le fun i =>
          le_supₛ_of_le ⟨{i}, rfl⟩
            (le_supᵢ_of_le i (le_supᵢ_of_le (Finset.mem_singleton_self i) le_rfl)))
    obtain ⟨-, ⟨s, rfl⟩, hs⟩ :=
      (isCompactElement_iff_le_of_directed_supₛ_le α k).mp hk (Set.range g) (Set.range_nonempty g)
        h1 h2
    exact ⟨s, hs⟩
#align complete_lattice.is_compact_element.exists_finset_of_le_supr CompleteLattice.IsCompactElement.exists_finset_of_le_supᵢ

/-- A compact element `k` has the property that any directed set lying strictly below `k` has
its `supₛ` strictly below `k`. -/
theorem IsCompactElement.directed_supₛ_lt_of_lt {α : Type _} [CompleteLattice α] {k : α}
    (hk : IsCompactElement k) {s : Set α} (hemp : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s)
    (hbelow : ∀ x ∈ s, x < k) : supₛ s < k := by
  rw [isCompactElement_iff_le_of_directed_supₛ_le] at hk
  by_contra h
  have sSup : supₛ s ≤ k := supₛ_le s k fun s hs => (hbelow s hs).le
  replace sSup : supₛ s = k := eq_iff_le_not_lt.mpr ⟨sSup, h⟩
  obtain ⟨x, hxs, hkx⟩ := hk s hemp hdir sSup.symm.le
  obtain hxk := hbelow x hxs
  exact hxk.ne (hxk.le.antisymm hkx)
#align complete_lattice.is_compact_element.directed_Sup_lt_of_lt CompleteLattice.IsCompactElement.directed_supₛ_lt_of_lt

theorem finset_sup_compact_of_compact {α β : Type _} [CompleteLattice α] {f : β → α} (s : Finset β)
    (h : ∀ x ∈ s, IsCompactElement (f x)) : IsCompactElement (s.sup f) := by
  classical
    rw [isCompactElement_iff_le_of_directed_supₛ_le]
    intro d hemp hdir hsup
    rw [← Function.comp.left_id f]
    rw [← Finset.sup_image]
    apply Finset.sup_le_of_le_directed d hemp hdir
    rintro x hx
    obtain ⟨p, ⟨hps, rfl⟩⟩ := Finset.mem_image.mp hx
    specialize h p hps
    rw [isCompactElement_iff_le_of_directed_supₛ_le] at h
    specialize h d hemp hdir (le_trans (Finset.le_sup hps) hsup)
    simpa only [exists_prop]
#align complete_lattice.finset_sup_compact_of_compact CompleteLattice.finset_sup_compact_of_compact

theorem WellFounded.isSupFiniteCompact (h : WellFounded ((· > ·) : α → α → Prop)) :
    IsSupFiniteCompact α := fun s => by
  let S := { x | ∃ t : Finset α, ↑t ⊆ s ∧ t.sup id = x }
  obtain ⟨m, ⟨t, ⟨ht₁, rfl⟩⟩, hm⟩ := h.has_min S ⟨⊥, ∅, by simp⟩
  refine' ⟨t, ht₁, (supₛ_le _ _ fun y hy => _).antisymm _⟩
  · classical
    rw [eq_of_le_of_not_lt (Finset.sup_mono (t.subset_insert y))
        (hm _ ⟨insert y t, by simp [Set.insert_subset, hy, ht₁]⟩)]
    simp
  · rw [Finset.sup_id_eq_supₛ]
    exact supₛ_le_supₛ ht₁
#align complete_lattice.well_founded.is_Sup_finite_compact CompleteLattice.WellFounded.isSupFiniteCompact

theorem IsSupFiniteCompact.isSupClosedCompact (h : IsSupFiniteCompact α) :
    IsSupClosedCompact α := by
  intro s hne hsc; obtain ⟨t, ht₁, ht₂⟩ := h s; clear h
  cases' t.eq_empty_or_nonempty with h h
  · subst h
    rw [Finset.sup_empty] at ht₂
    rw [ht₂]
    simp [eq_singleton_bot_of_supₛ_eq_bot_of_nonempty ht₂ hne]
  · rw [ht₂]
    exact t.sup_closed_of_sup_closed h ht₁ hsc
#align complete_lattice.is_Sup_finite_compact.is_sup_closed_compact CompleteLattice.IsSupFiniteCompact.isSupClosedCompact

theorem IsSupClosedCompact.wellFounded (h : IsSupClosedCompact α) :
    WellFounded ((· > ·) : α → α → Prop) := by
  refine' RelEmbedding.wellFounded_iff_no_descending_seq.mpr ⟨fun a => _⟩
  suffices supₛ (Set.range a) ∈ Set.range a by
    obtain ⟨n, hn⟩ := Set.mem_range.mp this
    have h' : supₛ (Set.range a) < a (n + 1) := by
      change _ > _
      simp [← hn, a.map_rel_iff]
    apply lt_irrefl (a (n + 1))
    apply lt_of_le_of_lt _ h'
    apply le_supₛ
    apply Set.mem_range_self
  apply h (Set.range a)
  · use a 37
    apply Set.mem_range_self
  · rintro x ⟨m, hm⟩ y ⟨n, hn⟩
    use m ⊔ n
    rw [← hm, ← hn]
    apply RelHomClass.map_sup a
#align complete_lattice.is_sup_closed_compact.well_founded CompleteLattice.IsSupClosedCompact.wellFounded

theorem isSupFiniteCompact_iff_all_elements_compact :
    IsSupFiniteCompact α ↔ ∀ k : α, IsCompactElement k := by
  refine' ⟨fun h k s hs => _, fun h s => _⟩
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h s
    use t, hts
    rwa [← htsup]
  · obtain ⟨t, ⟨hts, htsup⟩⟩ := h (supₛ s) s (by rfl)
    have : supₛ s = t.sup id := by
      suffices t.sup id ≤ supₛ s by apply le_antisymm <;> assumption
      simp only [id.def, Finset.sup_le_iff]
      intro x hx
      exact le_supₛ _ _ (hts hx)
    exact ⟨t, hts, this⟩
#align complete_lattice.is_Sup_finite_compact_iff_all_elements_compact CompleteLattice.isSupFiniteCompact_iff_all_elements_compact

open List in
theorem wellFounded_characterisations : List.TFAE
    [WellFounded (( · > · ) : α → α → Prop),
      IsSupFiniteCompact α, IsSupClosedCompact α, ∀ k : α, IsCompactElement k] := by
  tfae_have 1 → 2
  · exact WellFounded.isSupFiniteCompact α
  tfae_have 2 → 3
  · exact IsSupFiniteCompact.isSupClosedCompact α
  tfae_have 3 → 1
  · exact IsSupClosedCompact.wellFounded α
  tfae_have 2 ↔ 4
  · exact isSupFiniteCompact_iff_all_elements_compact α
  tfae_finish
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

alias wellFounded_iff_isSupFiniteCompact ↔ _ IsSupFiniteCompact.wellFounded
#align complete_lattice.is_Sup_finite_compact.well_founded CompleteLattice.IsSupFiniteCompact.wellFounded

alias isSupFiniteCompact_iff_isSupClosedCompact ↔ _ IsSupClosedCompact.isSupFiniteCompact
#align complete_lattice.is_sup_closed_compact.is_Sup_finite_compact CompleteLattice.IsSupClosedCompact.isSupFiniteCompact

alias isSupClosedCompact_iff_wellFounded ↔ _ _root_.WellFounded.isSupClosedCompact
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
    replace hs : x ⊓ supₛ s = ⊥
    · have := hs.mono (by simp [ht₁, hx₀, -Set.union_singleton] : ↑t ∪ {x} ≤ s) (by simp : x ∈ _)
      simpa [Disjoint, hx₂, ← t.sup_id_eq_supₛ, ← ht₂] using this.eq_bot
    apply hx₁
    rw [← hs, eq_comm, inf_eq_left]
    exact le_supₛ _ _ hx₀
#align complete_lattice.well_founded.finite_of_set_independent CompleteLattice.WellFounded.finite_of_setIndependent

theorem WellFounded.finite_of_independent (hwf : WellFounded ((· > ·) : α → α → Prop)) {ι : Type _}
    {t : ι → α} (ht : Independent t) (h_ne_bot : ∀ i, t i ≠ ⊥) : Finite ι :=
  haveI := (WellFounded.finite_of_setIndependent hwf ht.setIndependent_range).to_subtype
  Finite.of_injective_finite_range (ht.injective h_ne_bot)
#align complete_lattice.well_founded.finite_of_independent CompleteLattice.WellFounded.finite_of_independent

end CompleteLattice

/-- A complete lattice is said to be compactly generated if any
element is the `supₛ` of compact elements. -/
class IsCompactlyGenerated (α : Type _) [CompleteLattice α] : Prop where
  /-- In a compactly generated complete lattice,
    every element is the `supₛ` of some set of compact elements. -/
  exists_supₛ_eq : ∀ x : α, ∃ s : Set α, (∀ x ∈ s, CompleteLattice.IsCompactElement x) ∧ supₛ s = x
#align is_compactly_generated IsCompactlyGenerated

section

variable [CompleteLattice α] [IsCompactlyGenerated α] {a b : α} {s : Set α}

@[simp]
theorem supₛ_compact_le_eq (b) :
    supₛ { c : α | CompleteLattice.IsCompactElement c ∧ c ≤ b } = b := by
  rcases IsCompactlyGenerated.exists_supₛ_eq b with ⟨s, hs, rfl⟩
  exact le_antisymm (supₛ_le fun c hc => hc.2) (supₛ_le_supₛ fun c cs => ⟨hs c cs, le_supₛ cs⟩)
#align Sup_compact_le_eq supₛ_compact_le_eq

@[simp]
theorem supₛ_compact_eq_top : supₛ { a : α | CompleteLattice.IsCompactElement a } = ⊤ := by
  refine' Eq.trans (congr rfl (Set.ext fun x => _)) (supₛ_compact_le_eq ⊤)
  exact (and_iff_left le_top).symm
#align Sup_compact_eq_top supₛ_compact_eq_top

theorem le_iff_compact_le_imp {a b : α} :
    a ≤ b ↔ ∀ c : α, CompleteLattice.IsCompactElement c → c ≤ a → c ≤ b :=
  ⟨fun ab c _ ca => le_trans ca ab, fun h => by
    rw [← supₛ_compact_le_eq a, ← supₛ_compact_le_eq b]
    exact supₛ_le_supₛ fun c hc => ⟨hc.1, h c hc.1 hc.2⟩⟩
#align le_iff_compact_le_imp le_iff_compact_le_imp

/-- This property is sometimes referred to as `α` being upper continuous. -/
theorem DirectedOn.inf_supₛ_eq (h : DirectedOn (· ≤ ·) s) : a ⊓ supₛ s = ⨆ b ∈ s, a ⊓ b :=
  le_antisymm
    (by
      rw [le_iff_compact_le_imp]
      by_cases hs : s.Nonempty
      · intro c hc hcinf
        rw [le_inf_iff] at hcinf
        rw [CompleteLattice.isCompactElement_iff_le_of_directed_supₛ_le] at hc
        rcases hc s hs h hcinf.2 with ⟨d, ds, cd⟩
        refine' (le_inf hcinf.1 cd).trans (le_trans _ (le_supᵢ₂ d ds))
        rfl
      · rw [Set.not_nonempty_iff_eq_empty] at hs
        simp [hs])
    supᵢ_inf_le_inf_supₛ
#align directed_on.inf_Sup_eq DirectedOn.inf_supₛ_eq

/-- This property is sometimes referred to as `α` being upper continuous. -/
protected theorem DirectedOn.supₛ_inf_eq (h : DirectedOn (· ≤ ·) s) : supₛ s ⊓ a = ⨆ b ∈ s, b ⊓ a :=
  by simp_rw [@inf_comm _ _ _ a, h.inf_supₛ_eq]
#align directed_on.Sup_inf_eq DirectedOn.supₛ_inf_eq

protected theorem Directed.inf_supᵢ_eq (h : Directed (· ≤ ·) f) : (a ⊓ ⨆ i, f i) = ⨆ i, a ⊓ f i :=
  by rw [supᵢ, h.directedOn_range.inf_supₛ_eq, supᵢ_range]
#align directed.inf_supr_eq Directed.inf_supᵢ_eq

protected theorem Directed.supᵢ_inf_eq (h : Directed (· ≤ ·) f) : (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a :=
  by rw [supᵢ, h.directedOn_range.supₛ_inf_eq, supᵢ_range]
#align directed.supr_inf_eq Directed.supᵢ_inf_eq

protected theorem DirectedOn.disjoint_supₛ_right (h : DirectedOn (· ≤ ·) s) :
    Disjoint a (supₛ s) ↔ ∀ ⦃b⦄, b ∈ s → Disjoint a b := by
  simp_rw [disjoint_iff, h.inf_supₛ_eq, supᵢ_eq_bot]
#align directed_on.disjoint_Sup_right DirectedOn.disjoint_supₛ_right

protected theorem DirectedOn.disjoint_supₛ_left (h : DirectedOn (· ≤ ·) s) :
    Disjoint (supₛ s) a ↔ ∀ ⦃b⦄, b ∈ s → Disjoint b a := by
  simp_rw [disjoint_iff, h.supₛ_inf_eq, supᵢ_eq_bot]
#align directed_on.disjoint_Sup_left DirectedOn.disjoint_supₛ_left

protected theorem Directed.disjoint_supᵢ_right (h : Directed (· ≤ ·) f) :
    Disjoint a (⨆ i, f i) ↔ ∀ i, Disjoint a (f i) := by
  simp_rw [disjoint_iff, h.inf_supᵢ_eq, supᵢ_eq_bot]
#align directed.disjoint_supr_right Directed.disjoint_supᵢ_right

protected theorem Directed.disjoint_supᵢ_left (h : Directed (· ≤ ·) f) :
    Disjoint (⨆ i, f i) a ↔ ∀ i, Disjoint (f i) a := by
  simp_rw [disjoint_iff, h.supᵢ_inf_eq, supᵢ_eq_bot]
#align directed.disjoint_supr_left Directed.disjoint_supᵢ_left

/-- This property is equivalent to `α` being upper continuous. -/
theorem inf_supₛ_eq_supᵢ_inf_sup_finset :
    a ⊓ supₛ s = ⨆ (t : Finset α) (_H : ↑t ⊆ s), a ⊓ t.sup id :=
  le_antisymm
    (by
      rw [le_iff_compact_le_imp]
      intro c hc hcinf
      rw [le_inf_iff] at hcinf
      rcases hc s hcinf.2 with ⟨t, ht1, ht2⟩
      refine' (le_inf hcinf.1 ht2).trans (le_trans _ (le_supᵢ₂ t ht1))
      rfl)
    (supᵢ_le fun t =>
      supᵢ_le fun h => inf_le_inf_left _ ((Finset.sup_id_eq_supₛ t).symm ▸ supₛ_le_supₛ h))
#align inf_Sup_eq_supr_inf_sup_finset inf_supₛ_eq_supᵢ_inf_sup_finset

theorem CompleteLattice.setIndependent_iff_finite {s : Set α} :
    CompleteLattice.SetIndependent s ↔
      ∀ t : Finset α, ↑t ⊆ s → CompleteLattice.SetIndependent (↑t : Set α) :=
  ⟨fun hs t ht => hs.mono ht, fun h a ha => by
    rw [disjoint_iff, inf_supₛ_eq_supᵢ_inf_sup_finset, supᵢ_eq_bot]
    intro t
    rw [supᵢ_eq_bot, Finset.sup_id_eq_supₛ]
    intro ht
    classical
      have h' := (h (insert a t) ?_ (t.mem_insert_self a)).eq_bot
      · rwa [Finset.coe_insert, Set.insert_diff_self_of_not_mem] at h'
        exact fun con => ((Set.mem_diff a).1 (ht con)).2 (Set.mem_singleton a)
      · rw [Finset.coe_insert, Set.insert_subset]
        exact ⟨ha, Set.Subset.trans ht (Set.diff_subset _ _)⟩⟩
#align complete_lattice.set_independent_iff_finite CompleteLattice.setIndependent_iff_finite

theorem CompleteLattice.setIndependent_unionᵢ_of_directed {η : Type _} {s : η → Set α}
    (hs : Directed (· ⊆ ·) s) (h : ∀ i, CompleteLattice.SetIndependent (s i)) :
    CompleteLattice.SetIndependent (⋃ i, s i) := by
  by_cases hη : Nonempty η
  · rw [CompleteLattice.setIndependent_iff_finite]
    intro t ht
    obtain ⟨I, fi, hI⟩ := Set.finite_subset_unionᵢ t.finite_toSet ht
    obtain ⟨i, hi⟩ := hs.finset_le fi.toFinset
    exact (h i).mono
        (Set.Subset.trans hI <| Set.unionᵢ₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
  · rintro a ⟨_, ⟨i, _⟩, _⟩
    exfalso
    exact hη ⟨i⟩
#align complete_lattice.set_independent_Union_of_directed CompleteLattice.setIndependent_unionᵢ_of_directed

theorem CompleteLattice.independent_unionₛ_of_directed {s : Set (Set α)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ a ∈ s, CompleteLattice.SetIndependent a) : CompleteLattice.SetIndependent (⋃₀ s) := by
  rw [Set.unionₛ_eq_unionᵢ]
  exact CompleteLattice.setIndependent_unionᵢ_of_directed hs.directed_val (by simpa using h)
#align complete_lattice.independent_sUnion_of_directed CompleteLattice.independent_unionₛ_of_directed

end

namespace CompleteLattice

theorem isCompactlyGenerated_of_wellFounded (h : WellFounded ((· > ·) : α → α → Prop)) :
    IsCompactlyGenerated α := by
  rw [wellFounded_iff_isSupFiniteCompact, isSupFiniteCompact_iff_all_elements_compact] at h
  -- x is the join of the set of compact elements {x}
  exact ⟨fun x => ⟨{x}, ⟨fun x _ => h x, supₛ_singleton⟩⟩⟩
#align complete_lattice.compactly_generated_of_well_founded CompleteLattice.isCompactlyGenerated_of_wellFounded

/-- A compact element `k` has the property that any `b < k` lies below a "maximal element below
`k`", which is to say `[⊥, k]` is coatomic. -/
theorem Iic_coatomic_of_compact_element {k : α} (h : IsCompactElement k) :
    IsCoatomic (Set.Iic k) := by
  constructor
  rintro ⟨b, hbk⟩
  obtain rfl | H := eq_or_ne b k
  · left; ext; simp only [Set.Iic.coe_top, Subtype.coe_mk]
  right
  have ih : ?_ := ?_ -- Porting note: this is an ugly hack, but `?ih` on the next line fails
  obtain ⟨a, a₀, ba, h⟩ := zorn_nonempty_partialOrder₀ (Set.Iio k) ih b (lt_of_le_of_ne hbk H)
  · refine' ⟨⟨a, le_of_lt a₀⟩, ⟨ne_of_lt a₀, fun c hck => by_contradiction fun c₀ => _⟩, ba⟩
    cases h c.1 (lt_of_le_of_ne c.2 fun con => c₀ (Subtype.ext con)) hck.le
    exact lt_irrefl _ hck
  · intro S SC cC I _
    by_cases hS : S.Nonempty
    · refine' ⟨supₛ S, h.directed_supₛ_lt_of_lt hS cC.directedOn SC, _⟩
      intro; apply le_supₛ
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
    · left
      rw [← supₛ_compact_le_eq b, supₛ_eq_bot]
      exact h
    · rcases Set.not_subset.1 h with ⟨c, ⟨hc, hcb⟩, hcbot⟩
      right
      have hc' := CompleteLattice.Iic_coatomic_of_compact_element hc
      rw [← isAtomic_iff_isCoatomic] at hc'
      haveI := hc'
      obtain con | ⟨a, ha, hac⟩ := eq_bot_or_exists_atom_le (⟨c, le_refl c⟩ : Set.Iic c)
      · exfalso
        apply hcbot
        simp only [Subtype.ext_iff, Set.Iic.coe_bot, Subtype.coe_mk] at con
        exact con
      rw [← Subtype.coe_le_coe, Subtype.coe_mk] at hac
      exact ⟨a, ha.of_isAtom_coe_Iic, hac.trans hcb⟩⟩
#align is_atomic_of_complemented_lattice isAtomic_of_complementedLattice

/-- See [Lemma 5.1][calugareanu]. -/
instance (priority := 100) isAtomistic_of_complementedLattice [ComplementedLattice α] :
    IsAtomistic α :=
  ⟨fun b =>
    ⟨{ a | IsAtom a ∧ a ≤ b }, by
      symm
      have hle : supₛ { a : α | IsAtom a ∧ a ≤ b } ≤ b := supₛ_le fun _ => And.right
      apply (lt_or_eq_of_le hle).resolve_left _
      intro con
      obtain ⟨c, hc⟩ := exists_isCompl (⟨supₛ { a : α | IsAtom a ∧ a ≤ b }, hle⟩ : Set.Iic b)
      obtain rfl | ⟨a, ha, hac⟩ := eq_bot_or_exists_atom_le c
      · exact ne_of_lt con (Subtype.ext_iff.1 (eq_top_of_isCompl_bot hc))
      · apply ha.1
        rw [eq_bot_iff]
        apply le_trans (le_inf _ hac) hc.disjoint.le_bot
        rw [← Subtype.coe_le_coe, Subtype.coe_mk]
        exact le_supₛ ⟨ha.of_isAtom_coe_Iic, a.2⟩, fun _ => And.left⟩⟩
#align is_atomistic_of_complemented_lattice isAtomistic_of_complementedLattice

/-!
Now we will prove that a compactly generated modular atomistic lattice is a complemented lattice.
Most explicitly, every element is the complement of a supremum of indepedendent atoms.
-/

/-- In an atomic lattice, every element `b` has a complement of the form `Sup s`, where each element
of `s` is an atom. See also `complemented_lattice_of_Sup_atoms_eq_top`. -/
theorem exists_setIndependent_isCompl_supₛ_atoms (h : supₛ { a : α | IsAtom a } = ⊤) (b : α) :
    ∃ s : Set α, CompleteLattice.SetIndependent s ∧
    IsCompl b (supₛ s) ∧ ∀ ⦃a⦄, a ∈ s → IsAtom a := by
  -- porting note: `obtain` chokes on the placeholder.
  have := zorn_subset
    {s : Set α | CompleteLattice.SetIndependent s ∧ Disjoint b (supₛ s) ∧ ∀ a ∈ s, IsAtom a}
    fun c hc1 hc2 =>
      ⟨⋃₀ c,
        ⟨CompleteLattice.independent_unionₛ_of_directed hc2.directedOn fun s hs => (hc1 hs).1, ?_,
          fun a ⟨s, sc, as⟩ => (hc1 sc).2.2 a as⟩,
        fun _ => Set.subset_unionₛ_of_mem⟩
  obtain ⟨s, ⟨s_ind, b_inf_Sup_s, s_atoms⟩, s_max⟩ := this
  swap
  · rw [supₛ_unionₛ, ← supₛ_image, DirectedOn.disjoint_supₛ_right]
    · rintro _ ⟨s, hs, rfl⟩
      exact (hc1 hs).2.1
    · rw [directedOn_image]
      exact hc2.directedOn.mono @fun s t => supₛ_le_supₛ
  refine' ⟨s, s_ind, ⟨b_inf_Sup_s, _⟩, s_atoms⟩
  rw [codisjoint_iff_le_sup, ← h, supₛ_le_iff]
  intro a ha
  rw [← inf_eq_left]
  refine' (ha.le_iff.mp inf_le_left).resolve_left fun con => ha.1 _
  rw [← con, eq_comm, inf_eq_left]
  refine' (le_supₛ _).trans le_sup_right
  rw [← disjoint_iff] at con
  have a_dis_Sup_s : Disjoint a (supₛ s) := con.mono_right le_sup_right
  -- porting note: The two following `fun x hx => _` are no-op
  rw [← s_max (s ∪ {a}) ⟨fun x hx => _, _, fun x hx => _⟩ (Set.subset_union_left _ _)]
  · exact Set.mem_union_right _ (Set.mem_singleton _)
  · intro x hx
    rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain rfl | xa := eq_or_ne x a
    · simp only [Set.mem_singleton, Set.insert_diff_of_mem, Set.union_singleton]
      exact con.mono_right ((supₛ_le_supₛ <| Set.diff_subset _ _).trans le_sup_right)
    · have h : (s ∪ {a}) \ {x} = s \ {x} ∪ {a} := by
        simp only [Set.union_singleton]
        rw [Set.insert_diff_of_not_mem]
        rw [Set.mem_singleton_iff]
        exact Ne.symm xa
      rw [h, supₛ_union, supₛ_singleton]
      apply
        (s_ind (hx.resolve_right xa)).disjoint_sup_right_of_disjoint_sup_left
          (a_dis_Sup_s.mono_right _).symm
      rw [← supₛ_insert, Set.insert_diff_singleton, Set.insert_eq_of_mem (hx.resolve_right xa)]
  · rw [supₛ_union, supₛ_singleton]
    exact b_inf_Sup_s.disjoint_sup_right_of_disjoint_sup_left con.symm
  · intro x hx
    rw [Set.mem_union, Set.mem_singleton_iff] at hx
    obtain hx | rfl := hx
    · exact s_atoms x hx
    · exact ha
#align exists_set_independent_is_compl_Sup_atoms exists_setIndependent_isCompl_supₛ_atoms

theorem exists_setIndependent_of_supₛ_atoms_eq_top (h : supₛ { a : α | IsAtom a } = ⊤) :
    ∃ s : Set α, CompleteLattice.SetIndependent s ∧ supₛ s = ⊤ ∧ ∀ ⦃a⦄, a ∈ s → IsAtom a :=
  let ⟨s, s_ind, s_top, s_atoms⟩ := exists_setIndependent_isCompl_supₛ_atoms h ⊥
  ⟨s, s_ind, eq_top_of_isCompl_bot s_top.symm, s_atoms⟩
#align exists_set_independent_of_Sup_atoms_eq_top exists_setIndependent_of_supₛ_atoms_eq_top

/-- See [Theorem 6.6][calugareanu]. -/
theorem complementedLattice_of_supₛ_atoms_eq_top (h : supₛ { a : α | IsAtom a } = ⊤) :
    ComplementedLattice α :=
  ⟨fun b =>
    let ⟨s, _, s_top, _⟩ := exists_setIndependent_isCompl_supₛ_atoms h b
    ⟨supₛ s, s_top⟩⟩
#align complemented_lattice_of_Sup_atoms_eq_top complementedLattice_of_supₛ_atoms_eq_top

/-- See [Theorem 6.6][calugareanu]. -/
theorem complementedLattice_of_isAtomistic [IsAtomistic α] : ComplementedLattice α :=
  complementedLattice_of_supₛ_atoms_eq_top supₛ_atoms_eq_top
#align complemented_lattice_of_is_atomistic complementedLattice_of_isAtomistic

theorem complementedLattice_iff_isAtomistic : ComplementedLattice α ↔ IsAtomistic α := by
  constructor <;> intros
  · exact isAtomistic_of_complementedLattice
  · exact complementedLattice_of_isAtomistic
#align complemented_lattice_iff_is_atomistic complementedLattice_iff_isAtomistic

end
