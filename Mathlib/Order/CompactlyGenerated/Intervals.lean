/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/

import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Order.CompactlyGenerated.Basic

/-!
# Results about compactness properties for intervals in complete lattices
-/

variable {ι α : Type*} [CompleteLattice α]

namespace Set.Iic

theorem isCompactElement {a : α} {b : Iic a} (h : CompleteLattice.IsCompactElement (b : α)) :
    CompleteLattice.IsCompactElement b := by
  simp only [CompleteLattice.isCompactElement_iff, Finset.sup_eq_iSup] at h ⊢
  intro ι s hb
  replace hb : (b : α) ≤ iSup ((↑) ∘ s) := le_trans hb <| (coe_iSup s) ▸ le_refl _
  obtain ⟨t, ht⟩ := h ι ((↑) ∘ s) hb
  exact ⟨t, (by simpa using ht : (b : α) ≤ _)⟩

instance instIsCompactlyGenerated [IsCompactlyGenerated α] {a : α} :
    IsCompactlyGenerated (Iic a) := by
  refine ⟨fun ⟨x, (hx : x ≤ a)⟩ ↦ ?_⟩
  obtain ⟨s, hs, rfl⟩ := IsCompactlyGenerated.exists_sSup_eq x
  rw [sSup_le_iff] at hx
  let f : s → Iic a := fun y ↦ ⟨y, hx _ y.property⟩
  refine ⟨range f, ?_, ?_⟩
  · rintro - ⟨⟨y, hy⟩, hy', rfl⟩
    exact isCompactElement (hs _ hy)
  · rw [Subtype.ext_iff]
    change sSup (((↑) : Iic a → α) '' (range f)) = sSup s
    congr
    ext b
    simpa [f] using hx b

end Set.Iic

open Set (Iic)

theorem complementedLattice_of_complementedLattice_Iic
    [IsModularLattice α] [IsCompactlyGenerated α]
    {s : Set ι} {f : ι → α}
    (h : ∀ i ∈ s, ComplementedLattice <| Iic (f i))
    (h' : ⨆ i ∈ s, f i = ⊤) :
    ComplementedLattice α := by
  apply complementedLattice_of_sSup_atoms_eq_top
  have : ∀ i ∈ s, ∃ t : Set α, f i = sSup t ∧ ∀ a ∈ t, IsAtom a := fun i hi ↦ by
    replace h := complementedLattice_iff_isAtomistic.mp (h i hi)
    obtain ⟨u, hu, hu'⟩ := eq_sSup_atoms (⊤ : Iic (f i))
    refine ⟨(↑) '' u, ?_, ?_⟩
    · replace hu : f i = ↑(sSup u) := Subtype.ext_iff.mp hu
      simp_rw [hu, Iic.coe_sSup]
    · rintro b ⟨⟨a, ha'⟩, ha, rfl⟩
      exact IsAtom.of_isAtom_coe_Iic (hu' _ ha)
  choose t ht ht' using this
  let u : Set α := ⋃ i, ⋃ hi : i ∈ s, t i hi
  have hu₁ : u ⊆ {a | IsAtom a} := by
    rintro a ⟨-, ⟨i, rfl⟩, ⟨-, ⟨hi, rfl⟩, ha : a ∈ t i hi⟩⟩
    exact ht' i hi a ha
  have hu₂ : sSup u = ⨆ i ∈ s, f i := by simp_rw [u, sSup_iUnion, biSup_congr' ht]
  rw [eq_top_iff, ← h', ← hu₂]
  exact sSup_le_sSup hu₁
