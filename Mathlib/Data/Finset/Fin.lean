/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Kim Morrison, Johan Commelin
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic

/-!
# Finsets in `Fin n`

A few constructions for Finsets in `Fin n`.

## Main declarations

* `Finset.attachFin`: Turns a Finset of naturals strictly less than `n` into a `Finset (Fin n)`.
-/


variable {n : ℕ}

namespace Finset

/-- Given a Finset `s` of `ℕ` contained in `{0,..., n-1}`, the corresponding Finset in `Fin n`
is `s.attachFin h` where `h` is a proof that all elements of `s` are less than `n`. -/
def attachFin (s : Finset ℕ) {n : ℕ} (h : ∀ m ∈ s, m < n) : Finset (Fin n) :=
  ⟨s.1.pmap (fun a ha ↦ ⟨a, ha⟩) h, s.nodup.pmap fun _ _ _ _ ↦ Fin.val_eq_of_eq⟩

@[simp]
theorem mem_attachFin {s : Finset ℕ} (h : ∀ m ∈ s, m < n) {a : Fin n} :
    a ∈ s.attachFin h ↔ (a : ℕ) ∈ s :=
  ⟨fun h ↦
    let ⟨_, hb₁, hb₂⟩ := Multiset.mem_pmap.1 h
    hb₂ ▸ hb₁,
    fun h ↦ Multiset.mem_pmap.2 ⟨a, h, Fin.eta _ _⟩⟩

@[simp]
lemma coe_attachFin {s : Finset ℕ} (h : ∀ m ∈ s, m < n) :
    (attachFin s h : Set (Fin n)) = Fin.val ⁻¹' s := by
  ext; simp

@[simp]
theorem card_attachFin (s : Finset ℕ) (h : ∀ m ∈ s, m < n) :
    (s.attachFin h).card = s.card :=
  Multiset.card_pmap _ _ _

@[simp]
lemma image_val_attachFin {s : Finset ℕ} (h : ∀ m ∈ s, m < n) :
    image Fin.val (s.attachFin h) = s := by
  apply coe_injective
  rw [coe_image, coe_attachFin, Set.image_preimage_eq_iff]
  exact fun m hm ↦ ⟨⟨m, h m hm⟩, rfl⟩

@[simp]
lemma map_valEmbedding_attachFin {s : Finset ℕ} (h : ∀ m ∈ s, m < n) :
    map Fin.valEmbedding (s.attachFin h) = s := by
  simp [map_eq_image]

@[simp]
lemma attachFin_subset_attachFin_iff {s t : Finset ℕ} (hs : ∀ m ∈ s, m < n) (ht : ∀ m ∈ t, m < n) :
    s.attachFin hs ⊆ t.attachFin ht ↔ s ⊆ t := by
  simp [← map_subset_map (f := Fin.valEmbedding)]

@[mono, gcongr]
lemma attachFin_subset_attachFin {s t : Finset ℕ} (hst : s ⊆ t) (ht : ∀ m ∈ t, m < n) :
    s.attachFin (fun m hm ↦ ht m (hst hm)) ⊆ t.attachFin ht := by simpa

@[simp]
lemma attachFin_ssubset_attachFin_iff {s t : Finset ℕ} (hs : ∀ m ∈ s, m < n) (ht : ∀ m ∈ t, m < n) :
    s.attachFin hs ⊂ t.attachFin ht ↔ s ⊂ t := by
  simp [← map_ssubset_map (f := Fin.valEmbedding)]

@[mono, gcongr]
lemma attachFin_ssubset_attachFin {s t : Finset ℕ} (hst : s ⊂ t) (ht : ∀ m ∈ t, m < n) :
    s.attachFin (fun m hm ↦ ht m (hst.subset hm)) ⊂ t.attachFin ht := by simpa

/-- Given a finset `s` of natural numbers and a bound `n`,
`s.fin n` is the finset of all elements of `s` less than `n`.

This definition was introduced to define a `LocallyFiniteOrder` instance on `Fin n`.
Later, this instance was rewritten using a more efficient `attachFin`.
Since this definition had no other uses in the library, it was deprecated.
-/
@[deprecated attachFin (since := "2025-04-08")]
protected def fin (n : ℕ) (s : Finset ℕ) : Finset (Fin n) :=
  (s.subtype _).map Fin.equivSubtype.symm.toEmbedding

set_option linter.deprecated false

@[simp, deprecated mem_attachFin (since := "2025-04-08")]
theorem mem_fin {s : Finset ℕ} : ∀ a : Fin n, a ∈ s.fin n ↔ (a : ℕ) ∈ s
  | ⟨a, ha⟩ => by simp [Finset.fin, ha, and_comm]

@[simp, deprecated coe_attachFin (since := "2025-04-08")]
theorem coe_fin (n : ℕ) (s : Finset ℕ) : (s.fin n : Set (Fin n)) = Fin.val ⁻¹' s := by ext; simp

@[mono, deprecated attachFin_subset_attachFin (since := "2025-04-08")]
theorem fin_mono : Monotone (Finset.fin n) := fun s t h x => by simpa using @h x

@[gcongr, deprecated attachFin_subset_attachFin (since := "2025-04-08")]
theorem fin_subset_fin (n : ℕ) {s t : Finset ℕ} (h : s ⊆ t) : s.fin n ⊆ t.fin n := fin_mono h

@[simp, deprecated map_valEmbedding_attachFin (since := "2025-04-08")]
theorem fin_map {s : Finset ℕ} : (s.fin n).map Fin.valEmbedding = s.filter (· < n) := by
  simp [Finset.fin, Finset.map_map]

@[deprecated "No replacement" (since := "2025-04-08")]
theorem attachFin_eq_fin {s : Finset ℕ} (h : ∀ m ∈ s, m < n) :
    attachFin s h = s.fin n := by
  ext
  simp

end Finset
