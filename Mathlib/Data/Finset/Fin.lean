/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Scott Morrison, Johan Commelin
-/
import Mathlib.Data.Finset.Card

#align_import data.finset.fin from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

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
#align finset.attach_fin Finset.attachFin

@[simp]
theorem mem_attachFin {n : ℕ} {s : Finset ℕ} (h : ∀ m ∈ s, m < n) {a : Fin n} :
    a ∈ s.attachFin h ↔ (a : ℕ) ∈ s :=
  ⟨fun h ↦
    let ⟨_, hb₁, hb₂⟩ := Multiset.mem_pmap.1 h
    hb₂ ▸ hb₁,
    fun h ↦ Multiset.mem_pmap.2 ⟨a, h, Fin.eta _ _⟩⟩
#align finset.mem_attach_fin Finset.mem_attachFin

@[simp]
theorem card_attachFin {n : ℕ} (s : Finset ℕ) (h : ∀ m ∈ s, m < n) :
    (s.attachFin h).card = s.card :=
  Multiset.card_pmap _ _ _
#align finset.card_attach_fin Finset.card_attachFin

end Finset
