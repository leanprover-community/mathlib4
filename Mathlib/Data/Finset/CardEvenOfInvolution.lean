/-
Copyright (c) 2026 papanokechi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: papanokechi
-/
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Even
import Mathlib.Logic.Function.Basic

/-!
# Even cardinality from a fixed-point-free involution

This file provides the elementary combinatorial lemma that a `Finset α` admits
a fixed-point-free involution only if its cardinality is even.

## Main results

* `Finset.card_even_of_involution`: If `σ : α → α` is an involution that maps
  `s : Finset α` into itself and has no fixed point in `s`, then `Even s.card`.
* `Finset.two_dvd_card_of_involution`: The same conclusion phrased as
  `2 ∣ s.card`.

## Application

This lemma is the abstract core of orbit-pairing arguments. In particular it
arises in the formalization of Tunnell's criterion for the Congruent Number
Problem (see <https://github.com/papanokechi/tunnell-cnp-lean4>): the
involution `(x, y, z) ↦ (-x, -y, -z)` pairs the nonzero integer
representations of `n` by a positive-definite ternary quadratic form, hence
their count is even. The lemma itself involves no number theory.

## Implementation notes

The proof is by strong induction on `s.card`: pick any `x ∈ s`, observe that
`σ x ∈ s` and `σ x ≠ x`, erase both, and apply the induction hypothesis to
the smaller set. We package the involution hypotheses pointwise on `s` rather
than using `Function.Involutive σ` directly, so the lemma can be applied even
when `σ` is only an involution on `s` (which is the typical situation in
combinatorial parity arguments).
-/

namespace Finset

variable {α : Type*} [DecidableEq α]

/-- A `Finset α` equipped with a fixed-point-free involution has even
cardinality.

The hypotheses are stated pointwise on `s`:
* `hMem`  : `σ` maps `s` into itself.
* `hInv`  : `σ` is an involution on `s`.
* `hFix`  : `σ` has no fixed point in `s`.

This is the abstract orbit-pairing lemma underlying many parity arguments. -/
theorem card_even_of_involution
    (s : Finset α) (σ : α → α)
    (hMem : ∀ x ∈ s, σ x ∈ s)
    (hInv : ∀ x ∈ s, σ (σ x) = x)
    (hFix : ∀ x ∈ s, σ x ≠ x) :
    Even s.card := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hs : s = ∅
    · subst hs
      simp only [Finset.card_empty]
      exact ⟨0, rfl⟩
    · obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hs
      have hσx : σ x ∈ s := hMem x hx
      have hne : σ x ≠ x := hFix x hx
      let s' := (s.erase x).erase (σ x)
      have hsub : s' ⊆ s := fun a ha => by
        simp only [s', Finset.mem_erase] at ha
        exact ha.2.2
      have hxmem' : x ∉ s' := by
        simp [s', Finset.mem_erase]
      have hs'_sub : s' ⊂ s :=
        Finset.ssubset_iff_subset_ne.mpr
          ⟨hsub, fun heq => hxmem' (heq ▸ hx)⟩
      have hMem' : ∀ y ∈ s', σ y ∈ s' := by
        intro y hy
        have hy_ne_σx : y ≠ σ x := (Finset.mem_erase.mp hy).1
        have hy_in_erase : y ∈ s.erase x := (Finset.mem_erase.mp hy).2
        have hy_ne_x : y ≠ x := (Finset.mem_erase.mp hy_in_erase).1
        have hy_s : y ∈ s := (Finset.mem_erase.mp hy_in_erase).2
        have hσy_s : σ y ∈ s := hMem y hy_s
        have hσy_ne_σx : σ y ≠ σ x := by
          intro h
          apply hy_ne_x
          calc y = σ (σ y) := (hInv y hy_s).symm
            _ = σ (σ x) := by rw [h]
            _ = x := hInv x hx
        have hσy_ne_x : σ y ≠ x := by
          intro h
          apply hy_ne_σx
          calc y = σ (σ y) := (hInv y hy_s).symm
            _ = σ x := by rw [h]
        exact Finset.mem_erase.mpr ⟨hσy_ne_σx,
          Finset.mem_erase.mpr ⟨hσy_ne_x, hσy_s⟩⟩
      have hInv' : ∀ y ∈ s', σ (σ y) = y := fun y hy => by
        have hy_s : y ∈ s :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).2
        exact hInv y hy_s
      have hFix' : ∀ y ∈ s', σ y ≠ y := fun y hy => by
        have hy_s : y ∈ s :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).2
        exact hFix y hy_s
      have heven' : Even s'.card := ih s' hs'_sub hMem' hInv' hFix'
      have hcard : s.card = s'.card + 2 := by
        have h1 : (s.erase x).card = s.card - 1 := Finset.card_erase_of_mem hx
        have hσx_in : σ x ∈ s.erase x :=
          Finset.mem_erase.mpr ⟨hne, hσx⟩
        have h2 : s'.card = (s.erase x).card - 1 :=
          Finset.card_erase_of_mem hσx_in
        have hcard_pos : 1 ≤ s.card := Finset.one_le_card.mpr ⟨x, hx⟩
        have hcard_pos2 : 1 ≤ (s.erase x).card :=
          Finset.one_le_card.mpr ⟨σ x, hσx_in⟩
        omega
      rw [hcard]
      obtain ⟨r, hr⟩ := heven'
      exact ⟨r + 1, by omega⟩

/-- Variant of `Finset.card_even_of_involution` phrased as `2 ∣ s.card`. -/
theorem two_dvd_card_of_involution
    (s : Finset α) (σ : α → α)
    (hMem : ∀ x ∈ s, σ x ∈ s)
    (hInv : ∀ x ∈ s, σ (σ x) = x)
    (hFix : ∀ x ∈ s, σ x ≠ x) :
    2 ∣ s.card := by
  obtain ⟨r, hr⟩ := card_even_of_involution s σ hMem hInv hFix
  exact ⟨r, by omega⟩

/-- If `σ : α → α` is a global involution with no fixed point in `s`, and `σ`
maps `s` into itself, then `s.card` is even. -/
theorem card_even_of_involutive
    (s : Finset α) {σ : α → α}
    (hInv : Function.Involutive σ)
    (hMem : ∀ x ∈ s, σ x ∈ s)
    (hFix : ∀ x ∈ s, σ x ≠ x) :
    Even s.card :=
  card_even_of_involution s σ hMem (fun x _ => hInv x) hFix

end Finset
