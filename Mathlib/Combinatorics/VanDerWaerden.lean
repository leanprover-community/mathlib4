/-
Copyright (c) 2026 shunfeng8421. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: shunfeng8421
-/
module

public import Mathlib.Combinatorics.Compactness
public import Mathlib.Combinatorics.HalesJewett

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith

/-! # Van der Waerden's theorem

This file proves the *finitary* version of Van der Waerden's theorem: every
finite coloring of a sufficiently large initial segment of the natural numbers
contains a monochromatic arithmetic progression of any prescribed length `k`.

The proof is by compactness (Rado's selection lemma, `Finset.rado_selection`,
proved in `Mathlib/Combinatorics/Compactness.lean`): assuming every finite
segment admits a "bad" coloring with no monochromatic arithmetic progression,
one stitches these bad colorings into a global coloring `χ : ℕ → κ`, and then
contradicts the infinite version `Combinatorics.exists_mono_homothetic_copy`
(a corollary of the Hales-Jewett theorem, proved in
`Mathlib/Combinatorics/HalesJewett.lean`).

This resolves the TODO in `HalesJewett.lean` asking for a finitary version of
Van der Waerden's theorem "by compactness".
-/

namespace Combinatorics

public section

/-- A coloring `C : Fin (N + 1) → κ` of the initial segment `[0, N]` contains a
monochromatic arithmetic progression of length `k`. -/
def HasMonoAPWithin (k N : ℕ) {κ : Type*} (C : Fin (N + 1) → κ) : Prop :=
  ∃ a > 0, ∃ b : ℕ, ∃ hb : ∀ t : ℕ, t < k → a * t + b < N + 1,
    ∃ c : κ, ∀ (t : ℕ) (ht : t < k), C ⟨a * t + b, hb t ht⟩ = c

/-- **Finitary Van der Waerden theorem**: for any finite color type `κ`, there
exists `N` such that every `κ`-coloring of `Fin (N + 1)` contains a
monochromatic arithmetic progression of length `k`. -/
theorem van_der_waerden (k : ℕ) {κ : Type*} [Finite κ] [Nonempty κ] :
    ∃ N : ℕ, ∀ C : Fin (N + 1) → κ, HasMonoAPWithin k N C := by
  classical
  by_contra h
  -- (1) Every segment admits a "bad" coloring
  have hbad : ∀ N : ℕ, ∃ C : Fin (N + 1) → κ, ¬ HasMonoAPWithin k N C := by
    intro N
    by_contra hN
    exact h ⟨N, fun C => by
      by_contra hC
      exact hN ⟨C, hC⟩⟩
  -- (2) Local bad colorings: for a finite set `s`, take the bad coloring of the
  -- covering interval `[0, s.sup id]`, and pick an arbitrary color outside it
  let g : Finset ℕ → ℕ → κ := fun s n =>
    if hn : n ≤ s.sup id then (Classical.choose (hbad (s.sup id))) ⟨n, by linarith⟩
    else Classical.choice ‹Nonempty κ›
  -- (3) Rado selection: global χ agreeing with some bad coloring on every finite set
  obtain ⟨χ, hχ⟩ := Finset.rado_selection g
  -- (4) Infinite vdW (Hales-Jewett corollary) applied to χ
  obtain ⟨a, ha, b, c, hmono⟩ :=
    Combinatorics.exists_mono_homothetic_copy (M := ℕ) (S := Finset.range k) (C := χ)
  -- (5) The arithmetic progression from (4), as a finite set of points
  let s : Finset ℕ := (Finset.range k).image (fun u => a * u + b)
  obtain ⟨t, hst, hagree⟩ := hχ s
  let C := Classical.choose (hbad (t.sup id))
  have hCbad : ¬ HasMonoAPWithin k (t.sup id) C := Classical.choose_spec (hbad (t.sup id))
  -- (6) The AP lies inside the covering interval of `t`
  have hb : ∀ u : ℕ, u < k → a * u + b < t.sup id + 1 := by
    intro u hu
    exact Nat.lt_succ_of_le
      (Finset.le_sup (s := t) (f := id)
        (hst (Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr hu, rfl⟩)))
  -- (7) C agrees with χ on the AP, which is monochromatic in χ
  have hm : ∀ (u : ℕ) (hu : u < k), C ⟨a * u + b, hb u hu⟩ = c := by
    intro u hu
    have hxs : a * u + b ∈ s := Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr hu, rfl⟩
    have hle : a * u + b ≤ t.sup id := Nat.le_of_lt_succ (hb u hu)
    have hx : χ (a * u + b) = c := by
      simpa using hmono u (Finset.mem_range.mpr hu)
    have hx2 : χ (a * u + b) = g t (a * u + b) := hagree (a * u + b) hxs
    have hg : g t (a * u + b) = C ⟨a * u + b, by linarith⟩ := by
      simp [g, C, hle]
    calc
      C ⟨a * u + b, hb u hu⟩ = g t (a * u + b) := hg.symm
      _ = χ (a * u + b) := hx2.symm
      _ = c := hx
  -- (8) Contradiction with (1)
  exact hCbad ⟨a, ha, b, hb, c, hm⟩

end

end Combinatorics
