/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.Order.KrullDimension

/-!
# Characterising `Order.KrullDimLE` via coheight and height

This file records two order-theoretic characterisations of `Order.KrullDimLE n` on a preorder:
`KrullDimLE n` holds iff every point of coheight at least `n` is minimal (equivalently, every
point of height at least `n` is maximal). Geometrically, applied to the specialization order of
a scheme, `KrullDimLE 1` says exactly that the codimension-one points are closed, which is how
a curve enters Riemann–Roch-type arguments.

NOTE (PR): these lemmas are natural companions of the `krullDim`/`height`/`coheight` API and
could be merged into `Mathlib.Order.KrullDimension` instead of living in their own file.
-/

namespace Order

open Order

variable {X : Type*} [Preorder X] {n : ℕ}

/--
`X` has Krull dimension at most `n` if and only if every point of coheight at least `n` is
minimal. Geometrically, in the specialization order of a scheme, this says that the
codimension-`n` points are closed.
-/
lemma krullDimLE_iff_coheight_le_isMin :
    Order.KrullDimLE n X ↔ (∀ x : X, n ≤ coheight x → IsMin x) := by
  rw [Order.krullDimLE_iff]
  constructor
  · -- If `krullDim X ≤ n` and `coheight x ≥ n`, then `x` is minimal: a strict predecessor
    -- `y < x` would extend any chain above `x`, giving `coheight y ≥ coheight x + 1 ≥ n + 1`
    -- and hence `krullDim X ≥ n + 1`, contradicting `krullDim X ≤ n`.
    intro h x hx y hy
    by_contra hxy
    have h2 : ((n + 1 : ℕ) : ℕ∞) ≤ coheight y := by
      push_cast
      exact (by gcongr : (n : ℕ∞) + 1 ≤ coheight x + 1).trans
        (coheight_add_one_le (lt_of_le_not_ge hy hxy))
    have h3 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) :=
      le_trans (le_trans (by exact_mod_cast h2) (coheight_le_krullDim y)) h
    exact absurd (by exact_mod_cast h3 : n + 1 ≤ n) (by omega)
  · -- Conversely, if `krullDim X > n`, take a chain of length `n + 1`. Its second point `l 1`
    -- has a chain of length `n` above it, so `coheight (l 1) ≥ n`, yet its predecessor `l 0`
    -- lies strictly below it, so `l 1` is not minimal — contradicting the hypothesis.
    intro h
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨l, hl⟩ := le_krullDim_iff.mp (show ((n + 1 : ℕ) : WithBot ℕ∞) ≤ krullDim X by
      push_cast
      exact ENat.WithBot.add_one_le_iff.mpr hcon)
    have hidx : 1 < l.length + 1 := by omega
    have hcoh := rev_index_le_coheight l ⟨1, hidx⟩
    rw [show ((⟨1, hidx⟩ : Fin (l.length + 1)).rev : ℕ) = n by simp [Fin.val_rev]; omega] at hcoh
    have h0lt : l ⟨0, by omega⟩ < l ⟨1, hidx⟩ := l.strictMono (by simp [Fin.lt_def])
    exact h0lt.not_ge (h _ (by exact_mod_cast hcoh) h0lt.le)

/--
Dual form of `krullDimLE_iff_coheight_le_isMin`: `X` has Krull dimension at most `n` if and
only if every point of height at least `n` is maximal. Obtained by running the previous lemma
on the order dual `Xᵒᵈ`, where height/coheight and minimal/maximal swap roles.
-/
lemma krullDimLE_iff_height_le_isMax :
    Order.KrullDimLE n X ↔ (∀ x : X, n ≤ height x → IsMax x) := by
  rw [show Order.KrullDimLE n X ↔ Order.KrullDimLE n Xᵒᵈ by
    rw [Order.krullDimLE_iff, Order.krullDimLE_iff, krullDim_orderDual]]
  exact krullDimLE_iff_coheight_le_isMin

/-- In a preorder of Krull dimension at most `n`, a point of coheight at least `n` is
minimal. -/
lemma KrullDimLE.isMin_of_le_coheight [Order.KrullDimLE n X] {x : X}
    (hx : n ≤ coheight x) : IsMin x :=
  krullDimLE_iff_coheight_le_isMin.mp ‹_› x hx

/-- In a preorder of Krull dimension at most `n`, a point of height at least `n` is
maximal. -/
lemma KrullDimLE.isMax_of_le_height [Order.KrullDimLE n X] {x : X}
    (hx : n ≤ height x) : IsMax x :=
  krullDimLE_iff_height_le_isMax.mp ‹_› x hx

end Order
