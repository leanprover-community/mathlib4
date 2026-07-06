import Mathlib.Order.KrullDimension

/-!
# Characterising `Order.KrullDimLE` via coheight and height

This file records two order-theoretic characterisations of `Order.KrullDimLE n` on a preorder:
`KrullDimLE n` holds iff every point of coheight at least `n` is minimal (equivalently, every point
of height at least `n` is maximal). Geometrically, applied to the specialization order of a scheme,
`KrullDimLE 1` says exactly that the codimension-one points are closed, which is how a curve enters
the Riemann–Roch argument.

TODO: These are general facts about `Order.KrullDimLE` and should be upstreamed to
`Mathlib.Order.KrullDimension`.
-/

open Order

/--
`X` has Krull dimension at most `n` if and only if every point of coheight at least `n` is
minimal. Geometrically, in the specialization order of a scheme, this says that the
codimension-`n` points are closed.
-/
lemma krullDimLE_iff_coheight_le_isMin {X : Type*} [Preorder X] {n : ℕ} :
    Order.KrullDimLE n X ↔ (∀ x : X, n ≤ coheight x → IsMin x) := by
  rw [Order.krullDimLE_iff]
  constructor
  · -- If `krullDim X ≤ n` and `coheight x ≥ n`, then `x` is minimal: a strict predecessor `y < x`
    -- would extend any chain above `x`, giving `coheight y ≥ coheight x + 1 ≥ n + 1` and hence
    -- `krullDim X ≥ n + 1`, contradicting `krullDim X ≤ n`.
    intro h x hx y hy
    by_contra hxy
    have hlt : y < x := lt_of_le_not_ge hy hxy
    have h2 : ((n + 1 : ℕ) : ℕ∞) ≤ coheight y := by
      have hstep : (n : ℕ∞) + 1 ≤ coheight x + 1 := by gcongr
      rw [Nat.cast_add, Nat.cast_one]
      exact hstep.trans (coheight_add_one_le hlt)
    have h3 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) :=
      le_trans (le_trans (by exact_mod_cast h2) (coheight_le_krullDim y)) h
    have : n + 1 ≤ n := by exact_mod_cast h3
    omega
  · -- Conversely, if `krullDim X > n`, take a chain of length `n + 1`. Its second point `l 1` has a
    -- chain of length `n` above it, so `coheight (l 1) ≥ n`, yet its predecessor `l 0` lies
    -- strictly below it, so `l 1` is not minimal — contradicting the hypothesis.
    intro h
    by_contra hcon
    rw [not_le] at hcon
    have hn1 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ krullDim X := by
      rw [Nat.cast_add, Nat.cast_one]
      exact ENat.WithBot.add_one_le_iff.mpr hcon
    obtain ⟨l, hl⟩ := le_krullDim_iff.mp hn1
    have hidx : 1 < l.length + 1 := by omega
    have hcoh : (n : ℕ∞) ≤ coheight (l ⟨1, hidx⟩) := by
      have hrev := rev_index_le_coheight l ⟨1, hidx⟩
      have hval : ((⟨1, hidx⟩ : Fin (l.length + 1)).rev : ℕ) = n := by
        simp only [Fin.val_rev]; omega
      calc (n : ℕ∞) = (((⟨1, hidx⟩ : Fin (l.length + 1)).rev : ℕ) : ℕ∞) := by rw [hval]
        _ ≤ coheight (l ⟨1, hidx⟩) := by exact_mod_cast hrev
    have h0lt : l ⟨0, by omega⟩ < l ⟨1, hidx⟩ := l.strictMono (by simp [Fin.lt_def])
    exact h0lt.not_ge (h _ hcoh h0lt.le)

/--
Dual form of `krullDimLE_iff_coheight_le_isMin`: `X` has Krull dimension at most `n` if and
only if every point of height at least `n` is maximal. Obtained by running the previous lemma on
the order dual `Xᵒᵈ`, where height/coheight and minimal/maximal swap roles.
-/
lemma krullDimLE_iff_height_le_isMax {X : Type*} [Preorder X] {n : ℕ} :
    Order.KrullDimLE n X ↔ (∀ x : X, n ≤ height x → IsMax x) := by
  rw [show Order.KrullDimLE n X ↔ Order.KrullDimLE n Xᵒᵈ by
    rw [Order.krullDimLE_iff, Order.krullDimLE_iff, krullDim_orderDual]]
  exact krullDimLE_iff_coheight_le_isMin

/-- In a preorder of Krull dimension at most `n`, a point of coheight at least `n` is minimal. -/
lemma Order.KrullDimLE.isMin_of_le_coheight {X : Type*} [Preorder X] {n : ℕ}
    [Order.KrullDimLE n X] {x : X} (hx : n ≤ coheight x) : IsMin x :=
  krullDimLE_iff_coheight_le_isMin.mp ‹_› x hx

/-- In a preorder of Krull dimension at most `n`, a point of height at least `n` is maximal. -/
lemma Order.KrullDimLE.isMax_of_le_height {X : Type*} [Preorder X] {n : ℕ}
    [Order.KrullDimLE n X] {x : X} (hx : n ≤ height x) : IsMax x :=
  krullDimLE_iff_height_le_isMax.mp ‹_› x hx
