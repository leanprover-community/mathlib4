/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li, Joachim Breitner
-/

import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.SuccPred.WithBot
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.Atoms
import Mathlib.Order.RelSeries
import Mathlib.Tactic.FinCases

/-!
# Krull dimension of a preordered set and height of an element

If `α` is a preordered set, then `krullDim α : WithBot ℕ∞` is defined to be
`sup {n | a₀ < a₁ < ... < aₙ}`.

In case that `α` is empty, then its Krull dimension is defined to be negative infinity; if the
length of all series `a₀ < a₁ < ... < aₙ` is unbounded, then its Krull dimension is defined to be
positive infinity.

For `a : α`, its height (in `ℕ∞`) is defined to be `sup {n | a₀ < a₁ < ... < aₙ ≤ a}`, while its
coheight is defined to be `sup {n | a ≤ a₀ < a₁ < ... < aₙ}` .

## Main results

* The Krull dimension is the same as that of the dual order (`krullDim_orderDual`).

* The Krull dimension is the supremum of the heights of the elements (`krullDim_eq_iSup_height`),
  or their coheights (`krullDim_eq_iSup_coheight`), or their sums of height and coheight
  (`krullDim_eq_iSup_height_add_coheight_of_nonempty`)

* The height in the dual order equals the coheight, and vice versa.

* The height is monotone (`height_mono`), and strictly monotone if finite (`height_strictMono`).

* The coheight is antitone (`coheight_anti`), and strictly antitone if finite
  (`coheight_strictAnti`).

* The height is the supremum of the successor of the height of all smaller elements
  (`height_eq_iSup_lt_height`).

* The elements of height zero are the minimal elements (`height_eq_zero`), and the elements of
  height `n` are minimal among those of height `≥ n` (`height_eq_coe_iff_minimal_le_height`).

* Concrete calculations for the height, coheight and Krull dimension in `ℕ`, `ℤ`, `WithTop`,
  `WithBot` and `ℕ∞`.

## Design notes

Krull dimensions are defined to take value in `WithBot ℕ∞` so that `(-∞) + (+∞)` is
also negative infinity. This is because we want Krull dimensions to be additive with respect
to product of varieties so that `-∞` being the Krull dimension of empty variety is equal to
sum of `-∞` and the Krull dimension of any other varieties.

We could generalize the notion of Krull dimension to an arbitrary binary relation; many results
in this file would generalize as well. But we don't think it would be useful, so we only define
Krull dimension of a preorder.
-/

assert_not_exists Field

namespace Order

section definitions

/--
The **Krull dimension** of a preorder `α` is the supremum of the rightmost index of all relation
series of `α` ordered by `<`. If there is no series `a₀ < a₁ < ... < aₙ` in `α`, then its Krull
dimension is defined to be negative infinity; if the length of all series `a₀ < a₁ < ... < aₙ` is
unbounded, its Krull dimension is defined to be positive infinity.
-/
noncomputable def krullDim (α : Type*) [Preorder α] : WithBot ℕ∞ :=
  ⨆ (p : LTSeries α), p.length

/--
The **height** of an element `a` in a preorder `α` is the supremum of the rightmost index of all
relation series of `α` ordered by `<` and ending below or at `a`. In other words, it is
the largest `n` such that there's a series `a₀ < a₁ < ... < aₙ = a` (or `∞` if there is
no largest `n`).
-/
noncomputable def height {α : Type*} [Preorder α] (a : α) : ℕ∞ :=
  ⨆ (p : LTSeries α) (_ : p.last ≤ a), p.length

/--
The **coheight** of an element `a` in a preorder `α` is the supremum of the rightmost index of all
relation series of `α` ordered by `<` and beginning with `a`. In other words, it is
the largest `n` such that there's a series `a = a₀ < a₁ < ... < aₙ` (or `∞` if there is
no largest `n`).

The definition of `coheight` is via the `height` in the dual order, in order to easily transfer
theorems between `height` and `coheight`. See `coheight_eq` for the definition with a
series ordered by `<` and beginning with `a`.
-/
noncomputable def coheight {α : Type*} [Preorder α] (a : α) : ℕ∞ := height (α := αᵒᵈ) a

end definitions

/-!
## Height
-/

section height

variable {α β : Type*}

variable [Preorder α] [Preorder β]

@[simp] lemma height_toDual (x : α) : height (OrderDual.toDual x) = coheight x := rfl
@[simp] lemma height_ofDual (x : αᵒᵈ) : height (OrderDual.ofDual x) = coheight x := rfl
@[simp] lemma coheight_toDual (x : α) : coheight (OrderDual.toDual x) = height x := rfl
@[simp] lemma coheight_ofDual (x : αᵒᵈ) : coheight (OrderDual.ofDual x) = height x := rfl

/--
The **coheight** of an element `a` in a preorder `α` is the supremum of the rightmost index of all
relation series of `α` ordered by `<` and beginning with `a`.

This is not the definition of `coheight`. The definition of `coheight` is via the `height` in the
dual order, in order to easily transfer theorems between `height` and `coheight`.
-/
lemma coheight_eq (a : α) :
    coheight a = ⨆ (p : LTSeries α) (_ : a ≤ p.head), (p.length : ℕ∞) := by
  apply Equiv.iSup_congr ⟨RelSeries.reverse, RelSeries.reverse, fun _ ↦ RelSeries.reverse_reverse _,
    fun _ ↦ RelSeries.reverse_reverse _⟩
  congr! 1

lemma height_le_iff {a : α} {n : ℕ∞} :
    height a ≤ n ↔ ∀ ⦃p : LTSeries α⦄, p.last ≤ a → p.length ≤ n := by
  rw [height, iSup₂_le_iff]

lemma coheight_le_iff {a : α} {n : ℕ∞} :
    coheight a ≤ n ↔ ∀ ⦃p : LTSeries α⦄, a ≤ p.head → p.length ≤ n := by
  rw [coheight_eq, iSup₂_le_iff]

lemma height_le {a : α} {n : ℕ∞} (h : ∀ (p : LTSeries α), p.last = a → p.length ≤ n) :
    height a ≤ n := by
  apply height_le_iff.mpr
  intro p hlast
  wlog hlenpos : p.length ≠ 0
  · simp_all
  -- We replace the last element in the series with `a`
  let p' := p.eraseLast.snoc a (lt_of_lt_of_le (p.eraseLast_last_rel_last (by simp_all)) hlast)
  rw [show p.length = p'.length by simp [p']; cutsat]
  apply h
  simp [p']

/--
Variant of `height_le_iff` ranging only over those series that end exactly on `a`.
-/
lemma height_le_iff' {a : α} {n : ℕ∞} :
    height a ≤ n ↔ ∀ ⦃p : LTSeries α⦄, p.last = a → p.length ≤ n := by
  constructor
  · rw [height_le_iff]
    exact fun h p hlast => h (le_of_eq hlast)
  · exact height_le

/--
Alternative definition of height, with the supremum ranging only over those series that end at `a`.
-/
lemma height_eq_iSup_last_eq (a : α) :
    height a = ⨆ (p : LTSeries α) (_ : p.last = a), ↑(p.length) := by
  apply eq_of_forall_ge_iff
  intro n
  rw [height_le_iff', iSup₂_le_iff]

/--
Alternative definition of coheight, with the supremum only ranging over those series
that begin at `a`.
-/
lemma coheight_eq_iSup_head_eq (a : α) :
    coheight a = ⨆ (p : LTSeries α) (_ : p.head = a), ↑(p.length) := by
  change height (α := αᵒᵈ) a = ⨆ (p : LTSeries α) (_ : p.head = a), ↑(p.length)
  rw [height_eq_iSup_last_eq]
  apply Equiv.iSup_congr ⟨RelSeries.reverse, RelSeries.reverse, fun _ ↦ RelSeries.reverse_reverse _,
    fun _ ↦ RelSeries.reverse_reverse _⟩
  simp

/--
Variant of `coheight_le_iff` ranging only over those series that begin exactly on `a`.
-/
lemma coheight_le_iff' {a : α} {n : ℕ∞} :
    coheight a ≤ n ↔ ∀ ⦃p : LTSeries α⦄, p.head = a → p.length ≤ n := by
  rw [coheight_eq_iSup_head_eq, iSup₂_le_iff]

lemma coheight_le {a : α} {n : ℕ∞} (h : ∀ (p : LTSeries α), p.head = a → p.length ≤ n) :
    coheight a ≤ n :=
  coheight_le_iff'.mpr h

lemma length_le_height {p : LTSeries α} {x : α} (hlast : p.last ≤ x) :
    p.length ≤ height x := by
  by_cases hlen0 : p.length ≠ 0
  · let p' := p.eraseLast.snoc x (by
      apply lt_of_lt_of_le
      · apply p.step ⟨p.length - 1, by cutsat⟩
      · convert hlast
        simp only [Fin.succ_mk, RelSeries.last, Fin.last]
        congr; cutsat)
    suffices p'.length ≤ height x by
      simp [p'] at this
      convert this
      norm_cast
      cutsat
    refine le_iSup₂_of_le p' ?_ le_rfl
    simp [p']
  · simp_all

lemma length_le_coheight {x : α} {p : LTSeries α} (hhead : x ≤ p.head) :
    p.length ≤ coheight x :=
  length_le_height (α := αᵒᵈ) (p := p.reverse) (by simpa)

/--
The height of the last element in a series is larger or equal to the length of the series.
-/
lemma length_le_height_last {p : LTSeries α} : p.length ≤ height p.last :=
  length_le_height le_rfl

/--
The coheight of the first element in a series is larger or equal to the length of the series.
-/
lemma length_le_coheight_head {p : LTSeries α} : p.length ≤ coheight p.head :=
  length_le_coheight le_rfl

/--
The height of an element in a series is larger or equal to its index in the series.
-/
lemma index_le_height (p : LTSeries α) (i : Fin (p.length + 1)) : i ≤ height (p i) :=
  length_le_height_last (p := p.take i)

/--
The coheight of an element in a series is larger or equal to its reverse index in the series.
-/
lemma rev_index_le_coheight (p : LTSeries α) (i : Fin (p.length + 1)) : i.rev ≤ coheight (p i) := by
  simpa using index_le_height (α := αᵒᵈ) p.reverse i.rev

/--
In a maximally long series, i.e one as long as the height of the last element, the height of each
element is its index in the series.
-/
lemma height_eq_index_of_length_eq_height_last {p : LTSeries α} (h : p.length = height p.last)
    (i : Fin (p.length + 1)) : height (p i) = i := by
  refine le_antisymm (height_le ?_) (index_le_height p i)
  intro p' hp'
  have hp'' := length_le_height_last (p := p'.smash (p.drop i) (by simpa))
  simp [← h] at hp''; clear h
  norm_cast at *
  cutsat

/--
In a maximally long series, i.e one as long as the coheight of the first element, the coheight of
each element is its reverse index in the series.
-/
lemma coheight_eq_index_of_length_eq_head_coheight {p : LTSeries α} (h : p.length = coheight p.head)
    (i : Fin (p.length + 1)) : coheight (p i) = i.rev := by
  simpa using height_eq_index_of_length_eq_height_last (α := αᵒᵈ) (p := p.reverse) (by simpa) i.rev

@[gcongr]
lemma height_mono : Monotone (α := α) height :=
  fun _ _ hab ↦ biSup_mono (fun _ hla => hla.trans hab)

@[gcongr]
lemma coheight_anti : Antitone (α := α) coheight :=
  (height_mono (α := αᵒᵈ)).dual_left

private lemma height_add_const (a : α) (n : ℕ∞) :
    height a + n = ⨆ (p : LTSeries α) (_ : p.last = a), p.length + n := by
  have hne : Nonempty { p : LTSeries α // p.last = a } := ⟨RelSeries.singleton _ a, rfl⟩
  rw [height_eq_iSup_last_eq, iSup_subtype', iSup_subtype', ENat.iSup_add]

/- For elements of finite height, `height` is strictly monotone. -/
@[gcongr] lemma height_strictMono {x y : α} (hxy : x < y) (hfin : height x < ⊤) :
    height x < height y := by
  rw [← ENat.add_one_le_iff hfin.ne, height_add_const, iSup₂_le_iff]
  intro p hlast
  have := length_le_height_last (p := p.snoc y (by simp [*]))
  simpa using this

lemma height_add_one_le {a b : α} (hab : a < b) : height a + 1 ≤ height b := by
  cases hfin : height a with
  | top =>
    have : ⊤ ≤ height b := by
      rw [← hfin]
      gcongr
    simp [this]
  | coe n =>
    apply Order.add_one_le_of_lt
    rw [← hfin]
    gcongr
    simp [hfin]

/- For elements of finite height, `coheight` is strictly antitone. -/
@[gcongr] lemma coheight_strictAnti {x y : α} (hyx : y < x) (hfin : coheight x < ⊤) :
    coheight x < coheight y :=
  height_strictMono (α := αᵒᵈ) hyx hfin

lemma coheight_add_one_le {a b : α} (hab : b < a) : coheight a + 1 ≤ coheight b := by
  cases hfin : coheight a with
  | top =>
    have : ⊤ ≤ coheight b := by
      rw [← hfin]
      gcongr
    simp [this]
  | coe n =>
    apply Order.add_one_le_of_lt
    rw [← hfin]
    gcongr
    simp [hfin]

lemma height_le_height_apply_of_strictMono (f : α → β) (hf : StrictMono f) (x : α) :
    height x ≤ height (f x) := by
  simp only [height_eq_iSup_last_eq]
  apply iSup₂_le
  intro p hlast
  apply le_iSup₂_of_le (p.map f hf) (by simp [hlast]) (by simp)

lemma coheight_le_coheight_apply_of_strictMono (f : α → β) (hf : StrictMono f) (x : α) :
    coheight x ≤ coheight (f x) := by
  apply height_le_height_apply_of_strictMono (α := αᵒᵈ)
  exact fun _ _ h ↦ hf h

@[simp]
lemma height_orderIso (f : α ≃o β) (x : α) : height (f x) = height x := by
  apply le_antisymm
  · simpa using height_le_height_apply_of_strictMono _ f.symm.strictMono (f x)
  · exact height_le_height_apply_of_strictMono _ f.strictMono x

lemma coheight_orderIso (f : α ≃o β) (x : α) : coheight (f x) = coheight x :=
  height_orderIso (α := αᵒᵈ) f.dual x

private lemma exists_eq_iSup_of_iSup_eq_coe {α : Type*} [Nonempty α] {f : α → ℕ∞} {n : ℕ}
    (h : (⨆ x, f x) = n) : ∃ x, f x = n := by
  obtain ⟨x, hx⟩ := ENat.sSup_mem_of_nonempty_of_lt_top (h ▸ ENat.coe_lt_top _)
  use x
  simpa [hx] using h

/-- There exist a series ending in a element for any length up to the element’s height. -/
lemma exists_series_of_le_height (a : α) {n : ℕ} (h : n ≤ height a) :
    ∃ p : LTSeries α, p.last = a ∧ p.length = n := by
  have hne : Nonempty { p : LTSeries α // p.last = a } := ⟨RelSeries.singleton _ a, rfl⟩
  cases ha : height a with
  | top =>
    clear h
    rw [height_eq_iSup_last_eq, iSup_subtype', ENat.iSup_coe_eq_top, bddAbove_def] at ha
    contrapose! ha
    use n
    rintro m ⟨⟨p, rfl⟩, hp⟩
    simp only at hp
    by_contra! hnm
    apply ha (p.drop ⟨m-n, by cutsat⟩) (by simp) (by simp; cutsat)
  | coe m =>
    rw [ha, Nat.cast_le] at h
    rw [height_eq_iSup_last_eq, iSup_subtype'] at ha
    obtain ⟨⟨p, hlast⟩, hlen⟩ := exists_eq_iSup_of_iSup_eq_coe ha
    simp only [Nat.cast_inj] at hlen
    use p.drop ⟨m-n, by cutsat⟩
    constructor
    · simp [hlast]
    · simp [hlen]; cutsat

lemma exists_series_of_le_coheight (a : α) {n : ℕ} (h : n ≤ coheight a) :
    ∃ p : LTSeries α, p.head = a ∧ p.length = n := by
  obtain ⟨p, hp, hl⟩ := exists_series_of_le_height (α := αᵒᵈ) a h
  exact ⟨p.reverse, by simpa, by simpa⟩

/-- For an element of finite height there exists a series ending in that element of that height. -/
lemma exists_series_of_height_eq_coe (a : α) {n : ℕ} (h : height a = n) :
    ∃ p : LTSeries α, p.last = a ∧ p.length = n :=
  exists_series_of_le_height a (le_of_eq h.symm)

lemma exists_series_of_coheight_eq_coe (a : α) {n : ℕ} (h : coheight a = n) :
    ∃ p : LTSeries α, p.head = a ∧ p.length = n :=
  exists_series_of_le_coheight a (le_of_eq h.symm)

/-- Another characterization of height, based on the supremum of the heights of elements below. -/
lemma height_eq_iSup_lt_height (x : α) : height x = ⨆ y < x, height y + 1 := by
  apply le_antisymm
  · apply height_le
    intro p hp
    cases hlen : p.length with
    | zero => simp
    | succ n =>
      apply le_iSup_of_le p.eraseLast.last
      apply le_iSup_of_le (by rw [← hp]; exact p.eraseLast_last_rel_last (by cutsat))
      rw [height_add_const]
      apply le_iSup₂_of_le p.eraseLast (by rfl) (by simp [hlen])
  · apply iSup₂_le; intro y hyx
    rw [height_add_const]
    apply iSup₂_le; intro p hp
    apply le_iSup₂_of_le (p.snoc x (hp ▸ hyx)) (by simp) (by simp)

/--
Another characterization of coheight, based on the supremum of the coheights of elements above.
-/
lemma coheight_eq_iSup_gt_coheight (x : α) : coheight x = ⨆ y > x, coheight y + 1 :=
  height_eq_iSup_lt_height (α := αᵒᵈ) x

lemma height_le_coe_iff {x : α} {n : ℕ} : height x ≤ n ↔ ∀ y < x, height y < n := by
  conv_lhs => rw [height_eq_iSup_lt_height, iSup₂_le_iff]
  congr! 2 with y _
  cases height y
  · simp
  · norm_cast

lemma coheight_le_coe_iff {x : α} {n : ℕ} : coheight x ≤ n ↔ ∀ y > x, coheight y < n :=
  height_le_coe_iff (α := αᵒᵈ)

/--
The height of an element is infinite iff there exist series of arbitrary length ending in that
element.
-/
lemma height_eq_top_iff {x : α} :
    height x = ⊤ ↔ ∀ n, ∃ p : LTSeries α, p.last = x ∧ p.length = n where
  mp h n := by
    apply exists_series_of_le_height x (n := n)
    simp [h]
  mpr h := by
    rw [height_eq_iSup_last_eq, iSup_subtype', ENat.iSup_coe_eq_top, bddAbove_def]
    push_neg
    intro n
    obtain ⟨p, hlast, hp⟩ := h (n + 1)
    exact ⟨p.length, ⟨⟨⟨p, hlast⟩, by simp [hp]⟩, by simp [hp]⟩⟩

/--
The coheight of an element is infinite iff there exist series of arbitrary length ending in that
element.
-/
lemma coheight_eq_top_iff {x : α} :
    coheight x = ⊤ ↔ ∀ n, ∃ p : LTSeries α, p.head = x ∧ p.length = n := by
  convert height_eq_top_iff (α := αᵒᵈ) (x := x) using 2 with n
  constructor <;> (intro ⟨p, hp, hl⟩; use p.reverse; constructor <;> simpa)

/-- The elements of height zero are the minimal elements. -/
@[simp] lemma height_eq_zero {x : α} : height x = 0 ↔ IsMin x := by
  simpa [isMin_iff_forall_not_lt] using height_le_coe_iff (x := x) (n := 0)

protected alias ⟨_, IsMin.height_eq_zero⟩ := height_eq_zero

/-- The elements of coheight zero are the maximal elements. -/
@[simp] lemma coheight_eq_zero {x : α} : coheight x = 0 ↔ IsMax x :=
  height_eq_zero (α := αᵒᵈ)

protected alias ⟨_, IsMax.coheight_eq_zero⟩ := coheight_eq_zero

lemma height_ne_zero {x : α} : height x ≠ 0 ↔ ¬ IsMin x := height_eq_zero.not

@[simp] lemma height_pos {x : α} : 0 < height x ↔ ¬ IsMin x := by
  simp [pos_iff_ne_zero]

lemma coheight_ne_zero {x : α} : coheight x ≠ 0 ↔ ¬ IsMax x := coheight_eq_zero.not

@[simp] lemma coheight_pos {x : α} : 0 < coheight x ↔ ¬ IsMax x := by
  simp [pos_iff_ne_zero]

@[simp] lemma height_bot (α : Type*) [Preorder α] [OrderBot α] : height (⊥ : α) = 0 := by simp

@[simp] lemma coheight_top (α : Type*) [Preorder α] [OrderTop α] : coheight (⊤ : α) = 0 := by simp

lemma coe_lt_height_iff {x : α} {n : ℕ} (hfin : height x < ⊤) :
    n < height x ↔ ∃ y < x, height y = n where
  mp h := by
    obtain ⟨m, hx : height x = m⟩ := Option.ne_none_iff_exists'.mp hfin.ne_top
    rw [hx] at h; norm_cast at h
    obtain ⟨p, hp, hlen⟩ := exists_series_of_height_eq_coe x hx
    use p ⟨n, by omega⟩
    constructor
    · rw [← hp]
      apply LTSeries.strictMono
      simp [Fin.last]; omega
    · exact height_eq_index_of_length_eq_height_last (by simp [hlen, hp, hx]) ⟨n, by omega⟩
  mpr := fun ⟨y, hyx, hy⟩ =>
    hy ▸ height_strictMono hyx (lt_of_le_of_lt (height_mono hyx.le) hfin)

lemma coe_lt_coheight_iff {x : α} {n : ℕ} (hfin : coheight x < ⊤) :
    n < coheight x ↔ ∃ y > x, coheight y = n :=
  coe_lt_height_iff (α := αᵒᵈ) hfin

lemma height_eq_coe_add_one_iff {x : α} {n : ℕ} :
    height x = n + 1 ↔ height x < ⊤ ∧ (∃ y < x, height y = n) ∧ (∀ y < x, height y ≤ n) := by
  wlog hfin : height x < ⊤
  · simp_all
    exact ne_of_beq_false rfl
  simp only [hfin, true_and]
  trans n < height x ∧ height x ≤ n + 1
  · rw [le_antisymm_iff, and_comm]
    simp [ENat.add_one_le_iff]
  · congr! 1
    · exact coe_lt_height_iff hfin
    · simpa [hfin, ENat.lt_add_one_iff] using height_le_coe_iff (x := x) (n := n + 1)

lemma coheight_eq_coe_add_one_iff {x : α} {n : ℕ} :
    coheight x = n + 1 ↔
      coheight x < ⊤ ∧ (∃ y > x, coheight y = n) ∧ (∀ y > x, coheight y ≤ n) :=
  height_eq_coe_add_one_iff (α := αᵒᵈ)

lemma height_eq_coe_iff {x : α} {n : ℕ} :
    height x = n ↔
      height x < ⊤ ∧ (n = 0 ∨ ∃ y < x, height y = n - 1) ∧ (∀ y < x, height y < n) := by
  wlog hfin : height x < ⊤
  · simp_all
  simp only [hfin, true_and]
  cases n
  case zero => simp [isMin_iff_forall_not_lt]
  case succ n =>
    simp only [Nat.cast_add, Nat.cast_one, add_eq_zero, one_ne_zero, and_false, false_or]
    rw [height_eq_coe_add_one_iff]
    simp only [hfin, true_and]
    congr! 3
    rename_i y _
    cases height y <;> simp; norm_cast; cutsat

lemma coheight_eq_coe_iff {x : α} {n : ℕ} :
    coheight x = n ↔
      coheight x < ⊤ ∧ (n = 0 ∨ ∃ y > x, coheight y = n - 1) ∧ (∀ y > x, coheight y < n) :=
  height_eq_coe_iff (α := αᵒᵈ)

/-- The elements of finite height `n` are the minimal elements among those of height `≥ n`. -/
lemma height_eq_coe_iff_minimal_le_height {a : α} {n : ℕ} :
    height a = n ↔ Minimal (fun y => n ≤ height y) a := by
  by_cases! hfin : height a < ⊤
  · cases hn : n with
    | zero => simp
    | succ => simp [minimal_iff_forall_lt, height_eq_coe_add_one_iff, ENat.add_one_le_iff,
        coe_lt_height_iff, *]
  · suffices ∃ x < a, ↑n ≤ height x by
      simp_all [minimal_iff_forall_lt]
    simp only [top_le_iff, height_eq_top_iff] at hfin
    obtain ⟨p, rfl, hp⟩ := hfin (n + 1)
    use p.eraseLast.last, p.eraseLast_last_rel_last (by cutsat)
    simpa [hp] using length_le_height_last (p := p.eraseLast)

/-- The elements of finite coheight `n` are the maximal elements among those of coheight `≥ n`. -/
lemma coheight_eq_coe_iff_maximal_le_coheight {a : α} {n : ℕ} :
    coheight a = n ↔ Maximal (fun y => n ≤ coheight y) a :=
  height_eq_coe_iff_minimal_le_height (α := αᵒᵈ)

lemma one_lt_height_iff {x : α} : 1 < Order.height x ↔ ∃ y z, z < y ∧ y < x := by
  rw [← ENat.add_one_le_iff ENat.one_ne_top, one_add_one_eq_two]
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨p, hp, hlen⟩ := Order.exists_series_of_le_height x (n := 2) h
    refine ⟨p 1, p 0, p.rel_of_lt ?_, hp ▸ p.rel_of_lt ?_⟩ <;> simp [Fin.lt_def, hlen]
  · rintro ⟨y, z, hzy, hyx⟩
    let p : LTSeries α := RelSeries.fromListIsChain [z, y, x] (List.cons_ne_nil z [y, x])
      (List.IsChain.cons_cons hzy <| List.isChain_pair.mpr hyx)
    have : p.last = x := by simp [p, ← RelSeries.getLast_toList]
    exact Order.length_le_height this.le

end height

/-!
## Krull dimension
-/

section krullDim

variable {α β : Type*}

variable [Preorder α] [Preorder β]

lemma LTSeries.length_le_krullDim (p : LTSeries α) : p.length ≤ krullDim α := le_sSup ⟨_, rfl⟩

@[simp]
lemma krullDim_eq_bot_iff : krullDim α = ⊥ ↔ IsEmpty α := by
  rw [eq_bot_iff, krullDim, iSup_le_iff]
  simp only [le_bot_iff, WithBot.natCast_ne_bot, isEmpty_iff]
  exact ⟨fun H x ↦ H ⟨0, fun _ ↦ x, by simp⟩, (· <| · 1)⟩

lemma krullDim_nonneg_iff : 0 ≤ krullDim α ↔ Nonempty α := by
  rw [← not_iff_not, not_le, not_nonempty_iff, ← krullDim_eq_bot_iff, ← WithBot.lt_coe_bot,
    bot_eq_zero, WithBot.coe_zero]

lemma krullDim_eq_bot [IsEmpty α] : krullDim α = ⊥ := krullDim_eq_bot_iff.mpr ‹_›

lemma krullDim_nonneg [Nonempty α] : 0 ≤ krullDim α := krullDim_nonneg_iff.mpr ‹_›

theorem krullDim_ne_bot_iff : krullDim α ≠ ⊥ ↔ Nonempty α := by
  rw [ne_eq, krullDim_eq_bot_iff, not_isEmpty_iff]

theorem bot_lt_krullDim_iff : ⊥ < krullDim α ↔ Nonempty α := by
  rw [bot_lt_iff_ne_bot, krullDim_ne_bot_iff]

theorem bot_lt_krullDim [Nonempty α] : ⊥ < krullDim α :=
  bot_lt_krullDim_iff.mpr ‹_›

lemma krullDim_nonpos_iff_forall_isMax : krullDim α ≤ 0 ↔ ∀ x : α, IsMax x := by
  simp only [krullDim, iSup_le_iff, isMax_iff_forall_not_lt]
  refine ⟨fun H x y h ↦ (H ⟨1, ![x, y],
    fun i ↦ by obtain rfl := Subsingleton.elim i 0; simpa⟩).not_gt (by simp), ?_⟩
  · rintro H ⟨_ | n, l, h⟩
    · simp
    · cases H (l 0) (l 1) (h 0)

lemma krullDim_nonpos_iff_forall_isMin : krullDim α ≤ 0 ↔ ∀ x : α, IsMin x := by
  simp only [krullDim_nonpos_iff_forall_isMax, IsMax, IsMin]
  exact forall_swap

lemma krullDim_le_one_iff : krullDim α ≤ 1 ↔ ∀ x : α, IsMin x ∨ IsMax x := by
  rw [← not_iff_not]
  simp_rw [isMax_iff_forall_not_lt, isMin_iff_forall_not_lt, krullDim, iSup_le_iff]
  push_neg
  constructor
  · rintro ⟨⟨_ | _ | n, l, hl⟩, hl'⟩
    iterate 2 · cases hl'.not_ge (by simp)
    exact ⟨l 1, ⟨l 0, hl 0⟩, l 2, hl 1⟩
  · rintro ⟨x, ⟨y, hxy⟩, z, hzx⟩
    exact ⟨⟨2, ![y, x, z], fun i ↦ by fin_cases i <;> simpa⟩, by simp⟩

lemma krullDim_le_one_iff_forall_isMax {α : Type*} [PartialOrder α] [OrderBot α] :
    krullDim α ≤ 1 ↔ ∀ x : α, x ≠ ⊥ → IsMax x := by
  simp [krullDim_le_one_iff, ← or_iff_not_imp_left]

lemma krullDim_le_one_iff_forall_isMin {α : Type*} [PartialOrder α] [OrderTop α] :
    krullDim α ≤ 1 ↔ ∀ x : α, x ≠ ⊤ → IsMin x := by
  simp [krullDim_le_one_iff, ← or_iff_not_imp_right]

lemma krullDim_pos_iff : 0 < krullDim α ↔ ∃ x y : α, x < y := by
  rw [← not_iff_not]
  push_neg
  simp_rw [← isMax_iff_forall_not_lt, ← krullDim_nonpos_iff_forall_isMax]

lemma one_le_krullDim_iff : 1 ≤ krullDim α ↔ ∃ x y : α, x < y := by
  rw [← krullDim_pos_iff, ← Nat.cast_zero, ← WithBot.add_one_le_iff, Nat.cast_zero, zero_add]

lemma krullDim_nonpos_of_subsingleton [Subsingleton α] : krullDim α ≤ 0 := by
  rw [krullDim_nonpos_iff_forall_isMax]
  exact fun x y h ↦ (Subsingleton.elim x y).ge

lemma krullDim_eq_zero [Nonempty α] [Subsingleton α] :
    krullDim α = 0 :=
  le_antisymm krullDim_nonpos_of_subsingleton krullDim_nonneg

lemma krullDim_eq_zero_of_unique [Unique α] : krullDim α = 0 :=
  le_antisymm krullDim_nonpos_of_subsingleton krullDim_nonneg

section PartialOrder

variable {α : Type*} [PartialOrder α]

lemma krullDim_eq_zero_iff_of_orderBot [OrderBot α] :
    krullDim α = 0 ↔ Subsingleton α :=
  ⟨fun H ↦ subsingleton_of_forall_eq ⊥ fun _ ↦ le_bot_iff.mp
    (krullDim_nonpos_iff_forall_isMax.mp H.le ⊥ bot_le), fun _ ↦ Order.krullDim_eq_zero⟩

lemma krullDim_pos_iff_of_orderBot [OrderBot α] :
    0 < krullDim α ↔ Nontrivial α := by
  rw [← not_subsingleton_iff_nontrivial, ← Order.krullDim_eq_zero_iff_of_orderBot,
    ← ne_eq, ← lt_or_lt_iff_ne, or_iff_right]
  simp [Order.krullDim_nonneg]

lemma krullDim_eq_zero_iff_of_orderTop [OrderTop α] :
    krullDim α = 0 ↔ Subsingleton α :=
  ⟨fun H ↦ subsingleton_of_forall_eq ⊤ fun _ ↦ top_le_iff.mp
    (krullDim_nonpos_iff_forall_isMin.mp H.le ⊤ le_top), fun _ ↦ Order.krullDim_eq_zero⟩

lemma krullDim_pos_iff_of_orderTop [OrderTop α] :
    0 < krullDim α ↔ Nontrivial α := by
  rw [← not_subsingleton_iff_nontrivial, ← Order.krullDim_eq_zero_iff_of_orderTop,
    ← ne_eq, ← lt_or_lt_iff_ne, or_iff_right]
  simp [Order.krullDim_nonneg]

end PartialOrder

lemma krullDim_eq_length_of_finiteDimensionalOrder [FiniteDimensionalOrder α] :
    krullDim α = (LTSeries.longestOf α).length :=
  le_antisymm
    (iSup_le <| fun _ ↦ WithBot.coe_le_coe.mpr <| WithTop.coe_le_coe.mpr <|
      RelSeries.length_le_length_longestOf _ _) <|
    le_iSup (fun (i : LTSeries _) ↦ (i.length : WithBot (WithTop ℕ))) <| LTSeries.longestOf _

lemma krullDim_eq_top [InfiniteDimensionalOrder α] :
    krullDim α = ⊤ :=
  le_antisymm le_top <| le_iSup_iff.mpr <| fun m hm ↦ match m, hm with
  | ⊥, hm => False.elim <| by
    haveI : Inhabited α := ⟨LTSeries.withLength _ 0 0⟩
    exact not_le_of_gt (WithBot.bot_lt_coe _ : ⊥ < (0 : WithBot (WithTop ℕ))) <| hm default
  | some ⊤, _ => le_refl _
  | some (some m), hm => by
    refine (not_lt_of_ge (hm (LTSeries.withLength _ (m + 1))) ?_).elim
    rw [WithBot.some_eq_coe, ← WithBot.coe_natCast, WithBot.coe_lt_coe,
      WithTop.some_eq_coe, ← WithTop.coe_natCast, WithTop.coe_lt_coe]
    simp

lemma krullDim_eq_top_iff : krullDim α = ⊤ ↔ InfiniteDimensionalOrder α := by
  refine ⟨fun h ↦ ?_, fun _ ↦ krullDim_eq_top⟩
  cases isEmpty_or_nonempty α
  · simp [krullDim_eq_bot] at h
  cases finiteDimensionalOrder_or_infiniteDimensionalOrder α
  · rw [krullDim_eq_length_of_finiteDimensionalOrder] at h
    cases h
  · infer_instance

lemma le_krullDim_iff {n : ℕ} : n ≤ krullDim α ↔ ∃ l : LTSeries α, l.length = n := by
  cases isEmpty_or_nonempty α
  · simp [krullDim_eq_bot]
  cases finiteDimensionalOrder_or_infiniteDimensionalOrder α
  · rw [krullDim_eq_length_of_finiteDimensionalOrder, Nat.cast_le]
    constructor
    · exact fun H ↦ ⟨(LTSeries.longestOf α).take ⟨_, Nat.lt_succ.mpr H⟩, rfl⟩
    · exact fun ⟨l, hl⟩ ↦ hl ▸ l.longestOf_is_longest
  · simpa [krullDim_eq_top] using SetRel.InfiniteDimensional.exists_relSeries_with_length n

/-- A definition of krullDim for nonempty `α` that avoids `WithBot` -/
lemma krullDim_eq_iSup_length [Nonempty α] :
    krullDim α = ⨆ (p : LTSeries α), (p.length : ℕ∞) := by
  unfold krullDim
  rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
  rfl

lemma krullDim_lt_coe_iff {n : ℕ} : krullDim α < n ↔ ∀ l : LTSeries α, l.length < n := by
  rw [krullDim, ← WithBot.coe_natCast]
  rcases n with - | n
  · rw [ENat.coe_zero, ← bot_eq_zero, WithBot.lt_coe_bot]
    simp
  · simp [WithBot.lt_add_one_iff, WithBot.coe_natCast, Nat.lt_succ]

lemma krullDim_le_of_strictMono (f : α → β) (hf : StrictMono f) : krullDim α ≤ krullDim β :=
  iSup_le fun p ↦ le_sSup ⟨p.map f hf, rfl⟩

lemma krullDim_le_of_strictComono_and_surj
    (f : α → β) (hf : ∀ ⦃a b⦄, f a < f b → a < b) (hf' : Function.Surjective f) :
    krullDim β ≤ krullDim α :=
  iSup_le fun p ↦ le_sSup ⟨p.comap _ hf hf', rfl⟩

lemma krullDim_eq_of_orderIso (f : α ≃o β) : krullDim α = krullDim β :=
  le_antisymm (krullDim_le_of_strictMono _ f.strictMono) <|
    krullDim_le_of_strictMono _ f.symm.strictMono

@[simp] lemma krullDim_orderDual : krullDim αᵒᵈ = krullDim α :=
  le_antisymm (iSup_le fun i ↦ le_sSup ⟨i.reverse, rfl⟩) <|
    iSup_le fun i ↦ le_sSup ⟨i.reverse, rfl⟩

lemma height_le_krullDim (a : α) : height a ≤ krullDim α := by
  have : Nonempty α := ⟨a⟩
  rw [krullDim_eq_iSup_length]
  simp only [WithBot.coe_le_coe]
  exact height_le fun p _ ↦ le_iSup_of_le p le_rfl

lemma coheight_le_krullDim (a : α) : coheight a ≤ krullDim α := by
  simpa using height_le_krullDim (α := αᵒᵈ) a

@[simp]
lemma _root_.LTSeries.height_last_longestOf [FiniteDimensionalOrder α] :
    height (LTSeries.longestOf α).last = krullDim α := by
  refine le_antisymm (height_le_krullDim _) ?_
  rw [krullDim_eq_length_of_finiteDimensionalOrder, height]
  norm_cast
  exact le_iSup_iff.mpr <| fun _ h ↦ iSup_le_iff.mp (h _) le_rfl

/--
The Krull dimension is the supremum of the elements' heights.

This version of the lemma assumes that `α` is nonempty. In this case, the coercion from `ℕ∞` to
`WithBot ℕ∞` is on the outside of the right-hand side, which is usually more convenient.

If `α` were empty, then `krullDim α = ⊥`. See `krullDim_eq_iSup_height` for the more general
version, with the coercion under the supremum.
-/
lemma krullDim_eq_iSup_height_of_nonempty [Nonempty α] : krullDim α = ↑(⨆ (a : α), height a) := by
  apply le_antisymm
  · apply iSup_le
    intro p
    suffices p.length ≤ ⨆ (a : α), height a from (WithBot.unbotD_le_iff fun _ => this).mp this
    apply le_iSup_of_le p.last (length_le_height_last (p := p))
  · rw [WithBot.coe_iSup (by bddDefault)]
    apply iSup_le
    apply height_le_krullDim

/--
The Krull dimension is the supremum of the elements' coheights.

This version of the lemma assumes that `α` is nonempty. In this case, the coercion from `ℕ∞` to
`WithBot ℕ∞` is on the outside of the right-hand side, which is usually more convenient.

If `α` were empty, then `krullDim α = ⊥`. See `krullDim_eq_iSup_coheight` for the more general
version, with the coercion under the supremum.
-/
lemma krullDim_eq_iSup_coheight_of_nonempty [Nonempty α] :
    krullDim α = ↑(⨆ (a : α), coheight a) := by
  simpa using krullDim_eq_iSup_height_of_nonempty (α := αᵒᵈ)

/--
The Krull dimension is the supremum of the elements' height plus coheight.
-/
lemma krullDim_eq_iSup_height_add_coheight_of_nonempty [Nonempty α] :
    krullDim α = ↑(⨆ (a : α), height a + coheight a) := by
  apply le_antisymm
  · rw [krullDim_eq_iSup_height_of_nonempty, WithBot.coe_le_coe]
    apply ciSup_mono (by bddDefault) (by simp)
  · wlog hnottop : krullDim α < ⊤
    · simp_all
    rw [krullDim_eq_iSup_length, WithBot.coe_le_coe]
    apply iSup_le
    intro a
    have : height a < ⊤ := WithBot.coe_lt_coe.mp (lt_of_le_of_lt (height_le_krullDim a) hnottop)
    have : coheight a < ⊤ := WithBot.coe_lt_coe.mp (lt_of_le_of_lt (coheight_le_krullDim a) hnottop)
    cases hh : height a with
    | top => simp_all
    | coe n =>
      cases hch : coheight a with
      | top => simp_all
      | coe m =>
        obtain ⟨p₁, hlast, hlen₁⟩ := exists_series_of_height_eq_coe a hh
        obtain ⟨p₂, hhead, hlen₂⟩ := exists_series_of_coheight_eq_coe a hch
        apply le_iSup_of_le ((p₁.smash p₂) (by simp [*])) (by simp [*])

/--
The Krull dimension is the supremum of the elements' heights.

If `α` is `Nonempty`, then `krullDim_eq_iSup_height_of_nonempty`, with the coercion from
`ℕ∞` to `WithBot ℕ∞` outside the supremum, can be more convenient.
-/
lemma krullDim_eq_iSup_height : krullDim α = ⨆ (a : α), ↑(height a) := by
  cases isEmpty_or_nonempty α with
  | inl h => rw [krullDim_eq_bot, ciSup_of_empty]
  | inr h => rw [krullDim_eq_iSup_height_of_nonempty, WithBot.coe_iSup (OrderTop.bddAbove _)]

/--
The Krull dimension is the supremum of the elements' coheights.

If `α` is `Nonempty`, then `krullDim_eq_iSup_coheight_of_nonempty`, with the coercion from
`ℕ∞` to `WithBot ℕ∞` outside the supremum, can be more convenient.
-/
lemma krullDim_eq_iSup_coheight : krullDim α = ⨆ (a : α), ↑(coheight a) := by
  cases isEmpty_or_nonempty α with
  | inl h => rw [krullDim_eq_bot, ciSup_of_empty]
  | inr h => rw [krullDim_eq_iSup_coheight_of_nonempty, WithBot.coe_iSup (OrderTop.bddAbove _)]

@[simp] -- not as useful as a simp lemma as it looks, due to the coe on the left
lemma height_top_eq_krullDim [OrderTop α] : height (⊤ : α) = krullDim α := by
  rw [krullDim_eq_iSup_length]
  simp only [WithBot.coe_inj]
  apply le_antisymm
  · exact height_le fun p _ ↦ le_iSup_of_le p le_rfl
  · exact iSup_le fun _ => length_le_height le_top

@[simp] -- not as useful as a simp lemma as it looks, due to the coe on the left
lemma coheight_bot_eq_krullDim [OrderBot α] : coheight (⊥ : α) = krullDim α := by
  rw [← krullDim_orderDual]
  exact height_top_eq_krullDim (α := αᵒᵈ)

lemma height_eq_krullDim_Iic (x : α) : (height x : ℕ∞) = krullDim (Set.Iic x) := by
  rw [← height_top_eq_krullDim, height, height, WithBot.coe_inj]
  apply le_antisymm
  · apply iSup_le; intro p; apply iSup_le; intro hp
    let q := LTSeries.mk p.length (fun i ↦ (⟨p.toFun i, le_trans (p.monotone (Fin.le_last _)) hp⟩
     : Set.Iic x)) (fun _ _ h ↦ p.strictMono h)
    simp only [le_top, iSup_pos, ge_iff_le]
    exact le_iSup (fun p ↦ (p.length : ℕ∞)) q
  · apply iSup_le; intro p; apply iSup_le; intro _
    have mono : StrictMono (fun (y : Set.Iic x) ↦ y.1) := fun _ _ h ↦ h
    rw [← LTSeries.map_length p (fun x ↦ x.1) mono, ]
    refine le_iSup₂ (f := fun p hp ↦ (p.length : ℕ∞)) (p.map (fun x ↦ x.1) mono) ?_
    exact (p.toFun (Fin.last p.length)).2

lemma coheight_eq_krullDim_Ici {α : Type*} [Preorder α] (x : α) :
    (coheight x : ℕ∞) = krullDim (Set.Ici x) := by
  rw [coheight, ← krullDim_orderDual, Order.krullDim_eq_of_orderIso (OrderIso.refl _)]
  exact height_eq_krullDim_Iic _

end krullDim

section finiteDimensional

variable {α : Type*} [Preorder α]

lemma finiteDimensionalOrder_iff_krullDim_ne_bot_and_top :
    FiniteDimensionalOrder α ↔ krullDim α ≠ ⊥ ∧ krullDim α ≠ ⊤ := by
  by_cases h : Nonempty α
  · simp [← not_infiniteDimensionalOrder_iff, ← krullDim_eq_top_iff]
  · constructor
    · exact (fun h1 ↦ False.elim (h (LTSeries.nonempty_of_finiteDimensionalOrder α)))
    · exact (fun h1 ↦ False.elim (h1.1 (krullDim_eq_bot_iff.mpr (not_nonempty_iff.mp h))))

lemma krullDim_ne_bot_of_finiteDimensionalOrder [FiniteDimensionalOrder α] : krullDim α ≠ ⊥ :=
  (finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mp ‹_›).1

lemma krullDim_ne_top_of_finiteDimensionalOrder [FiniteDimensionalOrder α] : krullDim α ≠ ⊤ :=
  (finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mp ‹_›).2

end finiteDimensional

section typeclass

/-- Typeclass for orders with krull dimension at most `n`. -/
@[mk_iff]
class KrullDimLE (n : ℕ) (α : Type*) [Preorder α] : Prop where
  krullDim_le : krullDim α ≤ n

lemma KrullDimLE.mono {n m : ℕ} (e : n ≤ m) (α : Type*) [Preorder α] [KrullDimLE n α] :
    KrullDimLE m α :=
  ⟨KrullDimLE.krullDim_le (n := n).trans (Nat.cast_le.mpr e)⟩

instance {α} [Preorder α] [Subsingleton α] : KrullDimLE 0 α := ⟨krullDim_nonpos_of_subsingleton⟩

end typeclass

/-!
## Concrete calculations
-/

section calculations

lemma krullDim_eq_one_iff_of_boundedOrder {α : Type*} [PartialOrder α] [BoundedOrder α] :
    krullDim α = 1 ↔ IsSimpleOrder α := by
  rw [le_antisymm_iff, krullDim_le_one_iff, WithBot.one_le_iff_pos,
    Order.krullDim_pos_iff_of_orderBot, isSimpleOrder_iff]
  simp only [isMin_iff_eq_bot, isMax_iff_eq_top, and_comm]

@[simp] lemma krullDim_of_isSimpleOrder {α : Type*} [PartialOrder α] [BoundedOrder α]
    [IsSimpleOrder α] : krullDim α = 1 :=
  krullDim_eq_one_iff_of_boundedOrder.mpr ‹_›

variable {α : Type*} [Preorder α]

/-
These two lemmas could possibly be used to simplify the subsequent calculations,
especially once the `Set.encard` api is richer.

(Commented out to avoid importing modules purely for `proof_wanted`.)
proof_wanted height_of_linearOrder {α : Type*} [LinearOrder α] (a : α) :
  height a = (Set.Iio a).encard

proof_wanted coheight_of_linearOrder {α : Type*} [LinearOrder α] (a : α) :
  coheight a = (Set.Ioi a).encard
-/

@[simp] lemma height_nat (n : ℕ) : height n = n := by
  induction n using Nat.strongRecOn with | ind n ih =>
  apply le_antisymm
  · apply height_le_coe_iff.mpr
    simp +contextual only [ih, Nat.cast_lt, implies_true]
  · exact length_le_height_last (p := LTSeries.range n)

@[simp] lemma coheight_of_noMaxOrder [NoMaxOrder α] (a : α) : coheight a = ⊤ := by
  obtain ⟨f, hstrictmono⟩ := Nat.exists_strictMono ↑(Set.Ioi a)
  apply coheight_eq_top_iff.mpr
  intro m
  use {length := m, toFun := fun i => if i = 0 then a else f i, step := ?step }
  case h => simp [RelSeries.head]
  case step =>
    intro ⟨i, hi⟩
    by_cases hzero : i = 0
    · subst i
      exact (f 1).prop
    · suffices f i < f (i + 1) by simp [Fin.ext_iff, hzero, this]
      apply hstrictmono
      cutsat

@[simp] lemma height_of_noMinOrder [NoMinOrder α] (a : α) : height a = ⊤ :=
  -- Implementation note: Here it's a bit easier to define the coheight variant first
  coheight_of_noMaxOrder (α := αᵒᵈ) a

@[simp] lemma krullDim_of_noMaxOrder [Nonempty α] [NoMaxOrder α] : krullDim α = ⊤ := by
  simp [krullDim_eq_iSup_coheight, coheight_of_noMaxOrder]

@[simp] lemma krullDim_of_noMinOrder [Nonempty α] [NoMinOrder α] : krullDim α = ⊤ := by
  simp [krullDim_eq_iSup_height, height_of_noMinOrder]

lemma coheight_nat (n : ℕ) : coheight n = ⊤ := coheight_of_noMaxOrder ..

lemma krullDim_nat : krullDim ℕ = ⊤ := krullDim_of_noMaxOrder ..

lemma height_int (n : ℤ) : height n = ⊤ := height_of_noMinOrder ..

lemma coheight_int (n : ℤ) : coheight n = ⊤ := coheight_of_noMaxOrder ..

lemma krullDim_int : krullDim ℤ = ⊤ := krullDim_of_noMaxOrder ..

@[simp] lemma height_coe_withBot (x : α) : height (x : WithBot α) = height x + 1 := by
  apply le_antisymm
  · apply height_le
    intro p hlast
    wlog hlenpos : p.length ≠ 0
    · simp_all
    -- essentially p' := (p.drop 1).map unbot
    let p' : LTSeries α := {
      length := p.length - 1
      toFun := fun ⟨i, hi⟩ => (p ⟨i+1, by cutsat⟩).unbot (by
        apply ne_bot_of_gt (a := p.head)
        apply p.strictMono
        exact compare_gt_iff_gt.mp rfl)
      step := fun i => by simpa [WithBot.unbot_lt_iff] using p.step ⟨i + 1, by cutsat⟩ }
    have hlast' : p'.last = x := by
      simp only [p', RelSeries.last, WithBot.unbot_eq_iff, ← hlast, Fin.last]
      congr
      omega
    suffices p'.length ≤ height p'.last by
      simpa [p', hlast'] using this
    apply length_le_height_last
  · rw [height_add_const]
    apply iSup₂_le
    intro p hlast
    let p' := (p.map _ WithBot.coe_strictMono).cons ⊥ (by simp)
    apply le_iSup₂_of_le p' (by simp [p', hlast]) (by simp [p'])

@[simp] lemma coheight_coe_withTop (x : α) : coheight (x : WithTop α) = coheight x + 1 :=
  height_coe_withBot (α := αᵒᵈ) x

@[simp] lemma height_coe_withTop (x : α) : height (x : WithTop α) = height x := by
  apply le_antisymm
  · apply height_le
    intro p hlast
    -- essentially p' := p.map untop
    let p' : LTSeries α := {
      length := p.length
      toFun := fun i => (p i).untop (by
        apply WithTop.lt_top_iff_ne_top.mp
        apply lt_of_le_of_lt
        · exact p.monotone (Fin.le_last _)
        · rw [RelSeries.last] at hlast
          simp [hlast])
      step := fun i => by simpa [WithTop.untop_lt_iff, WithTop.coe_untop] using p.step i }
    have hlast' : p'.last = x := by
      simp only [p', RelSeries.last, WithTop.untop_eq_iff, ← hlast]
    suffices p'.length ≤ height p'.last by
      rw [hlast'] at this
      simpa [p'] using this
    apply length_le_height_last
  · apply height_le
    intro p hlast
    let p' := p.map _ WithTop.coe_strictMono
    apply le_iSup₂_of_le p' (by simp [p', hlast]) (by simp [p'])

@[simp] lemma coheight_coe_withBot (x : α) : coheight (x : WithBot α) = coheight x :=
  height_coe_withTop (α := αᵒᵈ) x

@[simp] lemma krullDim_WithTop [Nonempty α] : krullDim (WithTop α) = krullDim α + 1 := by
  rw [← height_top_eq_krullDim, krullDim_eq_iSup_height_of_nonempty, height_eq_iSup_lt_height]
  norm_cast
  simp_rw [WithTop.lt_top_iff_ne_top]
  rw [ENat.iSup_add, iSup_subtype']
  symm
  apply Equiv.withTopSubtypeNe.symm.iSup_congr
  simp

@[simp] lemma krullDim_withBot [Nonempty α] : krullDim (WithBot α) = krullDim α + 1 := by
  conv_lhs => rw [← krullDim_orderDual]
  conv_rhs => rw [← krullDim_orderDual]
  exact krullDim_WithTop (α := αᵒᵈ)

@[simp]
lemma krullDim_enat : krullDim ℕ∞ = ⊤ := by
  change (krullDim (WithTop ℕ) = ⊤)
  simp [← WithBot.coe_top, ← WithBot.coe_one, ← WithBot.coe_add]

@[simp]
lemma height_enat (n : ℕ∞) : height n = n := by
  cases n with
  | top => simp only [← WithBot.coe_eq_coe, height_top_eq_krullDim, krullDim_enat, WithBot.coe_top]
  | coe n => exact (height_coe_withTop _).trans (height_nat _)

@[simp]
lemma coheight_coe_enat (n : ℕ) : coheight (n : ℕ∞) = ⊤ := by
  apply (coheight_coe_withTop _).trans
  simp only [coheight_nat, top_add]

end calculations

section orderHom

variable {α β : Type*} [Preorder α] [PartialOrder β]
variable {m : ℕ} (f : α →o β) (h : ∀ (x : β), Order.krullDim (f ⁻¹' {x}) ≤ m)

include h in
lemma height_le_of_krullDim_preimage_le (x : α) :
    Order.height x ≤ (m + 1) * Order.height (f x) + m := by
  generalize h' : Order.height (f x) = n
  cases n with | top => simp | coe n =>
    induction n using Nat.strong_induction_on generalizing x with | h n ih =>
    refine height_le_iff.mpr fun p hp ↦ le_of_not_gt fun h_len ↦ ?_
    let i : Fin (p.length + 1) := ⟨p.length - (m + 1), Nat.sub_lt_succ p.length _⟩
    suffices h'' : f (p i) < f x by
      obtain ⟨n', hn'⟩ : ∃ (n' : ℕ), n' = height (f (p i)) := ENat.ne_top_iff_exists.mp
        ((height_mono h''.le).trans_lt (h' ▸ ENat.coe_lt_top _)).ne
      have h_lt : n' < n := ENat.coe_lt_coe.mp
        (h' ▸ hn' ▸ height_strictMono h'' (hn' ▸ ENat.coe_lt_top _))
      have := (length_le_height_last (p := p.take i)).trans <| ih n' h_lt (p i) hn'.symm
      rw [RelSeries.take_length, ENat.coe_sub, Nat.cast_add, Nat.cast_one, tsub_le_iff_right,
        add_assoc, add_comm _ (_ + 1), ← add_assoc, ← mul_add_one] at this
      refine not_lt_of_ge ?_ (h_len.trans_le this)
      gcongr
      rwa [← ENat.coe_one, ← ENat.coe_add, ENat.coe_le_coe]
    refine (f.monotone ((p.monotone (Fin.le_last _)).trans hp)).lt_of_not_ge fun h'' ↦ ?_
    let q' : LTSeries α := p.drop i
    let q : LTSeries (f ⁻¹' {f x}) := ⟨q'.length, fun j ↦ ⟨q' j, le_antisymm
      (f.monotone (le_trans (b := q'.last) (q'.monotone (Fin.le_last _)) (p.last_drop _ ▸ hp)))
      (le_trans (b := f q'.head) (p.head_drop _ ▸ h'')
        (f.monotone (q'.monotone (Fin.zero_le _))))⟩, fun i ↦ q'.step i⟩
    have := (LTSeries.length_le_krullDim q).trans (h (f x))
    simp only [RelSeries.drop_length, Nat.cast_le, tsub_le_iff_right, q', i, q] at this
    have : p.length > m := ENat.coe_lt_coe.mp ((le_add_left le_rfl).trans_lt h_len)
    cutsat

include h in
lemma coheight_le_of_krullDim_preimage_le (x : α) :
    Order.coheight x ≤ (m + 1) * Order.coheight (f x) + m := by
  rw [Order.coheight, Order.coheight]
  apply height_le_of_krullDim_preimage_le (f := f.dual)
  exact fun x ↦ le_of_eq_of_le (krullDim_orderDual (α := f ⁻¹' {x})) (h x)

include f h in
lemma krullDim_le_of_krullDim_preimage_le :
    Order.krullDim α ≤ (m + 1) * Order.krullDim β + m := by
  rw [Order.krullDim_eq_iSup_height, Order.krullDim_eq_iSup_height, iSup_le_iff]
  refine fun x ↦ (WithBot.coe_mono (height_le_of_krullDim_preimage_le f h x)).trans ?_
  push_cast
  gcongr
  exacts [right_eq_inf.mp rfl, le_iSup_iff.mpr fun b a ↦ a (f x)]

/-- Another version when the `OrderHom` is unbundled -/
lemma krullDim_le_of_krullDim_preimage_le' (f : α → β) (h_mono : Monotone f)
    (h : ∀ (x : β), Order.krullDim (f ⁻¹' {x}) ≤ m) :
    Order.krullDim α ≤ (m + 1) * Order.krullDim β + m :=
  Order.krullDim_le_of_krullDim_preimage_le ⟨f, h_mono⟩ h

end orderHom

end Order
