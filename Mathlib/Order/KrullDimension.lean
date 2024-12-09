/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li, Joachim Breitner
-/

import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.Minimal
import Mathlib.Order.RelSeries

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
relation series of `α` ordered by `<` and ending below or at `a`.
-/
noncomputable def height {α : Type*} [Preorder α] (a : α) : ℕ∞ :=
  ⨆ (p : LTSeries α) (_ : p.last ≤ a), p.length

/--
The **coheight** of an element `a` in a preorder `α` is the supremum of the rightmost index of all
relation series of `α` ordered by `<` and beginning with `a`.

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
  apply Equiv.iSup_congr ⟨RelSeries.reverse, RelSeries.reverse, RelSeries.reverse_reverse,
    RelSeries.reverse_reverse⟩
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
  rw [show p.length = p'.length by simp [p']; omega]
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
  show height (α := αᵒᵈ) a = ⨆ (p : LTSeries α) (_ : p.head = a), ↑(p.length)
  rw [height_eq_iSup_last_eq]
  apply Equiv.iSup_congr ⟨RelSeries.reverse, RelSeries.reverse, RelSeries.reverse_reverse,
    RelSeries.reverse_reverse⟩
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
      · apply p.step ⟨p.length - 1, by omega⟩
      · convert hlast
        simp only [Fin.succ_mk, Nat.succ_eq_add_one, RelSeries.last, Fin.last]
        congr; omega)
    suffices p'.length ≤ height x by
      simp [p'] at this
      convert this
      norm_cast
      omega
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
  omega

/--
In a maximally long series, i.e one as long as the coheight of the first element, the coheight of
each element is its reverse index in the series.
-/
lemma coheight_eq_index_of_length_eq_head_coheight {p : LTSeries α} (h : p.length = coheight p.head)
    (i : Fin (p.length + 1)) : coheight (p i) = i.rev := by
  simpa using height_eq_index_of_length_eq_height_last (α := αᵒᵈ) (p := p.reverse) (by simpa) i.rev

lemma height_mono : Monotone (α := α) height :=
  fun _ _ hab ↦ biSup_mono (fun _ hla => hla.trans hab)

@[gcongr] protected lemma _root_.GCongr.height_le_height (a b : α) (hab : a ≤ b) :
    height a ≤ height b := height_mono hab

lemma coheight_anti : Antitone (α := α) coheight :=
  (height_mono (α := αᵒᵈ)).dual_left

@[gcongr] protected lemma _root_.GCongr.coheight_le_coheight (a b : α) (hba : b ≤ a) :
    coheight a ≤ coheight b := coheight_anti hba

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

/- For elements of finite height, `coheight` is strictly antitone. -/
@[gcongr] lemma coheight_strictAnti {x y : α} (hyx : y < x) (hfin : coheight x < ⊤) :
    coheight x < coheight y :=
  height_strictMono (α := αᵒᵈ) hyx hfin

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

/-- There exist a series ending in a element for any length up to the element’s height.  -/
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
    apply ha (p.drop ⟨m-n, by omega⟩) (by simp) (by simp; omega)
  | coe m =>
    rw [ha, Nat.cast_le] at h
    rw [height_eq_iSup_last_eq, iSup_subtype'] at ha
    obtain ⟨⟨p, hlast⟩, hlen⟩ := exists_eq_iSup_of_iSup_eq_coe ha
    simp only [Nat.cast_inj] at hlen
    use p.drop ⟨m-n, by omega⟩
    constructor
    · simp [hlast]
    · simp [hlen]; omega

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
      apply le_iSup_of_le (by rw [← hp]; apply RelSeries.eraseLast_last_rel_last _ (by omega))
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
    obtain ⟨p, hlast, hp⟩ := h (n+1)
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

lemma coe_lt_coheight_iff {x : α} {n : ℕ} (hfin : coheight x < ⊤):
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
    simp [hfin, ENat.lt_add_one_iff, ENat.add_one_le_iff]
  · congr! 1
    · exact coe_lt_height_iff hfin
    · simpa [hfin, ENat.lt_add_one_iff] using height_le_coe_iff (x := x) (n := n+1)

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
    cases height y <;> simp; norm_cast; omega

lemma coheight_eq_coe_iff {x : α} {n : ℕ} :
    coheight x = n ↔
      coheight x < ⊤ ∧ (n = 0 ∨ ∃ y > x, coheight y = n - 1) ∧ (∀ y > x, coheight y < n) :=
  height_eq_coe_iff (α := αᵒᵈ)

/-- The elements of finite height `n` are the minimial elements among those of height `≥ n`. -/
lemma height_eq_coe_iff_minimal_le_height {a : α} {n : ℕ} :
    height a = n ↔ Minimal (fun y => n ≤ height y) a := by
  by_cases hfin : height a < ⊤
  · cases hn : n with
    | zero => simp
    | succ => simp [minimal_iff_forall_lt, height_eq_coe_add_one_iff, ENat.add_one_le_iff,
        coe_lt_height_iff, *]
  · suffices ∃ x < a, ↑n ≤ height x by
      simp_all [minimal_iff_forall_lt]
    simp only [not_lt, top_le_iff, height_eq_top_iff] at hfin
    obtain ⟨p, rfl, hp⟩ := hfin (n+1)
    use p.eraseLast.last, RelSeries.eraseLast_last_rel_last _ (by omega)
    simpa [hp] using length_le_height_last (p := p.eraseLast)

/-- The elements of finite coheight `n` are the maximal elements among those of coheight `≥ n`. -/
lemma coheight_eq_coe_iff_maximal_le_coheight {a : α} {n : ℕ} :
    coheight a = n ↔ Maximal (fun y => n ≤ coheight y) a :=
  height_eq_coe_iff_minimal_le_height (α := αᵒᵈ)

end height

/-!
## Krull dimension
-/

section krullDim

variable {α β : Type*}

variable [Preorder α] [Preorder β]

lemma LTSeries.length_le_krullDim (p : LTSeries α) : p.length ≤ krullDim α := le_sSup ⟨_, rfl⟩

lemma krullDim_nonneg_of_nonempty [Nonempty α] : 0 ≤ krullDim α :=
  le_sSup ⟨⟨0, fun _ ↦ @Nonempty.some α inferInstance, fun f ↦ f.elim0⟩, rfl⟩

/-- A definition of krullDim for nonempty `α` that avoids `WithBot` -/
lemma krullDim_eq_iSup_length [Nonempty α] :
    krullDim α = ⨆ (p : LTSeries α), (p.length : ℕ∞) := by
  unfold krullDim
  rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
  rfl

lemma krullDim_eq_bot_of_isEmpty [IsEmpty α] : krullDim α = ⊥ := WithBot.ciSup_empty _

lemma krullDim_eq_top_of_infiniteDimensionalOrder [InfiniteDimensionalOrder α] :
    krullDim α = ⊤ :=
  le_antisymm le_top <| le_iSup_iff.mpr <| fun m hm ↦ match m, hm with
  | ⊥, hm => False.elim <| by
    haveI : Inhabited α := ⟨LTSeries.withLength _ 0 0⟩
    exact not_le_of_lt (WithBot.bot_lt_coe _ : ⊥ < (0 : WithBot (WithTop ℕ))) <| hm default
  | some ⊤, _ => le_refl _
  | some (some m), hm => by
    refine (not_lt_of_le (hm (LTSeries.withLength _ (m + 1))) ?_).elim
    erw [WithBot.coe_lt_coe, WithTop.coe_lt_coe]
    simp

lemma krullDim_le_of_strictMono (f : α → β) (hf : StrictMono f) : krullDim α ≤ krullDim β :=
  iSup_le <| fun p ↦ le_sSup ⟨p.map f hf, rfl⟩

lemma krullDim_eq_length_of_finiteDimensionalOrder [FiniteDimensionalOrder α] :
    krullDim α = (LTSeries.longestOf α).length :=
  le_antisymm
    (iSup_le <| fun _ ↦ WithBot.coe_le_coe.mpr <| WithTop.coe_le_coe.mpr <|
      RelSeries.length_le_length_longestOf _ _) <|
    le_iSup (fun (i : LTSeries _) ↦ (i.length : WithBot (WithTop ℕ))) <| LTSeries.longestOf _

lemma krullDim_eq_zero_of_unique [Unique α] : krullDim α = 0 := by
  rw [krullDim_eq_length_of_finiteDimensionalOrder (α := α), Nat.cast_eq_zero]
  refine (LTSeries.longestOf_len_unique (default : LTSeries α) fun q ↦ show _ ≤ 0 from ?_).symm
  by_contra r
  exact ne_of_lt (q.step ⟨0, not_le.mp r⟩) <| Subsingleton.elim _ _

lemma krullDim_nonpos_of_subsingleton [Subsingleton α] : krullDim α ≤ 0 := by
  by_cases hα : Nonempty α
  · have := uniqueOfSubsingleton (Classical.choice hα)
    exact le_of_eq krullDim_eq_zero_of_unique
  · have := not_nonempty_iff.mp hα
    exact le_of_lt <| lt_of_eq_of_lt krullDim_eq_bot_of_isEmpty <|
      Batteries.compareOfLessAndEq_eq_lt.mp rfl

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
  simp only [WithBot.coe_le_coe, iSup_le_iff]
  exact height_le fun p _ ↦ le_iSup_of_le p le_rfl

lemma coheight_le_krullDim (a : α) : coheight a ≤ krullDim α := by
  simpa using height_le_krullDim (α := αᵒᵈ) a

/--
The Krull dimension is the supremum of the elements' heights.

This version of the lemma assumes that `α` is nonempty. In this case, the coercion from `ℕ∞` to
`WithBot ℕ∞` is on the outside fo the right-hand side, which is usually more convenient.

If `α` were empty, then `krullDim α = ⊥`. See `krullDim_eq_iSup_height` for the more general
version, with the coercion under the supremum.
-/
lemma krullDim_eq_iSup_height_of_nonempty [Nonempty α] : krullDim α = ↑(⨆ (a : α), height a) := by
  apply le_antisymm
  · apply iSup_le
    intro p
    suffices p.length ≤ ⨆ (a : α), height a by
      exact (WithBot.unbot'_le_iff fun _ => this).mp this
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
  | inl h => rw [krullDim_eq_bot_of_isEmpty, ciSup_of_empty]
  | inr h => rw [krullDim_eq_iSup_height_of_nonempty, WithBot.coe_iSup (OrderTop.bddAbove _)]

/--
The Krull dimension is the supremum of the elements' coheights.

If `α` is `Nonempty`, then `krullDim_eq_iSup_coheight_of_nonempty`, with the coercion from
`ℕ∞` to `WithBot ℕ∞` outside the supremum, can be more convenient.
-/
lemma krullDim_eq_iSup_coheight : krullDim α = ⨆ (a : α), ↑(coheight a) := by
  cases isEmpty_or_nonempty α with
  | inl h => rw [krullDim_eq_bot_of_isEmpty, ciSup_of_empty]
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

end krullDim

/-!
## Concrete calculations
-/

section calculations

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
      omega

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
      toFun := fun ⟨i, hi⟩ => (p ⟨i+1, by omega⟩).unbot (by
        apply LT.lt.ne_bot (a := p.head)
        apply p.strictMono
        exact compare_gt_iff_gt.mp rfl)
      step := fun i => by simpa [WithBot.unbot_lt_iff] using p.step ⟨i + 1, by omega⟩ }
    have hlast' : p'.last = x := by
      simp only [p', RelSeries.last, Fin.val_last, WithBot.unbot_eq_iff, ← hlast, Fin.last]
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
      step := fun i => by simpa only [WithTop.untop_lt_iff, WithTop.coe_untop] using p.step i }
    have hlast' : p'.last = x := by
      simp only [p', RelSeries.last, Fin.val_last, WithTop.untop_eq_iff, ← hlast]
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
  show (krullDim (WithTop ℕ) = ⊤)
  simp only [krullDim_WithTop, krullDim_nat]
  rfl

@[simp]
lemma height_enat (n : ℕ∞) : height n = n := by
  cases n with
  | top => simp only [← WithBot.coe_eq_coe, height_top_eq_krullDim, krullDim_enat, WithBot.coe_top]
  | coe n => exact (height_coe_withTop _).trans (height_nat _)

@[simp]
lemma coheight_coe_enat (n : ℕ) : coheight (n : ℕ∞) = ⊤ := by
  apply (coheight_coe_withTop _).trans
  simp only [Nat.cast_id, coheight_nat, top_add]

end calculations

end Order
