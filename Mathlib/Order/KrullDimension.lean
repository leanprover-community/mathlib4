/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangming Li, Joachim Breitner
-/

import Mathlib.Order.RelSeries
import Mathlib.Data.ENat.Lattice

/-!
# Krull dimension of a preordered set and height of an element

If `α` is a preordered set, then `krullDim α : WithBot ℕ∞` is defined to be
`sup {n | a₀ < a₁ < ... < aₙ}`.

In case that `α` is empty, then its Krull dimension is defined to be negative infinity; if the
length of all series `a₀ < a₁ < ... < aₙ` is unbounded, then its Krull dimension is defined to be
positive infinity.

For `a : α`, its height (in ℕ∞) is defined to be `sup {n | a₀ < a₁ < ... < aₙ = a}` while its
coheight is defined to be `sup {n | a = a₀ < a₁ < ... < aₙ}` .

## Main results

* TOOD

* Concrete calculations for the height and Krull dimension in ℕ, ℤ, `WithTop`, `WithBot` and ℕ∞.

## Design notes

Krull dimensions are defined to take value in `WithBot ℕ∞` so that `(-∞) + (+∞)` is
also negative infinity. This is because we want Krull dimensions to be additive with respect
to product of varieties so that `-∞` being the Krull dimension of empty variety is equal to
sum of `-∞` and the Krull dimension of any other varieties.

We could generalize the notion of Krull dimension to an arbitrary binary relation; many results
in this file would generalize as well. But we don't think it would be useful, so we only define
Krull dimension of a preorder.
-/

section in_other_prs -- should be empty when this PR gets submitted

variable {α : Type*}

-- https://github.com/leanprover-community/mathlib4/pull/15344
lemma ENat.iSup_add (ι : Type*) [Nonempty ι] (f : ι → ℕ∞) (n : ℕ∞) :
    (⨆ x, f x) + n = (⨆ x, f x + n) := by
  cases n; simp; next n =>
  apply le_antisymm
  · apply le_iSup_iff.mpr
    intro m hm
    cases m; simp; next m =>
    have hnm : n ≤ m := by
      specialize hm Classical.ofNonempty
      revert hm
      cases f Classical.ofNonempty
      · simp
      · intro h; norm_cast at *; omega
    suffices (⨆ x, f x) ≤ ↑(m - n) by
      revert this
      generalize (⨆ x, f x) = k
      cases k
      · intro h; exfalso
        simp only [top_le_iff, coe_ne_top] at h
      · norm_cast; omega
    apply iSup_le
    intro i
    specialize hm i
    revert hm
    cases f i <;> intro hm
    · exfalso; simp at hm
    · norm_cast at *; omega
  · apply iSup_le
    intro i
    gcongr
    exact le_iSup f i

-- https://github.com/leanprover-community/mathlib4/pull/15386
lemma RelSeries.eraseLast_last_rel_last {r : Rel α α} (p : RelSeries r) (h : 0 < p.length) :
    r p.eraseLast.last p.last := by
  simp only [last, Fin.last, eraseLast_length, eraseLast_toFun]
  convert p.step ⟨p.length -1, by omega⟩
  simp; omega

-- https://github.com/leanprover-community/mathlib4/pull/15555
def LTSeries.iota (n : ℕ) : LTSeries ℕ :=
  { length := n, toFun := fun i => i, step := fun _ => Nat.lt_add_one _ }

@[simp] theorem LTSeries.length_iota (n : ℕ) : (LTSeries.iota n).length = n := rfl

@[simp] theorem LTSeries.head_iota (n : ℕ) : (LTSeries.iota n).head = 0 := rfl

@[simp] theorem LTSeries.last_iota (n : ℕ) : (LTSeries.iota n).last = n := rfl

-- Q: https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/WithTop.2Ecoe_iSup.20or.20WithTop.2Ecoe_ciSup/near/456575712
-- https://github.com/leanprover-community/mathlib4/pull/15560
theorem WithBot.coe_iSup_OrderTop {α : Type*} [Preorder α] {ι : Type*} [Nonempty ι] [SupSet α]
    [OrderTop α] {f : ι → α} : ↑(⨆ i, f i) = (⨆ i, f i : WithBot α) :=
  WithBot.coe_iSup (OrderTop.bddAbove (Set.range f))

end in_other_prs

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
relation series of `α` ordered by `<` and ending with `a`.
-/
noncomputable def height {α : Type*} [Preorder α] (a : α) : ℕ∞ :=
  ⨆ (p : LTSeries α) (_ : p.last = a), p.length

/--
The **coheight** of an element `a` in a preorder `α` is the supremum of the rightmost index of all
relation series of `α` ordered by `<` and beginning with `a`.

The definition of `coheight` is via the `height` in the dual order, in order to easily transfer
theorems between `height` and `coheight`. See `coheight_eq_isup_head` for the definition with a
series ordered by `<` and beginning with `a`.
-/
noncomputable def coheight {α : Type*} [Preorder α] (a : α) : ℕ∞ := height (α := αᵒᵈ) a

end definitions

section height

variable {α β : Type*}

variable [Preorder α] [Preorder β]

/-!
## Height
-/

lemma height_orderDual (x : αᵒᵈ) : height x = coheight (α := α) x := rfl

lemma coheight_orderDual (x : αᵒᵈ) : coheight x = height (α := α) x := rfl

lemma coheight_eq_iSup_head (a : α) :
    coheight a = ⨆ (p : LTSeries α) (_ : p.head = a), (p.length : ℕ∞) := by
  apply Equiv.iSup_congr ⟨RelSeries.reverse, RelSeries.reverse, RelSeries.reverse_reverse,
    RelSeries.reverse_reverse⟩
  simp

lemma height_le_iff (x : α) (n : ℕ∞) :
    height x ≤ n ↔ ∀ (p : LTSeries α), p.last = x → p.length ≤ n := by
  simp [height, iSup_le_iff]

lemma coheight_le_iff (x : α) (n : ℕ∞) :
    coheight x ≤ n ↔ ∀ (p : LTSeries α), p.head = x → p.length ≤ n := by
  simp [coheight_eq_iSup_head, iSup_le_iff]

lemma height_le (x : α) (n : ℕ∞) :
    (∀ (p : LTSeries α), p.last = x → p.length ≤ n) → height x ≤ n :=
  (height_le_iff x n).mpr

lemma coheight_le (x : α) (n : ℕ∞) :
    (∀ (p : LTSeries α), p.head = x → p.length ≤ n) → coheight x ≤ n :=
  (coheight_le_iff x n).mpr

lemma le_height_of_last_le (x : α) (p : LTSeries α) (hlast : p.last ≤ x) :
    p.length ≤ height x := by
  by_cases hlen0 : p.length > 0
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
    apply le_iSup_of_le p'
    apply le_iSup_of_le (by simp [p'])
    exact le_refl _
  · simp_all

lemma le_coheight_of_le_head (x : α) (p : LTSeries α) (hhead : x ≤ p.head) :
    p.length ≤ coheight x :=
  le_height_of_last_le (α := αᵒᵈ) x p.reverse (by simpa)

lemma length_le_height_last (p : LTSeries α) : p.length ≤ height p.last :=
  le_height_of_last_le _ p (le_refl _)

lemma length_le_coheight_last (p : LTSeries α) : p.length ≤ coheight p.head :=
  le_coheight_of_le_head _ p (le_refl _)

lemma index_le_height (p : LTSeries α) (i : Fin (p.length + 1)) : i ≤ height (p i) :=
  length_le_height_last (p.take i)

lemma index_le_coheight (p : LTSeries α) (i : Fin (p.length + 1)) : i.rev ≤ coheight (p i) := by
  simpa using index_le_height (α := αᵒᵈ) p.reverse i.rev

lemma height_eq_index_of_length_eq_last_height (p : LTSeries α) (h : p.length = height p.last) :
    ∀ (i : Fin (p.length + 1)), i = height (p i) := by
  suffices ∀ i, height (p i) ≤ i by
    apply_rules [le_antisymm, index_le_height]
  intro i
  apply height_le
  intro p' hp'
  simp only [Nat.cast_le]
  have hp'' := length_le_height_last <| p'.smash (p.drop i) (by simpa)
  simp [← h] at hp''; clear h
  norm_cast at hp''
  omega

lemma coheight_eq_index_of_length_eq_head_coheight (p : LTSeries α)
    (h : p.length = coheight p.head) :
    ∀ (i : Fin (p.length + 1)), i.rev = coheight (p i) := by
  intro i
  simpa using height_eq_index_of_length_eq_last_height (α := αᵒᵈ) p.reverse (by simpa) i.rev

lemma height_mono : Monotone (α := α) height := by
  intro x y hxy
  apply height_le
  intros p hlast _
  apply le_height_of_last_le y p (hlast ▸ hxy)

lemma coheight_mono : Antitone (α := α) coheight :=
  fun _ _ hxy => height_mono (α := αᵒᵈ) hxy

private lemma height_add_const (a : α) (n : ℕ∞) :
    height a + n = ⨆ (p : LTSeries α ) (_ : p.last = a), p.length + n := by
  have hne : Nonempty { p : LTSeries α // p.last = a } := ⟨RelSeries.singleton _ a, rfl⟩
  rw [height, iSup_subtype', iSup_subtype', ENat.iSup_add]

-- only true for finite height
lemma height_strictMono (x y : α) (hxy : x < y) (hfin : height y < ⊤) :
    height x < height y := by
  have : height x ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt (height_mono (le_of_lt hxy)) hfin)
  rw [← ENat.add_one_le_iff this]
  rw [height_add_const]
  apply iSup₂_le
  intro p hlast
  apply le_iSup₂_of_le (p.snoc y (hlast ▸ hxy)) (by simp) (by simp)

lemma coheight_strictAntitone (x y : α) (hxy : y < x) (hfin : coheight y < ⊤) :
    coheight x < coheight y :=
  height_strictMono (α := αᵒᵈ) x y hxy hfin

lemma height_le_height_of_strictmono (f : α → β) (hf : StrictMono f) (x : α) :
    height x ≤ height (f x) := by
  unfold height
  apply iSup₂_le
  intro p hlast
  apply le_iSup₂_of_le (p.map f hf) (by simp [hlast]) (by simp)

lemma coheight_le_coheight_of_strictmono (f : α → β) (hf : StrictMono f) (x : α) :
    coheight x ≤ coheight (f x) := by
  apply height_le_height_of_strictmono (α := αᵒᵈ)
  exact fun _ _ h ↦ hf h

@[simp]
lemma height_eq_of_orderIso (f : α ≃o β) (x : α) : height (f x) = height x := by
  apply le_antisymm
  · simpa using height_le_height_of_strictmono _ f.symm.strictMono (f x)
  · exact height_le_height_of_strictmono _ f.strictMono x

lemma coheight_eq_of_orderIso (f : α ≃o β) (x : α) : coheight (f x) = coheight x :=
  height_eq_of_orderIso (α := αᵒᵈ) f.dual x

-- TODO: Inline below?
lemma exist_eq_iSup_of_iSup_eq_coe {α : Type*} [Nonempty α] {f : α → ℕ∞} {n : ℕ}
    (h : (⨆ x, f x) = n) : ∃ x, f x = n := by
  have : (⨆ x, f x) < ⊤ := by simp [h]
  have := ENat.sSup_mem_of_Nonempty_of_lt_top this
  obtain ⟨x, hx⟩ := this
  simp only at hx
  use x
  rw [hx]
  exact h

/-- There exist a series ending in a element for any lenght up to the element’s height.  -/
lemma exists_series_of_le_height (a : α) {n : ℕ} (h : n ≤ height a) :
    ∃ p : LTSeries α, p.last = a ∧ p.length = n := by
  have hne : Nonempty { p : LTSeries α // p.last = a } := ⟨RelSeries.singleton _ a, rfl⟩
  cases ha : height a with
  | top =>
    clear h
    rw [height, iSup_subtype', ENat.iSup_coe_eq_top, bddAbove_def] at ha
    push_neg at ha
    contrapose! ha
    use n
    rintro m ⟨⟨p, rfl⟩, hp⟩
    simp at hp
    by_contra! hnm
    apply ha (p.drop ⟨m-n, by omega⟩) (by simp) (by simp; omega)
  | coe m =>
    rw [ha, Nat.cast_le] at h
    rw [height, iSup_subtype'] at ha
    obtain ⟨⟨p,hlast⟩, hlen⟩ := exist_eq_iSup_of_iSup_eq_coe ha
    simp only at hlen
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

/--
The height of an elemnet is infinite if there exist series of arbitrary length ending in that
element.
-/
lemma height_eq_top_iff (x : α) :
    height x = ⊤ ↔ (∀ n, ∃ p : LTSeries α, p.last = x ∧ p.length = n) := by
  constructor
  · intro h n
    apply exists_series_of_le_height x (n := n)
    simp [h]
  · intro h
    rw [height, iSup_subtype', ENat.iSup_coe_eq_top, bddAbove_def]
    push_neg
    intro n
    obtain ⟨p, hlast, hp⟩ := h (n+1)
    exact ⟨p.length, ⟨⟨⟨p, hlast⟩, by simp [hp]⟩, by simp [hp]⟩⟩

/--
The coheight of an elemnet is infinite if there exist series of arbitrary length ending in that
element.
-/
lemma coheight_eq_top_iff (x : α) :
    coheight x = ⊤ ↔ (∀ n, ∃ p : LTSeries α, p.head = x ∧ p.length = n) := by
  convert height_eq_top_iff (α := αᵒᵈ) x using 2 with n
  exact ⟨fun ⟨p, hp, hl⟩ => ⟨p.reverse, by simpa, by simpa⟩,
         fun ⟨p, hp, hl⟩ => ⟨p.reverse, by simpa, by simpa⟩⟩

/-- Another characterization of height, based on the supremum of the heights of elements below. -/
lemma height_eq_isup_lt_height (x : α) :
    height x = ⨆ (y : α) (_  : y < x), height y + 1 := by
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
lemma coheight_eq_isup_lt_height (x : α) :
    coheight x = ⨆ (y : α) (_  : x < y), coheight y + 1 :=
  height_eq_isup_lt_height (α := αᵒᵈ) x

lemma height_le_coe_iff (x : α) (n : ℕ) :
    height x ≤ n ↔ (∀ y, y < x → height y < n) := by
  conv_lhs => rw [height_eq_isup_lt_height, iSup₂_le_iff]
  congr! 2 with y _
  cases height y
  · simp
  · norm_cast

lemma coheight_le_coe_iff (x : α) (n : ℕ) :
    coheight x ≤ n ↔ (∀ y, x < y → coheight y < n) :=
  height_le_coe_iff (α := αᵒᵈ) x n

lemma height_eq_zero_iff (x : α) : height x = 0 ↔ (∀ y, ¬(y < x)) := by
  simpa using height_le_coe_iff x 0

lemma coheight_eq_zero_iff (x : α) : coheight x = 0 ↔ (∀ y, ¬(x < y)) :=
  height_eq_zero_iff (α := αᵒᵈ) x

@[simp] lemma height_bot (α : Type*) [Preorder α] [OrderBot α] : height (⊥ : α) = 0 := by
  simp [height_eq_zero_iff]

@[simp] lemma coheight_top (α : Type*) [Preorder α] [OrderTop α] : coheight (⊤ : α) = 0 := by
  simp [coheight_eq_zero_iff]

lemma coe_lt_height_iff (x : α) (n : ℕ) (hfin : height x < ⊤):
    n < height x ↔ (∃ y, y < x ∧ height y = n) := by
  constructor
  · intro h
    obtain ⟨m, hx : height x = m⟩ := Option.ne_none_iff_exists'.mp (LT.lt.ne_top hfin)
    rw [hx] at h; norm_num at h
    obtain ⟨p, hp, hlen⟩ := exists_series_of_height_eq_coe x hx
    use p ⟨n, by omega⟩
    constructor
    · rw [← hp]
      apply LTSeries.strictMono
      simp [Fin.last]; omega
    · symm
      exact height_eq_index_of_length_eq_last_height p (by simp [hlen, hp, hx]) ⟨n, by omega⟩
  · intro ⟨y, hyx, hy⟩
    exact hy ▸ height_strictMono y x hyx hfin

lemma coe_lt_coheight_iff (x : α) (n : ℕ) (hfin : coheight x < ⊤):
    n < coheight x ↔ (∃ y, x < y ∧ coheight y = n) :=
  coe_lt_height_iff (α := αᵒᵈ) x n hfin

lemma height_eq_coe_add_one_iff (x : α) (n : ℕ)  : height x = n + 1 ↔
    height x < ⊤ ∧ (∃ y < x, height y = n) ∧ (∀ y, y < x → height y ≤ n) := by
  wlog hfin : height x < ⊤
  · simp_all
    exact ne_of_beq_false rfl
  simp only [hfin, true_and]
  trans n < height x ∧ height x ≤ n + 1
  · rw [le_antisymm_iff, and_comm]
    simp [hfin, ENat.lt_add_one_iff, ENat.add_one_le_iff]
  · congr! 1
    · exact coe_lt_height_iff x n hfin
    · simpa [hfin, ENat.lt_add_one_iff] using height_le_coe_iff x (n+1)

lemma coheight_eq_coe_add_one_iff (x : α) (n : ℕ) : coheight x = n + 1 ↔
    coheight x < ⊤ ∧ (∃ y > x, coheight y = n) ∧ (∀ y, x < y → coheight y ≤ n) :=
  height_eq_coe_add_one_iff (α := αᵒᵈ) x n

lemma height_eq_coe_iff (x : α) (n : ℕ) : height x = n ↔
    height x < ⊤ ∧ (n = 0 ∨ ∃ y < x, height y = n - 1) ∧ (∀ y, y < x → height y < n) := by
  wlog hfin : height x < ⊤
  · simp_all
  simp only [hfin, true_and]
  cases n
  case zero => simp_all [height_eq_zero_iff x]
  case succ n =>
    simp only [Nat.cast_add, Nat.cast_one, add_eq_zero, one_ne_zero, and_false, false_or]
    rw [height_eq_coe_add_one_iff x n]
    simp only [hfin, true_and]
    congr! 3
    rename_i y _
    cases height y <;> simp; norm_cast; omega

lemma coheight_eq_coe_iff (x : α) (n : ℕ) : coheight x = n ↔
    coheight x < ⊤ ∧ (n = 0 ∨ ∃ y > x, coheight y = n - 1) ∧ (∀ y, y > x → coheight y < n) :=
  height_eq_coe_iff (α := αᵒᵈ) x n

/-- The elements of height zero are the minimal elements. -/
lemma isMin_iff_height_eq_zero (a : α) :
    IsMin a ↔ height a = 0 := by
  simp [isMin_iff_forall_not_lt, height_eq_zero_iff]

lemma isMax_iff_coheight_eq_zero (a : α) :
    IsMax a ↔ coheight a = 0 :=
  isMin_iff_height_eq_zero (α := αᵒᵈ) a

/-- The elements of height `n` are the minimial elements among those of height `≥ n`. -/
lemma minimal_le_height_iff_height (a : α) (n : ℕ) :
    Minimal (fun y => n ≤ height y) a ↔ height a = n := by -- TODO: swap statement
  by_cases hfin : height a < ⊤
  · simp only [minimal_iff_forall_lt, not_le, height_eq_coe_iff, hfin, true_and, and_congr_left_iff]
    intro _
    cases n
    case pos.zero => simp
    case pos.succ _ =>
      simp only [Nat.cast_add, Nat.cast_one, add_eq_zero, one_ne_zero, and_false, false_or]
      simp only [ne_eq, ENat.coe_ne_top, not_false_eq_true, ENat.add_one_le_iff]
      simp only [coe_lt_height_iff, hfin]
      rfl
  · suffices ∃ x, ∃ (_ : x < a), ↑n ≤ height x by
      simp only [not_lt, top_le_iff] at hfin
      simpa only [minimal_iff_forall_lt, Set.mem_setOf_eq, hfin, le_top, not_le,
        true_and, ENat.top_ne_coe, iff_false, not_forall, Classical.not_imp, not_lt]
    simp only [not_lt, top_le_iff, height_eq_top_iff] at hfin
    obtain ⟨p, rfl, hp⟩ := hfin (n+1)
    use p.eraseLast.last, RelSeries.eraseLast_last_rel_last _ (by omega)
    simpa [hp] using length_le_height_last p.eraseLast

/-- The elements of coheight `n` are the maximal elements among those of coheight `≥ n`. -/
lemma maximal_le_coheight_iff_coheight (a : α) (n : ℕ) :
    Maximal (fun y => n ≤ coheight y) a ↔ coheight a = n :=
  minimal_le_height_iff_height (α := αᵒᵈ) a n

end height

section krullDim

/-!
## Krull dimension
-/

variable {α β : Type*}

variable [Preorder α] [Preorder β]

lemma krullDim_nonneg_of_nonempty [Nonempty α] : 0 ≤ krullDim α :=
  le_sSup ⟨⟨0, fun _ ↦ @Nonempty.some α inferInstance, fun f ↦ f.elim0⟩, rfl⟩

/-- A definition of krullDim for nonempty `α` that avoids `WithBot` -/
lemma krullDim_eq_of_nonempty [Nonempty α] :
    krullDim α = ⨆ (p : LTSeries α), (p.length : ℕ∞) := by
  unfold krullDim
  rw [WithBot.coe_iSup_OrderTop]
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

/--
The Krull dimension is the supremum of the element's heights.

If `α` is `Nonempty`, then `krullDim_eq_iSup_height_of_nonempty`, with the coercion from
`ℕ∞` to `WithBot ℕ∞` outside the supremum, can be more convenient.
-/
lemma krullDim_eq_iSup_height : krullDim α = ⨆ (a : α), (height a : WithBot ℕ∞) := by
  cases isEmpty_or_nonempty α with
  | inl h => simp [krullDim_eq_bot_of_isEmpty]
  | inr h =>
    rw [← WithBot.coe_iSup_OrderTop]
    apply le_antisymm
    · apply iSup_le
      intro p
      suffices p.length ≤ ⨆ (a : α), height a by
        exact (WithBot.unbot'_le_iff fun _ => this).mp this
      apply le_iSup_of_le p.last (length_le_height_last p)
    · rw [krullDim_eq_of_nonempty]
      simp only [WithBot.coe_le_coe, iSup_le_iff]
      intro x
      exact height_le _ _ (fun p _ ↦ le_iSup_of_le p (le_refl _))

/--
The Krull dimension is the supremum of the element's coheights.

If `α` is `Nonempty`, then `krullDim_eq_iSup_coheight_of_nonempty`, with the coercion from
`ℕ∞` to `WithBot ℕ∞` outside the supremum, can be more convenient.
-/
lemma krullDim_eq_iSup_coheight : krullDim α = ⨆ (a : α), (coheight a : WithBot ℕ∞) := by
  rw [← krullDim_orderDual]
  exact krullDim_eq_iSup_height (α := αᵒᵈ)

/--
The Krull dimension is the supremum of the element's heights. Variant of `krullDim_eq_iSup_height`.
-/
lemma krullDim_eq_iSup_height_of_nonempty [Nonempty α] : krullDim α = ⨆ (a : α), height a := by
  rw [krullDim_eq_iSup_height, WithBot.coe_iSup_OrderTop]

/--
The Krull dimension is the supremum of the element's coheights.
Variant of `krullDim_eq_iSup_coheight`.
-/
lemma krullDim_eq_iSup_coheight_of_nonempty [Nonempty α] : krullDim α = ⨆ (a : α), coheight a := by
  rw [← krullDim_orderDual]
  exact krullDim_eq_iSup_height_of_nonempty (α := αᵒᵈ)

@[simp] -- not as useful as it looks, due to the coe on the left
lemma height_top_eq_krullDim [OrderTop α] : height (⊤ : α) = krullDim α := by
  rw [krullDim_eq_of_nonempty]
  simp only [WithBot.coe_inj]
  apply le_antisymm
  · exact height_le _ _ (fun p _ ↦ le_iSup_of_le p (le_refl _))
  · exact iSup_le (fun p => le_height_of_last_le ⊤ p le_top)

@[simp] -- not as useful as it looks, due to the coe on the left
lemma coheight_bot_eq_krullDim [OrderBot α] : coheight (⊥ : α) = krullDim α := by
  rw [← krullDim_orderDual]
  exact height_top_eq_krullDim (α := αᵒᵈ)

end krullDim

section calculations

variable {α : Type*} [Preorder α]

/-!
## Concrete calculations
-/


@[simp] lemma height_nat (n : ℕ) : height n = n := by
  induction n using Nat.strongInductionOn with | ind n ih =>
  apply le_antisymm
  · apply (height_le_coe_iff ..).mpr
    simp (config := { contextual := true }) only [ih, Nat.cast_lt, implies_true]
  · exact length_le_height_last (.iota n)

@[simp] lemma coheight_nat (n : ℕ) : coheight n = ⊤ := by
  rw [coheight_eq_top_iff]
  intro m
  use ((LTSeries.iota m).map (· + n) (StrictMono.add_const (fun _ _ x ↦ x) n))
  simp

@[simp]
lemma krullDim_nat : krullDim ℕ = ⊤ := by
  simp only [krullDim_eq_iSup_height, height_nat]
  rw [← WithBot.coe_iSup_OrderTop]
  simp only [WithBot.coe_eq_top]
  show (⨆ (i : ℕ), ↑i = (⊤ : ℕ∞)) -- nothing simpler from here on?
  rw [iSup_eq_top]
  intro n hn
  cases n with
  | top => contradiction
  | coe n =>
    use (n+1)
    norm_cast
    simp

@[simp] lemma height_int (a : ℤ) : height a = ⊤ := by
  rw [height_eq_top_iff]
  intro n
  use (LTSeries.iota n).map (a - (n : ℤ) + ·)
    (StrictMono.const_add Int.natCast_strictMono (a - (n : ℤ)))
  simp

@[simp] lemma coheight_int (a : ℤ) : coheight a = ⊤ := by
  rw [coheight_eq_top_iff]
  intro n
  use (LTSeries.iota n).map (fun i => a + (i : ℤ)) (StrictMono.const_add Int.natCast_strictMono a)
  simp

@[simp]
lemma height_coe_WithBot (x : α) : height (x : WithBot α) = height x + 1 := by
  apply le_antisymm
  · apply height_le
    intro p hlast
    wlog hlenpos : p.length > 0
    · simp_all
    let p' : LTSeries α := {
      length := p.length - 1
      toFun := fun ⟨i, hi⟩ => (p ⟨i+1, by omega⟩).unbot (by
        apply LT.lt.ne_bot (a := p.head)
        apply p.strictMono
        exact compare_gt_iff_gt.mp rfl)
      step := by
        intro ⟨i, hi⟩
        simp only [Fin.castSucc_mk, Nat.succ_eq_add_one, Fin.succ_mk, WithBot.unbot_lt_iff,
          WithBot.coe_unbot, gt_iff_lt]
        exact p.step ⟨i + 1, by omega⟩
      }
    have hlast' : p'.last = x := by
      simp only [RelSeries.last, Fin.val_last, WithBot.unbot_eq_iff, ← hlast]
      congr; omega
    suffices p'.length ≤ height p'.last by
      rw [hlast'] at this
      simpa [p'] using this
    apply length_le_height_last
  · rw [height_add_const]
    apply iSup₂_le
    intro p hlast
    let p' := (p.map _ WithBot.coe_strictMono).cons ⊥ (by simp)
    apply le_iSup₂_of_le p' (by simp [p', hlast]) (by simp [p'])

@[simp]
lemma coheight_coe_WithTop (x : α) : coheight (x : WithTop α) = coheight x + 1 :=
  height_coe_WithBot (α := αᵒᵈ) x

@[simp]
lemma height_coe_WithTop (x : α) : height (x : WithTop α) = height x := by
  apply le_antisymm
  · apply height_le
    intro p hlast
    let p' : LTSeries α := {
      length := p.length
      toFun := fun i => (p i).untop (by
        apply WithTop.lt_top_iff_ne_top.mp
        apply lt_of_le_of_lt
        · exact p.monotone (Fin.le_last _)
        · rw [RelSeries.last] at hlast
          simp [hlast])
      step := by
        intro i
        simp only [WithTop.untop_lt_iff, WithTop.coe_untop]
        exact p.step i
      }
    have hlast' : p'.last = x := by
      simp only [RelSeries.last, Fin.val_last, WithTop.untop_eq_iff, ← hlast]
    suffices p'.length ≤ height p'.last by
      rw [hlast'] at this
      simpa [p'] using this
    apply length_le_height_last
  · apply height_le
    intro p hlast
    let p' := p.map _ WithTop.coe_strictMono
    apply le_iSup₂_of_le p' (by simp [p', hlast]) (by simp [p'])

@[simp]
lemma coheight_coe_WithBot (x : α) : coheight (x : WithBot α) = coheight x :=
  height_coe_WithTop (α := αᵒᵈ) x

@[simp]
lemma krullDim_WithTop [Nonempty α] : krullDim (WithTop α) = krullDim α + 1 := by
  rw [← height_top_eq_krullDim]
  rw [krullDim_eq_iSup_height_of_nonempty]
  norm_cast
  rw [ENat.iSup_add]
  rw [height_eq_isup_lt_height]
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro h
    cases x with
    | top => simp at h
    | coe x =>
      simp only [height_coe_WithTop]
      exact le_iSup_of_le x (le_refl _)
  · apply iSup_le
    intro x
    apply le_iSup_of_le (↑x)
    apply le_iSup_of_le (WithTop.coe_lt_top x)
    simp only [height_coe_WithTop, le_refl]

@[simp]
lemma krullDim_WithBot [Nonempty α] : krullDim (WithBot α) = krullDim α + 1 := by
  conv_lhs => rw [← krullDim_orderDual]
  conv_rhs => rw [← krullDim_orderDual]
  exact krullDim_WithTop (α := αᵒᵈ)

@[simp]
lemma krullDim_ENat : krullDim ℕ∞ = ⊤ := by
  show (krullDim (WithTop ℕ) = ↑⊤)
  simp only [krullDim_WithTop, krullDim_nat]
  rfl

@[simp]
lemma height_ENat (n : ℕ∞) : height n = n := by
  cases n with
  | top => simp only [← WithBot.coe_eq_coe, height_top_eq_krullDim, krullDim_ENat, WithBot.coe_top]
  | coe n => exact (height_coe_WithTop _).trans (height_nat _)

@[simp]
lemma coheight_coe_ENat (n : ℕ) : coheight (n : ℕ∞) = ⊤ := by
  apply (coheight_coe_WithTop _).trans
  simp

end calculations
