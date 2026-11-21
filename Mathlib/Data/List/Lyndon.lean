/-
Copyright (c) 2026 Nikolay Murzin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolay Murzin
-/
module

public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.PeriodicityLemma

/-!
# Lyndon words

A *Lyndon word* over a linearly ordered alphabet is a nonempty word that is strictly smaller, in
the lexicographic order, than each of its proper nonempty suffixes.

## Main declarations

* `List.IsLyndon w`: the list `w` is a Lyndon word.
* `List.IsLyndon.not_hasPeriod`: a Lyndon word has no period `p` with `0 < p < w.length`, that is,
  it is unbordered.
* `List.IsLyndon.append`: if `u` and `v` are Lyndon words with `u < v`, then `u ++ v` is a Lyndon
  word.

## References

* M. Lothaire, *Combinatorics on Words*, Cambridge University Press (1997), Chapter 5.
* K. T. Chen, R. H. Fox, R. C. Lyndon, *Free differential calculus IV. The quotient groups of the
  lower central series*, Ann. of Math. 68 (1958) 81–95.
-/

@[expose] public section

namespace List

variable {α : Type*}

/-- If `Lex r u s` holds and `u` is not a prefix of `s`, the comparison is decided before `u` ends,
so it survives appending anything to both lists. -/
theorem Lex.append_of_not_isPrefix {r : α → α → Prop} {u s : List α} (h : Lex r u s)
    (hp : ¬ u <+: s) (v w : List α) : Lex r (u ++ v) (s ++ w) := by
  induction h with
  | nil => exact absurd nil_prefix hp
  | rel hab => exact Lex.rel hab
  | cons _ ih => exact Lex.cons (ih fun h' => hp (cons_prefix_cons.2 ⟨rfl, h'⟩))

variable [LinearOrder α]

/-- A list is smaller than each of its proper extensions. -/
theorem lt_append_of_ne_nil : ∀ (u : List α) {t : List α}, t ≠ [] → u < u ++ t
  | [], t, ht => by
    obtain ⟨a, t', rfl⟩ := exists_cons_of_ne_nil ht
    exact Lex.nil
  | _ :: u, _, ht => Lex.cons (lt_append_of_ne_nil u ht)

/-- A *Lyndon word* is a nonempty list that is strictly smaller, in the lexicographic order, than
each of its proper nonempty suffixes. -/
def IsLyndon (w : List α) : Prop :=
  w ≠ [] ∧ ∀ i, 0 < i → i < w.length → w < w.drop i

namespace IsLyndon

variable {u v w : List α}

theorem ne_nil (h : w.IsLyndon) : w ≠ [] := h.1

theorem lt_drop (h : w.IsLyndon) {i : ℕ} (hi : 0 < i) (hiw : i < w.length) : w < w.drop i :=
  h.2 i hi hiw

theorem singleton (a : α) : [a].IsLyndon :=
  ⟨cons_ne_nil a [], fun i hi hi' => by simp at hi'; omega⟩

/-- A Lyndon word has no period strictly between `0` and its length: it is unbordered. -/
theorem not_hasPeriod (h : w.IsLyndon) {p : ℕ} (hp : 0 < p) (hpw : p < w.length) :
    ¬ w.HasPeriod p := by
  intro hper
  obtain ⟨t, ht⟩ := hper.drop_prefix p
  have ht0 : t ≠ [] := by
    rintro rfl
    have := congrArg length ht
    simp at this
    omega
  have h2 : w.drop p < w := by
    conv_rhs => rw [← ht]
    exact lt_append_of_ne_nil _ ht0
  exact lt_asymm (h.lt_drop hp hpw) h2

/-- The concatenation `u ++ v` of Lyndon words `u < v` is a Lyndon word. -/
theorem append (hu : u.IsLyndon) (hv : v.IsLyndon) (huv : u < v) : (u ++ v).IsLyndon := by
  have hu0 : 0 < u.length := length_pos_iff.2 hu.ne_nil
  have key : u ++ v < v := by
    by_cases hp : u <+: v
    · obtain ⟨v', rfl⟩ := hp
      have hv' : v' ≠ [] := by
        rintro rfl
        simp at huv
      have := hv.lt_drop hu0 (by simpa using length_pos_iff.2 hv')
      rw [drop_left] at this
      exact append_left_lt this
    · simpa using Lex.append_of_not_isPrefix huv hp v []
  refine ⟨by simp [hu.ne_nil], fun i hi0 hi => ?_⟩
  rcases lt_trichotomy i u.length with h | rfl | h
  · rw [drop_append_of_le_length h.le]
    have hnp : ¬ u <+: u.drop i := fun hp => by
      have := hp.length_le
      simp at this
      omega
    exact Lex.append_of_not_isPrefix (hu.lt_drop hi0 h) hnp v v
  · rwa [drop_left]
  · have hd : (u ++ v).drop i = v.drop (i - u.length) := by
      rw [show i = u.length + (i - u.length) by omega, drop_append]
      simp
    rw [hd]
    simp at hi
    exact lt_trans key (hv.lt_drop (by omega) (by omega))

end IsLyndon

end List
