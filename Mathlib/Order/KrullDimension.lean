/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Fangmin Li
-/

import Mathlib.Order.Monotone.Basic
import Mathlib.Order.CompleteLattice
import Mathlib.Order.WithBot
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Logic.Equiv.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Conv

/-!
# Krull dimension of a preordered set

If `α` is a preordered set, then `krullDim α` is defined to be `sup {n | a₀ < a₁ < ... < aₙ}`.
In case that `α` is empty, then its Krull dimension is defined to be negative infinity; if the
length of all series `a₀ < a₁ < ... < aₙ` is unbounded, then its Krull dimension is defined to
be positive infinity.

For `a : α`, its height is defined to be the krull dimension of the subset `(-∞, a]` while its
coheight is defined to be the krull dimension of `[a, +∞)`.

## Implementation notes
Krull dimensions are defined to take value in `WithBot (WithTop ℕ)` so that `(-∞) + (+∞)` is
also negative infinity. This is because we want Krull dimensions to be additive with respect
to product of varieties so that `-∞` being the Krull dimension of empty variety is equal to
sum of `-∞` and the Krull dimension of any other varieties.
-/

variable (α : Type _) [Preorder α]

/--
For a preordered set `(α, <)`, a strict series of `α` of length `n` is a strictly monotonic function
`fin (n + 1) → α`, i.e. `a₀ < a₁ < ... < aₙ` with `aᵢ : α`.
-/
structure StrictSeries where
/-- the number of inequalities in the series -/
length : ℕ
/-- the underlying function of a strict series -/
toFun : Fin (length + 1) → α
/-- the underlying function should be strictly monotonic -/
StrictMono : StrictMono toFun

namespace StrictSeries

instance : CoeFun (StrictSeries α) (fun x ↦ Fin (x.length + 1) → α) :=
{ coe := StrictSeries.toFun }

instance : Preorder (StrictSeries α) :=
Preorder.lift StrictSeries.length

variable {α}

lemma le_def (x y : StrictSeries α) : x ≤ y ↔ x.length ≤ y.length :=
Iff.rfl

lemma lt_def (x y : StrictSeries α) : x < y ↔ x.length < y.length :=
Iff.rfl

/--
In a preordered set `α`, each term of `α` gives a strict series with the right most index to be 0.
-/
@[simps!] def singleton (a : α) : StrictSeries α :=
{ length := 0
  toFun := fun _ ↦ a
  StrictMono := fun _ _ h ↦ (ne_of_lt h $ @Subsingleton.elim _ subsingleton_fin_one _ _).elim }

instance [IsEmpty α] : IsEmpty (StrictSeries α) :=
{ false := fun x ↦ IsEmpty.false (x 0) }

instance [Inhabited α] : Inhabited (StrictSeries α) :=
{ default := singleton default }

instance [Nonempty α] : Nonempty (StrictSeries α) :=
Nonempty.map singleton inferInstance

lemma top_len_unique [OrderTop (StrictSeries α)] (p : StrictSeries α) (hp : IsTop p) :
  p.length = (⊤ : StrictSeries α).length :=
le_antisymm (@le_top (StrictSeries α) _ _ _) (hp ⊤)

lemma top_len_unique' (H1 H2 : OrderTop (StrictSeries α)) : H1.top.length = H2.top.length :=
le_antisymm (H2.le_top H1.top) (H1.le_top H2.top)

/--
A strict series `a_0 < a_1 < ... < a_n` in `α` gives a strict series in `αᵒᵈ` by reversing the
series `a_n < a_{n - 1} < ... < a_1 < a_0`.
-/
def reverse (p : StrictSeries α) : StrictSeries αᵒᵈ :=
{ length := p.length
  toFun := p ∘ (Sub.sub ⟨p.length, lt_add_one _⟩)
  StrictMono := by
    intros i j h
    refine p.StrictMono (?_ : (_ % _ : ℕ) < _ % _)
    dsimp only
    rw [←Nat.add_sub_assoc, add_comm, Nat.add_sub_assoc, Nat.add_mod_left (p.length + 1),
      ←Nat.add_sub_assoc, add_comm p.length (p.length + 1), Nat.add_sub_assoc,
      Nat.add_mod_left (p.length + 1), Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
    . exact Nat.sub_lt_sub_left (lt_of_lt_of_le h (Nat.lt_succ_iff.mp j.2)) h
    . exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_add_one _)
    . exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_add_one _)
    . exact Nat.lt_succ_iff.mp i.2
    . exact le_of_lt i.2
    . exact Nat.lt_succ_iff.mp j.2
    . exact le_of_lt j.2 }

/--
given a series `a_0 < a_1 < ... < a_n` and an `a` that is smaller than `a_0`, there is a series of
length `n+1`: `a < a_0 < a_1 < ... < a_n`.
-/
@[simps]
def cons (p : StrictSeries α) (a : α) (h : a < p 0) : StrictSeries α :=
{ length := p.length + 1
  toFun := Fin.cons a p
  StrictMono := fun i ↦ Fin.cases (fun j ↦ Fin.cases (fun r ↦ (lt_irrefl _ r).elim)
    (fun k _ ↦ by
      rw [Fin.cons_zero, Fin.cons_succ]
      exact lt_of_lt_of_le h (p.StrictMono.monotone $ by norm_num)) j)
    (fun i' j ↦ Fin.cases (fun r ↦ (not_lt_of_lt r (Fin.succ_pos i')).elim)
    (fun k hk ↦ by
      rw [Fin.cons_succ, Fin.cons_succ]
      exact p.StrictMono (Fin.succ_lt_succ_iff.mp hk)) j) i }

lemma cons_zero (p : StrictSeries α) (a : α) (h : a < p 0) : p.cons a h 0 = a :=
by simp only [cons_toFun, Fin.cons_zero]

lemma cons_succ (p : StrictSeries α) (a : α) (h : a < p 0) (x) :
  p.cons a h x.succ = p x :=
by simp only [cons_toFun, Fin.cons_succ]

/--
given a series `a_0 < a_1 < ... < a_n` and an `a` that is greater than `a_n`, there is a series of
length `n+1`: `a_0 < a_1 < ... < a_n < a`.
-/
@[simps]
def snoc (p : StrictSeries α) (a : α) (h : p (Fin.last _) < a) : StrictSeries α :=
{ length := p.length + 1
  toFun := Fin.snoc p a
  StrictMono := by
    intros i j H
    rw [Fin.snoc, Fin.snoc]
    by_cases h1 : (j : ℕ) < p.length + 1
    . rw [dif_pos h1, dif_pos]
      . exact p.StrictMono H
      . exact lt_trans H h1
    . rw [dif_neg h1, cast_eq]
      split_ifs with h2
      . rw [cast_eq]
        refine lt_of_le_of_lt (p.StrictMono.monotone (?_ : (i : ℕ) ≤ _)) h
        linarith
      . change i.1 < j.1 at H
        push_neg at h2 h1
        refine (ne_of_lt H ?_).elim
        rw [show i.1 = p.length + 1 from _, show j.1 = p.length + 1 from _]
        . linarith [j.2]
        . linarith [i.2] }

lemma snoc_last (p : StrictSeries α) (a : α) (h : p (Fin.last _) < a) :
  p.snoc a h (Fin.last _) = a :=
by simp

/--
If a series `a_0 < a_1 < ...` has positive length, then `a_1 < ...` is another series
-/
@[simps]
def tail (p : StrictSeries α) (h : p.length ≠ 0) : StrictSeries α :=
{ length := p.length.pred,
  toFun := fun j ↦ p ⟨j + 1, Nat.succ_lt_succ (by
    have hj := j.2
    conv_rhs at hj =>
      rw [← Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h)]
    exact hj)⟩
  StrictMono := fun _ _ H ↦ p.StrictMono (Nat.succ_lt_succ H) }

lemma tail_zero (p : StrictSeries α) (h : p.length ≠ 0) : p.tail h 0 = p 1 := by
  rw [tail_toFun]
  congr
  change (0 : ℕ) % (p.length.pred + 1) + 1 = 1 % (p.length + 1)
  rw [Nat.zero_mod, zero_add, Nat.mod_eq_of_lt]
  rw [lt_add_iff_pos_left]
  exact Nat.pos_of_ne_zero h

end StrictSeries

/--
Krull dimension of a preordered set `α` is the supremum of the right most index of all strict
series of `α`. If there is no strict series `a₀ < a₁ < ... < aₙ` in `α`, then its Krull dimension
is defined to be negative infinity; if the length of `a₀ < a₁ < ... < aₙ` is unbounded, its Krull
dimension is defined to be positive infinity.
-/
noncomputable def krullDim : WithBot (WithTop ℕ) :=
⨆ (p : StrictSeries α), p.length

/--
Height of an element `a` of a preordered set `α` is the Krull dimension of the subset `(-∞, a]`
-/
noncomputable def height (a : α) : WithBot (WithTop ℕ) := krullDim (Set.Iic a)

/--
Coheight of an element `a` of a pre-ordered set `α` is the Krull dimension of the subset `[a, +∞)`
-/
noncomputable def coheight (a : α) : WithBot (WithTop ℕ) := krullDim (Set.Ici a)
