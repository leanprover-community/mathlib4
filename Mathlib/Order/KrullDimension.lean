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
import Mathlib.Init.Function
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

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

variable (α β : Type _) [Preorder α] [Preorder β]

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
If `a_0 < a_1 < ... < a_n` and `b_0 < b_1 < ... < b_m` are two strict series such that `a_n < b_0`,
then there is a chain of length `n + m + 1` given by
`a_0 < a_1 < ... < a_n < b_0 < b_1 < ... < b_m`.
-/
@[simps]
def append (p q : StrictSeries α) (h : p (Fin.last _) < q 0) : StrictSeries α :=
{ length := p.length + q.length + 1
  toFun := Fin.append p q ∘ Fin.cast (by ring)
  StrictMono := StrictMono.comp (by
    refine Fin.addCases (fun i ↦ Fin.addCases (fun j H ↦ ?_) (fun j _ ↦ ?_))
      (fun i ↦ (Fin.addCases (fun j H ↦ ?_) (fun j H ↦ ?_)))
    . rw [Fin.append_left, Fin.append_left]
      exact p.StrictMono H
    . rw [Fin.append_left, Fin.append_right]
      refine lt_of_lt_of_le (lt_of_le_of_lt (p.StrictMono.monotone ?_) h) (q.StrictMono.monotone ?_)
      . show (i : ℕ) ≤ p.length
        linarith [i.2]
      . norm_num
    . rw [Fin.append_right, Fin.append_left]
      change (p.length + 1 + i : ℕ) < (j : ℕ) at H
      exfalso
      linarith [j.2]
    . rw [Fin.append_right, Fin.append_right]
      refine q.StrictMono (?_ : (i : ℕ) < (j : ℕ))
      change p.length + 1 + ↑i < p.length + 1 + ↑j at H
      linarith ) (OrderIso.strictMono _) }

/--
If `a_0 < a_1 < ... < a_n` is a strict series and `a` is such that `a_i < a < a_{i + 1}`, then
`a_0 < a_1 < ... < a_i < a < a_{i + 1} < ... < a_n` is another strict series
-/
@[simps]
def insert_nth (p : StrictSeries α) (i : Fin p.length) (a : α) (a_lt : p (Fin.castSucc i) < a)
  (lt_a : a < p i.succ) : StrictSeries α :=
{ length := p.length + 1
  toFun :=  (Fin.castSucc i.succ).insertNth a p
  StrictMono := by
    intros m n h
    obtain (hm|rfl|hm) := lt_trichotomy m (Fin.castSucc i.succ)
    . rw [Fin.insertNth_apply_below hm]
      obtain (hn|rfl|hn) := lt_trichotomy n (Fin.castSucc i.succ)
      . rw [Fin.insertNth_apply_below hn]
        simpa only [Fin.coe_castSucc, eq_rec_constant] using p.StrictMono h
      . rw [Fin.insertNth_apply_same]
        simp only [Fin.coe_castSucc, eq_rec_constant]
        refine lt_of_le_of_lt (p.StrictMono.monotone $ Nat.lt_succ_iff.mp ?_) a_lt
        exact h
      . rw [Fin.insertNth_apply_above hn]
        simp only [Fin.coe_castSucc, eq_rec_constant]
        generalize_proofs h1 h2
        refine lt_trans (lt_of_le_of_lt (p.StrictMono.monotone ?_) a_lt)
          (lt_of_lt_of_le lt_a $ p.StrictMono.monotone $ show (i : ℕ) + 1 ≤ (n : ℕ) - 1 from ?_)
        . change (m : ℕ) ≤ _
          change (m : ℕ) < _ at hm
          simp only [Fin.coe_castSucc] at hm ⊢
          linarith [show (m : ℕ) < i + 1 from hm]
        rwa [Nat.succ_le_iff, ←Nat.pred_eq_sub_one, Nat.lt_pred_iff, Nat.succ_eq_add_one]
    . rw [Fin.insertNth_apply_same, Fin.insertNth_apply_above h]
      simp only [Fin.coe_castSucc, eq_rec_constant]
      refine lt_of_lt_of_le lt_a (p.StrictMono.monotone $ show ↑i + 1 ≤ ↑n - 1 from ?_)
      change (_ : ℕ) < _ at h
      simp only [Fin.coe_castSucc, Fin.val_succ] at h
      rwa [Nat.succ_le_iff, ←Nat.pred_eq_sub_one, Nat.lt_pred_iff, Nat.succ_eq_add_one]
    . rw [Fin.insertNth_apply_above hm, Fin.insertNth_apply_above (lt_trans hm h)]
      simp only [Fin.coe_castSucc, eq_rec_constant]
      refine p.StrictMono ?_
      change (_ : ℕ) < _ at hm h ⊢
      simp only [Fin.coe_castSucc, Fin.val_succ, Fin.val_fin_lt, Fin.coe_pred, ge_iff_le] at hm h ⊢
      refine Nat.pred_lt_pred (?_ : (m : ℕ) ≠ 0) h
      linarith }

variable {β}

/--
For two pre-ordered sets `α, β`, if `f : α → β` is strictly monotonic, then a strict series of `α`
can be pushed out to a strict series of `β` by
`a₀ < a₁ < ... < aₙ ↦ f a₀ < f a₁ < ... < f aₙ`
-/
@[simps]
def map (p : StrictSeries α) (f : α → β) (hf : _root_.StrictMono f) : StrictSeries β :=
{ length := p.length
  toFun := f.comp p
  StrictMono := hf.comp p.StrictMono }

/--
For two pre-ordered sets `α, β`, if `f : α → β` is surjective and strictly comonotonic, then a
strict series of `β` can be pulled back to a strict chain of `α` by
`b₀ < b₁ < ... < bₙ ↦ f⁻¹ b₀ < f⁻¹ b₁ < ... < f⁻¹ bₙ` where `f⁻¹ bᵢ` is an arbitrary element in the
preimage of `f⁻¹ {bᵢ}`.
-/
@[simps]
noncomputable def comap (p : StrictSeries β) (f : α → β)
  (hf1 : ∀ ⦃x y⦄, f x < f y → x < y)
  (hf2 : Function.Surjective f) :
  StrictSeries α :=
{ length := p.length
  toFun := fun i ↦ (hf2 (p i)).choose
  StrictMono := fun i j h ↦ hf1 (by simpa only [(hf2 _).choose_spec] using p.StrictMono h) }

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
