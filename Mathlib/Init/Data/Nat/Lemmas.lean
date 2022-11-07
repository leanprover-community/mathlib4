/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Std.Data.Nat.Lemmas
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Algebra.Functions

universe u

namespace Nat

/- properties of inequality -/

instance : LinearOrder ℕ where
  le := Nat.le
  le_refl := @Nat.le_refl
  le_trans := @Nat.le_trans
  le_antisymm := @Nat.le_antisymm
  le_total := @Nat.le_total
  lt := Nat.lt
  lt_iff_le_not_le := @Nat.lt_iff_le_not_le
  decidable_lt := inferInstance
  decidable_le := inferInstance
  decidable_eq := inferInstance

/- TODO(Leo): sub + inequalities -/

protected def strong_rec_on {p : ℕ → Sort u}
  (n : ℕ) (H : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
Nat.lt_wfRel.wf.fix' H n

@[elab_as_elim]
protected lemma strong_induction_on {p : Nat → Prop} (n : Nat) (h : ∀ n, (∀ m, m < n → p m) → p n) :
    p n :=
Nat.strong_rec_on n h

protected lemma case_strong_induction_on {p : Nat → Prop} (a : Nat)
  (hz : p 0)
  (hi : ∀ n, (∀ m, m ≤ n → p m) → p (succ n)) : p a :=
Nat.strong_induction_on a $ λ n =>
  match n with
  | 0     => λ _ => hz
  | (n+1) => λ h₁ => hi n (λ _ h₂ => h₁ _ (lt_succ_of_le h₂))

/- mod -/

-- TODO mod_core_congr, mod_def

/- div & mod -/

-- TODO div_core_congr, div_def

/- div -/

def iterate {α : Sort u} (op : α → α) : ℕ → α → α
 | 0,      a => a
 | succ k, a => iterate op k (op a)

notation f "^["n"]" => iterate f n

/- successor and predecessor -/

def discriminate (H1 : n = 0 → α) (H2 : ∀m, n = succ m → α) : α :=
  match n with
  | 0 => H1 rfl
  | succ m => H2 m rfl

lemma one_eq_succ_zero : 1 = succ 0 := rfl

def two_step_induction {P : ℕ → Sort u} (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ), P n → P (succ n) → P (succ (succ n))) : (a : ℕ) → P a
| 0   => H1
| 1   => H2
| _+2 => H3 _ (two_step_induction H1 H2 H3 _) (two_step_induction H1 H2 H3 _)

def sub_induction {P : ℕ → ℕ → Sort u} (H1 : ∀m, P 0 m)
   (H2 : ∀n, P (succ n) 0) (H3 : ∀n m, P n m → P (succ n) (succ m)) : (n m : ℕ) → P n m
| 0,   _   => H1 _
| _+1, 0   => H2 _
| n+1, m+1 => H3 _ _ (sub_induction H1 H2 H3 n m)

protected def lt_ge_by_cases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : b ≤ a → C) : C :=
if h : a < b then h₁ h else h₂ (not_lt.1 h)

protected def lt_by_cases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : a = b → C)
  (h₃ : b < a → C) : C :=
Nat.lt_ge_by_cases h₁ fun h₁ =>
  Nat.lt_ge_by_cases h₃ fun h => h₂ (Nat.le_antisymm h h₁)

/- find -/

section find
variable (p : ℕ → Prop)

private def lbp (m n : ℕ) : Prop := m = n + 1 ∧ ∀ k, k ≤ n → ¬p k

variable [DecidablePred p] (H : ∃ n, p n)

private def wf_lbp : WellFounded (lbp p) := by
  refine ⟨let ⟨n, pn⟩ := H; ?_⟩
  suffices ∀ m k, n ≤ k + m → Acc (lbp p) k from fun a => this _ _ (Nat.le_add_left _ _)
  intro m
  induction m with refine fun k kn => ⟨_, fun | _, ⟨rfl, a⟩ => ?_⟩
  | zero => exact absurd pn (a _ kn)
  | succ m IH => exact IH _ (by rw [Nat.add_right_comm]; exact kn)

protected def find_x : {n // p n ∧ ∀ m, m < n → ¬p m} :=
(wf_lbp p H).fix' (C := fun k => (∀n, n < k → ¬p n) → {n // p n ∧ ∀ m, m < n → ¬p m})
  (fun m IH al => if pm : p m then ⟨m, pm, al⟩ else
      have this : ∀ n, n ≤ m → ¬p n := fun n h =>
        (lt_or_eq_of_le h).elim (al n) fun e => by rw [e]; exact pm
      IH _ ⟨rfl, this⟩ fun n h => this n $ Nat.le_of_succ_le_succ h)
  0 fun n h => absurd h (Nat.not_lt_zero _)

/--
If `p` is a (decidable) predicate on `ℕ` and `hp : ∃ (n : ℕ), p n` is a proof that
there exists some natural number satisfying `p`, then `nat.find hp` is the
smallest natural number satisfying `p`. Note that `nat.find` is protected,
meaning that you can't just write `find`, even if the `nat` namespace is open.

The API for `nat.find` is:

* `nat.find_spec` is the proof that `nat.find hp` satisfies `p`.
* `nat.find_min` is the proof that if `m < nat.find hp` then `m` does not satisfy `p`.
* `nat.find_min'` is the proof that if `m` does satisfy `p` then `nat.find hp ≤ m`.
-/

protected def find : ℕ := (Nat.find_x p H).1

protected lemma find_spec : p (Nat.find p H) := (Nat.find_x p H).2.1

protected lemma find_min : ∀ {m : ℕ}, m < Nat.find p H → ¬p m := @(Nat.find_x p H).2.2

protected lemma find_min' {m : ℕ} (h : p m) : Nat.find p H ≤ m :=
not_lt.1 fun l => Nat.find_min p H l h

end find

-- TODO cont_to_bool_mod_two

lemma to_digits_core_lens_eq_aux (b f : Nat) :
  ∀ (n : Nat) (l1 l2 : List Char), l1.length = l2.length →
    (Nat.toDigitsCore b f n l1).length = (Nat.toDigitsCore b f n l2).length := by
  induction f with
    simp only [Nat.toDigitsCore, List.length] <;> intro n l1 l2 hlen
  | zero => assumption
  | succ f ih =>
    by_cases hx : n / b = 0
    case pos => simp only [hx, if_true, List.length, congrArg (fun l => l + 1) hlen]
    case neg =>
      simp only [hx, if_false]
      specialize ih (n / b) (Nat.digitChar (n % b) :: l1) (Nat.digitChar (n % b) :: l2)
      simp only [List.length, congrArg (fun l => l + 1) hlen] at ih
      exact ih trivial

lemma to_digits_core_lens_eq (b f : Nat) : ∀ (n : Nat) (c : Char) (tl : List Char),
    (Nat.toDigitsCore b f n (c :: tl)).length = (Nat.toDigitsCore b f n tl).length + 1 := by
  induction f with
    intro n c tl <;> simp only [Nat.toDigitsCore, List.length]
  | succ f ih =>
    by_cases hnb : (n / b) = 0
    case pos => simp only [hnb, if_true, List.length]
    case neg =>
      generalize hx: Nat.digitChar (n % b) = x
      simp only [hx, hnb, if_false] at ih
      simp only [hnb, if_false]
      specialize ih (n / b) c (x :: tl)
      rw [← ih]
      have lens_eq : (x :: (c :: tl)).length = (c :: x :: tl).length := by simp
      apply to_digits_core_lens_eq_aux
      exact lens_eq

lemma nat_repr_len_aux (n b e : Nat) (h_b_pos : 0 < b) :  n < b ^ e.succ → n / b < b ^ e := by
  simp only [Nat.pow_succ]
  exact (@Nat.div_lt_iff_lt_mul b n (b ^ e) h_b_pos).mpr

/-- The String representation produced by toDigitsCore has the proper length relative to
the number of digits in `n < e` for some base `b`. Since this works with any base greater
than one, it can be used for binary, decimal, and hex. -/
lemma to_digits_core_length (b : Nat) (h : 2 <= b) (f n e : Nat)
    (hlt : n < b ^ e) (h_e_pos: 0 < e) : (Nat.toDigitsCore b f n []).length <= e := by
  induction f generalizing n e hlt h_e_pos with
    simp only [Nat.toDigitsCore, List.length, Nat.zero_le]
  | succ f ih =>
    cases e with
    | zero => exact False.elim (Nat.lt_irrefl 0 h_e_pos)
    | succ e =>
      by_cases h_pred_pos : 0 < e
      case pos =>
        have _ : 0 < b := Nat.lt_trans (by decide) h
        specialize ih (n / b) e (nat_repr_len_aux n b e ‹0 < b› hlt) h_pred_pos
        by_cases hdiv_ten : n / b = 0
        case pos => simp only [hdiv_ten]; exact Nat.le.step h_pred_pos
        case neg =>
          simp only [hdiv_ten,
            to_digits_core_lens_eq b f (n / b) (Nat.digitChar $ n % b), if_false]
          exact Nat.succ_le_succ ih
      case neg =>
        have _ : e = 0 := Nat.eq_zero_of_nonpos e h_pred_pos
        rw [‹e = 0›]
        have _ : b ^ 1 = b := by simp only [pow_succ, pow_zero, Nat.one_mul]
        have _ : n < b := ‹b ^ 1 = b› ▸ (‹e = 0› ▸ hlt : n < b ^ Nat.succ 0)
        simp only [(@Nat.div_eq_of_lt n b ‹n < b› : n / b = 0), if_true, List.length]

/-- The core implementation of `Nat.repr` returns a String with length less than or equal to the
number of digits in the decimal number (represented by `e`). For example, the decimal string
representation of any number less than 1000 (10 ^ 3) has a length less than or equal to 3. -/
lemma repr_length (n e : Nat) : 0 < e → n < 10 ^ e → (Nat.repr n).length <= e := by
  cases n with
    (intro e0 he; simp only [Nat.repr, Nat.toDigits, String.length, List.asString])
  | zero => assumption
  | succ n =>
    by_cases hterm : n.succ / 10 = 0
    case pos => simp only [hterm, Nat.toDigitsCore]; assumption
    case neg =>
      simp only [hterm]
      exact to_digits_core_length 10 (by decide) (Nat.succ n + 1) (Nat.succ n) e he e0

end Nat
