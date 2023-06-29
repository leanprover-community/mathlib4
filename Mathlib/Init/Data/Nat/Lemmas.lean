/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Std.Data.Nat.Lemmas
import Mathlib.Init.ZeroOne
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Algebra.Functions

universe u

namespace Nat

/- multiplication -/

theorem eq_zero_of_mul_eq_zero : ∀ {n m : ℕ}, n * m = 0 → n = 0 ∨ m = 0
  | 0,        m => fun _ => Or.inl rfl
  | (succ n), m => by
      rw [succ_mul]
      intro h
      exact Or.inr (Nat.eq_zero_of_add_eq_zero_left h)

/- properties of inequality -/

instance linearOrder : LinearOrder ℕ where
  le := Nat.le
  le_refl := @Nat.le_refl
  le_trans := @Nat.le_trans
  le_antisymm := @Nat.le_antisymm
  le_total := @Nat.le_total
  lt := Nat.lt
  lt_iff_le_not_le := @Nat.lt_iff_le_not_le
  decidableLT := inferInstance
  decidableLE := inferInstance
  decidableEq := inferInstance

/- TODO(Leo): sub + inequalities -/

protected def strong_rec_on {p : ℕ → Sort u}
  (n : ℕ) (H : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
Nat.lt_wfRel.wf.fix H n

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

-- TODO mod_core_congr

#align nat.mod_def Nat.mod_eq

/- div & mod -/

-- TODO div_core_congr

#align nat.div_def Nat.div_eq

/- div -/

def iterate {α : Sort u} (op : α → α) : ℕ → α → α
 | 0,      a => a
 | succ k, a => iterate op k (op a)

notation:max f "^["n"]" => iterate f n

/-! bit0/bit1 properties -/
section bit
set_option linter.deprecated false

protected theorem bit1_eq_succ_bit0 (n : ℕ) : bit1 n = succ (bit0 n) :=
  rfl
#align nat.bit1_eq_succ_bit0 Nat.bit1_eq_succ_bit0

protected theorem bit1_succ_eq (n : ℕ) : bit1 (succ n) = succ (succ (bit1 n)) :=
  Eq.trans (Nat.bit1_eq_succ_bit0 (succ n)) (congr_arg succ (Nat.bit0_succ_eq n))
#align nat.bit1_succ_eq Nat.bit1_succ_eq

protected theorem bit1_ne_one : ∀ {n : ℕ}, n ≠ 0 → bit1 n ≠ 1
  | 0, h, _ => absurd rfl h
  | _ + 1, _, h1 => Nat.noConfusion h1 fun h2 => absurd h2 (succ_ne_zero _)
#align nat.bit1_ne_one Nat.bit1_ne_one

protected theorem bit0_ne_one : ∀ n : ℕ, bit0 n ≠ 1
  | 0, h => absurd h (Ne.symm Nat.one_ne_zero)
  | n + 1, h =>
    have h1 : succ (succ (n + n)) = 1 := succ_add n n ▸ h
    Nat.noConfusion h1 fun h2 => absurd h2 (succ_ne_zero (n + n))
#align nat.bit0_ne_one Nat.bit0_ne_one

protected theorem bit1_ne_bit0 : ∀ n m : ℕ, bit1 n ≠ bit0 m
  | 0, m, h => absurd h (Ne.symm (Nat.add_self_ne_one m))
  | n + 1, 0, h =>
    have h1 : succ (bit0 (succ n)) = 0 := h
    absurd h1 (Nat.succ_ne_zero _)
  | n + 1, m + 1, h =>
    have h1 : succ (succ (bit1 n)) = succ (succ (bit0 m)) :=
      Nat.bit0_succ_eq m ▸ Nat.bit1_succ_eq n ▸ h
    have h2 : bit1 n = bit0 m := Nat.noConfusion h1 fun h2' => Nat.noConfusion h2' fun h2'' => h2''
    absurd h2 (Nat.bit1_ne_bit0 n m)
#align nat.bit1_ne_bit0 Nat.bit1_ne_bit0

protected theorem bit0_ne_bit1 : ∀ n m : ℕ, bit0 n ≠ bit1 m := fun n m : Nat =>
  Ne.symm (Nat.bit1_ne_bit0 m n)
#align nat.bit0_ne_bit1 Nat.bit0_ne_bit1

protected theorem bit0_inj : ∀ {n m : ℕ}, bit0 n = bit0 m → n = m
  | 0, 0, _ => rfl
  | 0, m + 1, h => by contradiction
  | n + 1, 0, h => by contradiction
  | n + 1, m + 1, h => by
    have h : succ (succ (n + n)) = succ (succ (m + m)) := by
      unfold bit0 at h
      simp [add_one, add_succ, succ_add] at h
      have aux : n + n = m + m := h
      rw [aux]
    have : n + n = m + m := by repeat
      injection h with h
    have : n = m := Nat.bit0_inj this
    rw [this]
#align nat.bit0_inj Nat.bit0_inj

protected theorem bit1_inj : ∀ {n m : ℕ}, bit1 n = bit1 m → n = m := @fun n m h =>
  have : succ (bit0 n) = succ (bit0 m) := by simp [Nat.bit1_eq_succ_bit0] at h; rw [h]
  have : bit0 n = bit0 m := by injection this
  Nat.bit0_inj this
#align nat.bit1_inj Nat.bit1_inj

protected theorem bit0_ne {n m : ℕ} : n ≠ m → bit0 n ≠ bit0 m := fun h₁ h₂ =>
  absurd (Nat.bit0_inj h₂) h₁
#align nat.bit0_ne Nat.bit0_ne

protected theorem bit1_ne {n m : ℕ} : n ≠ m → bit1 n ≠ bit1 m := fun h₁ h₂ =>
  absurd (Nat.bit1_inj h₂) h₁
#align nat.bit1_ne Nat.bit1_ne

protected theorem zero_ne_bit0 {n : ℕ} : n ≠ 0 → 0 ≠ bit0 n := fun h => Ne.symm (Nat.bit0_ne_zero h)
#align nat.zero_ne_bit0 Nat.zero_ne_bit0

protected theorem zero_ne_bit1 (n : ℕ) : 0 ≠ bit1 n :=
  Ne.symm (Nat.bit1_ne_zero n)
#align nat.zero_ne_bit1 Nat.zero_ne_bit1

protected theorem one_ne_bit0 (n : ℕ) : 1 ≠ bit0 n :=
  Ne.symm (Nat.bit0_ne_one n)
#align nat.one_ne_bit0 Nat.one_ne_bit0

protected theorem one_ne_bit1 {n : ℕ} : n ≠ 0 → 1 ≠ bit1 n := fun h => Ne.symm (Nat.bit1_ne_one h)
#align nat.one_ne_bit1 Nat.one_ne_bit1

protected theorem one_lt_bit1 : ∀ {n : Nat}, n ≠ 0 → 1 < bit1 n
  | 0, h => by contradiction
  | succ n, _ => by
    rw [Nat.bit1_succ_eq]
    apply succ_lt_succ
    apply zero_lt_succ
#align nat.one_lt_bit1 Nat.one_lt_bit1

protected theorem one_lt_bit0 : ∀ {n : Nat}, n ≠ 0 → 1 < bit0 n
  | 0, h => by contradiction
  | succ n, _ => by
    rw [Nat.bit0_succ_eq]
    apply succ_lt_succ
    apply zero_lt_succ
#align nat.one_lt_bit0 Nat.one_lt_bit0

protected theorem bit0_lt {n m : Nat} (h : n < m) : bit0 n < bit0 m :=
  Nat.add_lt_add h h
#align nat.bit0_lt Nat.bit0_lt

protected theorem bit1_lt {n m : Nat} (h : n < m) : bit1 n < bit1 m :=
  succ_lt_succ (Nat.add_lt_add h h)
#align nat.bit1_lt Nat.bit1_lt

protected theorem bit0_lt_bit1 {n m : Nat} (h : n ≤ m) : bit0 n < bit1 m :=
  lt_succ_of_le (Nat.add_le_add h h)
#align nat.bit0_lt_bit1 Nat.bit0_lt_bit1

protected theorem bit1_lt_bit0 : ∀ {n m : Nat}, n < m → bit1 n < bit0 m
  | n, 0, h => absurd h n.not_lt_zero
  | n, succ m, h =>
    have : n ≤ m := le_of_lt_succ h
    have : succ (n + n) ≤ succ (m + m) := succ_le_succ (Nat.add_le_add this this)
    have : succ (n + n) ≤ succ m + m := by rw [succ_add]; assumption
    show succ (n + n) < succ (succ m + m) from lt_succ_of_le this
#align nat.bit1_lt_bit0 Nat.bit1_lt_bit0

protected theorem one_le_bit1 (n : ℕ) : 1 ≤ bit1 n :=
  show 1 ≤ succ (bit0 n) from succ_le_succ (bit0 n).zero_le
#align nat.one_le_bit1 Nat.one_le_bit1

protected theorem one_le_bit0 : ∀ n : ℕ, n ≠ 0 → 1 ≤ bit0 n
  | 0, h => absurd rfl h
  | n + 1, _ =>
    suffices 1 ≤ succ (succ (bit0 n)) from Eq.symm (Nat.bit0_succ_eq n) ▸ this
    succ_le_succ (bit0 n).succ.zero_le
#align nat.one_le_bit0 Nat.one_le_bit0

end bit

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
  Nat.lt_ge_by_cases h₁ fun h₁ ↦
    Nat.lt_ge_by_cases h₃ fun h ↦ h₂ (Nat.le_antisymm h h₁)

/- find -/

section find
variable (p : ℕ → Prop)

private def lbp (m n : ℕ) : Prop := m = n + 1 ∧ ∀ k, k ≤ n → ¬p k

variable [DecidablePred p] (H : ∃ n, p n)

variable {p}

private def wf_lbp : WellFounded (lbp p) := by
  refine ⟨let ⟨n, pn⟩ := H; ?_⟩
  suffices ∀ m k, n ≤ k + m → Acc (lbp p) k from fun a ↦ this _ _ (Nat.le_add_left _ _)
  intro m
  induction m with refine fun k kn ↦ ⟨_, fun | _, ⟨rfl, a⟩ => ?_⟩
  | zero => exact absurd pn (a _ kn)
  | succ m IH => exact IH _ (by rw [Nat.add_right_comm]; exact kn)
/-- Used in the definition of `Nat.find`. Returns the smallest natural satisfying `p`-/
protected def findX : {n // p n ∧ ∀ m, m < n → ¬p m} :=
  (wf_lbp H).fix (C := fun k ↦ (∀n, n < k → ¬p n) → {n // p n ∧ ∀ m, m < n → ¬p m})
    (fun m IH al ↦ if pm : p m then ⟨m, pm, al⟩ else
        have this : ∀ n, n ≤ m → ¬p n := fun n h ↦
          (lt_or_eq_of_le h).elim (al n) fun e ↦ by rw [e]; exact pm
        IH _ ⟨rfl, this⟩ fun n h ↦ this n $ Nat.le_of_succ_le_succ h)
    0 fun n h ↦ absurd h (Nat.not_lt_zero _)

/--
If `p` is a (decidable) predicate on `ℕ` and `hp : ∃ (n : ℕ), p n` is a proof that
there exists some natural number satisfying `p`, then `Nat.find hp` is the
smallest natural number satisfying `p`. Note that `Nat.find` is protected,
meaning that you can't just write `find`, even if the `Nat` namespace is open.

The API for `Nat.find` is:

* `Nat.find_spec` is the proof that `Nat.find hp` satisfies `p`.
* `Nat.find_min` is the proof that if `m < Nat.find hp` then `m` does not satisfy `p`.
* `Nat.find_min'` is the proof that if `m` does satisfy `p` then `Nat.find hp ≤ m`.
-/
protected def find : ℕ := (Nat.findX H).1

protected lemma find_spec : p (Nat.find H) := (Nat.findX H).2.1

protected lemma find_min : ∀ {m : ℕ}, m < Nat.find H → ¬p m := @(Nat.findX H).2.2

protected lemma find_min' {m : ℕ} (h : p m) : Nat.find H ≤ m :=
  not_lt.1 fun l ↦ Nat.find_min H l h

end find

theorem cond_decide_mod_two (x : ℕ) [d : Decidable (x % 2 = 1)] :
    cond (@decide (x % 2 = 1) d) 1 0 = x % 2 := by
  by_cases h : x % 2 = 1
  · simp! [*]
  · cases mod_two_eq_zero_or_one x <;> simp! [*, Nat.zero_ne_one]
#align nat.cond_to_bool_mod_two Nat.cond_decide_mod_two

lemma to_digits_core_lens_eq_aux (b f : Nat) :
  ∀ (n : Nat) (l1 l2 : List Char), l1.length = l2.length →
    (Nat.toDigitsCore b f n l1).length = (Nat.toDigitsCore b f n l2).length := by
  induction f with (simp only [Nat.toDigitsCore, List.length]; intro n l1 l2 hlen)
  | zero => assumption
  | succ f ih =>
    by_cases hx : n / b = 0
    case pos => simp only [hx, if_true, List.length, congrArg (fun l ↦ l + 1) hlen]
    case neg =>
      simp only [hx, if_false]
      specialize ih (n / b) (Nat.digitChar (n % b) :: l1) (Nat.digitChar (n % b) :: l2)
      simp only [List.length, congrArg (fun l ↦ l + 1) hlen] at ih
      exact ih trivial

lemma to_digits_core_lens_eq (b f : Nat) : ∀ (n : Nat) (c : Char) (tl : List Char),
    (Nat.toDigitsCore b f n (c :: tl)).length = (Nat.toDigitsCore b f n tl).length + 1 := by
  induction f with (intro n c tl; simp only [Nat.toDigitsCore, List.length])
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

#align nat.succ_le_succ_iff Nat.succ_le_succ_iff
