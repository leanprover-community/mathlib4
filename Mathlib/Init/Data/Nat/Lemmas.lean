/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Std.Data.Nat.Lemmas
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Order.LinearOrder

#align_import init.data.nat.lemmas from "leanprover-community/lean"@"38b59111b2b4e6c572582b27e8937e92fc70ac02"

universe u

namespace Nat

/-! addition -/














/-! multiplication -/












theorem eq_zero_of_mul_eq_zero : ∀ {n m : ℕ}, n * m = 0 → n = 0 ∨ m = 0
  | 0, m => fun _ => Or.inl rfl
  | succ n, m => by
    rw [succ_mul]; intro h
    exact Or.inr (Nat.eq_zero_of_add_eq_zero_left h)

/-! properties of inequality -/

















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






































protected def ltGeByCases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : b ≤ a → C) : C :=
  Decidable.byCases h₁ fun h => h₂ (Or.elim (Nat.lt_or_ge a b) (fun a => absurd a h) fun a => a)

protected def ltByCases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : a = b → C) (h₃ : b < a → C) :
    C :=
  Nat.ltGeByCases h₁ fun h₁ => Nat.ltGeByCases h₃ fun h => h₂ (Nat.le_antisymm h h₁)









-- TODO: there are four variations, depending on which variables we assume to be nonneg

/-! bit0/bit1 properties -/
section bit
set_option linter.deprecated false

protected theorem bit1_eq_succ_bit0 (n : ℕ) : bit1 n = succ (bit0 n) :=
  rfl

protected theorem bit1_succ_eq (n : ℕ) : bit1 (succ n) = succ (succ (bit1 n)) :=
  Eq.trans (Nat.bit1_eq_succ_bit0 (succ n)) (congr_arg succ (Nat.bit0_succ_eq n))

protected theorem bit1_ne_one : ∀ {n : ℕ}, n ≠ 0 → bit1 n ≠ 1
  | 0, h, _h1 => absurd rfl h
  | _n + 1, _h, h1 => Nat.noConfusion h1 fun h2 => absurd h2 (succ_ne_zero _)

protected theorem bit0_ne_one : ∀ n : ℕ, bit0 n ≠ 1
  | 0, h => absurd h (Ne.symm Nat.one_ne_zero)
  | n + 1, h =>
    have h1 : succ (succ (n + n)) = 1 := succ_add n n ▸ h
    Nat.noConfusion h1 fun h2 => absurd h2 (succ_ne_zero (n + n))


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

protected theorem bit0_ne_bit1 : ∀ n m : ℕ, bit0 n ≠ bit1 m := fun n m : Nat =>
  Ne.symm (Nat.bit1_ne_bit0 m n)

protected theorem bit0_inj : ∀ {n m : ℕ}, bit0 n = bit0 m → n = m
  | 0, 0, _h => rfl
  | 0, m + 1, h => by contradiction
  | n + 1, 0, h => by contradiction
  | n + 1, m + 1, h => by
    have : succ (succ (n + n)) = succ (succ (m + m)) := by
      unfold bit0 at h; simp [add_one, add_succ, succ_add] at h
      have aux : n + n = m + m := h; rw [aux]
    have : n + n = m + m := by repeat injection this with this
    have : n = m := Nat.bit0_inj this
    rw [this]

protected theorem bit1_inj : ∀ {n m : ℕ}, bit1 n = bit1 m → n = m := @fun n m h =>
  have : succ (bit0 n) = succ (bit0 m) := by simp [Nat.bit1_eq_succ_bit0] at h; rw [h]
  have : bit0 n = bit0 m := by injection this
  Nat.bit0_inj this

protected theorem bit0_ne {n m : ℕ} : n ≠ m → bit0 n ≠ bit0 m := fun h₁ h₂ =>
  absurd (Nat.bit0_inj h₂) h₁

protected theorem bit1_ne {n m : ℕ} : n ≠ m → bit1 n ≠ bit1 m := fun h₁ h₂ =>
  absurd (Nat.bit1_inj h₂) h₁

protected theorem zero_ne_bit0 {n : ℕ} : n ≠ 0 → 0 ≠ bit0 n := fun h => Ne.symm (Nat.bit0_ne_zero h)

protected theorem zero_ne_bit1 (n : ℕ) : 0 ≠ bit1 n :=
  Ne.symm (Nat.bit1_ne_zero n)

protected theorem one_ne_bit0 (n : ℕ) : 1 ≠ bit0 n :=
  Ne.symm (Nat.bit0_ne_one n)

protected theorem one_ne_bit1 {n : ℕ} : n ≠ 0 → 1 ≠ bit1 n := fun h => Ne.symm (Nat.bit1_ne_one h)

protected theorem one_lt_bit1 : ∀ {n : Nat}, n ≠ 0 → 1 < bit1 n
  | 0, h => by contradiction
  | succ n, _h => by
    rw [Nat.bit1_succ_eq]
    apply succ_lt_succ
    apply zero_lt_succ

protected theorem one_lt_bit0 : ∀ {n : Nat}, n ≠ 0 → 1 < bit0 n
  | 0, h => by contradiction
  | succ n, _h => by
    rw [Nat.bit0_succ_eq]
    apply succ_lt_succ
    apply zero_lt_succ

protected theorem bit0_lt {n m : Nat} (h : n < m) : bit0 n < bit0 m :=
  Nat.add_lt_add h h

protected theorem bit1_lt {n m : Nat} (h : n < m) : bit1 n < bit1 m :=
  succ_lt_succ (Nat.add_lt_add h h)

protected theorem bit0_lt_bit1 {n m : Nat} (h : n ≤ m) : bit0 n < bit1 m :=
  lt_succ_of_le (Nat.add_le_add h h)

protected theorem bit1_lt_bit0 : ∀ {n m : Nat}, n < m → bit1 n < bit0 m
  | n, 0, h => absurd h n.not_lt_zero
  | n, succ m, h =>
    have : n ≤ m := le_of_lt_succ h
    have : succ (n + n) ≤ succ (m + m) := succ_le_succ (Nat.add_le_add this this)
    have : succ (n + n) ≤ succ m + m := by rw [succ_add]; assumption
    show succ (n + n) < succ (succ m + m) from lt_succ_of_le this

protected theorem one_le_bit1 (n : ℕ) : 1 ≤ bit1 n :=
  show 1 ≤ succ (bit0 n) from succ_le_succ (bit0 n).zero_le

protected theorem one_le_bit0 : ∀ n : ℕ, n ≠ 0 → 1 ≤ bit0 n
  | 0, h => absurd rfl h
  | n + 1, _h =>
    suffices 1 ≤ succ (succ (bit0 n)) from Eq.symm (Nat.bit0_succ_eq n) ▸ this
    succ_le_succ (bit0 n).succ.zero_le

end bit

/-! successor and predecessor -/






def discriminate {B : Sort u} {n : ℕ} (H1 : n = 0 → B) (H2 : ∀ m, n = succ m → B) : B := by
  induction n with
  | zero => exact H1 rfl
  | succ n _ => apply H2 _ rfl

theorem one_eq_succ_zero : 1 = succ 0 :=
  rfl


/-! subtraction

Many lemmas are proven more generally in mathlib `algebra/order/sub` -/










































/-! min -/






/-! induction principles -/


def twoStepInduction {P : ℕ → Sort u} (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ) (_IH1 : P n) (_IH2 : P (succ n)), P (succ (succ n))) : ∀ a : ℕ, P a
  | 0 => H1
  | 1 => H2
  | succ (succ _n) => H3 _ (twoStepInduction H1 H2 H3 _) (twoStepInduction H1 H2 H3 _)

def subInduction {P : ℕ → ℕ → Sort u} (H1 : ∀ m, P 0 m) (H2 : ∀ n, P (succ n) 0)
    (H3 : ∀ n m, P n m → P (succ n) (succ m)) : ∀ n m : ℕ, P n m
  | 0, _m => H1 _
  | succ _n, 0 => H2 _
  | succ n, succ m => H3 _ _ (subInduction H1 H2 H3 n m)


-- porting note: added `elab_as_elim`
@[elab_as_elim]
protected theorem strong_induction_on {p : Nat → Prop} (n : Nat)
    (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
  Nat.strongRecOn n h

protected theorem case_strong_induction_on {p : Nat → Prop} (a : Nat) (hz : p 0)
    (hi : ∀ n, (∀ m, m ≤ n → p m) → p (succ n)) : p a :=
  Nat.strong_induction_on a fun n =>
    match n with
    | 0 => fun _ => hz
    | n + 1 => fun h₁ => hi n fun _m h₂ => h₁ _ (lt_succ_of_le h₂)

/-! mod -/



















theorem cond_decide_mod_two (x : ℕ) [d : Decidable (x % 2 = 1)] :
    cond (@decide (x % 2 = 1) d) 1 0 = x % 2 := by
  by_cases h : x % 2 = 1
  · simp! [*]
  · cases mod_two_eq_zero_or_one x <;> simp! [*, Nat.zero_ne_one]


/-! div -/






























/-! dvd -/























/-! find -/


section Find

variable {p : ℕ → Prop}

private def lbp (m n : ℕ) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, ¬p k

variable [DecidablePred p] (H : ∃ n, p n)

private def wf_lbp : WellFounded (@lbp p) :=
  ⟨let ⟨n, pn⟩ := H
    suffices ∀ m k, n ≤ k + m → Acc lbp k from fun a => this _ _ (Nat.le_add_left _ _)
    fun m =>
    Nat.recOn m
      (fun k kn =>
        ⟨_, fun y r =>
          match y, r with
          | _, ⟨rfl, a⟩ => absurd pn (a _ kn)⟩)
      fun m IH k kn =>
      ⟨_, fun y r =>
        match y, r with
        | _, ⟨rfl, _a⟩ => IH _ (by rw [Nat.add_right_comm]; exact kn)⟩⟩

protected def findX : { n // p n ∧ ∀ m < n, ¬p m } :=
  @WellFounded.fix _ (fun k => (∀ n < k, ¬p n) → { n // p n ∧ ∀ m < n, ¬p m }) lbp (wf_lbp H)
    (fun m IH al =>
      if pm : p m then ⟨m, pm, al⟩
      else
        have : ∀ n ≤ m, ¬p n := fun n h =>
          Or.elim (Decidable.lt_or_eq_of_le h) (al n) fun e => by rw [e]; exact pm
        IH _ ⟨rfl, this⟩ fun n h => this n <| Nat.le_of_succ_le_succ h)
    0 fun n h => absurd h (Nat.not_lt_zero _)

/-- If `p` is a (decidable) predicate on `ℕ` and `hp : ∃ (n : ℕ), p n` is a proof that
there exists some natural number satisfying `p`, then `Nat.find hp` is the
smallest natural number satisfying `p`. Note that `Nat.find` is protected,
meaning that you can't just write `find`, even if the `Nat` namespace is open.

The API for `Nat.find` is:

* `Nat.find_spec` is the proof that `Nat.find hp` satisfies `p`.
* `Nat.find_min` is the proof that if `m < Nat.find hp` then `m` does not satisfy `p`.
* `Nat.find_min'` is the proof that if `m` does satisfy `p` then `Nat.find hp ≤ m`.
-/
protected def find : ℕ :=
  (Nat.findX H).1

protected theorem find_spec : p (Nat.find H) :=
  (Nat.findX H).2.left

protected theorem find_min : ∀ {m : ℕ}, m < Nat.find H → ¬p m :=
  @(Nat.findX H).2.right

protected theorem find_min' {m : ℕ} (h : p m) : Nat.find H ≤ m :=
  le_of_not_lt fun l => Nat.find_min H l h

end Find

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
        have _ : e = 0 := Nat.eq_zero_of_not_pos h_pred_pos
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
    case neg => exact to_digits_core_length 10 (by decide) (Nat.succ n + 1) (Nat.succ n) e he e0

end Nat
