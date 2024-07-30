/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Int

/-!
# Lemmas about powers in ordered fields.
-/


variable {α : Type*}

open Function Int

section LinearOrderedSemifield

variable [LinearOrderedSemifield α] {a b c d e : α} {m n : ℤ}

/-! ### Integer powers -/

@[gcongr]
theorem zpow_le_of_le (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n := by
  have ha₀ : 0 < a := one_pos.trans_le ha
  lift n - m to ℕ using sub_nonneg.2 h with k hk
  calc
    a ^ m = a ^ m * 1 := (mul_one _).symm
    _ ≤ a ^ m * a ^ k :=
      mul_le_mul_of_nonneg_left (one_le_pow_of_one_le ha _) (zpow_nonneg ha₀.le _)
    _ = a ^ n := by rw [← zpow_natCast, ← zpow_add₀ ha₀.ne', hk, add_sub_cancel]

theorem zpow_le_one_of_nonpos (ha : 1 ≤ a) (hn : n ≤ 0) : a ^ n ≤ 1 :=
  (zpow_le_of_le ha hn).trans_eq <| zpow_zero _

theorem one_le_zpow_of_nonneg (ha : 1 ≤ a) (hn : 0 ≤ n) : 1 ≤ a ^ n :=
  (zpow_zero _).symm.trans_le <| zpow_le_of_le ha hn

protected theorem Nat.zpow_pos_of_pos {a : ℕ} (h : 0 < a) (n : ℤ) : 0 < (a : α) ^ n := by
  apply zpow_pos_of_pos
  exact mod_cast h

theorem Nat.zpow_ne_zero_of_pos {a : ℕ} (h : 0 < a) (n : ℤ) : (a : α) ^ n ≠ 0 :=
  (Nat.zpow_pos_of_pos h n).ne'

theorem one_lt_zpow (ha : 1 < a) : ∀ n : ℤ, 0 < n → 1 < a ^ n
  | (n : ℕ), h => (zpow_natCast _ _).symm.subst (one_lt_pow ha <| Int.natCast_ne_zero.mp h.ne')
  | -[_+1], h => ((Int.negSucc_not_pos _).mp h).elim

theorem zpow_strictMono (hx : 1 < a) : StrictMono (a ^ · : ℤ → α) :=
  strictMono_int_of_lt_succ fun n =>
    have xpos : 0 < a := zero_lt_one.trans hx
    calc
      a ^ n < a ^ n * a := lt_mul_of_one_lt_right (zpow_pos_of_pos xpos _) hx
      _ = a ^ (n + 1) := (zpow_add_one₀ xpos.ne' _).symm

theorem zpow_strictAnti (h₀ : 0 < a) (h₁ : a < 1) : StrictAnti (a ^ · : ℤ → α) :=
  strictAnti_int_of_succ_lt fun n =>
    calc
      a ^ (n + 1) = a ^ n * a := zpow_add_one₀ h₀.ne' _
      _ < a ^ n * 1 := (mul_lt_mul_left <| zpow_pos_of_pos h₀ _).2 h₁
      _ = a ^ n := mul_one _

@[simp]
theorem zpow_lt_iff_lt (hx : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (zpow_strictMono hx).lt_iff_lt

@[gcongr] alias ⟨_, GCongr.zpow_lt_of_lt⟩ := zpow_lt_iff_lt

@[deprecated (since := "2024-02-10")] alias zpow_lt_of_lt := GCongr.zpow_lt_of_lt

@[simp]
theorem zpow_le_iff_le (hx : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  (zpow_strictMono hx).le_iff_le

@[simp]
theorem div_pow_le (ha : 0 ≤ a) (hb : 1 ≤ b) (k : ℕ) : a / b ^ k ≤ a :=
  div_le_self ha <| one_le_pow_of_one_le hb _

theorem zpow_injective (h₀ : 0 < a) (h₁ : a ≠ 1) : Injective (a ^ · : ℤ → α) := by
  rcases h₁.lt_or_lt with (H | H)
  · exact (zpow_strictAnti h₀ H).injective
  · exact (zpow_strictMono H).injective

@[simp]
theorem zpow_inj (h₀ : 0 < a) (h₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n :=
  (zpow_injective h₀ h₁).eq_iff

theorem zpow_le_max_of_min_le {x : α} (hx : 1 ≤ x) {a b c : ℤ} (h : min a b ≤ c) :
    x ^ (-c) ≤ max (x ^ (-a)) (x ^ (-b)) :=
  have : Antitone fun n : ℤ => x ^ (-n) := fun _ _ h => zpow_le_of_le hx (neg_le_neg h)
  (this h).trans_eq this.map_min

theorem zpow_le_max_iff_min_le {x : α} (hx : 1 < x) {a b c : ℤ} :
    x ^ (-c) ≤ max (x ^ (-a)) (x ^ (-b)) ↔ min a b ≤ c := by
  simp_rw [le_max_iff, min_le_iff, zpow_le_iff_le hx, neg_le_neg_iff]

end LinearOrderedSemifield

section LinearOrderedField

variable [LinearOrderedField α] {a b c d : α} {n : ℤ}

protected theorem Even.zpow_nonneg (hn : Even n) (a : α) : 0 ≤ a ^ n := by
  obtain ⟨k, rfl⟩ := hn; rw [zpow_add' (by simp [em'])]; exact mul_self_nonneg _

lemma zpow_two_nonneg (a : α) : 0 ≤ a ^ (2 : ℤ) := even_two.zpow_nonneg _

lemma zpow_neg_two_nonneg (a : α) : 0 ≤ a ^ (-2 : ℤ) := even_neg_two.zpow_nonneg _

protected lemma Even.zpow_pos (hn : Even n) (ha : a ≠ 0) : 0 < a ^ n :=
  (hn.zpow_nonneg _).lt_of_ne' (zpow_ne_zero _ ha)

lemma zpow_two_pos_of_ne_zero (ha : a ≠ 0) : 0 < a ^ (2 : ℤ) := even_two.zpow_pos ha

theorem Even.zpow_pos_iff (hn : Even n) (h : n ≠ 0) : 0 < a ^ n ↔ a ≠ 0 := by
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add' (by simp [em']), mul_self_pos, zpow_ne_zero_iff (by simpa using h)]

theorem Odd.zpow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0 := by
  refine ⟨lt_imp_lt_of_le_imp_le (zpow_nonneg · _), fun ha ↦ ?_⟩
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add_one₀ ha.ne]
  exact mul_neg_of_pos_of_neg (Even.zpow_pos (even_two_mul _) ha.ne) ha

protected lemma Odd.zpow_nonneg_iff (hn : Odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 hn.zpow_neg_iff

theorem Odd.zpow_nonpos_iff (hn : Odd n) : a ^ n ≤ 0 ↔ a ≤ 0 := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, hn.zpow_neg_iff, zpow_eq_zero_iff]
  rintro rfl
  exact Int.odd_iff_not_even.1 hn even_zero

lemma Odd.zpow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a := lt_iff_lt_of_le_iff_le hn.zpow_nonpos_iff

alias ⟨_, Odd.zpow_neg⟩ := Odd.zpow_neg_iff

alias ⟨_, Odd.zpow_nonpos⟩ := Odd.zpow_nonpos_iff

theorem Even.zpow_abs {p : ℤ} (hp : Even p) (a : α) : |a| ^ p = a ^ p := by
  cases' abs_choice a with h h <;> simp only [h, hp.neg_zpow _]

/-! ### Bernoulli's inequality -/

/-- Bernoulli's inequality reformulated to estimate `(n : α)`. -/
theorem Nat.cast_le_pow_sub_div_sub (H : 1 < a) (n : ℕ) : (n : α) ≤ (a ^ n - 1) / (a - 1) :=
  (le_div_iff (sub_pos.2 H)).2 <|
    le_sub_left_of_add_le <| one_add_mul_sub_le_pow ((neg_le_self zero_le_one).trans H.le) _

/-- For any `a > 1` and a natural `n` we have `n ≤ a ^ n / (a - 1)`. See also
`Nat.cast_le_pow_sub_div_sub` for a stronger inequality with `a ^ n - 1` in the numerator. -/
theorem Nat.cast_le_pow_div_sub (H : 1 < a) (n : ℕ) : (n : α) ≤ a ^ n / (a - 1) :=
  (n.cast_le_pow_sub_div_sub H).trans <|
    div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (sub_nonneg.2 H.le)

end LinearOrderedField

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

/-- The `positivity` extension which identifies expressions of the form `a ^ (b : ℤ)`,
such that `positivity` successfully recognises both `a` and `b`. -/
@[positivity _ ^ (_ : ℤ), Pow.pow _ (_ : ℤ)]
def evalZPow : PositivityExt where eval {u α} zα pα e := do
  let .app (.app _ (a : Q($α))) (b : Q(ℤ)) ← withReducible (whnf e) | throwError "not ^"
  let result ← catchNone do
    let _a ← synthInstanceQ q(LinearOrderedField $α)
    assumeInstancesCommute
    match ← whnfR b with
    | .app (.app (.app (.const `OfNat.ofNat _) _) (.lit (Literal.natVal n))) _ =>
      guard (n % 2 = 0)
      have m : Q(ℕ) := mkRawNatLit (n / 2)
      haveI' : $b =Q $m + $m := ⟨⟩
      haveI' : $e =Q $a ^ $b := ⟨⟩
      pure (.nonnegative q(Even.zpow_nonneg (even_add_self _) $a))
    | .app (.app (.app (.const `Neg.neg _) _) _) b' =>
      let b' ← whnfR b'
      let .true := b'.isAppOfArity ``OfNat.ofNat 3 | throwError "not a ^ -n where n is a literal"
      let some n := (b'.getRevArg! 1).rawNatLit? | throwError "not a ^ -n where n is a literal"
      guard (n % 2 = 0)
      have m : Q(ℕ) := mkRawNatLit (n / 2)
      haveI' : $b =Q (-$m) + (-$m) := ⟨⟩
      haveI' : $e =Q $a ^ $b := ⟨⟩
      pure (.nonnegative q(Even.zpow_nonneg (even_add_self _) $a))
    | _ => throwError "not a ^ n where n is a literal or a negated literal"
  orElse result do
    let ra ← core zα pα a
    let ofNonneg (pa : Q(0 ≤ $a)) (_oα : Q(LinearOrderedSemifield $α)) :
        MetaM (Strictness zα pα e) := do
      haveI' : $e =Q $a ^ $b := ⟨⟩
      assumeInstancesCommute
      pure (.nonnegative q(zpow_nonneg $pa $b))
    let ofNonzero (pa : Q($a ≠ 0)) (_oα : Q(GroupWithZero $α)) : MetaM (Strictness zα pα e) := do
      haveI' : $e =Q $a ^ $b := ⟨⟩
      let _a ← synthInstanceQ q(GroupWithZero $α)
      assumeInstancesCommute
      pure (.nonzero q(zpow_ne_zero $b $pa))
    match ra with
    | .positive pa =>
      try
        let _a ← synthInstanceQ (q(LinearOrderedSemifield $α) : Q(Type u))
        haveI' : $e =Q $a ^ $b := ⟨⟩
        assumeInstancesCommute
        pure (.positive q(zpow_pos_of_pos $pa $b))
      catch e : Exception =>
        trace[Tactic.positivity.failure] "{e.toMessageData}"
        let oα ← synthInstanceQ q(LinearOrderedSemifield $α)
        orElse (← catchNone (ofNonneg q(le_of_lt $pa) oα)) (ofNonzero q(ne_of_gt $pa) oα)
    | .nonnegative pa => ofNonneg pa (← synthInstanceQ (_ : Q(Type u)))
    | .nonzero pa => ofNonzero pa (← synthInstanceQ (_ : Q(Type u)))
    | .none => pure .none

end Mathlib.Meta.Positivity
