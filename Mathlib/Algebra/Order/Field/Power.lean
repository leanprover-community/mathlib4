/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn, Sabbir Rahman
-/
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Lemmas about powers in ordered fields.
-/


variable {α : Type*}

open Function Int

section LinearOrderedSemifield

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {m n : ℤ}

/-! ### Integer powers -/

@[deprecated zpow_le_zpow_right₀ (since := "2024-10-08")]
theorem zpow_le_of_le (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n := zpow_le_zpow_right₀ ha h

@[deprecated zpow_le_one_of_nonpos₀ (since := "2024-10-08")]
theorem zpow_le_one_of_nonpos (ha : 1 ≤ a) (hn : n ≤ 0) : a ^ n ≤ 1 :=
  zpow_le_one_of_nonpos₀ ha hn

@[deprecated one_le_zpow₀ (since := "2024-10-08")]
theorem one_le_zpow_of_nonneg (ha : 1 ≤ a) (hn : 0 ≤ n) : 1 ≤ a ^ n :=
  one_le_zpow₀ ha hn

@[deprecated zpow_pos (since := "2024-10-08")]
protected theorem Nat.zpow_pos_of_pos {a : ℕ} (h : 0 < a) (n : ℤ) : 0 < (a : α) ^ n :=
  zpow_pos (mod_cast h) _

@[deprecated zpow_ne_zero (since := "2024-10-08")]
theorem Nat.zpow_ne_zero_of_pos {a : ℕ} (h : 0 < a) (n : ℤ) : (a : α) ^ n ≠ 0 :=
  zpow_ne_zero _ (mod_cast h.ne')

@[deprecated zpow_right_strictMono₀ (since := "2024-10-08")]
theorem zpow_strictMono (hx : 1 < a) : StrictMono (a ^ · : ℤ → α) :=
  zpow_right_strictMono₀ hx

@[deprecated zpow_right_strictAnti₀ (since := "2024-10-08")]
theorem zpow_strictAnti (h₀ : 0 < a) (h₁ : a < 1) : StrictAnti (a ^ · : ℤ → α) :=
  zpow_right_strictAnti₀ h₀ h₁

@[deprecated zpow_lt_zpow_iff_right₀ (since := "2024-10-08")]
theorem zpow_lt_iff_lt (hx : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  zpow_lt_zpow_iff_right₀ hx

@[deprecated zpow_le_zpow_iff_right₀ (since := "2024-10-08")]
theorem zpow_le_iff_le (hx : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  zpow_le_zpow_iff_right₀ hx

@[deprecated div_le_self (since := "2024-10-08")]
theorem div_pow_le (ha : 0 ≤ a) (hb : 1 ≤ b) (k : ℕ) : a / b ^ k ≤ a :=
  div_le_self ha <| one_le_pow₀ hb

@[deprecated zpow_right_injective₀ (since := "2024-10-08")]
theorem zpow_injective (h₀ : 0 < a) (h₁ : a ≠ 1) : Injective (a ^ · : ℤ → α) :=
  zpow_right_injective₀ h₀ h₁

@[deprecated zpow_right_inj₀ (since := "2024-10-08")]
theorem zpow_inj (h₀ : 0 < a) (h₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n :=
  zpow_right_inj₀ h₀ h₁

@[deprecated "No deprecation message was provided." (since := "2024-10-08")]
theorem zpow_le_max_of_min_le {x : α} (hx : 1 ≤ x) {a b c : ℤ} (h : min a b ≤ c) :
    x ^ (-c) ≤ max (x ^ (-a)) (x ^ (-b)) :=
  have : Antitone fun n : ℤ => x ^ (-n) := fun _ _ h => zpow_le_zpow_right₀ hx (neg_le_neg h)
  (this h).trans_eq this.map_min

@[deprecated "No deprecation message was provided." (since := "2024-10-08")]
theorem zpow_le_max_iff_min_le {x : α} (hx : 1 < x) {a b c : ℤ} :
    x ^ (-c) ≤ max (x ^ (-a)) (x ^ (-b)) ↔ min a b ≤ c := by
  simp_rw [le_max_iff, min_le_iff, zpow_le_zpow_iff_right₀ hx, neg_le_neg_iff]

end LinearOrderedSemifield

section LinearOrderedField

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

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
  exact Int.not_even_iff_odd.2 hn .zero

lemma Odd.zpow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a := lt_iff_lt_of_le_iff_le hn.zpow_nonpos_iff

alias ⟨_, Odd.zpow_neg⟩ := Odd.zpow_neg_iff

alias ⟨_, Odd.zpow_nonpos⟩ := Odd.zpow_nonpos_iff

omit [IsStrictOrderedRing α] in
theorem Even.zpow_abs {p : ℤ} (hp : Even p) (a : α) : |a| ^ p = a ^ p := by
  rcases abs_choice a with h | h <;> simp only [h, hp.neg_zpow _]

lemma zpow_eq_zpow_iff_of_ne_zero₀ (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b ∨ a = -b ∧ Even n :=
  match n with
  | Int.ofNat m => by
    simp only [Int.ofNat_eq_coe, ne_eq, Nat.cast_eq_zero, zpow_natCast, Int.even_coe_nat] at *
    exact pow_eq_pow_iff_of_ne_zero hn
  | Int.negSucc m => by
    simp only [← neg_ofNat_succ, ne_eq, neg_eq_zero, Nat.cast_eq_zero, zpow_neg, zpow_natCast,
      inv_inj, even_neg, Int.even_coe_nat] at *
    exact pow_eq_pow_iff_of_ne_zero hn

lemma zpow_eq_zpow_iff_cases₀ : a ^ n = b ^ n ↔ n = 0 ∨ a = b ∨ a = -b ∧ Even n := by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [zpow_eq_zpow_iff_of_ne_zero₀, *]

lemma zpow_eq_one_iff_of_ne_zero₀ (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← zpow_eq_zpow_iff_of_ne_zero₀ hn]

lemma zpow_eq_one_iff_cases₀ : a ^ n = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← zpow_eq_zpow_iff_cases₀]

lemma zpow_eq_neg_zpow_iff₀ (hb : b ≠ 0) : a ^ n = -b ^ n ↔ a = -b ∧ Odd n :=
  match n with
  | Int.ofNat m => by
    simp [pow_eq_neg_pow_iff, hb]
  | Int.negSucc m => by
    simp [← neg_ofNat_succ, -Nat.cast_add, -Int.natCast_add, neg_inv, pow_eq_neg_pow_iff, hb]

lemma zpow_eq_neg_one_iff₀ : a ^ n = -1 ↔ a = -1 ∧ Odd n := by
  simpa using zpow_eq_neg_zpow_iff₀ (α := α) one_ne_zero

/-! ### Bernoulli's inequality -/

/-- Bernoulli's inequality reformulated to estimate `(n : α)`. -/
theorem Nat.cast_le_pow_sub_div_sub (H : 1 < a) (n : ℕ) : (n : α) ≤ (a ^ n - 1) / (a - 1) :=
  (le_div_iff₀ (sub_pos.2 H)).2 <|
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
    let _a ← synthInstanceQ q(Field $α)
    let _a ← synthInstanceQ q(LinearOrder $α)
    let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
    assumeInstancesCommute
    match ← whnfR b with
    | .app (.app (.app (.const `OfNat.ofNat _) _) (.lit (Literal.natVal n))) _ =>
      guard (n % 2 = 0)
      have m : Q(ℕ) := mkRawNatLit (n / 2)
      haveI' : $b =Q $m + $m := ⟨⟩
      haveI' : $e =Q $a ^ $b := ⟨⟩
      pure (.nonnegative q(Even.zpow_nonneg (Even.add_self _) $a))
    | .app (.app (.app (.const `Neg.neg _) _) _) b' =>
      let b' ← whnfR b'
      let .true := b'.isAppOfArity ``OfNat.ofNat 3 | throwError "not a ^ -n where n is a literal"
      let some n := (b'.getRevArg! 1).rawNatLit? | throwError "not a ^ -n where n is a literal"
      guard (n % 2 = 0)
      have m : Q(ℕ) := mkRawNatLit (n / 2)
      haveI' : $b =Q (-$m) + (-$m) := ⟨⟩
      haveI' : $e =Q $a ^ $b := ⟨⟩
      pure (.nonnegative q(Even.zpow_nonneg (Even.add_self _) $a))
    | _ => throwError "not a ^ n where n is a literal or a negated literal"
  orElse result do
    let ra ← core zα pα a
    let ofNonneg (pa : Q(0 ≤ $a))
        (_oα : Q(Semifield $α)) (_oα : Q(LinearOrder $α)) (_oα : Q(IsStrictOrderedRing $α)) :
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
        let _a ← synthInstanceQ (q(Semifield $α) : Q(Type u))
        let _a ← synthInstanceQ (q(LinearOrder $α) : Q(Type u))
        let _a ← synthInstanceQ (q(IsStrictOrderedRing $α) : Q(Prop))
        haveI' : $e =Q $a ^ $b := ⟨⟩
        assumeInstancesCommute
        pure (.positive q(zpow_pos $pa $b))
      catch e : Exception =>
        trace[Tactic.positivity.failure] "{e.toMessageData}"
        let sα ← synthInstanceQ q(Semifield $α)
        let oα ← synthInstanceQ q(LinearOrder $α)
        let iα ← synthInstanceQ q(IsStrictOrderedRing $α)
        orElse (← catchNone (ofNonneg q(le_of_lt $pa) sα oα iα))
          (ofNonzero q(ne_of_gt $pa) q(inferInstance))
    | .nonnegative pa => ofNonneg pa (← synthInstanceQ (_ : Q(Type u)))
                           (← synthInstanceQ (_ : Q(Type u))) (← synthInstanceQ (_ : Q(Prop)))
    | .nonzero pa => ofNonzero pa (← synthInstanceQ (_ : Q(Type u)))
    | .none => pure .none

end Mathlib.Meta.Positivity
