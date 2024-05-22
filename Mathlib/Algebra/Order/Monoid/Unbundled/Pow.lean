/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Yury G. Kudryashov
-/
import Mathlib.Algebra.Order.Monoid.OrderDual
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Monotonicity.Attr

/-!
# Lemmas about the interaction of power operations with order in terms of `CovariantClass`
-/

open Function

variable {β G M : Type*}

section Monoid

variable [Monoid M]

section Preorder

variable [Preorder M]

section Left

variable [CovariantClass M M (· * ·) (· ≤ ·)] {x : M}

@[to_additive (attr := mono, gcongr) nsmul_le_nsmul_right]
theorem pow_le_pow_left' [CovariantClass M M (swap (· * ·)) (· ≤ ·)] {a b : M} (hab : a ≤ b) :
    ∀ i : ℕ, a ^ i ≤ b ^ i
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, pow_succ]
    exact mul_le_mul' (pow_le_pow_left' hab k) hab
#align pow_le_pow_of_le_left' pow_le_pow_left'
#align nsmul_le_nsmul_of_le_right nsmul_le_nsmul_right

@[to_additive nsmul_nonneg]
theorem one_le_pow_of_one_le' {a : M} (H : 1 ≤ a) : ∀ n : ℕ, 1 ≤ a ^ n
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ]
    exact one_le_mul (one_le_pow_of_one_le' H k) H
#align one_le_pow_of_one_le' one_le_pow_of_one_le'
#align nsmul_nonneg nsmul_nonneg

@[to_additive nsmul_nonpos]
theorem pow_le_one' {a : M} (H : a ≤ 1) (n : ℕ) : a ^ n ≤ 1 :=
  @one_le_pow_of_one_le' Mᵒᵈ _ _ _ _ H n
#align pow_le_one' pow_le_one'
#align nsmul_nonpos nsmul_nonpos

@[to_additive (attr := gcongr) nsmul_le_nsmul_left]
theorem pow_le_pow_right' {a : M} {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
  let ⟨k, hk⟩ := Nat.le.dest h
  calc
    a ^ n ≤ a ^ n * a ^ k := le_mul_of_one_le_right' (one_le_pow_of_one_le' ha _)
    _ = a ^ m := by rw [← hk, pow_add]
#align pow_le_pow' pow_le_pow_right'
#align nsmul_le_nsmul nsmul_le_nsmul_left

@[to_additive nsmul_le_nsmul_left_of_nonpos]
theorem pow_le_pow_right_of_le_one' {a : M} {n m : ℕ} (ha : a ≤ 1) (h : n ≤ m) : a ^ m ≤ a ^ n :=
  pow_le_pow_right' (M := Mᵒᵈ) ha h
#align pow_le_pow_of_le_one' pow_le_pow_right_of_le_one'
#align nsmul_le_nsmul_of_nonpos nsmul_le_nsmul_left_of_nonpos

@[to_additive nsmul_pos]
theorem one_lt_pow' {a : M} (ha : 1 < a) {k : ℕ} (hk : k ≠ 0) : 1 < a ^ k := by
  rcases Nat.exists_eq_succ_of_ne_zero hk with ⟨l, rfl⟩
  clear hk
  induction' l with l IH
  · rw [pow_succ]; simpa using ha
  · rw [pow_succ]
    exact one_lt_mul'' IH ha
#align one_lt_pow' one_lt_pow'
#align nsmul_pos nsmul_pos

@[to_additive nsmul_neg]
theorem pow_lt_one' {a : M} (ha : a < 1) {k : ℕ} (hk : k ≠ 0) : a ^ k < 1 :=
  @one_lt_pow' Mᵒᵈ _ _ _ _ ha k hk
#align pow_lt_one' pow_lt_one'
#align nsmul_neg nsmul_neg

@[to_additive (attr := gcongr) nsmul_lt_nsmul_left]
theorem pow_lt_pow_right' [CovariantClass M M (· * ·) (· < ·)] {a : M} {n m : ℕ} (ha : 1 < a)
    (h : n < m) : a ^ n < a ^ m := by
  rcases Nat.le.dest h with ⟨k, rfl⟩; clear h
  rw [pow_add, pow_succ, mul_assoc, ← pow_succ']
  exact lt_mul_of_one_lt_right' _ (one_lt_pow' ha k.succ_ne_zero)
#align pow_lt_pow_right' pow_lt_pow_right'
#align nsmul_lt_nsmul_left nsmul_lt_nsmul_left

@[to_additive nsmul_left_strictMono]
theorem pow_right_strictMono' [CovariantClass M M (· * ·) (· < ·)] {a : M} (ha : 1 < a) :
    StrictMono ((a ^ ·) : ℕ → M) := fun _ _ => pow_lt_pow_right' ha
#align pow_strict_mono_left pow_right_strictMono'
#align nsmul_strict_mono_right nsmul_left_strictMono

@[to_additive Left.pow_nonneg]
theorem Left.one_le_pow_of_le (hx : 1 ≤ x) : ∀ {n : ℕ}, 1 ≤ x ^ n
  | 0 => (pow_zero x).ge
  | n + 1 => by
    rw [pow_succ]
    exact Left.one_le_mul (Left.one_le_pow_of_le hx) hx
#align left.one_le_pow_of_le Left.one_le_pow_of_le
#align left.pow_nonneg Left.pow_nonneg

@[to_additive Left.pow_nonpos]
theorem Left.pow_le_one_of_le (hx : x ≤ 1) : ∀ {n : ℕ}, x ^ n ≤ 1
  | 0 => (pow_zero _).le
  | n + 1 => by
    rw [pow_succ]
    exact Left.mul_le_one (Left.pow_le_one_of_le hx) hx
#align left.pow_le_one_of_le Left.pow_le_one_of_le
#align left.pow_nonpos Left.pow_nonpos

end Left

section Right

variable [CovariantClass M M (swap (· * ·)) (· ≤ ·)] {x : M}

@[to_additive Right.pow_nonneg]
theorem Right.one_le_pow_of_le (hx : 1 ≤ x) : ∀ {n : ℕ}, 1 ≤ x ^ n
  | 0 => (pow_zero _).ge
  | n + 1 => by
    rw [pow_succ]
    exact Right.one_le_mul (Right.one_le_pow_of_le hx) hx
#align right.one_le_pow_of_le Right.one_le_pow_of_le
#align right.pow_nonneg Right.pow_nonneg

@[to_additive Right.pow_nonpos]
theorem Right.pow_le_one_of_le (hx : x ≤ 1) : ∀ {n : ℕ}, x ^ n ≤ 1
  | 0 => (pow_zero _).le
  | n + 1 => by
    rw [pow_succ]
    exact Right.mul_le_one (Right.pow_le_one_of_le hx) hx
#align right.pow_le_one_of_le Right.pow_le_one_of_le
#align right.pow_nonpos Right.pow_nonpos

end Right

section CovariantLTSwap

variable [Preorder β] [CovariantClass M M (· * ·) (· < ·)]
  [CovariantClass M M (swap (· * ·)) (· < ·)] {f : β → M} {n : ℕ}

@[to_additive StrictMono.const_nsmul]
theorem StrictMono.pow_const (hf : StrictMono f) : ∀ {n : ℕ}, n ≠ 0 → StrictMono (f · ^ n)
  | 0, hn => (hn rfl).elim
  | 1, _ => by simpa
  | Nat.succ <| Nat.succ n, _ => by
    simpa only [pow_succ] using (hf.pow_const n.succ_ne_zero).mul' hf
#align strict_mono.pow_const StrictMono.pow_const
#align strict_mono.const_nsmul StrictMono.const_nsmul

/-- See also `pow_left_strictMonoOn`. -/
@[to_additive nsmul_right_strictMono]  -- Porting note: nolint to_additive_doc
theorem pow_left_strictMono (hn : n ≠ 0) : StrictMono (· ^ n : M → M) := strictMono_id.pow_const hn
#align pow_strict_mono_right' pow_left_strictMono
#align nsmul_strict_mono_left nsmul_right_strictMono

@[to_additive (attr := mono, gcongr) nsmul_lt_nsmul_right]
lemma pow_lt_pow_left' (hn : n ≠ 0) {a b : M} (hab : a < b) : a ^ n < b ^ n :=
  pow_left_strictMono hn hab

end CovariantLTSwap

section CovariantLESwap

variable [Preorder β] [CovariantClass M M (· * ·) (· ≤ ·)]
  [CovariantClass M M (swap (· * ·)) (· ≤ ·)]

@[to_additive Monotone.const_nsmul]
theorem Monotone.pow_const {f : β → M} (hf : Monotone f) : ∀ n : ℕ, Monotone fun a => f a ^ n
  | 0 => by simpa using monotone_const
  | n + 1 => by
    simp_rw [pow_succ]
    exact (Monotone.pow_const hf _).mul' hf
#align monotone.pow_right Monotone.pow_const
#align monotone.const_nsmul Monotone.const_nsmul

@[to_additive nsmul_right_mono]
theorem pow_left_mono (n : ℕ) : Monotone fun a : M => a ^ n := monotone_id.pow_const _
#align pow_mono_right pow_left_mono
#align nsmul_mono_left nsmul_right_mono

end CovariantLESwap

@[to_additive Left.pow_neg]
theorem Left.pow_lt_one_of_lt [CovariantClass M M (· * ·) (· < ·)] {n : ℕ} {x : M} (hn : 0 < n)
    (h : x < 1) : x ^ n < 1 :=
  Nat.le_induction ((pow_one _).trans_lt h)
    (fun n _ ih => by
      rw [pow_succ]
      exact mul_lt_one ih h)
    _ (Nat.succ_le_iff.2 hn)
#align left.pow_lt_one_of_lt Left.pow_lt_one_of_lt
#align left.pow_neg Left.pow_neg

@[to_additive Right.pow_neg]
theorem Right.pow_lt_one_of_lt [CovariantClass M M (swap (· * ·)) (· < ·)] {n : ℕ} {x : M}
    (hn : 0 < n) (h : x < 1) : x ^ n < 1 :=
  Nat.le_induction ((pow_one _).trans_lt h)
    (fun n _ ih => by
      rw [pow_succ]
      exact Right.mul_lt_one ih h)
    _ (Nat.succ_le_iff.2 hn)
#align right.pow_lt_one_of_lt Right.pow_lt_one_of_lt
#align right.pow_neg Right.pow_neg

end Preorder

section LinearOrder

variable [LinearOrder M]

section CovariantLE

variable [CovariantClass M M (· * ·) (· ≤ ·)]

-- This generalises to lattices. See `pow_two_semiclosed`
@[to_additive nsmul_nonneg_iff]
theorem one_le_pow_iff {x : M} {n : ℕ} (hn : n ≠ 0) : 1 ≤ x ^ n ↔ 1 ≤ x :=
  ⟨le_imp_le_of_lt_imp_lt fun h => pow_lt_one' h hn, fun h => one_le_pow_of_one_le' h n⟩
#align one_le_pow_iff one_le_pow_iff
#align nsmul_nonneg_iff nsmul_nonneg_iff

@[to_additive]
theorem pow_le_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n ≤ 1 ↔ x ≤ 1 :=
  @one_le_pow_iff Mᵒᵈ _ _ _ _ _ hn
#align pow_le_one_iff pow_le_one_iff
#align nsmul_nonpos_iff nsmul_nonpos_iff

@[to_additive nsmul_pos_iff]
theorem one_lt_pow_iff {x : M} {n : ℕ} (hn : n ≠ 0) : 1 < x ^ n ↔ 1 < x :=
  lt_iff_lt_of_le_iff_le (pow_le_one_iff hn)
#align one_lt_pow_iff one_lt_pow_iff
#align nsmul_pos_iff nsmul_pos_iff

@[to_additive]
theorem pow_lt_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n < 1 ↔ x < 1 :=
  lt_iff_lt_of_le_iff_le (one_le_pow_iff hn)
#align pow_lt_one_iff pow_lt_one_iff
#align nsmul_neg_iff nsmul_neg_iff

@[to_additive]
theorem pow_eq_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 := by
  simp only [le_antisymm_iff]
  rw [pow_le_one_iff hn, one_le_pow_iff hn]
#align pow_eq_one_iff pow_eq_one_iff
#align nsmul_eq_zero_iff nsmul_eq_zero_iff

variable [CovariantClass M M (· * ·) (· < ·)] {a : M} {m n : ℕ}

@[to_additive nsmul_le_nsmul_iff_left]
theorem pow_le_pow_iff_right' (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  (pow_right_strictMono' ha).le_iff_le
#align pow_le_pow_iff' pow_le_pow_iff_right'
#align nsmul_le_nsmul_iff nsmul_le_nsmul_iff_left

@[to_additive nsmul_lt_nsmul_iff_left]
theorem pow_lt_pow_iff_right' (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  (pow_right_strictMono' ha).lt_iff_lt
#align pow_lt_pow_iff' pow_lt_pow_iff_right'
#align nsmul_lt_nsmul_iff nsmul_lt_nsmul_iff_left

end CovariantLE

section CovariantLESwap

variable [CovariantClass M M (· * ·) (· ≤ ·)] [CovariantClass M M (swap (· * ·)) (· ≤ ·)]

@[to_additive lt_of_nsmul_lt_nsmul_right]
theorem lt_of_pow_lt_pow_left' {a b : M} (n : ℕ) : a ^ n < b ^ n → a < b :=
  (pow_left_mono _).reflect_lt
#align lt_of_pow_lt_pow' lt_of_pow_lt_pow_left'
#align lt_of_nsmul_lt_nsmul lt_of_nsmul_lt_nsmul_right

@[to_additive min_lt_of_add_lt_two_nsmul]
theorem min_lt_of_mul_lt_sq {a b c : M} (h : a * b < c ^ 2) : min a b < c := by
  simpa using min_lt_max_of_mul_lt_mul (h.trans_eq <| pow_two _)
#align min_lt_of_mul_lt_sq min_lt_of_mul_lt_sq
#align min_lt_of_add_lt_two_nsmul min_lt_of_add_lt_two_nsmul

@[to_additive lt_max_of_two_nsmul_lt_add]
theorem lt_max_of_sq_lt_mul {a b c : M} (h : a ^ 2 < b * c) : a < max b c := by
  simpa using min_lt_max_of_mul_lt_mul ((pow_two _).symm.trans_lt h)
#align lt_max_of_sq_lt_mul lt_max_of_sq_lt_mul
#align lt_max_of_two_nsmul_lt_add lt_max_of_two_nsmul_lt_add

end CovariantLESwap

section CovariantLTSwap

variable [CovariantClass M M (· * ·) (· < ·)] [CovariantClass M M (swap (· * ·)) (· < ·)]

@[to_additive le_of_nsmul_le_nsmul_right]
theorem le_of_pow_le_pow_left' {a b : M} {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ b ^ n → a ≤ b :=
  (pow_left_strictMono hn).le_iff_le.1
#align le_of_pow_le_pow' le_of_pow_le_pow_left'
#align le_of_nsmul_le_nsmul le_of_nsmul_le_nsmul_right

@[to_additive min_le_of_add_le_two_nsmul]
theorem min_le_of_mul_le_sq {a b c : M} (h : a * b ≤ c ^ 2) : min a b ≤ c := by
  simpa using min_le_max_of_mul_le_mul (h.trans_eq <| pow_two _)
#align min_le_of_mul_le_sq min_le_of_mul_le_sq
#align min_le_of_add_le_two_nsmul min_le_of_add_le_two_nsmul

@[to_additive le_max_of_two_nsmul_le_add]
theorem le_max_of_sq_le_mul {a b c : M} (h : a ^ 2 ≤ b * c) : a ≤ max b c := by
  simpa using min_le_max_of_mul_le_mul ((pow_two _).symm.trans_le h)
#align le_max_of_sq_le_mul le_max_of_sq_le_mul
#align le_max_of_two_nsmul_le_add le_max_of_two_nsmul_le_add

end CovariantLTSwap

@[to_additive Left.nsmul_neg_iff]
theorem Left.pow_lt_one_iff' [CovariantClass M M (· * ·) (· < ·)] {n : ℕ} {x : M} (hn : 0 < n) :
    x ^ n < 1 ↔ x < 1 :=
  haveI := covariantClass_le_of_lt M M (· * ·)
  pow_lt_one_iff hn.ne'
#align left.nsmul_neg_iff Left.nsmul_neg_iff

theorem Left.pow_lt_one_iff [CovariantClass M M (· * ·) (· < ·)] {n : ℕ} {x : M} (hn : 0 < n) :
    x ^ n < 1 ↔ x < 1 := Left.pow_lt_one_iff' hn
#align left.pow_lt_one_iff Left.pow_lt_one_iff

@[to_additive]
theorem Right.pow_lt_one_iff [CovariantClass M M (swap (· * ·)) (· < ·)] {n : ℕ} {x : M}
    (hn : 0 < n) : x ^ n < 1 ↔ x < 1 :=
  ⟨fun H =>
    not_le.mp fun k =>
      haveI := covariantClass_le_of_lt M M (swap (· * ·))
      H.not_le <| Right.one_le_pow_of_le k,
    Right.pow_lt_one_of_lt hn⟩
#align right.pow_lt_one_iff Right.pow_lt_one_iff
#align right.nsmul_neg_iff Right.nsmul_neg_iff

end LinearOrder

end Monoid

section DivInvMonoid

variable [DivInvMonoid G] [Preorder G] [CovariantClass G G (· * ·) (· ≤ ·)]

@[to_additive zsmul_nonneg]
theorem one_le_zpow {x : G} (H : 1 ≤ x) {n : ℤ} (hn : 0 ≤ n) : 1 ≤ x ^ n := by
  lift n to ℕ using hn
  rw [zpow_natCast]
  apply one_le_pow_of_one_le' H
#align one_le_zpow one_le_zpow
#align zsmul_nonneg zsmul_nonneg

end DivInvMonoid

/-!
### Deprecated lemmas

Those lemmas have been deprecated on 2023-12-23.
-/

@[deprecated] alias pow_le_pow_of_le_left' := pow_le_pow_left'
@[deprecated] alias nsmul_le_nsmul_of_le_right := nsmul_le_nsmul_right
@[deprecated] alias pow_lt_pow' := pow_lt_pow_right'
@[deprecated] alias nsmul_lt_nsmul := nsmul_lt_nsmul_left
@[deprecated] alias pow_strictMono_left := pow_right_strictMono'
@[deprecated] alias nsmul_strictMono_right := nsmul_left_strictMono
@[deprecated] alias StrictMono.pow_right' := StrictMono.pow_const
@[deprecated] alias StrictMono.nsmul_left := StrictMono.const_nsmul
@[deprecated] alias pow_strictMono_right' := pow_left_strictMono
@[deprecated] alias nsmul_strictMono_left := nsmul_right_strictMono
@[deprecated] alias Monotone.pow_right := Monotone.pow_const
@[deprecated] alias Monotone.nsmul_left := Monotone.const_nsmul
@[deprecated] alias lt_of_pow_lt_pow' := lt_of_pow_lt_pow_left'
@[deprecated] alias lt_of_nsmul_lt_nsmul := lt_of_nsmul_lt_nsmul_right
@[deprecated] alias pow_le_pow' := pow_le_pow_right'
@[deprecated] alias nsmul_le_nsmul := nsmul_le_nsmul_left
@[deprecated] alias pow_le_pow_of_le_one' := pow_le_pow_right_of_le_one'
@[deprecated] alias nsmul_le_nsmul_of_nonpos := nsmul_le_nsmul_left_of_nonpos
@[deprecated] alias le_of_pow_le_pow' := le_of_pow_le_pow_left'
@[deprecated] alias le_of_nsmul_le_nsmul := le_of_nsmul_le_nsmul_right
@[deprecated] alias pow_le_pow_iff' := pow_le_pow_iff_right'
@[deprecated] alias nsmul_le_nsmul_iff := nsmul_le_nsmul_iff_left
@[deprecated] alias pow_lt_pow_iff' := pow_lt_pow_iff_right'
@[deprecated] alias nsmul_lt_nsmul_iff := nsmul_lt_nsmul_iff_left
@[deprecated] alias pow_mono_right := pow_left_mono
@[deprecated] alias nsmul_mono_left := nsmul_right_mono
