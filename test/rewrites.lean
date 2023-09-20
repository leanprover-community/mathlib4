import Mathlib.Tactic.Rewrites
import Mathlib.Data.Nat.Prime
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Basic

private axiom test_sorry : ∀ {α}, α
set_option autoImplicit true
set_option pp.unicode.fun true

-- To see the (sorted) list of lemmas that `rw?` will try rewriting by, use:
-- set_option trace.Tactic.rewrites.lemmas true

-- Recall that `rw?` caches the discrimination tree on disk.
-- If you are modifying the way that `rewrites` indexes lemmas,
-- while testing you will probably want to delete
-- `build/lib/MathlibExtras/Rewrites.extra`
-- so that the cache is rebuilt.

set_option autoImplicit true

/--
info: Try this: rw [@List.map_append]
-- "no goals"
-/
#guard_msgs in
example (f : α → β) (L M : List α) : (L ++ M).map f = L.map f ++ M.map f := by
  rw?

open CategoryTheory

/--
info: Try this: rw [@Category.id_comp]
-- "no goals"
-/
#guard_msgs in
example [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ 𝟙 _ ≫ g = f ≫ g := by
  rw?

/--
info: Try this: rw [@mul_left_eq_self]
-- "no goals"
-/
#guard_msgs in
example [Group G] (h : G) : 1 * h = h := by
  rw?

/--
info: Try this: rw [← @Nat.prime_iff]
-- "no goals"
-/
#guard_msgs in
lemma prime_of_prime (n : ℕ) : Prime n ↔ Nat.Prime n := by
  rw?

/--
info: Try this: rw [@mul_one] at hyp
-- g = h
---
info: Try this: rw [← @eq_div_iff_mul_eq'] at hyp
-- g = h / 1
---
info: Try this: rw [← @eq_mul_inv_iff_mul_eq] at hyp
-- g = h * 1⁻¹
---
info: Try this: rw [← @eq_inv_mul_iff_mul_eq] at hyp
-- 1 = g⁻¹ * h
---
info: Try this: rw [← smul_eq_mul] at hyp
-- g • 1 = h
---
info: Try this: rw [← @div_inv_eq_mul] at hyp
-- g / 1⁻¹ = h
---
info: Try this: rw [← @Equiv.divRight_symm_apply] at hyp
-- ↑(Equiv.divRight 1).symm g = h
---
info: Try this: rw [← @inv_one] at hyp
-- g * 1⁻¹ = h
---
info: Try this: rw [← @ofLex_one] at hyp
-- g * ↑ofLex 1 = h
---
info: Try this: rw [← @ofDual_one] at hyp
-- g * ↑OrderDual.ofDual 1 = h
---
info: Try this: rw [← @toMul_zero] at hyp
-- g * ↑Additive.toMul 0 = h
---
info: Try this: rw [← @one_div_one] at hyp
-- g * (1 / 1) = h
---
info: Try this: rw [← @Units.val_one] at hyp
-- g * ↑1 = h
---
info: Try this: rw [← @WithBot.unbot_one] at hyp
-- g * WithBot.unbot 1 _ = h
---
info: Try this: rw [← @WithTop.untop_one] at hyp
-- g * WithTop.untop 1 _ = h
---
info: Try this: rw [← MulOpposite.unop_one] at hyp
-- g * MulOpposite.unop 1 = h
---
info: Try this: rw [← @AddOpposite.unop_one] at hyp
-- g * AddOpposite.unop 1 = h
-/
#guard_msgs in
example [Group G] (h : G) (hyp : g * 1 = h) : g = h := by
  rw? at hyp
  assumption

/--
info: Try this: rw [@Nat.le_iff_lt_or_eq]
-- x < y ∨ x = y
---
info: Try this: rw [@Nat.mul_self_le_mul_self_iff]
-- x * x ≤ y * y
---
info: Try this: rw [@le_iff_eq_or_lt]
-- x = y ∨ x < y
---
info: Try this: rw [@le_iff_exists_add]
-- ∃ c, y = x + c
---
info: Try this: rw [@le_iff_exists_sup]
-- ∃ c, y = x ⊔ c
---
info: Try this: rw [@le_iff_exists_add']
-- ∃ c, y = c + x
---
info: Try this: rw [← @Nat.le_eq]
-- Nat.le x y
---
info: Try this: rw [← @Nat.ble_eq]
-- Nat.ble x y = true
---
info: Try this: rw [← @Nat.not_lt]
-- ¬y < x
---
info: Try this: rw [← @Nat.lt_succ]
-- x < Nat.succ y
---
info: Try this: rw [← @Int.ofNat_le]
-- ↑x ≤ ↑y
---
info: Try this: rw [← Nat.not_gt_eq]
-- ¬x > y
---
info: Try this: rw [← @List.range_subset]
-- List.range x ⊆ List.range y
---
info: Try this: rw [← @Nat.lt_one_add_iff]
-- x < 1 + y
---
info: Try this: rw [← @Nat.lt_add_one_iff]
-- x < y + 1
---
info: Try this: rw [← @List.range_sublist]
-- List.Sublist (List.range x) (List.range y)
---
info: Try this: rw [← @String.Pos.mk_le_mk]
-- { byteIdx := x } ≤ { byteIdx := y }
---
info: Try this: rw [← @Nat.bit0_lt_bit1_iff]
-- bit0 x < bit1 y
---
info: Try this: rw [← @Nat.bit0_le_bit1_iff]
-- bit0 x ≤ bit1 y
---
info: Try this: rw [← @Nat.succ_le_succ_iff]
-- Nat.succ x ≤ Nat.succ y
-/
#guard_msgs in
example : ∀ (x y : ℕ), x ≤ y := by
  intros x y
  rw? -- Used to be an error here https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/panic.20and.20error.20with.20rw.3F/near/370495531
  exact test_sorry

example : ∀ (x y : ℕ), x ≤ y := by
  -- Used to be a panic here https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/panic.20and.20error.20with.20rw.3F/near/370495531
  success_if_fail_with_msg "Could not find any lemmas which can rewrite the goal" rw?
  exact test_sorry

axiom K : Type
@[instance] axiom K.ring : Ring K

noncomputable def foo : K → K := test_sorry

/--
info: Try this: rw [@iff_def]
-- (foo x = 1 → ∃ k, x = ↑k) ∧ ((∃ k, x = ↑k) → foo x = 1)
---
info: Try this: rw [@Iff.comm]
-- (∃ k, x = ↑k) ↔ foo x = 1
---
info: Try this: rw [@iff_def']
-- ((∃ k, x = ↑k) → foo x = 1) ∧ (foo x = 1 → ∃ k, x = ↑k)
---
info: Try this: rw [@iff_eq_eq]
-- (foo x = 1) = ∃ k, x = ↑k
---
info: Try this: rw [@iff_iff_not_or_and_or_not]
-- (¬foo x = 1 ∨ ∃ k, x = ↑k) ∧ (foo x = 1 ∨ ¬∃ k, x = ↑k)
---
info: Try this: rw [@iff_iff_and_or_not_and_not]
-- (foo x = 1 ∧ ∃ k, x = ↑k) ∨ ¬foo x = 1 ∧ ¬∃ k, x = ↑k
---
info: Try this: rw [← @ofMul_eq_zero]
-- ↑Additive.ofMul (foo x) = 0 ↔ ∃ k, x = ↑k
---
info: Try this: rw [← @WithTop.coe_eq_one]
-- ↑(foo x) = 1 ↔ ∃ k, x = ↑k
---
info: Try this: rw [← @WithTop.one_eq_coe]
-- 1 = ↑(foo x) ↔ ∃ k, x = ↑k
---
info: Try this: rw [← @AddOpposite.op_eq_one_iff]
-- AddOpposite.op (foo x) = 1 ↔ ∃ k, x = ↑k
---
info: Try this: rw [← @MulOpposite.op_eq_one_iff]
-- MulOpposite.op (foo x) = 1 ↔ ∃ k, x = ↑k
---
info: Try this: rw [← @ofLex_one]
-- foo x = ↑ofLex 1 ↔ ∃ k, x = ↑k
---
info: Try this: rw [← @bit1_zero]
-- foo x = bit1 0 ↔ ∃ k, x = ↑k
---
info: Try this: rw [← @ofDual_one]
-- foo x = ↑OrderDual.ofDual 1 ↔ ∃ k, x = ↑k
---
info: Try this: rw [← @toMul_zero]
-- foo x = ↑Additive.toMul 0 ↔ ∃ k, x = ↑k
---
info: Try this: rw [← @neg_one_sq]
-- foo x = (-1) ^ 2 ↔ ∃ k, x = ↑k
---
info: Try this: rw [← @Int.cast_one]
-- foo x = ↑1 ↔ ∃ k, x = ↑k
---
info: Try this: rw [← Ring.inverse_one]
-- foo x = Ring.inverse 1 ↔ ∃ k, x = ↑k
---
info: Try this: rw [← @WithBot.unbot_one]
-- foo x = WithBot.unbot 1 _ ↔ ∃ k, x = ↑k
---
info: Try this: rw [← @WithTop.untop_one]
-- foo x = WithTop.untop 1 _ ↔ ∃ k, x = ↑k
-/
#guard_msgs in
example : foo x = 1 ↔ ∃ k : ℤ, x = k := by
  rw? -- Used to panic, see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/panic.20and.20error.20with.20rw.3F/near/370598036
  exact test_sorry

lemma six_eq_seven : 6 = 7 := test_sorry

-- This test also verifies that we are removing duplicate results;
-- it previously also reported `Nat.cast_ofNat`
/--
info: Try this: rw [six_eq_seven]
-- ∀ (x : ℕ), x ≤ 7
---
info: Try this: rw [← @Nat.cast_eq_ofNat]
-- ∀ (x : ℕ), x ≤ ↑6
-/
#guard_msgs in
example : ∀ (x : ℕ), x ≤ 6 := by
  rw?
  guard_target = ∀ (x : ℕ), x ≤ 7
  exact test_sorry

/--
info: Try this: rw [six_eq_seven]
-- ∀ (x : ℕ), x ≤ 7 → x ≤ 8
---
info: Try this: rw [← @Nat.cast_eq_ofNat]
-- ∀ (x : ℕ), x ≤ ↑6 → x ≤ 8
-/
#guard_msgs in
example : ∀ (x : ℕ) (_w : x ≤ 6), x ≤ 8 := by
  rw?
  guard_target = ∀ (x : ℕ) (_w : x ≤ 7), x ≤ 8
  exact test_sorry

-- check we can look inside let expressions
/-- info: Try this: rw [@AddCommMonoidWithOne.add_comm]
-- "no goals"
-/
#guard_msgs in
example (n : ℕ) : let y := 3; n + y = 3 + n := by
  rw?

axiom α : Type
axiom f : α → α
axiom z : α
axiom f_eq (n) : f n = z

-- Check that the same lemma isn't used multiple times.
-- This used to report two redundant copies of `f_eq`.
-- It be lovely if `rw?` could produce two *different* rewrites by `f_eq` here!
/-- info: Try this: rw [f_eq]
-- z = f m
-/
#guard_msgs in
lemma test : f n = f m := by
  rw?
  rw [f_eq]

-- Check that we can rewrite by local hypotheses.
/-- info: Try this: rw [h]
-- "no goals"
-/
#guard_msgs in
example (h : 1 = 2) : 2 = 1 := by
  rw?

def zero : Nat := 0

-- This used to (incorrectly!) succeed because `rw?` would try `rfl`,
-- rather than `withReducible` `rfl`.
/--
info: Try this: rw [@Nat.le_antisymm_iff]
-- zero ≤ 0 ∧ 0 ≤ zero
---
info: Try this: rw [← @Nat.le_zero]
-- zero ≤ 0
---
info: Try this: rw [← @Nat.lt_one_iff]
-- zero < 1
---
info: Try this: rw [← @Nat.one_eq_bit1]
-- 1 = bit1 zero
---
info: Try this: rw [← @Nat.bit1_eq_one]
-- bit1 zero = 1
---
info: Try this: rw [← @Nat.bit0_eq_zero]
-- bit0 zero = 0
---
info: Try this: rw [← @Nat.size_eq_zero]
-- Nat.size zero = 0
---
info: Try this: rw [← @Nat.sqrt_eq_zero]
-- Nat.sqrt zero = 0
---
info: Try this: rw [← @List.range_eq_nil]
-- List.range zero = []
---
info: Try this: rw [← @Int.ofNat_eq_zero]
-- ↑zero = 0
---
info: Try this: rw [← @Nat.pred_eq_self_iff]
-- Nat.pred zero = zero
---
info: Try this: rw [← @Int.coe_nat_nonpos_iff]
-- ↑zero ≤ 0
---
info: Try this: rw [← @Nat.beq_eq]
-- Nat.beq zero 0 = true
---
info: Try this: rw [← @Nat.bit0_eq_bit0]
-- bit0 zero = bit0 0
---
info: Try this: rw [← @Nat.bit1_eq_bit1]
-- bit1 zero = bit1 0
---
info: Try this: rw [← Nat.beq_eq_true_eq]
-- (zero == 0) = true
---
info: Try this: rw [← @Nat.dvd_left_iff_eq]
-- ∀ (a : ℕ), a ∣ zero ↔ a ∣ 0
---
info: Try this: rw [← @Nat.dvd_right_iff_eq]
-- ∀ (a : ℕ), zero ∣ a ↔ 0 ∣ a
---
info: Try this: rw [← Int.cast_eq_cast_iff_Nat]
-- ↑zero = ↑0
---
info: Try this: rw [← @not_neZero]
-- ¬NeZero zero
-/
#guard_msgs in
example : zero = 0 := by
  rw?
  exact test_sorry
