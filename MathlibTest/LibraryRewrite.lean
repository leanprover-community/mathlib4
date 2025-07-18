import Mathlib.Tactic.Widget.LibraryRewrite
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Subtype
import Batteries.Data.Nat.Gcd

-- set_option trace.profiler true
-- set_option trace.rw?? true

variable (n : Nat) (p q : Prop)

/--
info: Pattern ∀ (p : P), P → Q p
· p → q
  forall_self_imp

Pattern a → b → c
· p ∧ p → q
  and_imp

Pattern ∀ (x : α), p x → b
· (∃ x, p) → q
  exists_imp

Pattern ∀ (x : α) (h : p x), q x h
· ∀ (x : { a // p }), q
  Subtype.forall'

Pattern a → b
· ¬p ∨ (p → q)
  imp_iff_not_or
· (p → q) ∨ ¬p
  imp_iff_or_not
· ¬(p → q) → ¬p
  not_imp_not
· p → q ↔ p ∨ (p → q)
  iff_or_self
· p → q ↔ (p → q) ∨ p
  iff_self_or
· p ↔ (p → q) ∧ p
  iff_and_self
· p ↔ p ∧ (p → q)
  iff_self_and
· Nonempty p → p → q
  Nonempty.imp
· ¬(p ∧ ¬(p → q))
  not_and_not_right
· (p → q) ∨ p ↔ p → q
  or_iff_left_iff_imp
· p ∧ (p → q) ↔ p
  and_iff_left_iff_imp
· spred(p → p → q)
  Std.Do.SPred.imp_nil
· p ∨ (p → q) ↔ p → q
  or_iff_right_iff_imp
· (p → q) ∧ p ↔ p
  and_iff_right_iff_imp
· p ⊢ₛ p → q
  Std.Do.SPred.entails_nil
· ¬p
  ⊢ ¬(p → q)
  imp_iff_not
· p → q
  ⊢ p
  imp_iff_right

Pattern ∀ (p : P), Q p
· p → p → p → q
  forall_self_imp
· spred(∀ a, p → q)
  Std.Do.SPred.forall_nil
· ¬∃ x, ¬(p → q)
  Classical.not_exists_not
· True
  ⊢ p → (p → q ↔ True)
  forall_true_iff'
· p → q
  ⊢ p
  forall_prop_of_true
-/
#guard_msgs in
#rw?? p → p → q

/--
info: Pattern n + 1
· n.succ
  Nat.add_one
· Std.PRange.UpwardEnumerable.succ n
  Std.PRange.Nat.succ_eq
· (↑n + 1).toNat
  Int.toNat_natCast_add_one

Pattern n + m
· 1 + n
  Nat.add_comm
· n.add 1
  Nat.add_eq
· n.succ + 1 - 1
  Nat.succ_add_sub_one
· n + Nat.succ 1 - 1
  Nat.add_succ_sub_one
· max (n + 1) 1
  Nat.add_left_max_self
· max 1 (n + 1)
  Nat.max_add_left_self
· max (n + 1) n
  Nat.add_right_max_self
· max n (n + 1)
  Nat.max_add_right_self

Pattern a + b
· 1 + n
  add_comm
-/
#guard_msgs in
#rw?? n + 1

/--
info: Pattern n / 2
· n >>> 1
  Nat.shiftRight_one

Pattern x / y
· if 0 < 2 ∧ 2 ≤ n then (n - 2) / 2 + 1 else 0
  Nat.div_eq
· (n - n % 2) / 2
  Nat.div_eq_sub_mod_div
· 0
  ⊢ n < 2
  Nat.div_eq_of_lt
· (n + 1) / 2
  ⊢ ¬2 ∣ n + 1
  Nat.succ_div_of_not_dvd
· (n - 2) / 2 + 1
  ⊢ 0 < 2
  ⊢ 2 ≤ n
  Nat.div_eq_sub_div
-/
#guard_msgs in
#rw?? n/2

/--
info: Pattern n.gcd n
· n
  Nat.gcd_self

Pattern m.gcd n
· (n % n).gcd n
  Nat.gcd_rec
· if n = 0 then n else (n % n).gcd n
  Nat.gcd_def
· (n + n).gcd n
  Nat.gcd_add_self_left
· n.gcd (n + n)
  Nat.gcd_add_self_right
· (↑n).gcd ↑n
  Int.gcd_natCast_natCast
· (n.gcd n).gcd n
  Nat.gcd_gcd_self_left_left
· n.gcd (n.gcd n)
  Nat.gcd_gcd_self_right_left
· n
  ⊢ n ∣ n
  Nat.gcd_eq_left
· 1
  ⊢ n.Coprime n
  Nat.Coprime.gcd_eq_one
· (n - n).gcd n
  ⊢ n ≤ n
  Nat.gcd_self_sub_left
· n.gcd (n - n)
  ⊢ n ≤ n
  Nat.gcd_self_sub_right
-/
#guard_msgs in
#rw?? Nat.gcd n n

def atZero (f : Int → Int) : Int := f 0

theorem atZero_neg (f : Int → Int) : atZero (fun x => - f x) = - atZero f := rfl
theorem neg_atZero_neg (f : Int → Int) : - atZero (fun x => - f x) = atZero f := Int.neg_neg (f 0)

theorem atZero_add (f g : Int → Int) : atZero (fun x => f x + g x) = atZero f + atZero g := rfl
theorem atZero_add_const (f : Int → Int) (c : Int) : atZero (fun x => f x + c) = atZero f + c := rfl

/--
info: Pattern atZero fun x => f x + c
· (atZero fun x => x) + 1
  atZero_add_const

Pattern atZero fun x => f x + g x
· (atZero fun x => x) + atZero fun x => 1
  atZero_add

Pattern atZero f
· -atZero fun x => -(x + 1)
  neg_atZero_neg
-/
#guard_msgs in
#rw?? atZero fun x => x + 1
/--
info: Pattern atZero fun x => -f x
· -atZero fun x => x
  atZero_neg

Pattern atZero f
· -atZero fun x => - -x
  neg_atZero_neg
-/
#guard_msgs in
#rw?? atZero (Neg.neg : Int → Int)

-- `Nat.Coprime` is reducible, so we might get matches with the pattern `n = 1`.
-- This doesn't work with the `rw` tactic though, so we make sure to avoid them.
/--
info: Pattern n.Coprime m
· Nat.Coprime 3 2
  Nat.coprime_comm
· Nat.gcd 2 3 = 1
  Nat.coprime_iff_gcd_eq_one
-/
#guard_msgs in
#rw?? Nat.Coprime 2 3
