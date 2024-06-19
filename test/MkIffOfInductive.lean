import Batteries.Data.List.Basic
import Mathlib.Tactic.MkIffOfInductiveProp
import Mathlib.Data.List.Perm

mk_iff_of_inductive_prop List.Chain test.chain_iff
example {α : Type _} (R : α → α → Prop) (a : α) (al : List α) :
    List.Chain R a al ↔
      al = List.nil ∨ ∃ (b : α) (l : List α), R a b ∧ List.Chain R b l ∧ al = b :: l :=
  test.chain_iff R a al

-- check that the statement prints nicely
/--
info: test.chain_iff.{u_1} {α : Type u_1} (R : α → α → Prop) :
  ∀ (a : α) (a_1 : List α), List.Chain R a a_1 ↔ a_1 = [] ∨ ∃ b l, R a b ∧ List.Chain R b l ∧ a_1 = b :: l
-/
#guard_msgs in
#check test.chain_iff

mk_iff_of_inductive_prop False    test.false_iff
example : False ↔ False := test.false_iff

mk_iff_of_inductive_prop True     test.true_iff
example : True ↔ True := test.true_iff

universe u
mk_iff_of_inductive_prop Nonempty test.non_empty_iff
example (α : Sort u) : Nonempty α ↔ ∃ (_ : α), True := test.non_empty_iff α

mk_iff_of_inductive_prop And      test.and_iff
example (p q : Prop) : And p q ↔ p ∧ q := test.and_iff p q

mk_iff_of_inductive_prop Or       test.or_iff
example (p q : Prop) : Or p q ↔ p ∨ q := test.or_iff p q

mk_iff_of_inductive_prop Eq       test.eq_iff
example (α : Sort u) (a b : α) : a = b ↔ b = a := test.eq_iff a b

mk_iff_of_inductive_prop HEq      test.heq_iff
example {α : Sort u} (a : α) {β : Sort u} (b : β) : HEq a b ↔ β = α ∧ HEq b a := test.heq_iff a b

mk_iff_of_inductive_prop List.Perm test.perm_iff
open scoped List in
example {α : Type _} (a b : List α) :
    a ~ b ↔
      a = List.nil ∧ b = List.nil ∨
        (∃ (x : α) (l₁ l₂ : List α), l₁ ~ l₂ ∧ a = x :: l₁ ∧ b = x :: l₂) ∨
          (∃ (x y : α) (l : List α), a = y :: x :: l ∧ b = x :: y :: l) ∨
            ∃ (l₂ : List α), a ~ l₂ ∧ l₂ ~ b := test.perm_iff a b

mk_iff_of_inductive_prop List.Pairwise test.pairwise_iff
example {α : Type} (R : α → α → Prop) (al : List α) :
    List.Pairwise R al ↔
      al = List.nil ∨
        ∃ (a : α) (l : List α), (∀ (a' : α), a' ∈ l → R a a') ∧ List.Pairwise R l ∧ al = a :: l
 := test.pairwise_iff R al

inductive test.is_true (p : Prop) : Prop
| triviality (h : p) : test.is_true p

mk_iff_of_inductive_prop test.is_true test.is_true_iff
example (p : Prop) : test.is_true p ↔ p := test.is_true_iff p

@[mk_iff]
structure foo (m n : Nat) : Prop where
  equal : m = n
  sum_eq_two : m + n = 2

example (m n : Nat) : foo m n ↔ m = n ∧ m + n = 2 := foo_iff m n

@[mk_iff bar]
structure foo2 (m n : Nat) : Prop where
  equal : m = n
  sum_eq_two : m + n = 2

example (m n : Nat) : foo2 m n ↔ m = n ∧ m + n = 2 := bar m n

@[mk_iff]
inductive ReflTransGen {α : Type _} (r : α → α → Prop) (a : α) : α → Prop
| refl : ReflTransGen r a a
| tail {b c} : ReflTransGen r a b → r b c → ReflTransGen r a c

example {α : Type} (r: α → α → Prop) (a c : α) :
    ReflTransGen r a c ↔ c = a ∨ ∃ b : α, ReflTransGen r a b ∧ r b c :=
 reflTransGen_iff r a c
