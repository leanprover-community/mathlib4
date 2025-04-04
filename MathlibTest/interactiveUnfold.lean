/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib

/-!
The `unfold?` tactic is used interactively, so it is tricky to test directly.
In order to test it, we use the `#unfold?` command.
-/

/--
info: Unfolds for 0:
· ↑0
· ↑0
· Rat.ofInt ↑0
-/
#guard_msgs in
#unfold? (0 : Rat)

/--
info: Unfolds for -42:
· Int.negOfNat 42
· Int.negSucc 41
-/
#guard_msgs in
#unfold? -42

-- Rat.mk is private, so it doesn't show up here
/--
info: Unfolds for 42:
· ↑42
· ↑42
· Rat.ofInt ↑42
-/
#guard_msgs in
#unfold? (42 : ℚ)

/--
info: Unfolds for 1 + 1:
· Nat.add 1 1
· 2
-/
#guard_msgs in
#unfold? 1 + 1

/--
info: Unfolds for 5 / 3:
· Nat.div 5 3
· 1
-/
#guard_msgs in
#unfold? 5 / 3

/--
info: Unfolds for 1 + 1:
· Ordinal.type (Sum.Lex EmptyRelation EmptyRelation)
· ⟦{ α := PUnit.{u_1 + 1} ⊕ PUnit.{u_1 + 1}, r := Sum.Lex EmptyRelation EmptyRelation, wo := ⋯ }⟧
· Quot.mk ⇑Ordinal.isEquivalent
  { α := PUnit.{u_1 + 1} ⊕ PUnit.{u_1 + 1}, r := Sum.Lex EmptyRelation EmptyRelation, wo := ⋯ }
-/
#guard_msgs in
#unfold? (1 : Ordinal) + 1

/--
info: Unfolds for 3 ∈ {1, 2, 3}:
· {1, 2, 3}.Mem 3
· {1, 2, 3} 3
· Set.insert 1 {2, 3} 3
· {b | b = 1 ∨ b ∈ {2, 3}} 3
· 3 = 1 ∨ 3 ∈ {2, 3}
-/
#guard_msgs in
#unfold? 3 ∈ ({1, 2, 3} : Set ℕ)

/--
info: Unfolds for Function.Injective fun x => x:
· ∀ ⦃a₁ a₂ : ℕ⦄, (fun x => x) a₁ = (fun x => x) a₂ → a₁ = a₂
-/
#guard_msgs in
#unfold? Function.Injective (fun x : Nat => x)


variable (A B : Set Nat) (n : Nat)

/--
info: Unfolds for 1 ∈ A ∪ B:
· (A ∪ B).Mem 1
· (A ∪ B) 1
· A.union B 1
· {a | a ∈ A ∨ a ∈ B} 1
· 1 ∈ A ∨ 1 ∈ B
-/
#guard_msgs in
#unfold? 1 ∈ A ∪ B

/--
info: Unfolds for (fun x => x) (1 + 1):
· 1 + 1
· Nat.add 1 1
· 2
-/
#guard_msgs in
#unfold? (fun x => x) (1 + 1)

/--
info: Unfolds for fun x => id x:
· id
· fun a => a
-/
#guard_msgs in
#unfold? fun x => id x
