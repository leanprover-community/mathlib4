import Mathlib

/-- info: No unfolds found for 42 -/
#guard_msgs in
#unfold? 42

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
· NatCast.natCast 42
· Rat.ofInt ↑42
-/
#guard_msgs in
#unfold? (42 : Rat)

/--
info: Unfolds for 42:
· ↑42
· NatCast.natCast 42
· { cauchy := ↑42 }
-/
#guard_msgs in
#unfold? (42 : Real)

variable (n : Nat)

/--
info: Unfolds for n ∈ {n}:
· Set.Mem n {n}
· {n} n
· Set.singleton n n
· {b | b = n} n
· n = n
-/
#guard_msgs in
#unfold? n ∈ ({n} : Set Nat)
variable (A B : Set Nat)
/--
info: Unfolds for n ∈ A ∪ B:
· Set.Mem n (A ∪ B)
· (A ∪ B) n
· Set.union A B n
· {a | a ∈ A ∨ a ∈ B} n
· n ∈ A ∨ n ∈ B
-/
#guard_msgs in
#unfold? n ∈ A ∪ B


/--
info: Pattern n + 1
· Nat.succ n
  Nat.add_one
· ack 0 n
  ack_zero
· (Finset.Iic n).card
  Nat.card_Iic
· Nat.size (2 ^ n)
  Nat.size_pow
· Fintype.card ↑(Set.Iic n)
  Nat.card_fintypeIic
· Nat.multichoose 2 n
  Nat.multichoose_two
· Int.toNat (↑n + 1)
  Int.toNat_ofNat_add_one
· Nat.choose (n + 1) n
  Nat.choose_succ_self_right
· (Finset.antidiagonal n).card
  Finset.Nat.card_antidiagonal
· List.length (List.Nat.antidiagonal n)
  List.Nat.length_antidiagonal
· Multiset.card (Multiset.Nat.antidiagonal n)
  Multiset.Nat.card_antidiagonal
· (ArithmeticFunction.sigma 0) (?p ^ n)
  ⊢ Nat.Prime ?p
  ArithmeticFunction.sigma_zero_apply_prime_pow

Pattern x + 1
· Finset.sum (Finset.range 2) fun i => n ^ i
  geom_sum_two
· ComplexShape.prev (ComplexShape.down ℕ) n
  ChainComplex.prev
· ComplexShape.next (ComplexShape.up ℕ) n
  CochainComplex.next

Pattern n + m
· 1 + n
  Nat.add_comm
· Nat.add n 1
  Nat.add_eq
· Nat.succ^[1] n
  Nat.succ_iterate
· n + Nat.succ 1 - 1
  Nat.add_succ_sub_one
· Nat.succ n + 1 - 1
  Nat.succ_add_sub_one
· List.nthLe (List.range' n ?m) 1 ?H
  ⊢ 1 < List.length (List.range' n ?m)
  List.nthLe_range'_1

Pattern a + b
· 1 + n
  add_comm
· n +ᵥ 1
  vadd_eq_add
· AddOpposite.op 1 +ᵥ n
  op_vadd_eq_add
· Multiset.sum {n, 1}
  Multiset.sum_pair
· max n 1 + min n 1
  max_add_min
· min n 1 + max n 1
  min_add_max
· (addLeftEmbedding n) 1
  addLeftEmbedding_apply
· (addRightEmbedding 1) n
  addRightEmbedding_apply
· ?y + n
  ⊢ AddSemiconjBy n 1 ?y
  AddSemiconjBy.eq
· (OrderEmbedding.addLeft n) 1
  OrderEmbedding.addLeft_apply
· (OrderEmbedding.addRight 1) n
  OrderEmbedding.addRight_apply
· ?a + n - (?a - 1)
  ⊢ 1 ≤ ?a
  add_tsub_tsub_cancel
· ?a + n - (?a - 1)
  ⊢ AddLECancellable (?a - 1)
  ⊢ 1 ≤ ?a
  AddLECancellable.add_tsub_tsub_cancel
-/
#guard_msgs in
#rw?? n+1

/--
info: Pattern n / 2
· Nat.div2 n
  Nat.div2_val

Pattern x / y
· if 0 < 2 ∧ 2 ≤ n then (n - 2) / 2 + 1 else 0
  Nat.div_eq
· (n - n % 2) / 2
  Nat.div_eq_sub_mod_div
· bit0 n / bit0 2
  Nat.bit0_div_bit0
· bit1 n / bit0 2
  Nat.bit1_div_bit0
· (Finset.filter (fun e => 2 ∣ e + 1) (Finset.range n)).card
  Nat.card_multiples
· (Finset.filter (fun k => k ≠ 0 ∧ 2 ∣ k) (Finset.range (Nat.succ n))).card
  Nat.card_multiples'
· n ⌊/⌋ 2
  Nat.floorDiv_eq_div
· (Finset.filter (fun x => 2 ∣ x) (Finset.Ioc 0 n)).card
  Nat.Ioc_filter_dvd_card_eq_div
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
· ?m * n / (?m * 2)
  ⊢ 0 < ?m
  Nat.mul_div_mul_left
· n * ?m / (2 * ?m)
  ⊢ 0 < ?m
  Nat.mul_div_mul_right
· (Finset.filter (fun x => x * 2 ≤ n) (Finset.Ico 1 (Nat.succ ?c))).card
  ⊢ 0 < 2
  ⊢ n / 2 ≤ ?c
  ZMod.div_eq_filter_card
· n / (2 / ?b) / ?b
  ⊢ ?b ∣ 2
  ⊢ 2 ∣ n
  Nat.div_div_div_eq_div
-/
#guard_msgs in
#rw?? n/2
