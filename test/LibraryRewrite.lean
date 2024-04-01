import Mathlib
set_option profiler true
set_option profiler.threshold 20

#rw?? 42+90
#check HasSum.update'
#synth T3Space ℂ


open Qq Lean Meta
run_meta
  let e := q(T3Space ℂ)
  let x ← synthInstance? e
  logInfo m! "{e}"
/--
info: Unfolds for -42:
· Int.negOfNat 42
· Int.negSucc 41
-/
#guard_msgs in
#rw?? -42

-- Rat.mk is private, so it doesn't show up here
/--
info: Unfolds for 42:
· ↑42
· NatCast.natCast 42
· Rat.ofInt ↑42
-/
#guard_msgs in
#rw?? (42 : Rat)

/--
info: Unfolds for 42:
· ↑42
· NatCast.natCast 42
· { cauchy := ↑42 }
-/
#guard_msgs in
#rw?? (42 : Real)

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
#rw?? n ∈ ({n} : Set Nat)
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
#rw?? n ∈ A ∪ B


/--
info: discrimination tree lookup took 3ms
---
info: checking the candidates took 131ms
---
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
info: discrimination tree lookup took 4ms
---
info: checking the candidates took 98ms
---
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

open BigOperators

/--
info: discrimination tree lookup took 5ms
---
info: checking the candidates took 159ms
---
info: Pattern ∑ x in s, (f x + g x)
· ∑ x in Finset.range n, x + ∑ x in Finset.range n, 1
  Finset.sum_add_distrib

Pattern ∑ i in Finset.range n, f i
· ∑ i : Fin n, (↑i + 1)
  Finset.sum_range
· ∑ j in Finset.range n, (n - 1 - j + 1)
  Finset.sum_range_reflect
· ∑ k in Finset.range ?m, (k + 1) + ∑ k in Finset.Ico ?m n, (k + 1)
  ⊢ ?m ≤ n
  Finset.sum_range_add_sum_Ico
· ?s n
  ⊢ ℕ → ℕ
  ⊢ ?s 0 = 0
  ⊢ ∀ (n : ℕ), ?s (n + 1) = ?s n + (n + 1)
  Finset.sum_range_induction
· ∑ k in Finset.range ?N, (k + 1)
  ⊢ ∀ n ≥ ?N, n + 1 = 0
  ⊢ ?N ≤ n
  Finset.eventually_constant_sum

Pattern ∑ x in s, f x
· (Finset.range n).card * ?m
  ⊢ ∀ x ∈ Finset.range n, x + 1 = ?m
  Finset.sum_const_nat

Pattern ∑ x in s, f x
· Finset.fold (fun x x_1 => x + x_1) 0 (fun x => x + 1) (Finset.range n)
  Finset.sum_eq_fold
· Multiset.sum (Multiset.map (fun x => x + 1) (Finset.range n).val)
  Finset.sum_eq_multiset_sum
· ∑ x in Finset.attach (Finset.range n), (↑x + 1)
  Finset.sum_attach
· List.sum (List.map (fun n => n + 1) (Finset.toList (Finset.range n)))
  Finset.sum_to_list
· ∑ i : { x // x ∈ Finset.range n }, (↑i + 1)
  Finset.sum_coe_sort
· ∑ᶠ (i : ℕ) (_ : i ∈ ↑(Finset.range n)), (i + 1)
  finsum_mem_coe_finset
· ∑ i : ↑↑(Finset.range n), (↑i + 1)
  Finset.sum_finset_coe
· ∑ᶠ (i : ℕ) (_ : i ∈ Finset.range n), (i + 1)
  finsum_mem_finset_eq_sum
· Finset.noncommSum (Finset.range n) (fun n => n + 1) ⋯
  Finset.noncommSum_eq_sum
· 0
  ⊢ ∀ x ∈ Finset.range n, x + 1 = 0
  Finset.sum_eq_zero
· ∑' (x : ℕ), Set.indicator (↑(Finset.range n)) (fun x => x + 1) x
  sum_eq_tsum_indicator
· ∑' (x : { x // x ∈ Finset.range n }), (↑x + 1)
  Finset.tsum_subtype
· ∑' (x : ↑↑(Finset.range n)), (↑x + 1)
  Finset.tsum_subtype'
· ∑ i in Finset.range n, if i ∈ Finset.range n then i + 1 else 0
  Finset.sum_extend_by_zero
· ∑ x in Finset.filter (fun x => x + 1 ≠ 0) (Finset.range n), (x + 1)
  Finset.sum_filter_ne_zero
· ∑ᶠ (i : ℕ), (i + 1)
  ⊢ (Function.support fun i => i + 1) ⊆ ↑(Finset.range n)
  finsum_eq_sum_of_support_subset
· (Finset.range n).card • ?b
  ⊢ ∀ a ∈ Finset.range n, a + 1 = ?b
  Finset.sum_eq_card_nsmul
· ∑' (b : ℕ), (b + 1)
  ⊢ ∀ b ∉ Finset.range n, b + 1 = 0
  tsum_eq_sum
· Finset.sum (Finset.range n) (fun c => HAdd.hAdd c) 1
  Finset.sum_apply
· ∑ x in Finset.range n, (?σ x + 1)
  ⊢ Equiv.Perm ℕ
  ⊢ {a | ?σ a ≠ a} ⊆ ↑(Finset.range n)
  Equiv.Perm.sum_comp
· ∑ i in ?t, Set.indicator (↑(Finset.range n)) (fun i => i + 1) i
  ⊢ Finset.range n ⊆ ?t
  Finset.sum_indicator_subset
· ∑ x in Finset.range n ∩ ?t, (x + 1) + ∑ x in Finset.range n \ ?t, (x + 1)
  ⊢ Finset ℕ
  Finset.sum_inter_add_sum_diff
· ∑ᶠ (i : ℕ) (_ : ?p i), (i + 1)
  ⊢ ∀ {x : ℕ}, x + 1 ≠ 0 → (?p x ↔ x ∈ Finset.range n)
  finsum_cond_eq_sum_of_cond_iff
· ∑ᶠ (i : ℕ) (_ : i ∈ ?s), (i + 1)
  ⊢ (?s ∩ Function.support fun i => i + 1) = ↑(Finset.range n) ∩ Function.support fun i => i + 1
  finsum_mem_eq_sum_of_inter_support_eq
· ∑ x in ?s₂, (x + 1)
  ⊢ Finset.range n ⊆ ?s₂
  ⊢ ∀ x ∈ ?s₂, x ∉ Finset.range n → x + 1 = 0
  Finset.sum_subset
· ∑ a : Subtype ?p, (↑a + 1)
  ⊢ ∀ (x : ℕ), x ∈ Finset.range n ↔ ?p x
  Finset.sum_subtype
· ?a + 1
  ⊢ ℕ
  ⊢ ∀ b ∈ Finset.range n, b ≠ ?a → b + 1 = 0
  ⊢ ?a ∉ Finset.range n → ?a + 1 = 0
  Finset.sum_eq_single
· ?a + 1
  ⊢ ℕ
  ⊢ ?a ∈ Finset.range n
  ⊢ ∀ b ∈ Finset.range n, b ≠ ?a → b + 1 = 0
  Finset.sum_eq_single_of_mem
· ?i + 1 + ∑ x in Finset.range n \ {?i}, (x + 1)
  ⊢ ?i ∈ Finset.range n
  Finset.sum_eq_add_sum_diff_singleton
· ∑ x in Finset.range n \ {?i}, (x + 1) + (?i + 1)
  ⊢ ?i ∈ Finset.range n
  Finset.sum_eq_sum_diff_singleton_add
· ∑ x in Finset.erase (Finset.range n) ?a, (x + 1)
  ⊢ ?a + 1 = 0
  Finset.sum_erase
· ∑ x in Finset.range n \ ?s₁, (x + 1) + ∑ x in ?s₁, (x + 1)
  ⊢ ?s₁ ⊆ Finset.range n
  Finset.sum_sdiff
· ?a + 1 + ∑ x in Finset.erase (Finset.range n) ?a, (x + 1)
  ⊢ ?a ∈ Finset.range n
  Finset.add_sum_erase
· ∑ x in Finset.erase (Finset.range n) ?a, (x + 1) + (?a + 1)
  ⊢ ?a ∈ Finset.range n
  Finset.sum_erase_add
· ∑ x in insert ?a (Finset.range n), (x + 1)
  ⊢ ?a + 1 = 0
  Finset.sum_insert_zero
· ∑ a in Finset.range n ∪ ?s₂, (a + 1)
  ⊢ ∀ a ∈ ?s₂, a ∉ Finset.range n → a + 1 = 0
  Finset.sum_union_eq_left
· ∑ a in ?s₁ ∪ Finset.range n, (a + 1)
  ⊢ ∀ a ∈ ?s₁, a ∉ Finset.range n → a + 1 = 0
  Finset.sum_union_eq_right
· ∑ x in Finset.preimage (Finset.range n) ?f ⋯, (?f x + 1)
  ⊢ ?α → ℕ
  ⊢ Set.BijOn ?f (?f ⁻¹' ↑(Finset.range n)) ↑(Finset.range n)
  Finset.sum_preimage_of_bij
· ∑ᶠ (i : ℕ) (_ : i ∈ ?s), (i + 1)
  ⊢ (?s ∩ Function.support fun i => i + 1) ⊆ ↑(Finset.range n)
  ⊢ ↑(Finset.range n) ⊆ ?s
  finsum_mem_eq_sum_of_subset
· ∑ x in insert ?a (Finset.range n), (x + 1)
  ⊢ ?a ∉ Finset.range n → ?a + 1 = 0
  Finset.sum_insert_of_eq_zero_if_not_mem
· Finset.sum ?s₂ ?g
  ⊢ Finset.range n = ?s₂
  ⊢ ∀ x ∈ ?s₂, x + 1 = ?g x
  Finset.sum_congr
· ∑ x in Finset.preimage (Finset.range n) ?f ?hf, (?f x + 1)
  ⊢ ?α → ℕ
  ⊢ Set.InjOn ?f (?f ⁻¹' ↑(Finset.range n))
  ⊢ ∀ x ∈ Finset.range n, x ∉ Set.range ?f → x + 1 = 0
  Finset.sum_preimage
· ∑ x in Finset.range n, if ?p x then x + 1 else ?g x
  ⊢ ℕ → ℕ
  ⊢ ∀ x ∈ Finset.range n, ?p x
  Finset.sum_ite_of_true
· ∑ x in Finset.range n, if ?p x then ?f x else x + 1
  ⊢ ℕ → ℕ
  ⊢ ∀ x ∈ Finset.range n, ¬?p x
  Finset.sum_ite_of_false
· Finsupp.sum (Finsupp.indicator (Finset.range n) fun x x => 1) fun x => HAdd.hAdd x
  ⊢ ∀ a ∈ Finset.range n, a + 0 = 0
  Finsupp.sum_indicator_index
· ∑ x in Finset.range n, Function.update (fun x => x + 1) ?i ?b x
  ⊢ ?i ∉ Finset.range n
  ⊢ ℕ
  Finset.sum_update_of_not_mem
· Finsupp.sum (Finsupp.onFinset (Finset.range n) (fun a => 1) ?hf) fun a => HAdd.hAdd a
  ⊢ ∀ (a : ℕ), 1 ≠ 0 → a ∈ Finset.range n
  ⊢ ∀ (a : ℕ), a + 0 = 0
  Finsupp.onFinset_sum
· ∑ i in ?t, ?g i
  ⊢ ℕ ≃ ?κ
  ⊢ ∀ (i : ℕ), i ∈ Finset.range n ↔ ?e i ∈ ?t
  ⊢ ∀ i ∈ Finset.range n, i + 1 = ?g (?e i)
  Finset.sum_equiv
· ?a + 1 + (?b + 1)
  ⊢ ℕ
  ⊢ ℕ
  ⊢ ?a ≠ ?b
  ⊢ ∀ c ∈ Finset.range n, c ≠ ?a ∧ c ≠ ?b → c + 1 = 0
  ⊢ ?a ∉ Finset.range n → ?a + 1 = 0
  ⊢ ?b ∉ Finset.range n → ?b + 1 = 0
  Finset.sum_eq_add
· ?a + 1 + (?b + 1)
  ⊢ ℕ
  ⊢ ℕ
  ⊢ ?a ∈ Finset.range n
  ⊢ ?b ∈ Finset.range n
  ⊢ ?a ≠ ?b
  ⊢ ∀ c ∈ Finset.range n, c ≠ ?a ∧ c ≠ ?b → c + 1 = 0
  Finset.sum_eq_add_of_mem
· ∑ i in ?s₂, ?g i
  ⊢ Finset.range n ⊆ ?s₂
  ⊢ ∀ x ∈ ?s₂ \ Finset.range n, ?g x = 0
  ⊢ ∀ x ∈ Finset.range n, x + 1 = ?g x
  Finset.sum_subset_zero_on_sdiff
· ∑ i in ?t, (i + Set.indicator (↑(Finset.range n)) (fun i => 1) i)
  ⊢ Finset.range n ⊆ ?t
  ⊢ ∀ (a : ℕ), a + 0 = 0
  Finset.sum_indicator_subset_of_eq_zero
· ∑ i in ?t, ?g i
  ⊢ ℕ → ?κ
  ⊢ Function.Bijective ?e
  ⊢ ∀ (i : ℕ), i ∈ Finset.range n ↔ ?e i ∈ ?t
  ⊢ ∀ i ∈ Finset.range n, i + 1 = ?g (?e i)
  Finset.sum_bijective
· ∑ x in ?t, ?g x
  ⊢ (a : ℕ) → a ∈ Finset.range n → ?κ
  ⊢ ∀ (a : ℕ) (ha : a ∈ Finset.range n), ?i a ha ∈ ?t
  ⊢ ∀ (a₁ : ℕ) (ha₁ : a₁ ∈ Finset.range n) (a₂ : ℕ) (ha₂ : a₂ ∈ Finset.range n), ?i a₁ ha₁ = ?i a₂ ha₂ → a₁ = a₂
  ⊢ ∀ b ∈ ?t, ∃ a, ∃ (ha : a ∈ Finset.range n), ?i a ha = b
  ⊢ ∀ (a : ℕ) (ha : a ∈ Finset.range n), a + 1 = ?g (?i a ha)
  Finset.sum_bij
· ∑ x in ?t, ?g x
  ⊢ ℕ → ?κ
  ⊢ ∀ a ∈ Finset.range n, ?i a ∈ ?t
  ⊢ Set.InjOn ?i ↑(Finset.range n)
  ⊢ Set.SurjOn ?i ↑(Finset.range n) ↑?t
  ⊢ ∀ a ∈ Finset.range n, a + 1 = ?g (?i a)
  Finset.sum_nbij
· ∑ j in ?t, ?g j
  ⊢ ℕ → ?κ
  ⊢ Set.InjOn ?e ↑(Finset.range n)
  ⊢ Set.MapsTo ?e ↑(Finset.range n) ↑?t
  ⊢ ∀ i ∈ ?t, i ∉ ?e '' ↑(Finset.range n) → ?g i = 0
  ⊢ ∀ i ∈ Finset.range n, i + 1 = ?g (?e i)
  Finset.sum_of_injOn
· ∑ x in ?t, ?g x
  ⊢ (a : ℕ) → a ∈ Finset.range n → a + 1 ≠ 0 → ?γ
  ⊢ ∀ (a : ℕ) (h₁ : a ∈ Finset.range n) (h₂ : a + 1 ≠ 0), ?i a h₁ h₂ ∈ ?t
  ⊢ ∀ (a₁ : ℕ) (h₁₁ : a₁ ∈ Finset.range n) (h₁₂ : a₁ + 1 ≠ 0) (a₂ : ℕ) (h₂₁ : a₂ ∈ Finset.range n) (h₂₂ : a₂ + 1 ≠ 0),
    ?i a₁ h₁₁ h₁₂ = ?i a₂ h₂₁ h₂₂ → a₁ = a₂
  ⊢ ∀ b ∈ ?t, ?g b ≠ 0 → ∃ a, ∃ (h₁ : a ∈ Finset.range n) (h₂ : a + 1 ≠ 0), ?i a h₁ h₂ = b
  ⊢ ∀ (a : ℕ) (h₁ : a ∈ Finset.range n) (h₂ : a + 1 ≠ 0), a + 1 = ?g (?i a h₁ h₂)
  Finset.sum_bij_ne_zero
· ∑ x in ?t, ?g x
  ⊢ (a : ℕ) → a ∈ Finset.range n → ?κ
  ⊢ (a : ?κ) → a ∈ ?t → ℕ
  ⊢ ∀ (a : ℕ) (ha : a ∈ Finset.range n), ?i a ha ∈ ?t
  ⊢ ∀ (a : ?κ) (ha : a ∈ ?t), ?j a ha ∈ Finset.range n
  ⊢ ∀ (a : ℕ) (ha : a ∈ Finset.range n), ?j (?i a ha) ⋯ = a
  ⊢ ∀ (a : ?κ) (ha : a ∈ ?t), ?i (?j a ha) ⋯ = a
  ⊢ ∀ (a : ℕ) (ha : a ∈ Finset.range n), a + 1 = ?g (?i a ha)
  Finset.sum_bij'
· ∑ x in ?t, ?g x
  ⊢ ℕ → ?κ
  ⊢ ?κ → ℕ
  ⊢ ∀ a ∈ Finset.range n, ?i a ∈ ?t
  ⊢ ∀ a ∈ ?t, ?j a ∈ Finset.range n
  ⊢ ∀ a ∈ Finset.range n, ?j (?i a) = a
  ⊢ ∀ a ∈ ?t, ?i (?j a) = a
  ⊢ ∀ a ∈ Finset.range n, a + 1 = ?g (?i a)
  Finset.sum_nbij'
-/
#guard_msgs in
#rw?? ∑ n in Finset.range n, (n + 1)
