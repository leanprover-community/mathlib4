import Mathlib

-- set_option trace.profiler true
-- set_option trace.profiler.threshold 5
-- set_option trace.rw?? true

variable (A B : Set Nat)

/--
info: Unfolds for 0:
· ↑0
· NatCast.natCast 0
· Rat.ofInt ↑0
-/
#guard_msgs in
#unfold? (0:Rat)

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
#unfold? (42 : ℚ )

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
info: Unfolds for (fun x => x) (1 + 1):
· 1 + 1
· Nat.add 1 1
· 2
-/
#guard_msgs in
#unfold? (fun x => x) (1+1)

/--
info: Unfolds for fun x => id x:
· id
· fun a => a
-/
#guard_msgs in
#unfold? fun x => id x

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
· ?a + n - (?a - 1)
  ⊢ 1 ≤ ?a
  Nat.add_sub_sub_cancel

Pattern a + b
· 1 + n
  add_comm
· max n 1 + min n 1
  max_add_min
· min n 1 + max n 1
  min_add_max
· n +ᵥ 1
  vadd_eq_add
· AddOpposite.op 1 +ᵥ n
  op_vadd_eq_add
· Multiset.sum {n, 1}
  Multiset.sum_pair
· (addLeftEmbedding n) 1
  addLeftEmbedding_apply
· (addRightEmbedding 1) n
  addRightEmbedding_apply
· (OrderEmbedding.addLeft n) 1
  OrderEmbedding.addLeft_apply
· (OrderEmbedding.addRight 1) n
  OrderEmbedding.addRight_apply
· ?y + n
  ⊢ AddSemiconjBy n 1 ?y
  AddSemiconjBy.eq
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

open BigOperators

/--
info: Pattern ∑ x in s, (f x + g x)
· ∑ x in Finset.range n, x + ∑ x in Finset.range n, 1
  Finset.sum_add_distrib
· ∑ a in Finset.range n, a + (Finset.range n).card • 1
  Finset.sum_add_card_nsmul

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
· ∑' (x : ℕ), Set.indicator (↑(Finset.range n)) (fun x => x + 1) x
  sum_eq_tsum_indicator
· Multiset.sum (Multiset.map (fun x => x + 1) (Finset.range n).val)
  Finset.sum_eq_multiset_sum
· Finset.sum (Finset.range n) (fun c => HAdd.hAdd c) 1
  Finset.sum_apply
· ∑ x in Finset.attach (Finset.range n), (↑x + 1)
  Finset.sum_attach
· List.sum (List.map (fun n => n + 1) (Finset.toList (Finset.range n)))
  Finset.sum_to_list
· ∑ i : { x // x ∈ Finset.range n }, (↑i + 1)
  Finset.sum_coe_sort
· ∑' (x : { x // x ∈ Finset.range n }), (↑x + 1)
  Finset.tsum_subtype
· ∑' (x : ↑↑(Finset.range n)), (↑x + 1)
  Finset.tsum_subtype'
· ∑ᶠ (i : ℕ) (_ : i ∈ ↑(Finset.range n)), (i + 1)
  finsum_mem_coe_finset
· ∑ i : ↑↑(Finset.range n), (↑i + 1)
  Finset.sum_finset_coe
· ∑ᶠ (i : ℕ) (_ : i ∈ Finset.range n), (i + 1)
  finsum_mem_finset_eq_sum
· Finset.noncommSum (Finset.range n) (fun n => n + 1) ⋯
  Finset.noncommSum_eq_sum
· ∑ i in Finset.range n, if i ∈ Finset.range n then i + 1 else 0
  Finset.sum_extend_by_zero
· ∑ x in Finset.filter (fun x => x + 1 ≠ 0) (Finset.range n), (x + 1)
  Finset.sum_filter_ne_zero
· 0
  ⊢ ∀ x ∈ Finset.range n, x + 1 = 0
  Finset.sum_eq_zero
· ∑' (b : ℕ), (b + 1)
  ⊢ ∀ b ∉ Finset.range n, b + 1 = 0
  tsum_eq_sum
· Finsupp.sum (Finsupp.indicator (Finset.range n) fun x x => 1) fun x => HAdd.hAdd x
  ⊢ ∀ a ∈ Finset.range n, a + 0 = 0
  Finsupp.sum_indicator_index
· ∑ x in Finset.range n ∩ ?t, (x + 1) + ∑ x in Finset.range n \ ?t, (x + 1)
  ⊢ Finset ℕ
  Finset.sum_inter_add_sum_diff
· ∑ᶠ (i : ℕ), (i + 1)
  ⊢ (Function.support fun i => i + 1) ⊆ ↑(Finset.range n)
  finsum_eq_sum_of_support_subset
· (Finset.range n).card • ?b
  ⊢ ∀ a ∈ Finset.range n, a + 1 = ?b
  Finset.sum_eq_card_nsmul
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
· ∑ x in Finset.range n, (?σ x + 1)
  ⊢ Equiv.Perm ℕ
  ⊢ {a | ?σ a ≠ a} ⊆ ↑(Finset.range n)
  Equiv.Perm.sum_comp
· ?a + 1 + ∑ x in Finset.erase (Finset.range n) ?a, (x + 1)
  ⊢ ?a ∈ Finset.range n
  Finset.add_sum_erase
· ∑ x in Finset.erase (Finset.range n) ?a, (x + 1) + (?a + 1)
  ⊢ ?a ∈ Finset.range n
  Finset.sum_erase_add
· Finsupp.sum (Finsupp.onFinset (Finset.range n) (fun a => 1) ?hf) fun a => HAdd.hAdd a
  ⊢ ∀ (a : ℕ), 1 ≠ 0 → a ∈ Finset.range n
  ⊢ ∀ (a : ℕ), a + 0 = 0
  Finsupp.onFinset_sum
· ∑ x in insert ?a (Finset.range n), (x + 1)
  ⊢ ?a + 1 = 0
  Finset.sum_insert_zero
· ∑ a in Finset.range n ∪ ?s₂, (a + 1)
  ⊢ ∀ a ∈ ?s₂, a ∉ Finset.range n → a + 1 = 0
  Finset.sum_union_eq_left
· ∑ a in ?s₁ ∪ Finset.range n, (a + 1)
  ⊢ ∀ a ∈ ?s₁, a ∉ Finset.range n → a + 1 = 0
  Finset.sum_union_eq_right
· ∑ i in ?t, Set.indicator (↑(Finset.range n)) (fun i => i + 1) i
  ⊢ Finset.range n ⊆ ?t
  Finset.sum_indicator_subset
· ∑ᶠ (i : ℕ) (_ : ?p i), (i + 1)
  ⊢ ∀ {x : ℕ}, x + 1 ≠ 0 → (?p x ↔ x ∈ Finset.range n)
  finsum_cond_eq_sum_of_cond_iff
· ∑ᶠ (i : ℕ) (_ : i ∈ ?s), (i + 1)
  ⊢ (?s ∩ Function.support fun i => i + 1) = ↑(Finset.range n) ∩ Function.support fun i => i + 1
  finsum_mem_eq_sum_of_inter_support_eq
· ∑ x in insert ?a (Finset.range n), (x + 1)
  ⊢ ?a ∉ Finset.range n → ?a + 1 = 0
  Finset.sum_insert_of_eq_zero_if_not_mem
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
· ∑ x in Finset.preimage (Finset.range n) ?f ⋯, (?f x + 1)
  ⊢ ?ι → ℕ
  ⊢ Set.BijOn ?f (?f ⁻¹' ↑(Finset.range n)) ↑(Finset.range n)
  Finset.sum_preimage_of_bij
· ∑ᶠ (i : ℕ) (_ : i ∈ ?s), (i + 1)
  ⊢ (?s ∩ Function.support fun i => i + 1) ⊆ ↑(Finset.range n)
  ⊢ ↑(Finset.range n) ⊆ ?s
  finsum_mem_eq_sum_of_subset
· ∑ x in Finset.range n, Function.update (fun x => x + 1) ?i ?b x
  ⊢ ?i ∉ Finset.range n
  ⊢ ℕ
  Finset.sum_update_of_not_mem
· ∑ i in ?t, (i + Set.indicator (↑(Finset.range n)) (fun i => 1) i)
  ⊢ Finset.range n ⊆ ?t
  ⊢ ∀ (a : ℕ), a + 0 = 0
  Finset.sum_indicator_subset_of_eq_zero
· Finset.sum ?s₂ ?g
  ⊢ Finset.range n = ?s₂
  ⊢ ∀ x ∈ ?s₂, x + 1 = ?g x
  Finset.sum_congr
· ∑ x in Finset.preimage (Finset.range n) ?f ?hf, (?f x + 1)
  ⊢ ?ι → ℕ
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
· ∑ i in ?s₂, ?g i
  ⊢ Finset.range n ⊆ ?s₂
  ⊢ ∀ x ∈ ?s₂ \ Finset.range n, ?g x = 0
  ⊢ ∀ x ∈ Finset.range n, x + 1 = ?g x
  Finset.sum_subset_zero_on_sdiff
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

axiom foo (f : Rat → Rat) : Continuous (fun x => (f x)⁻¹) = True
-- `Inv.inv` is indexed as `id⁻¹`, and `fun x => (f x)⁻¹` is indexed as `f⁻¹`.
/--
info: Pattern Continuous fun x => (f x)⁻¹
· True
  foo

Pattern Continuous f
· ∀ (s : Set ℚ), IsOpen s → IsOpen (Inv.inv ⁻¹' s)
  continuous_def
· ∀ (b : ℚ), ∀ ε > 0, ∃ δ > 0, ∀ (a : ℚ), dist a b < δ → dist a⁻¹ b⁻¹ < ε
  Metric.continuous_iff
· Continuous (Rat.cast ∘ Inv.inv)
  continuous_induced_rng
· ∀ (a : ℚ), ∀ ε > 0, ∀ᶠ (x : ℚ) in nhds a, dist x⁻¹ a⁻¹ < ε
  Metric.continuous_iff'
· ∀ (s : Set ℚ), IsClosed s → IsClosed (Inv.inv ⁻¹' s)
  continuous_iff_isClosed
· UniformSpace.toTopologicalSpace ≤ TopologicalSpace.induced Inv.inv UniformSpace.toTopologicalSpace
  continuous_iff_le_induced
· ∀ (x : ℚ) (g : Ultrafilter ℚ), ↑g ≤ nhds x → Filter.Tendsto Inv.inv (↑g) (nhds x⁻¹)
  continuous_iff_ultrafilter
· TopologicalSpace.coinduced Inv.inv UniformSpace.toTopologicalSpace ≤ UniformSpace.toTopologicalSpace
  continuous_iff_coinduced_le
· ∀ (x : ℚ), ContinuousAt Inv.inv x
  continuous_iff_continuousAt
· SeqContinuous Inv.inv
  continuous_iff_seqContinuous
· ∀ (b : ℚ), Filter.Tendsto (fun x => (x⁻¹, b⁻¹)) (nhds b) (uniformity ℚ)
  Uniform.continuous_iff'_left
· ∀ (b : ℚ), Filter.Tendsto (fun x => (b⁻¹, x⁻¹)) (nhds b) (uniformity ℚ)
  Uniform.continuous_iff'_right
· Continuous fun x => dist x.1⁻¹ x.2⁻¹
  continuous_iff_continuous_dist
· ContinuousOn Inv.inv Set.univ
  continuous_iff_continuousOn_univ
· LowerSemicontinuous Inv.inv ∧ UpperSemicontinuous Inv.inv
  continuous_iff_lower_upperSemicontinuous
· Continuous (SeparationQuotient.lift Inv.inv ?hf)
  SeparationQuotient.continuous_lift
· Continuous ?g
  ⊢ ∀ (x : ℚ), x⁻¹ = ?g x
  continuous_congr
· Continuous ?g
  ⊢ ∀ (x : ℚ), Inseparable x⁻¹ (?g x)
  continuous_congr_of_inseparable
· ∀ s ∈ ?B, IsOpen (Inv.inv ⁻¹' s)
  ⊢ TopologicalSpace.IsTopologicalBasis ?B
  TopologicalSpace.IsTopologicalBasis.continuous_iff
-/
#guard_msgs in
#rw?? Continuous (Inv.inv : Rat → Rat)

-- Nat.Coprime is reducible, so we would get matches with the pattern `n = 1`.
-- But this wouldn't work with the `rw` tactic, so we make sure to avoid this.
/--
info: Pattern Nat.Coprime 2 n
· Odd 3
  Nat.coprime_two_left

Pattern Nat.Coprime n m
· Nat.Coprime 3 2
  Nat.coprime_comm
· Nat.gcd 2 3 = 1
  Nat.coprime_iff_gcd_eq_one
· IsRelPrime 2 3
  Nat.coprime_iff_isRelPrime
· IsUnit ↑2
  ZMod.isUnit_iff_coprime
· Nat.Coprime (2 + 3) 3
  Nat.coprime_add_self_left
· Nat.Coprime (3 + 2) 3
  Nat.coprime_self_add_left
· IsCoprime ↑2 ↑3
  Nat.isCoprime_iff_coprime
· Nat.Coprime 2 (3 + 2)
  Nat.coprime_add_self_right
· Nat.Coprime 2 (2 + 3)
  Nat.coprime_self_add_right
· ¬2 ∣ 3
  ⊢ Nat.Prime 2
  Nat.Prime.coprime_iff_not_dvd
· Nat.Coprime (3 - 2) 3
  ⊢ 2 ≤ 3
  Nat.coprime_self_sub_left
· Nat.Coprime (2 - 3) 3
  ⊢ 3 ≤ 2
  Nat.coprime_sub_self_left
· Nat.Coprime 2 (2 - 3)
  ⊢ 3 ≤ 2
  Nat.coprime_self_sub_right
· Nat.Coprime 2 (3 - 2)
  ⊢ 2 ≤ 3
  Nat.coprime_sub_self_right
· Nat.Coprime (2 + 3 * ?k) 3
  ⊢ ℕ
  Nat.coprime_add_mul_left_left
· Nat.Coprime (3 * ?k + 2) 3
  ⊢ ℕ
  Nat.coprime_mul_left_add_left
· Nat.Coprime 2 (3 + 2 * ?k)
  ⊢ ℕ
  Nat.coprime_add_mul_left_right
· Nat.Coprime (2 + ?k * 3) 3
  ⊢ ℕ
  Nat.coprime_add_mul_right_left
· Nat.Coprime 2 (2 * ?k + 3)
  ⊢ ℕ
  Nat.coprime_mul_left_add_right
· Nat.Coprime (?k * 3 + 2) 3
  ⊢ ℕ
  Nat.coprime_mul_right_add_left
· Nat.Coprime 2 (3 + ?k * 2)
  ⊢ ℕ
  Nat.coprime_add_mul_right_right
· Nat.Coprime 2 (?k * 2 + 3)
  ⊢ ℕ
  Nat.coprime_mul_right_add_right
· 2 ≠ 3
  ⊢ Nat.Prime 2
  ⊢ Nat.Prime 3
  Nat.coprime_primes
· Nat.Coprime (2 ^ ?n) 3
  ⊢ 0 < ?n
  Nat.coprime_pow_left_iff
· Nat.Coprime 2 (3 ^ ?n)
  ⊢ 0 < ?n
  Nat.coprime_pow_right_iff
· Disjoint 2.primeFactors 3.primeFactors
  ⊢ 2 ≠ 0
  ⊢ 3 ≠ 0
  Nat.disjoint_primeFactors
-/
#guard_msgs in
#rw?? Nat.Coprime 2 3
