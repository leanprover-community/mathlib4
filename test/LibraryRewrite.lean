import Mathlib.Tactic.Widget.LibraryRewrite
import Mathlib

-- set_option trace.profiler true
-- set_option trace.rw?? true

variable (n : Nat)

/--
info: Pattern n + 1
· n.succ
  Nat.add_one
· ack 0 n
  ack_zero
· (Finset.Iic n).card
  Nat.card_Iic
· (2 ^ n).size
  Nat.size_pow
· Fintype.card ↑(Set.Iic n)
  Nat.card_fintypeIic
· Nat.multichoose 2 n
  Nat.multichoose_two
· (↑n + 1).toNat
  Int.toNat_ofNat_add_one
· (n + 1).choose n
  Nat.choose_succ_self_right
· (Finset.antidiagonal n).card
  Finset.Nat.card_antidiagonal
· (List.Nat.antidiagonal n).length
  List.Nat.length_antidiagonal
· Multiset.card (Multiset.Nat.antidiagonal n)
  Multiset.Nat.card_antidiagonal

Pattern n + m
· 1 + n
  Nat.add_comm
· n.add 1
  Nat.add_eq
· Nat.succ^[1] n
  Nat.succ_iterate
· n + Nat.succ 1 - 1
  Nat.add_succ_sub_one
· n.succ + 1 - 1
  Nat.succ_add_sub_one

Pattern x + 1
· ∑ i ∈ Finset.range 2, n ^ i
  geom_sum_two
· (ComplexShape.down ℕ).prev n
  ChainComplex.prev
· (ComplexShape.up ℕ).next n
  CochainComplex.next

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
· {n, 1}.sum
  Multiset.sum_pair
· (addLeftEmbedding n) 1
  addLeftEmbedding_apply
· (addRightEmbedding 1) n
  addRightEmbedding_apply
· (OrderEmbedding.addLeft n) 1
  OrderEmbedding.addLeft_apply
· (OrderEmbedding.addRight 1) n
  OrderEmbedding.addRight_apply
-/
#guard_msgs in
#rw?? n+1

/--
info: Pattern p = 2
· Even 5
  ⊢ Nat.Prime 5
  Nat.Prime.even_iff

Pattern a = b
· 5 ≤ 2 ∧ 2 ≤ 5
  Nat.le_antisymm_iff
· Nat.beq 5 2 = true
  Nat.beq_eq
· Nat.succ 5 = Nat.succ 2
  Nat.succ_inj
· ↑5 = ↑2
  Int.ofNat_inj
· List.iota 5 = List.iota 2
  List.iota_inj
· ↑5 = ↑2
  Num.of_nat_inj
· Int.negSucc 5 = Int.negSucc 2
  Int.negSucc_inj
· 5 + 1 = 2 + 1
  Nat.add_one_inj
· 5 ^^^ 2 = 0
  Nat.xor_eq_zero
· ↑5 = ↑2
  Rat.natCast_inj
· Nonempty (Fin 5 ≃ Fin 2)
  Fin.equiv_iff_eq
· Nat.divisors 5 = Nat.divisors 2
  Nat.divisors_inj
· 5 * 5 = 2 * 2
  Nat.mul_self_inj
· Nat.succPNat 5 = Nat.succPNat 2
  Nat.succPNat_inj
· compare 5 2 = Ordering.eq
  Nat.compare_eq_eq
· (5 == 2) = true
  Nat.beq_eq_true_eq
· 5 ≡ 2 [MOD 0]
  Nat.modEq_zero_iff
· ∀ (a : ℕ), a ∣ 5 ↔ a ∣ 2
  Nat.dvd_left_iff_eq
· ↑5 = ↑2
  Ordinal.natCast_inj
· ↑5 = ↑2
  Cardinal.natCast_inj
· ↑5 = ↑2
  EReal.natCast_eq_iff
· ∀ (a : ℕ), 5 ∣ a ↔ 2 ∣ a
  Nat.dvd_right_iff_eq
· ↑5 = ↑2
  Ordinal.nat_cast_inj
· ↑5 = ↑2
  PartENat.natCast_inj
· Batteries.UnionFind.empty.Equiv 5 2
  Batteries.UnionFind.equiv_empty
· Nat.factorial 5 = Nat.factorial 2
  ⊢ 1 < 5
  Nat.factorial_inj
· ∀ (p : ℕ), Nat.Prime p → (p ∣ 5 ↔ p ∣ 2)
  ⊢ Squarefree 5
  ⊢ Squarefree 2
  Nat.Squarefree.ext_iff
· ∀ (p : ℕ), Nat.Prime p → padicValNat p 5 = padicValNat p 2
  ⊢ 5 ≠ 0
  ⊢ 2 ≠ 0
  Nat.eq_iff_prime_padicValNat_eq
· 5 ∣ 2
  ⊢ Nat.Prime 2
  ⊢ 2 ≤ 5
  Nat.dvd_prime_two_le
· 2 ∣ 5
  ⊢ Nat.Prime 5
  ⊢ 2 ≠ 1
  Nat.Prime.dvd_iff_eq
-/
#guard_msgs in
#rw?? 5=2

/--
info: Pattern n / 2
· n.div2
  Nat.div2_val

Pattern x / y
· if 0 < 2 ∧ 2 ≤ n then (n - 2) / 2 + 1 else 0
  Nat.div_eq
· (n - n % 2) / 2
  Nat.div_eq_sub_mod_div
· (Finset.filter (fun e => 2 ∣ e + 1) (Finset.range n)).card
  Nat.card_multiples
· (Finset.filter (fun k => k ≠ 0 ∧ 2 ∣ k) (Finset.range n.succ)).card
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
-/
#guard_msgs in
#rw?? n/2

-- showing all rewrites:
/--
info: Pattern n / 2
· n.div2
  Nat.div2_val

Pattern x / y
· if 0 < 2 ∧ 2 ≤ n then (n - 2) / 2 + 1 else 0
  Nat.div_eq
· (n - n % 2) / 2
  Nat.div_eq_sub_mod_div
· (Finset.filter (fun e => 2 ∣ e + 1) (Finset.range n)).card
  Nat.card_multiples
· (Finset.filter (fun k => k ≠ 0 ∧ 2 ∣ k) (Finset.range n.succ)).card
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
· ?k
  ⊢ ?k * 2 ≤ n
  ⊢ n < (?k + 1) * 2
  Nat.div_eq_of_lt_le
· (Finset.filter (fun x => x * 2 ≤ n) (Finset.Ico 1 ?c.succ)).card
  ⊢ 0 < 2
  ⊢ n / 2 ≤ ?c
  ZMod.div_eq_filter_card
· ?k
  ⊢ 0 < 2
  ⊢ n = ?k * 2
  Nat.div_eq_of_eq_mul_left
· ?k
  ⊢ 0 < 2
  ⊢ n = 2 * ?k
  Nat.div_eq_of_eq_mul_right
· n / (2 / ?b) / ?b
  ⊢ ?b ∣ 2
  ⊢ 2 ∣ n
  Nat.div_div_div_eq_div
· ?a
  ⊢ 2 ≠ 0
  ⊢ ?a * 2 = n
  Nat.eq_div_of_mul_eq_left
· ?a
  ⊢ 2 ≠ 0
  ⊢ 2 * ?a = n
  Nat.eq_div_of_mul_eq_right
-/
#guard_msgs in
#rw?? all n/2

open BigOperators

/--
info: Pattern ∑ x ∈ s, (f x + g x)
· ∑ x ∈ Finset.range n, x + ∑ x ∈ Finset.range n, 1
  Finset.sum_add_distrib
· ∑ a ∈ Finset.range n, a + (Finset.range n).card • 1
  Finset.sum_add_card_nsmul

Pattern ∑ i ∈ Finset.range n, f i
· ∑ i : Fin n, (↑i + 1)
  Finset.sum_range
· ∑ j ∈ Finset.range n, (n - 1 - j + 1)
  Finset.sum_range_reflect

Pattern ∑ x ∈ s, f x
· Finset.fold (fun x1 x2 => x1 + x2) 0 (fun x => x + 1) (Finset.range n)
  Finset.sum_eq_fold
· ∑' (x : ℕ), (↑(Finset.range n)).indicator (fun x => x + 1) x
  sum_eq_tsum_indicator
· (Multiset.map (fun x => x + 1) (Finset.range n).val).sum
  Finset.sum_eq_multiset_sum
· (∑ c ∈ Finset.range n, HAdd.hAdd c) 1
  Finset.sum_apply
· ∑ x ∈ (Finset.range n).attach, (↑x + 1)
  Finset.sum_attach
· (List.map (fun n => n + 1) (Finset.range n).toList).sum
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
· (Finset.range n).noncommSum (fun n => n + 1) ⋯
  Finset.noncommSum_eq_sum
· ∑ i ∈ Finset.range n, if i ∈ Finset.range n then i + 1 else 0
  Finset.sum_extend_by_zero
· ∑ x ∈ Finset.filter (fun x => x + 1 ≠ 0) (Finset.range n), (x + 1)
  Finset.sum_filter_ne_zero
· 0
  ⊢ ∀ x ∈ Finset.range n, x + 1 = 0
  Finset.sum_eq_zero
· ∑' (b : ℕ), (b + 1)
  ⊢ ∀ b ∉ Finset.range n, b + 1 = 0
  tsum_eq_sum
· (Finsupp.indicator (Finset.range n) fun x x => 1).sum HAdd.hAdd
  ⊢ ∀ a ∈ Finset.range n, a + 0 = 0
  Finsupp.sum_indicator_index
· ∑ᶠ (i : ℕ), (i + 1)
  ⊢ (Function.support fun i => i + 1) ⊆ ↑(Finset.range n)
  finsum_eq_sum_of_support_subset
-/
#guard_msgs in
#rw?? ∑ n ∈ Finset.range n, (n + 1)

-- `Inv.inv` is indexed as `id⁻¹`, and `fun x => (f x)⁻¹` is indexed as `f⁻¹`.
axiom foo (f : Rat → Rat) : Continuous (fun x => (f x)⁻¹) = True

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
· Continuous (-Inv.inv)
  continuous_neg_iff
-/
#guard_msgs in
#rw?? Continuous (Inv.inv : Rat → Rat)

-- Nat.Coprime is reducible, so we would get matches with the pattern `n = 1`.
-- But this wouldn't work with the `rw` tactic, so we make sure to avoid this.
/--
info: Pattern Nat.Coprime 2 n
· Odd 3
  Nat.coprime_two_left

Pattern n.Coprime m
· Nat.Coprime 3 2
  Nat.coprime_comm
· Nat.gcd 2 3 = 1
  Nat.coprime_iff_gcd_eq_one
· IsRelPrime 2 3
  Nat.coprime_iff_isRelPrime
· IsUnit ↑2
  ZMod.isUnit_iff_coprime
· (2 + 3).Coprime 3
  Nat.coprime_add_self_left
· (3 + 2).Coprime 3
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
· (3 - 2).Coprime 3
  ⊢ 2 ≤ 3
  Nat.coprime_self_sub_left
· (2 - 3).Coprime 3
  ⊢ 3 ≤ 2
  Nat.coprime_sub_self_left
· Nat.Coprime 2 (2 - 3)
  ⊢ 3 ≤ 2
  Nat.coprime_self_sub_right
· Nat.Coprime 2 (3 - 2)
  ⊢ 2 ≤ 3
  Nat.coprime_sub_self_right
· 2 ≠ 3
  ⊢ Nat.Prime 2
  ⊢ Nat.Prime 3
  Nat.coprime_primes
· Disjoint (Nat.primeFactors 2) (Nat.primeFactors 3)
  ⊢ 2 ≠ 0
  ⊢ 3 ≠ 0
  Nat.disjoint_primeFactors
-/
#guard_msgs in
#rw?? Nat.Coprime 2 3
