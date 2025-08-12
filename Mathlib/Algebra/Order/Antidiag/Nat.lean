/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic.IntervalCases

/-!
# Sets of tuples with a fixed product

This file defines the finite set of `d`-tuples of natural numbers with a fixed product `n` as
`Nat.finMulAntidiag`.

## Main Results
* There are `d^(ω n)` ways to write `n` as a product of `d` natural numbers, when `n` is squarefree
(`card_finMulAntidiag_of_squarefree`)
* There are `3^(ω n)` pairs of natural numbers whose `lcm` is `n`, when `n` is squarefree
(`card_pair_lcm_eq`)
-/

open Finset
open scoped BigOperators ArithmeticFunction
namespace PNat

instance instHasAntidiagonal : Finset.HasAntidiagonal (Additive ℕ+) :=
  /- The set of divisors of a positive natural number.
This is `Nat.divisorsAntidiagonal` without a special case for `n = 0`. -/
  let divisorsAntidiagonal (n : ℕ+) : Finset (ℕ+ × ℕ+) :=
    (Nat.divisorsAntidiagonal n).attach.map
      ⟨fun x =>
        (⟨x.val.1, Nat.pos_of_mem_divisors <| Nat.fst_mem_divisors_of_mem_antidiagonal x.prop⟩,
        ⟨x.val.2, Nat.pos_of_mem_divisors <| Nat.snd_mem_divisors_of_mem_antidiagonal x.prop⟩),
      fun _ _ h => Subtype.ext <| Prod.ext (congr_arg (·.1.val) h) (congr_arg (·.2.val) h)⟩
  have mem_divisorsAntidiagonal {n : ℕ+} (x : ℕ+ × ℕ+) :
    x ∈ divisorsAntidiagonal n ↔ x.1 * x.2 = n := by
    simp_rw [divisorsAntidiagonal, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk,
      Prod.ext_iff, true_and, ← coe_inj, Subtype.exists]
    simp
  { antidiagonal := fun n ↦ divisorsAntidiagonal (Additive.toMul n) |>.map
      (.prodMap (Additive.ofMul.toEmbedding) (Additive.ofMul.toEmbedding))
    mem_antidiagonal := by simp [← ofMul_mul, mem_divisorsAntidiagonal] }

end PNat

namespace Nat

/-- The `Finset` of all `d`-tuples of natural numbers whose product is `n`. Defined to be `∅` when
`n = 0`. -/
def finMulAntidiag (d : ℕ) (n : ℕ) : Finset (Fin d → ℕ) :=
  if hn : 0 < n then
    (Finset.finAntidiagonal d (Additive.ofMul (α := ℕ+) ⟨n, hn⟩)).map <|
      .arrowCongrRight <| Additive.toMul.toEmbedding.trans <| ⟨PNat.val, PNat.coe_injective⟩
  else
    ∅

@[simp]
theorem mem_finMulAntidiag {d n : ℕ} {f : Fin d → ℕ} :
    f ∈ finMulAntidiag d n ↔ ∏ i, f i = n ∧ n ≠ 0 := by
  unfold finMulAntidiag
  split_ifs with h
  · simp_rw [mem_map, mem_finAntidiagonal, Function.Embedding.arrowCongrRight_apply,
      Function.comp_def, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
      Function.Embedding.coeFn_mk, ← Additive.ofMul.symm_apply_eq, Additive.ofMul_symm_eq,
      toMul_sum, (Equiv.piCongrRight fun _=> Additive.ofMul).surjective.exists,
      Equiv.piCongrRight_apply, Pi.map_apply, toMul_ofMul, ← PNat.coe_inj, PNat.mk_coe,
      PNat.coe_prod]
    constructor
    · rintro ⟨a, ha_mem, rfl⟩
      exact ⟨ha_mem, h.ne.symm⟩
    · rintro ⟨rfl, _⟩
      refine ⟨fun i ↦ ⟨f i, ?_⟩, rfl, funext fun _ => rfl⟩
      apply Nat.pos_of_ne_zero
      exact Finset.prod_ne_zero_iff.mp h.ne.symm _ (mem_univ _)
  · simp only [not_lt, nonpos_iff_eq_zero] at h
    simp only [h, notMem_empty, ne_eq, not_true_eq_false, and_false]

@[simp]
theorem finMulAntidiag_zero_right (d : ℕ) :
    finMulAntidiag d 0 = ∅ := rfl

theorem finMulAntidiag_one {d : ℕ} :
    finMulAntidiag d 1 = {fun _ => 1} := by
  ext
  simp only [mem_finMulAntidiag, prod_eq_one_iff, mem_univ, forall_const, ne_eq, one_ne_zero,
    not_false_eq_true, and_true, mem_singleton]
  grind

theorem finMulAntidiag_zero_left {n : ℕ} (hn : n ≠ 1) :
    finMulAntidiag 0 n = ∅ := by
  ext
  simp [hn.symm]

theorem dvd_of_mem_finMulAntidiag {n d : ℕ} {f : Fin d → ℕ} (hf : f ∈ finMulAntidiag d n)
    (i : Fin d) : f i ∣ n := by
  rw [mem_finMulAntidiag] at hf
  rw [← hf.1]
  exact dvd_prod_of_mem f (mem_univ i)

theorem ne_zero_of_mem_finMulAntidiag {d n : ℕ} {f : Fin d → ℕ}
    (hf : f ∈ finMulAntidiag d n) (i : Fin d) : f i ≠ 0 :=
  ne_zero_of_dvd_ne_zero (mem_finMulAntidiag.mp hf).2 (dvd_of_mem_finMulAntidiag hf i)

theorem prod_eq_of_mem_finMulAntidiag {d n : ℕ} {f : Fin d → ℕ}
    (hf : f ∈ finMulAntidiag d n) : ∏ i, f i = n :=
  (mem_finMulAntidiag.mp hf).1

theorem finMulAntidiag_eq_piFinset_divisors_filter {d m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    finMulAntidiag d m =
      {f ∈ Fintype.piFinset fun _ : Fin d => n.divisors | ∏ i, f i = m} := by
  ext f
  simp only [ne_eq,
    Fintype.mem_piFinset, mem_divisors, mem_filter]
  constructor
  · intro hf
    refine ⟨?_, prod_eq_of_mem_finMulAntidiag hf⟩
    exact fun i => ⟨(dvd_of_mem_finMulAntidiag hf i).trans hmn, hn⟩
  · rw [mem_finMulAntidiag]
    exact fun ⟨_, hprod⟩ => ⟨hprod, ne_zero_of_dvd_ne_zero hn hmn⟩

lemma image_apply_finMulAntidiag {d n : ℕ} {i : Fin d} (hd : d ≠ 1) :
    (finMulAntidiag d n).image (fun f => f i) = divisors n := by
  ext k
  simp only [mem_image, ne_eq, mem_divisors]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨dvd_of_mem_finMulAntidiag hf _, (mem_finMulAntidiag.mp hf).2⟩
  · simp_rw [mem_finMulAntidiag]
    rintro ⟨⟨r, rfl⟩, hn⟩
    have hs : Nontrivial (Fin d) := by
      rw [Fin.nontrivial_iff_two_le]
      obtain rfl | hd' := eq_or_ne d 0
      · exact i.elim0
      omega
    obtain ⟨i', hi_ne⟩ := exists_ne i
    use fun j => if j = i then k else if j = i' then r else 1
    simp only [ite_true, and_true]
    rw [← Finset.mul_prod_erase (h := mem_univ i),
      ← Finset.mul_prod_erase (a := i')]
    · simp_all
    exact mem_erase.mpr ⟨hi_ne, mem_univ _⟩

lemma image_piFinTwoEquiv_finMulAntidiag {n : ℕ} :
    (finMulAntidiag 2 n).image (piFinTwoEquiv <| fun _ => ℕ) = divisorsAntidiagonal n := by
  ext x
  simp [(piFinTwoEquiv <| fun _ => ℕ).symm.surjective.exists]

lemma finMulAntidiag_existsUnique_prime_dvd {d n p : ℕ} (hn : Squarefree n)
    (hp : p ∈ n.primeFactorsList) (f : Fin d → ℕ) (hf : f ∈ finMulAntidiag d n) :
    ∃! i, p ∣ f i := by
  rw [mem_finMulAntidiag] at hf
  rw [mem_primeFactorsList hf.2, ← hf.1, hp.1.prime.dvd_finset_prod_iff] at hp
  obtain ⟨i, his, hi⟩ := hp.2
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hij
  apply Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.1, hi, hj⟩
  apply Nat.coprime_of_squarefree_mul
  apply hn.squarefree_of_dvd
  rw [← hf.1, ← Finset.mul_prod_erase _ _ his,
    ← Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨hij, mem_univ _⟩), ← mul_assoc]
  apply Nat.dvd_mul_right

@[deprecated (since := "2024-12-17")]
alias finMulAntidiag_exists_unique_prime_dvd := finMulAntidiag_existsUnique_prime_dvd

private def primeFactorsPiBij (d n : ℕ) :
    ∀ f ∈ (n.primeFactors.pi fun _ => (univ : Finset <| Fin d)), Fin d → ℕ :=
  fun f _ i => ∏ p ∈ {p ∈ n.primeFactors.attach | f p.1 p.2 = i} , p

private theorem primeFactorsPiBij_img (d n : ℕ) (hn : Squarefree n)
    (f : (p : ℕ) → p ∈ n.primeFactors → Fin d) (hf : f ∈ pi n.primeFactors fun _ => univ) :
    Nat.primeFactorsPiBij d n f hf ∈ finMulAntidiag d n := by
  rw [mem_finMulAntidiag]
  refine ⟨?_, hn.ne_zero⟩
  unfold Nat.primeFactorsPiBij
  rw [prod_fiberwise_of_maps_to, prod_attach (f := fun x => x)]
  · apply prod_primeFactors_of_squarefree hn
  · apply fun _ _ => mem_univ _

private theorem primeFactorsPiBij_inj (d n : ℕ)
    (f : (p : ℕ) → p ∈ n.primeFactors → Fin d) (hf : f ∈ pi n.primeFactors fun _ => univ)
    (g : (p : ℕ) → p ∈ n.primeFactors → Fin d) (hg : g ∈ pi n.primeFactors fun _ => univ) :
    Nat.primeFactorsPiBij d n f hf = Nat.primeFactorsPiBij d n g hg → f = g := by
  contrapose!
  simp_rw [Function.ne_iff]
  intro ⟨p, hp, hfg⟩
  use f p hp
  dsimp only [Nat.primeFactorsPiBij]
  apply ne_of_mem_of_not_mem (s := {x | p ∣ x}) <;> simp_rw [Set.mem_setOf_eq]
  · rw [Finset.prod_filter]
    convert Finset.dvd_prod_of_mem _ (mem_attach (n.primeFactors) ⟨p, hp⟩)
    rw [if_pos rfl]
  · rw [mem_primeFactors] at hp
    rw [Prime.dvd_finset_prod_iff hp.1.prime]
    push_neg
    intro q hq
    rw [Nat.prime_dvd_prime_iff_eq hp.1 (Nat.prime_of_mem_primeFactorsList
      <| List.mem_toFinset.mp q.2)]
    rintro rfl
    rw [(mem_filter.mp hq).2] at hfg
    exact hfg rfl

private theorem primeFactorsPiBij_surj (d n : ℕ) (hn : Squarefree n)
    (t : Fin d → ℕ) (ht : t ∈ finMulAntidiag d n) : ∃ (g : _)
    (hg : g ∈ pi n.primeFactors fun _ => univ), Nat.primeFactorsPiBij d n g hg = t := by
  have existsUnique := fun (p : ℕ) (hp : p ∈ n.primeFactors) =>
    (finMulAntidiag_existsUnique_prime_dvd hn
      (mem_primeFactors_iff_mem_primeFactorsList.mp hp) t ht)
  choose f hf hf_unique using existsUnique
  refine ⟨f, ?_, ?_⟩
  · simp only [mem_pi, mem_univ, forall_true_iff]
  funext i
  have : t i ∣ n := dvd_of_mem_finMulAntidiag ht _
  trans (∏ p ∈ n.primeFactors.attach, if p.1 ∣ t i then p else 1)
  · rw [Nat.primeFactorsPiBij, ← prod_filter]
    congr
    ext ⟨p, hp⟩
    refine ⟨by rintro rfl; apply hf, fun h => (hf_unique p hp i h).symm⟩
  rw [prod_attach (f:=fun p => if p ∣ t i then p else 1), ← Finset.prod_filter]
  rw [primeFactors_filter_dvd_of_dvd hn.ne_zero this]
  exact prod_primeFactors_of_squarefree <| hn.squarefree_of_dvd this

private theorem card_finMulAntidiag_pi (d n : ℕ) (hn : Squarefree n) :
    #(n.primeFactors.pi fun _ => (univ : Finset <| Fin d)) =
      #(finMulAntidiag d n) := by
  apply Finset.card_bij (Nat.primeFactorsPiBij d n) (primeFactorsPiBij_img d n hn)
    (primeFactorsPiBij_inj d n) (primeFactorsPiBij_surj d n hn)

theorem card_finMulAntidiag_of_squarefree {d n : ℕ} (hn : Squarefree n) :
    #(finMulAntidiag d n) = d ^ ω n := by
  rw [← card_finMulAntidiag_pi d n hn, Finset.card_pi, Finset.prod_const,
    ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, toFinset_factors,
    Finset.card_fin]

theorem finMulAntidiag_three {n : ℕ} (a) (ha : a ∈ finMulAntidiag 3 n) : a 0 * a 1 * a 2 = n := by
  rw [← (mem_finMulAntidiag.mp ha).1, Fin.prod_univ_three a]

namespace card_pair_lcm_eq

/-!
The following private declarations are ingredients for the proof of `card_pair_lcm_eq`.
-/

@[reducible]
private def f {n : ℕ} : ∀ a ∈ finMulAntidiag 3 n, ℕ × ℕ := fun a _ => (a 0 * a 1, a 0 * a 2)

private theorem f_img {n : ℕ} (hn : Squarefree n) (a : Fin 3 → ℕ)
    (ha : a ∈ finMulAntidiag 3 n) :
    f a ha ∈ Finset.filter (fun ⟨x, y⟩ => x.lcm y = n) (n.divisors ×ˢ n.divisors) := by
  rw [mem_filter, Finset.mem_product, mem_divisors, mem_divisors]
  refine ⟨⟨⟨?_, hn.ne_zero⟩, ⟨?_, hn.ne_zero⟩⟩, ?_⟩ <;> rw [f, ← finMulAntidiag_three a ha]
  · apply dvd_mul_right
  · use a 1; ring
  dsimp only
  rw [lcm_mul_left, Nat.Coprime.lcm_eq_mul]
  · ring
  refine coprime_of_squarefree_mul (hn.squarefree_of_dvd ?_)
  use a 0; rw [← finMulAntidiag_three a ha]; ring

private theorem f_inj {n : ℕ} (a : Fin 3 → ℕ) (ha : a ∈ finMulAntidiag 3 n)
    (b : Fin 3 → ℕ) (hb : b ∈ finMulAntidiag 3 n) (hfab : f a ha = f b hb) :
    a = b := by
  obtain ⟨hfab1, hfab2⟩ := Prod.mk.inj hfab
  have hprods : a 0 * a 1 * a 2 = a 0 * a 1 * b 2 := by
    rw [finMulAntidiag_three a ha, hfab1, finMulAntidiag_three b hb]
  have hab2 : a 2 = b 2 := by
    rw [← mul_right_inj' <| mul_ne_zero (ne_zero_of_mem_finMulAntidiag ha 0)
      (ne_zero_of_mem_finMulAntidiag ha 1)]
    exact hprods
  have hab0 : a 0 = b 0 := by
    rw [hab2] at hfab2
    exact (mul_left_inj' <| ne_zero_of_mem_finMulAntidiag hb 2).mp hfab2;
  have hab1 : a 1 = b 1 := by
    rw [hab0] at hfab1
    exact (mul_right_inj' <| ne_zero_of_mem_finMulAntidiag hb 0).mp hfab1;
  funext i; fin_cases i <;> assumption

private theorem f_surj {n : ℕ} (hn : n ≠ 0) (b : ℕ × ℕ)
    (hb : b ∈ Finset.filter (fun ⟨x, y⟩ => x.lcm y = n) (n.divisors ×ˢ n.divisors)) :
    ∃ (a : Fin 3 → ℕ) (ha : a ∈ finMulAntidiag 3 n), f a ha = b := by
  dsimp only at hb
  let g := b.fst.gcd b.snd
  let a := ![g, b.fst/g, b.snd/g]
  have ha : a ∈ finMulAntidiag 3 n := by
    rw [mem_finMulAntidiag]
    rw [mem_filter, Finset.mem_product] at hb
    refine ⟨?_, hn⟩
    · rw [Fin.prod_univ_three a]
      dsimp only [a, Matrix.cons_val]
      rw [Nat.mul_div_cancel_left' (Nat.gcd_dvd_left _ _), ← hb.2, lcm,
        Nat.mul_div_assoc b.fst (Nat.gcd_dvd_right b.fst b.snd)]
  use a; use ha
  apply Prod.ext <;> dsimp only [a, Matrix.cons_val]
    <;> apply Nat.mul_div_cancel'
  · apply Nat.gcd_dvd_left
  · apply Nat.gcd_dvd_right

end card_pair_lcm_eq

open card_pair_lcm_eq in
theorem card_pair_lcm_eq {n : ℕ} (hn : Squarefree n) :
    #{p ∈ (n.divisors ×ˢ n.divisors) | p.1.lcm p.2 = n} = 3 ^ ω n := by
  rw [← card_finMulAntidiag_of_squarefree hn, eq_comm]
  apply Finset.card_bij f (f_img hn) (f_inj) (f_surj hn.ne_zero)

end Nat
