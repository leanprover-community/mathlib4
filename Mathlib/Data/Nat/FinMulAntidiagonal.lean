/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.NumberTheory.ArithmeticFunction

/-!
# Sets of tuples with a fixed product

This file defines the finite set of `d`-tuples of natural numbers with a fixed product `n` as
`Nat.finMulAntidiagonal`.

## Main Results
* There are `d^(ω n)` ways to write `n` as a product of `d` natural numbers, when `n` is squarefree
(`card_finMulAntidiagonal_of_squarefree`)
-/

open Finset
open scoped BigOperators ArithmeticFunction
namespace PNat

/-- The set of divisors of a positive natural number.
This is `Nat.divisorsAntidiagonal` without a special case for `n = 0`. -/
def divisorsAntidiagonal (n : ℕ+) : Finset (ℕ+ × ℕ+) :=
  (Nat.divisorsAntidiagonal n).attach.map
    ⟨fun x =>
      (⟨x.val.1, Nat.pos_of_mem_divisors <| Nat.fst_mem_divisors_of_mem_antidiagonal x.prop⟩,
      ⟨x.val.2, Nat.pos_of_mem_divisors <| Nat.snd_mem_divisors_of_mem_antidiagonal x.prop⟩),
    fun _ _ h => Subtype.ext <| Prod.ext (congr_arg (·.1.val) h) (congr_arg (·.2.val) h)⟩

@[simp]
theorem mem_divisorsAntidiagonal {n : ℕ+} (x : ℕ+ × ℕ+) :
    x ∈ divisorsAntidiagonal n ↔ x.1 * x.2 = n := by
  simp_rw [divisorsAntidiagonal, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk,
    Prod.ext_iff, true_and, ← coe_inj, Subtype.exists]
  aesop

instance instHasAntidiagonal : Finset.HasAntidiagonal (Additive ℕ+) where
  antidiagonal n := divisorsAntidiagonal (Additive.toMul n) |>.map
    (.prodMap (Additive.ofMul.toEmbedding) (Additive.ofMul.toEmbedding))
  mem_antidiagonal {n a} := by
    obtain ⟨a₁, a₂⟩ := a
    revert n a₁ a₂
    simp_rw [Additive.ofMul.surjective.forall, ← ofMul_mul, Additive.ofMul.injective.eq_iff]
    simp

end PNat

namespace Nat

/-- The `Finset` of all `d`-tuples of natural numbers whose product is `n`. Defined to be `∅` when
`n = 0`. -/
def finMulAntidiagonal (d : ℕ) (n : ℕ) : Finset (Fin d → ℕ) :=
  if hn : 0 < n then
    (Finset.finAntidiagonal d (Additive.ofMul (α := ℕ+) ⟨n, hn⟩)).map <|
      .arrowCongrRight <| Additive.toMul.toEmbedding.trans <| ⟨PNat.val, PNat.coe_injective⟩
  else
    ∅

@[simp]
theorem mem_finMulAntidiagonal {d n : ℕ} {f : Fin d → ℕ} :
    f ∈ finMulAntidiagonal d n ↔ ∏ i, f i = n ∧ n ≠ 0 := by
  unfold finMulAntidiagonal
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
    simp only [h, not_mem_empty, ne_eq, not_true_eq_false, and_false]

@[simp]
theorem finMulAntidiagonal_zero_right (d : ℕ) :
    finMulAntidiagonal d 0 = ∅ := rfl

theorem finMulAntidiagonal_one {d : ℕ} :
    finMulAntidiagonal d 1 = {fun _ => 1} := by
  ext f
  simp only [mem_finMulAntidiagonal, and_true, mem_singleton]
  constructor
  · intro ⟨hf, _⟩; ext i
    rw [← Nat.dvd_one, ← hf]
    exact dvd_prod_of_mem f (mem_univ _)
  · rintro rfl
    simp only [prod_const_one, implies_true, ne_eq, one_ne_zero, not_false_eq_true,
    and_self]

theorem finMulAntidiagonal_zero_left {n : ℕ} (hn : n ≠ 1) :
    finMulAntidiagonal 0 n = ∅ := by
  ext
  simp [hn.symm]

theorem dvd_of_mem_finMulAntidiagonal {n d : ℕ} {f : Fin d → ℕ} (hf : f ∈ finMulAntidiagonal d n)
    (i : Fin d) : f i ∣ n := by
  rw [mem_finMulAntidiagonal] at hf
  rw [← hf.1]
  exact dvd_prod_of_mem f (mem_univ i)

theorem ne_zero_of_mem_finMulAntidiagonal {d n : ℕ} {f : Fin d → ℕ}
    (hf : f ∈ finMulAntidiagonal d n) (i : Fin d) : f i ≠ 0 :=
  ne_zero_of_dvd_ne_zero (mem_finMulAntidiagonal.mp hf).2 (dvd_of_mem_finMulAntidiagonal hf i)

theorem prod_eq_of_mem_finMulAntidiagonal {d n : ℕ} {f : Fin d → ℕ}
    (hf : f ∈ finMulAntidiagonal d n) : ∏ i, f i = n :=
  (mem_finMulAntidiagonal.mp hf).1

theorem finMulAntidiagonal_eq_piFinset_divisors_filter {d m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    finMulAntidiagonal d m =
      {f ∈ Fintype.piFinset fun _ : Fin d => n.divisors | ∏ i, f i = m} := by
  ext f
  simp only [mem_univ, not_true, IsEmpty.forall_iff, implies_true, ne_eq, true_and,
    Fintype.mem_piFinset, mem_divisors, Nat.isUnit_iff, mem_filter]
  constructor
  · intro hf
    refine ⟨?_, prod_eq_of_mem_finMulAntidiagonal hf⟩
    exact fun i => ⟨(dvd_of_mem_finMulAntidiagonal hf i).trans hmn, hn⟩
  · rw [mem_finMulAntidiagonal]
    exact fun ⟨_, hprod⟩ => ⟨hprod, ne_zero_of_dvd_ne_zero hn hmn⟩

lemma image_apply_finMulAntidiagonal {d n : ℕ} {i : Fin d} (hd : d ≠ 1) :
    (finMulAntidiagonal d n).image (fun f => f i) = divisors n := by
  ext k
  simp only [mem_image, ne_eq, mem_divisors, Nat.isUnit_iff]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨dvd_of_mem_finMulAntidiagonal hf _, (mem_finMulAntidiagonal.mp hf).2⟩
  · simp_rw [mem_finMulAntidiagonal]
    rintro ⟨⟨r, rfl⟩, hn⟩
    have hs : Nontrivial (Fin d) := by
      rw [Fin.nontrivial_iff_two_le]
      obtain rfl | hd' := eq_or_ne d 0
      · exact i.elim0
      omega
    obtain ⟨i', hi_ne⟩ := exists_ne i
    use fun j => if j = i then k else if j = i' then r else 1
    simp only [ite_true, and_true, hn]
    rw [← Finset.mul_prod_erase (a:=i) (h:=mem_univ _),
      ← Finset.mul_prod_erase (a:= i')]
    · rw [if_neg hi_ne, if_pos rfl, if_pos rfl, prod_eq_one]
      · refine ⟨by ring, hn⟩
      intro j hj
      simp only [mem_erase, ne_eq, mem_univ, and_true] at hj
      rw [if_neg hj.1, if_neg hj.2]
    exact mem_erase.mpr ⟨hi_ne, mem_univ _⟩

lemma image_piFinTwoEquiv {n : ℕ} :
    (finMulAntidiagonal 2 n).image (piFinTwoEquiv <| fun _ => ℕ) = divisorsAntidiagonal n := by
  ext x
  simp [(piFinTwoEquiv <| fun _ => ℕ).symm.surjective.exists]

lemma finMulAntidiagonal_exists_unique_prime_dvd {d n p : ℕ} (hn : Squarefree n)
    (hp : p ∈ n.primeFactorsList) (f : Fin d → ℕ) (hf : f ∈ finMulAntidiagonal d n) :
    ∃! i, p ∣ f i := by
  rw [mem_finMulAntidiagonal] at hf
  rw [mem_primeFactorsList hf.2, ← hf.1, hp.1.prime.dvd_finset_prod_iff] at hp
  obtain ⟨i, his, hi⟩ := hp.2
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hij
  apply Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.1, hi, hj⟩
  apply Nat.coprime_of_squarefree_mul
  apply hn.squarefree_of_dvd
  rw [← hf.1, ← Finset.mul_prod_erase _ _ (his),
    ← Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨hij, mem_univ _⟩), ← mul_assoc]
  apply Nat.dvd_mul_right

private def primeFactorsPiBij (d n : ℕ) :
    ∀ f ∈ (n.primeFactors.pi fun _ => (univ : Finset <| Fin d)), Fin d → ℕ :=
  fun f _ i => ∏ p ∈ {p ∈ n.primeFactors.attach | f p.1 p.2 = i} , p

private theorem primeFactorsPiBij_img (d n : ℕ) (hn : Squarefree n)
  (f : (p : ℕ) → p ∈ n.primeFactors → Fin d) (hf : f ∈ pi n.primeFactors fun _ => univ) :
    Nat.primeFactorsPiBij d n f hf ∈ finMulAntidiagonal d n := by
  rw [mem_finMulAntidiagonal]
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
  apply ne_of_mem_of_not_mem (s:= ({x | (p ∣ x)}:Set ℕ)) <;> simp_rw [Set.mem_setOf_eq]
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
    (t : Fin d → ℕ) (ht : t ∈ finMulAntidiagonal d n) : ∃ (g : _)
    (hg : g ∈ pi n.primeFactors fun _ => univ), Nat.primeFactorsPiBij d n g hg = t := by
  have exists_unique := fun (p : ℕ) (hp : p ∈ n.primeFactors) =>
    (finMulAntidiagonal_exists_unique_prime_dvd hn
      (mem_primeFactors_iff_mem_primeFactorsList.mp hp) t ht)
  choose f hf hf_unique using exists_unique
  refine ⟨f, ?_, ?_⟩
  · simp only [mem_pi]
    exact fun a h => mem_univ (f a h)
  funext i
  have : t i ∣ n := dvd_of_mem_finMulAntidiagonal ht _
  trans (∏ p ∈ n.primeFactors.attach, if p.1 ∣ t i then p else 1)
  · rw [Nat.primeFactorsPiBij, ← prod_filter]
    congr
    ext ⟨p, hp⟩
    refine ⟨by rintro rfl; apply hf, fun h => (hf_unique p hp i h).symm⟩
  rw [prod_attach (f:=fun p => if p ∣ t i then p else 1), ← Finset.prod_filter]
  rw [primeFactors_filter_dvd_of_dvd hn.ne_zero this]
  exact prod_primeFactors_of_squarefree <| hn.squarefree_of_dvd this

theorem card_finMulAntidiagonal_pi (d n : ℕ) (hn : Squarefree n) :
    #(n.primeFactors.pi (fun _ => (univ : Finset <| Fin d))) =
      #(finMulAntidiagonal d n) := by
  apply Finset.card_bij (Nat.primeFactorsPiBij d n) (primeFactorsPiBij_img d n hn)
    (primeFactorsPiBij_inj d n) (primeFactorsPiBij_surj d n hn)

theorem card_finMulAntidiagonal_of_squarefree {d n : ℕ} (hn : Squarefree n) :
    #(finMulAntidiagonal d n) = d ^ ω n := by
  rw [← card_finMulAntidiagonal_pi d n hn, Finset.card_pi, Finset.prod_const,
    ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, toFinset_factors,
    Finset.card_fin]

end Nat
