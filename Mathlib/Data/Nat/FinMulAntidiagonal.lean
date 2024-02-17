/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Logic.Embedding.Basic

/-!
# Sets of tuples with a fixed product

This file defines the finite set of `d`-tuples of natural numbers with a fixed product `n` as
`Nat.finMulAntidiagonal`.

## Main Results
* There are `d^(ω n)` ways to write `n` as a product of `d` natural numbers, when `n` is squarefree
(`card_finMulAntidiagonal_of_squarefree`)
* There are `3^(ω n)` pairs of natural numbers whose `lcm` is `n`, when `n` is squarefree
(`card_pair_lcm_eq`)
-/

namespace Nat

open BigOperators Finset ArithmeticFunction

/--
  The `Finset` of all `d`-tuples of natural numbers whose product is `n`. Defined to be `∅` when
  `n=0`.
  -/
def finMulAntidiagonal (d : ℕ) (n : ℕ) : Finset (Fin d → ℕ) :=
  aux d n
where
  /-- Auxiliary construction for `finMulAntidiagonal` that bundles a proof of lawfulness
  (`mem_finMulAntidiagonal`), as this is needed to invoke `disjiUnion`. Using `Finset.disjiUnion`
  makes this computationally much more efficient than using `Finset.biUnion`. -/
  aux (d : ℕ) (n : ℕ) : {s : Finset (Fin d → ℕ) // ∀ f, f ∈ s ↔ ∏ i, f i = n ∧ n ≠ 0} :=
    match d with
    | 0 =>
      if h : n = 1 then
        ⟨{1}, by simp [h]; exact List.ofFn_inj.mp rfl⟩
      else
        ⟨∅, by simp [Ne.symm h]⟩
    | d + 1 =>
      { val := (divisorsAntidiagonal n).disjiUnion
          (fun ab => (aux d ab.2).1.map {
              toFun := Fin.cons (ab.1)
              inj' := Fin.cons_right_injective _ })
          (fun i _hi j _hj hij => Finset.disjoint_left.2 fun t hti htj => hij <| by
            simp_rw [Finset.mem_map, Function.Embedding.coeFn_mk] at hti htj
            obtain ⟨ai, hai, hij'⟩ := hti
            obtain ⟨aj, haj, rfl⟩ := htj
            rw [Fin.cons_eq_cons] at hij'
            ext
            · exact hij'.1
            · obtain ⟨-, rfl⟩ := hij'
              rw [← (aux d i.2).prop ai |>.mp hai |>.1, ← (aux d j.2).prop ai |>.mp haj |>.1])
        property := fun f => by
          simp_rw [mem_disjiUnion, mem_divisorsAntidiagonal, mem_map, Function.Embedding.coeFn_mk,
            Prod.exists, (aux d _).prop, Fin.prod_univ_succ]
          constructor
          · rintro ⟨a, b, ⟨rfl, hab⟩, g, ⟨rfl, hb⟩, rfl⟩
            simp only [Fin.cons_zero, Fin.cons_succ]
            exact (true_and_iff (a * ∏ x : Fin d, g x ≠ 0)).mpr hab
          · intro ⟨rfl, hf⟩
            exact ⟨_, _, ⟨rfl, hf⟩, _, ⟨rfl, by exact right_ne_zero_of_mul hf⟩,
              Fin.cons_self_tail f⟩}

@[simp]
theorem mem_finMulAntidiagonal {d n : ℕ} {f : (Fin d) → ℕ} :
    f ∈ finMulAntidiagonal d n ↔ ∏ i, f i = n ∧ n ≠ 0 :=
  (finMulAntidiagonal.aux d n).prop f

@[simp]
theorem finMulAntidiagonal_zero {d : ℕ} :
    finMulAntidiagonal d 0 = ∅ := by
  ext; simp

theorem finMulAntidiagonal_one {d : ℕ} :
    finMulAntidiagonal d 1 = {fun _ => 1} := by
  ext f; simp only [mem_finMulAntidiagonal, and_true, mem_singleton]
  constructor
  · intro ⟨hf, _⟩; ext i;
    rw [← Nat.dvd_one, ← hf];
    exact dvd_prod_of_mem f (mem_univ _)
  · rintro rfl; simp only [prod_const_one, implies_true, ne_eq, one_ne_zero, not_false_eq_true,
    and_self]

theorem finMulAntidiagonal_empty_of_ne_one {n : ℕ} (hn : n ≠ 1) :
    finMulAntidiagonal 0 n = ∅ := by
  ext; simp [hn.symm]

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

theorem finMulAntidiagonal_univ_eq {d m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    finMulAntidiagonal d m =
      (Fintype.piFinset fun _ : Fin d => n.divisors).filter fun f => ∏ i, f i = m := by
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
    refine ⟨dvd_of_mem_finMulAntidiagonal hf _, (mem_finMulAntidiagonal.mp hf).2⟩
  · simp_rw [mem_finMulAntidiagonal]
    rintro ⟨⟨r, rfl⟩, hn⟩
    have hs : Nontrivial (Fin d)
    · rw [Fin.nontrivial_iff_two_le]
      by_cases hd' : d = 0
      · subst hd'
        apply Fin.isEmpty.elim' i
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
    (finMulAntidiagonal 2 n).image (piFinTwoEquiv $ fun _ => ℕ) = divisorsAntidiagonal n := by
  ext x
  simp only [piFinTwoEquiv_apply, mem_image, mem_finMulAntidiagonal, Fin.prod_univ_two, ne_eq,
    mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h, hn⟩
    use fun i => if i = 0 then x.fst else x.snd
    simp (config:={decide:=true}) only [ite_true, ite_false, h, mem_univ, not_true,
      IsEmpty.forall_iff, forall_const, not_false_eq_true, and_self, Prod.mk.eta, hn]

lemma filter_primeFactors {m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    n.primeFactors.filter fun p => p ∣ m = m.primeFactors := by
  ext p
  simp only [mem_filter, mem_primeFactors, ne_eq, hn, not_false_eq_true, and_true,
    ne_zero_of_dvd_ne_zero hn hmn, and_congr_left_iff, and_iff_left_iff_imp]
  exact fun h _ ↦ h.trans hmn

lemma finMulAntidiagonal_exists_unique_prime_dvd {d n p : ℕ} (hn : Squarefree n)
    (hp : p ∈ n.factors) (f : Fin d → ℕ) (hf : f ∈ finMulAntidiagonal d n) :
    ∃! i, p ∣ f i := by
  rw [mem_finMulAntidiagonal] at hf
  rw [mem_factors hf.2, ← hf.1, hp.1.prime.dvd_finset_prod_iff] at hp
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
  fun f _ i => ∏ p in Finset.filter (fun p => f p.1 p.2 = i) n.primeFactors.attach,  p

private theorem primeFactorsPiBij_img (d n : ℕ) (hn : Squarefree n)
  (f : (p : ℕ) → p ∈ n.primeFactors → Fin d) (hf : f ∈ pi n.primeFactors fun _ => univ) :
    Nat.primeFactorsPiBij d n f hf ∈ finMulAntidiagonal d n := by
  rw [mem_finMulAntidiagonal]
  refine ⟨?_, hn.ne_zero⟩
  unfold Nat.primeFactorsPiBij
  rw [prod_fiberwise_of_maps_to, prod_attach (f := fun x => x)]
  apply prod_primeFactors_of_squarefree hn
  apply fun _ _ => mem_univ _

private theorem primeFactorsPiBij_inj (d n : ℕ)
    (f g : (p : ℕ) → p ∈ n.primeFactors → Fin d) (hf : f ∈ pi n.primeFactors fun _ => univ)
    (hg : g ∈ pi n.primeFactors fun _ => univ) :
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
    rw [Nat.prime_dvd_prime_iff_eq hp.1 (Nat.prime_of_mem_factors $ List.mem_toFinset.mp q.2)]
    intro hpq; subst hpq
    rw [(mem_filter.mp hq).2] at hfg
    exact hfg rfl

private theorem primeFactorsPiBij_surj (d n : ℕ) (hn : Squarefree n)
    (t : Fin d → ℕ) (ht : t ∈ finMulAntidiagonal d n) : ∃ (g : _)
    (hg : g ∈ pi n.primeFactors fun _ => univ), Nat.primeFactorsPiBij d n g hg = t := by
  have exists_unique := fun (p : ℕ) (hp : p ∈ n.primeFactors) =>
    (finMulAntidiagonal_exists_unique_prime_dvd hn
      (mem_primeFactors_iff_mem_factors.mp hp) t ht)
  choose f hf hf_unique using exists_unique
  refine ⟨f, ?_, ?_⟩
  · simp only [mem_pi]
    exact fun a h => mem_univ (f a h)
  funext i
  have : t i ∣ n := dvd_of_mem_finMulAntidiagonal ht _
  trans (∏ p in n.primeFactors.attach, if p.1 ∣ t i then p else 1)
  · rw [Nat.primeFactorsPiBij, ← prod_filter]
    congr
    ext ⟨p, hp⟩
    refine ⟨by rintro rfl; apply hf, fun h => (hf_unique p hp i h).symm⟩
  rw [prod_attach (f:=fun p => if p ∣ t i then p else 1), ← Finset.prod_filter]
  rw [filter_primeFactors this hn.ne_zero]
  apply prod_primeFactors_of_squarefree $ hn.squarefree_of_dvd this

theorem card_finMulAntidiagonal_pi (d n : ℕ) (hn : Squarefree n) :
    (n.factors.toFinset.pi (fun _ => (univ : Finset <| Fin d))).card =
      (finMulAntidiagonal d n).card := by
  apply Finset.card_congr (Nat.primeFactorsPiBij d n) (primeFactorsPiBij_img d n hn)
    (primeFactorsPiBij_inj d n) (primeFactorsPiBij_surj d n hn)

theorem card_finMulAntidiagonal_of_squarefree {d n : ℕ} (hn : Squarefree n) :
    (finMulAntidiagonal d n).card = d ^ ω n := by
  rw [← card_finMulAntidiagonal_pi d n hn, Finset.card_pi, Finset.prod_const,
    cardDistinctFactors_apply, List.card_toFinset, Finset.card_fin]

@[reducible]
private def f {n : ℕ} : ∀ a ∈ finMulAntidiagonal 3 n, ℕ × ℕ := fun a _ => (a 0 * a 1, a 0 * a 2)

private theorem finMulAntidiagonal_three {n : ℕ} :
    ∀ a ∈ finMulAntidiagonal 3 n, a 0 * a 1 * a 2 = n := by
    intro a ha
    rw [← (mem_finMulAntidiagonal.mp ha).1, Fin.prod_univ_three a]

private theorem f_img {n : ℕ} (hn : Squarefree n) (a : Fin 3 → ℕ)
  (ha : a ∈ finMulAntidiagonal 3 n) :
    f a ha ∈ Finset.filter (fun ⟨x, y⟩ => x.lcm y = n) (n.divisors ×ˢ n.divisors) := by
  rw [mem_filter, Finset.mem_product, mem_divisors, mem_divisors]
  refine ⟨⟨⟨?_, hn.ne_zero⟩, ⟨?_, hn.ne_zero⟩⟩, ?_⟩ <;> rw [f, ← finMulAntidiagonal_three a ha]
  · apply dvd_mul_right
  · use a 1; ring
  dsimp only
  rw [lcm_mul_left, Nat.Coprime.lcm_eq_mul]
  · ring
  refine coprime_of_squarefree_mul (hn.squarefree_of_dvd ?_)
  use a 0; rw [← finMulAntidiagonal_three a ha]; ring

private theorem f_inj {n : ℕ} :
    ∀ (a b : Fin 3 → ℕ) (ha : a ∈ finMulAntidiagonal 3 n) (hb : b ∈ finMulAntidiagonal 3 n),
      f a ha = f b hb → a = b := by
  intro a b ha hb hfab
  obtain ⟨hfab1, hfab2⟩ := Prod.mk.inj hfab
  have hprods : a 0 * a 1 * a 2 = a 0 * a 1 * b 2
  · rw [finMulAntidiagonal_three a ha, hfab1, finMulAntidiagonal_three b hb]
  have hab2 : a 2 = b 2
  · rw [← mul_right_inj' $ mul_ne_zero (ne_zero_of_mem_finMulAntidiagonal ha 0)
      (ne_zero_of_mem_finMulAntidiagonal ha 1)]
    exact hprods
  have hab0 : a 0 = b 0
  · rw [hab2] at hfab2
    exact (mul_left_inj' $ ne_zero_of_mem_finMulAntidiagonal hb 2).mp hfab2;
  have hab1 : a 1 = b 1
  · rw [hab0] at hfab1
    exact (mul_right_inj' $ ne_zero_of_mem_finMulAntidiagonal hb 0).mp hfab1;
  funext i; fin_cases i <;> assumption

private theorem f_surj {n : ℕ} (hn : n ≠ 0) :
    ∀ b : ℕ × ℕ,
      b ∈ Finset.filter (fun ⟨x, y⟩ => x.lcm y = n) (n.divisors ×ˢ n.divisors) →
        ∃ (a : Fin 3 → ℕ) (ha : a ∈ finMulAntidiagonal 3 n), f a ha = b := by
  intro b hb
  dsimp only at hb
  let g := b.fst.gcd b.snd
  let a := ![g, b.fst/g, b.snd/g]
  have ha : a ∈ finMulAntidiagonal 3 n := by
    rw [mem_finMulAntidiagonal]
    rw [mem_filter, Finset.mem_product] at hb
    refine ⟨?_, hn⟩
    · rw [Fin.prod_univ_three a]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      rw [Nat.mul_div_cancel_left' (Nat.gcd_dvd_left _ _), ← hb.2, lcm,
        Nat.mul_div_assoc b.fst (Nat.gcd_dvd_right b.fst b.snd)]
  use a; use ha
  apply Prod.ext <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    <;> apply Nat.mul_div_cancel'
  · apply Nat.gcd_dvd_left
  · apply Nat.gcd_dvd_right

theorem card_pair_lcm_eq {n : ℕ} (hn : Squarefree n) :
    Finset.card ((n.divisors ×ˢ n.divisors).filter fun ⟨x, y⟩ => x.lcm y = n) =
      3 ^ ω n := by
  rw [← card_finMulAntidiagonal_of_squarefree hn, eq_comm]
  apply Finset.card_congr f (f_img hn) (f_inj) (f_surj hn.ne_zero)

end Nat
