/-
Copyright (c) 2025 John Rathgeber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Rathgeber
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors

/-!
# IMO 1998 Q3

For any positive integer `n`, let `d(n)` denote the number of positive divisors of `n`.
Determine all positive integers `k` such that `d(n^2)/d(n) = k` for some `n`.

## Solution:

The answer to this problem is every odd number, so to formalize this,
we must prove that if a `k` satisfies `d(n^2)/d(n) = k` for some `n`, then
`k` is odd, and also if `k` is odd, then it satisfies `d(n^2)/d(n) = k` for some `n`.

## Proof:

We follow Evan Chen's proof: <https://web.evanchen.cc/exams/IMO-1998-notes.pdf>.

Throughout this proof, we will use the following facts from number theory:
* $d(ab) = d(a)d(b)$ when $a$ and $b$ are coprime
* $p_1^{k_1}$ is coprime to $p_2^{k_2}$ when both $p_1$ and $p_2$ are prime,
  $p_1 \neq p_2$, and $k_1, k_2 \geq 0$.
* $d(p^k) = k + 1$ for prime $p$ and $k \geq 1$

### Necessity: $(\exists n > 0, d(n^2)/d(n) = k) → k \equiv 1 \pmod{2}$.

To prove this, we write $n$ in its prime factorization as

$$n = \prod_{i=1}^tp_i^{k_i}$$

Then, using the above number theory facts, we can write

$$d(n) = d\left(\prod_{i=1}^tp_i^{k_i}\right) = \prod_{i=1}^td\left(p_i^{k_i}\right)
 = \prod_{i=1}^t(k_i + 1)$$

$$d(n^2) = d\left(\prod_{i=1}^tp_i^{2k_i}\right) = \prod_{i=1}^td\left(p_i^{2k_i}\right)
 = \prod_{i=1}^t(2k_i + 1)$$

so

$$k = \frac{d(n^2)}{d(n)} = \prod_{i=1}^t\frac{2k_i + 1}{k_i + 1}$$

Since the numerator is always odd, $k$ is always odd. This concludes the proof of necessity.

### Sufficiency: For positive $k$, $k \equiv 1 \pmod{2} \to (\exists n > 0, d(n^2)/d(n) = k)$.

We prove this by strong induction.

Base Case: $k = 1$. $n = 1$ works.

Inductive Step: Assume $k > 1$, and
$\forall j < k, j \equiv 1 \pmod{2} \to \exists n > 0, d(n^2)/d(n) = j$.
Let $k = 2^tj - 1$ be odd, where $j$ is also odd.
We can write $k$ in this way because every even number has both an even and an odd part,
and since $k + 1$ is even, we can let $2^t$ be its even part and $j$ be its odd part.
In particular, $t$ will be the power $2$ is raised to in $k+1$'s prime factorization.

We get $j < k$ immediately, so by our inductive hypothesis,

$$\exists n_j > 0, \frac{d(n_j^2)}{d(n_j)} = j$$

We now aim to construct a number $x$ such that $d((n_jx)^2)/d(n_jx) = k$. Let

$$x = \prod_{i=0}^{t-1} p_i^{2^{t + i}j - 2^i(j + 1)}$$

where each $p_i$ is prime, distinct, and does not appear as a prime in $n_j$'s prime factorization.
This is justified by the infinitude of primes.
We also have that $d(p_i^{2^{t + i}j - 2^i(j + 1)}) = (2^{t + i}j - 2^i(j + 1)) + 1$ for all $i$,
as $2^{t + i}j - 2^i(j + 1) \geq 1$ for all $i$. We can now compute

$$\frac{d(x^2)}{d(x)} =
\prod_{i=0}^{t-1}\frac{2(2^{t + i}j - 2^i(j + 1)) + 1}{(2^{t + i}j - 2^i(j + 1)) + 1}
 = \prod_{i=0}^{t-1}\frac{2^{t + i + 1}j - 2^{i + 1}(j + 1) + 1}{2^{t+i}j - 2^i(j + 1) + 1}$$

$$ = \frac{2^{2t}j-2^t(j+1)+1}{2^{2t-1}j-2^{t-1}(j+1)+1}\cdot
\frac{2^{2t-1}j-2^{t-1}(j+1)+1}{2^{2t-2}j-2^{t-2}(j+1)+1}\cdot\cdots
\cdot\frac{2^{t+1}j-2(j+1)+1}{2^tj-(j+1)+1}$$

Which telescopes cleanly to

$$= \frac{2^{2t}j-2^t(j+1)+1}{2^tj-(j+1)+1} = \frac{(2^tj-1)(2^t-1)}{j(2^t-1)} = \frac{2^tj-1}{j}$$

We can multiply both sides by $j$ to achieve

$$k = 2^tj - 1 = j \cdot \frac{d(x^2)}{d(x)} = \frac{d(n_j^2)d(x^2)}{d(n_j)d(x)} =
\frac{d((n_jx)^2)}{d(n_jx)}$$

where the last equality holds because each prime in $x$'s factorization does not appear in $n_j$'s
factorization, so $x$ and $n_j$ are coprime, and similarly for $x^2$ and $n_j^2$.
This concludes the proof of sufficiency.

Since we have proven both necessity and sufficiency, we know for any positive integer $k$,

$$k \equiv 1 \pmod{2} \iff \exists n > 0, \frac{d(n^2)}{d(n)} = k$$

as desired.
-/

namespace Imo1998Q3

/-- Define `d(n)`, the function counting the number of positive divisors of `n`. -/
def d (n : ℕ) : ℕ := (Nat.divisors n).card

/--
`dComputed` takes in `n` and produces the product of `n`'s factorization's powers plus one.
We want to argue later that `dComputed(n) = d(n)`.
-/
def dComputed (n : ℕ) : ℕ := if n = 0 then 0 else n.factorization.prod (fun _ k ↦ k + 1)

/-- Proof that `d` is multiplicative. -/
lemma d_multiplicative (m n : ℕ) (h : Nat.Coprime m n) : d (m * n) = d m * d n :=
  Nat.Coprime.card_divisors_mul h

/-- Proof that `d(pᵏ) = k + 1` for `p` prime. -/
lemma prime_power_divisors {p k : ℕ} (hp : p.Prime) : d (p ^ k) = k + 1 := by
  simp only [d]
  rw [Nat.divisors_prime_pow hp]
  rw [Finset.card_map]
  simp

/--
Proof that `dComputed n = d n`, using the fact that `d` is multiplicative
and `d(pᵏ) = k + 1` for `p` prime.
-/
lemma d_eq_dComputed (n : ℕ) : d n = dComputed n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [d, dComputed]
  · rw [dComputed, if_neg hn]
    rw [Nat.multiplicative_factorization d d_multiplicative (by simp [d]) hn]
    refine Finset.prod_congr ?_ ?_
    · rfl
    · intro p hp; exact prime_power_divisors (Nat.prime_of_mem_primeFactors hp)

/-- Proof that `d(n²) = ∏ᵢ(2kᵢ + 1)` for `n = ∏ᵢpᵢᵏᵢ` (prime factorization). -/
lemma d_n2 (n : ℕ) (hn : n ≠ 0) : d (n ^ 2) = n.factorization.prod (fun _ k ↦ 2 * k + 1) := by
  rw [d_eq_dComputed, dComputed]
  rw [if_neg (pow_ne_zero 2 hn)]
  rw [Nat.factorization_pow]
  apply Finset.prod_congr (Finsupp.support_smul_eq two_ne_zero)
  simp

/-- Proof that if every number in a list is odd, the product of the list is odd. -/
lemma list_prod_odd (l : List ℕ) : (∀ x ∈ l, Odd x) → Odd l.prod := by
  induction l with
  | nil => simp
  | cons head tail ih =>
      intro hallodd2
      rw [List.prod_cons]
      apply Odd.mul
      · apply hallodd2; exact @List.mem_cons_self _ head tail
      · apply ih
        intro x hx
        apply hallodd2
        exact List.mem_cons_of_mem head hx

/-- We begin by first proving that every value of `k` must be an odd number. -/
theorem k_is_odd (k : ℕ)
    (h : ∃ n : ℕ, n ≠ 0 ∧ d (n ^ 2) = k * d n) :
    (k % 2 = 1) := by
  obtain ⟨n, hn⟩ := h
  let nfac := n.factorization
  have hprime : ∀ p ∈ nfac.support, Nat.Prime p := by
    intro p hp
    dsimp [nfac] at hp
    exact Nat.prime_of_mem_primeFactors hp
  have hnfac := Nat.eq_factorization_iff hn.left hprime
  have hneqnfac : (nfac.prod fun x1 x2 ↦ x1 ^ x2) = n := hnfac.mp (by rfl)
  have hdn2odd : (d (n ^ 2)) % 2 = 1 := by
    have hn2eqnfac : (nfac.prod fun p k ↦ p ^ (2 * k)) = n ^ 2 := calc
      (nfac.prod fun p k ↦ p ^ (2 * k))
      _ = (nfac.prod fun p k ↦ (p ^ k) ^ 2) := by
          apply Finset.prod_congr rfl
          intro p _
          simp only
          rw [pow_mul']
      _ = (nfac.prod fun p k ↦ p ^ k) ^ 2 := by
          unfold Finsupp.prod
          simp only
          rw [Finset.prod_pow]
      _ = n ^ 2 := by rw [hneqnfac]
    have hd : d (n ^ 2) = (nfac.prod fun _ x2 ↦ ((2 * x2) + 1)) := d_n2 n hn.left
    let powers := nfac.support.toList.map (fun x ↦ 2 * nfac x + 1)
    have hallodd : (∀ i ∈ powers, Odd i) := by
      intro i hi
      rw [Nat.odd_iff]
      rw [List.mem_map] at hi
      obtain ⟨p, _, rfl⟩ := hi
      simp
    have hoddmul : (Odd (nfac.prod fun _ x2 ↦ ((2 * x2) + 1))) := by
      have h_eq : (nfac.prod fun _ x2 ↦ ((2 * x2) + 1)) = powers.prod := by
        dsimp [powers]
        rw [Finsupp.prod]
        rw [Finset.prod_eq_multiset_prod]
        simp
      rw [h_eq]
      exact list_prod_odd powers hallodd
    rw [hd]
    exact Nat.odd_iff.mp hoddmul
  rw [hn.right] at hdn2odd
  have hodd : Odd (k * (d n)) := Nat.odd_iff.mpr hdn2odd
  have hkodd : Odd k := (Nat.odd_mul.mp hodd).left
  exact Nat.odd_iff.mp hkodd

/-- Proof that we can pick `t` new and distinct primes given a list of `t` primes. -/
lemma exists_distinct_primes (t n : ℕ) (hnneq0 : n ≠ 0) (primes : List ℕ) :
    (∃ l : List ℕ, (∀ i ∈ l, Nat.Prime i ∧ i ∉ primes ∧ Nat.Coprime i n)
        ∧ List.length l = t ∧ List.Nodup l) := by
  induction t with
  | zero => use []; simp
  | succ t ih =>
      obtain ⟨l, props⟩ := ih
      let existing_numbers := (primes ++ l ++ [n])
      have he : existing_numbers ≠ [] := by dsimp [existing_numbers]; simp
      let bound := existing_numbers.max he
      have hexists := Nat.exists_infinite_primes (bound + 1)
      obtain ⟨new, hnew⟩ := hexists
      have hnewgtbound : new > bound := Nat.add_one_le_iff.mp hnew.left
      have hnewprime : Nat.Prime new := hnew.right
      use l ++ [new]
      apply And.intro
      · intro i hiinlist
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hiinlist
        cases hiinlist with
        | inl h => exact props.left i h
        | inr h =>
            rw [h]
            have hnewnotinprimes : new ∉ primes := by
              intro hin
              have hnewlebound : new ≤ bound := by
                have hnewinexisting : new ∈ existing_numbers := by
                  apply List.mem_append_left
                  apply List.mem_append_left
                  exact hin
                have hnewlemax := List.le_max_of_mem (l := existing_numbers) hnewinexisting
                simp only [bound]
                exact hnewlemax
              linarith [hnewlebound, hnewgtbound]
            have hnewcoprimen : new.Coprime n := by
              refine Nat.coprime_of_lt_prime hnneq0 ?_ hnewprime
              have hnleqbound : n ≤ bound := by
                simp only [bound]
                have hninexisting : n ∈ existing_numbers :=
                  List.mem_append_right _ (List.mem_singleton_self n)
                exact List.le_max_of_mem hninexisting
              linarith
            exact And.intro hnewprime (And.intro hnewnotinprimes hnewcoprimen)
      · apply And.intro
        · rw [List.length_append, props.right.left, List.length_singleton]
        · have hconsnodup : (new :: l).Nodup := by
            refine List.nodup_cons.mpr (And.intro ?_ props.right.right)
            intro hnewinl
            have hnewinexisting : new ∈ existing_numbers := by
              simp only [List.append_assoc, List.mem_append, List.mem_cons,
                List.not_mem_nil, or_false, existing_numbers]
              right
              left
              exact hnewinl
            have hle : new ≤ bound := by
              simp only [bound]
              exact List.le_max_of_mem hnewinexisting
            linarith
          rw [List.singleton_append.symm] at hconsnodup
          exact List.nodup_append_comm.mp hconsnodup

/-- Proof that `d(∏ᵢxᵢ) = ∏ᵢd(xᵢ)` for coprime `xᵢ`'s (repeated mulitiplicity). -/
lemma repeated_multiplicity_of_d (l : List ℕ) (hcoprime : l.Pairwise Nat.Coprime) :
    d (l.prod) = (List.map (fun i ↦ d i) l).prod := by
  induction l with
  | nil => simp [d]
  | cons head tail ih =>
      rw [List.pairwise_cons] at hcoprime
      obtain ⟨hhead, htail⟩ := hcoprime
      simp only [List.prod_cons, List.map_cons]
      rw [d_multiplicative]
      · rw [ih]; exact htail
      · apply Nat.coprime_list_prod_right_iff.mpr
        intro n hnintail
        exact hhead n hnintail

/--
Proof that `d(∏ᵢpᵢᵏᵢ) = ∏ᵢ(kᵢ + 1)`. Intuitively, we know `ps` and `exps` form
a factorization of `x`, but Lean doesn't know this, so we have to give this lemma
all the properties of `x`'s factorization without explicitly saying so.
-/
lemma d_of_factorization (t : ℕ) (ps exps : List ℕ)
    (hlen : ps.length = exps.length)
    (hlent : exps.length = t)
    (hallprime : ∀ i ∈ ps, Nat.Prime i)
    (hpsnodups : List.Nodup ps)
    (hexpsgt0 : ∀ i ∈ exps, i > 0) :
      d ((ps.zip exps).map (fun (p, e) ↦ p ^ e)).prod = (List.map (fun i ↦ i + 1) exps).prod := by
    rw [repeated_multiplicity_of_d (List.map (fun x ↦ x.1 ^ x.2) (ps.zip exps))]
    · apply congr_arg List.prod
      apply List.ext_get
      · rw [List.length_map, List.length_map, List.length_map]
        rw [List.length_zip, min_eq_left]
        · exact hlen
        · simp [hlen]
      · intro n hind1 hind2
        have hnltexpslen : n < exps.length := by rw [List.length_map] at hind2; exact hind2
        simp only [List.get_eq_getElem, List.map_map, List.getElem_map,
          List.getElem_zip, Function.comp_apply]
        have hnltpslen : n < ps.length := by
          rw [List.length_map, List.length_map] at hind1; exact List.lt_length_left_of_zip hind1
        have hpsnprime : Nat.Prime (ps[n]'hnltpslen) :=
          hallprime ps[n] (List.get_mem ps ⟨n, hnltpslen⟩)
        exact @prime_power_divisors ps[n] exps[n] hpsnprime
    · apply List.Nodup.pairwise_of_forall_ne
      · rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
        refine List.Pairwise.imp_of_mem (R := Ne) (fun {a b} ha hb hneq => ?_) ?_
        · obtain ⟨p₁, k₁⟩ := a
          obtain ⟨p₂, k₂⟩ := b
          simp only [ne_eq]
          have hp₁prime : Nat.Prime p₁ := hallprime p₁ (List.of_mem_zip ha).left
          have hp₂prime : Nat.Prime p₂ := hallprime p₂ (List.of_mem_zip hb).left
          have hk₁gt0 : k₁ > 0 := hexpsgt0 k₁ (List.of_mem_zip ha).right
          have hk₂gt0 : k₂ > 0 := hexpsgt0 k₂ (List.of_mem_zip hb).right
          by_cases h : p₁ = p₂
          · have hksneq : k₁ ≠ k₂ := by grind
            rw [h]
            intro heq
            apply hksneq
            exact (Nat.pow_right_inj hp₂prime.two_le).mp heq
          · intro heq
            have hpowdvd : p₁ ∣ p₂ ^ k₂ := by
              rw [←heq]
              apply dvd_pow_self
              apply Nat.ne_of_gt hk₁gt0
            have hdvd : p₁ ∣ p₂ := Nat.Prime.dvd_of_dvd_pow hp₁prime hpowdvd
            have heq2 : p₁ = p₂ := (Nat.prime_dvd_prime_iff_eq hp₁prime hp₂prime).mp hdvd
            contradiction
        · apply List.nodup_iff_pairwise_ne.mp
          apply List.Nodup.of_map Prod.fst
          rw [List.map_fst_zip]
          · exact hpsnodups
          · simp [hlent, hlen]
      · intro a ha b hb haneqb
        rw [List.mem_map] at ha
        obtain ⟨⟨p₁, k₁⟩, ha'⟩ := ha
        rw [List.mem_map] at hb
        obtain ⟨⟨p₂, k₂⟩, hb'⟩ := hb
        simp at ha' hb'
        have hp₁inps : p₁ ∈ ps := (List.of_mem_zip ha'.left).left
        have hp₁prime : Nat.Prime p₁ := (hallprime p₁) hp₁inps
        have hp₂inps : p₂ ∈ ps := (List.of_mem_zip hb'.left).left
        have hp₂prime : Nat.Prime p₂ := (hallprime p₂) hp₂inps
        rw [ha'.right.symm, hb'.right.symm]
        apply Nat.coprime_pow_primes k₁ k₂ hp₁prime hp₂prime
        have hpowsneq : p₁ ^ k₁ ≠ p₂ ^ k₂ := by rw [ha'.right, hb'.right]; exact haneqb
        intro hcon
        have hp₁k₁zip : (p₁, k₁) ∈ ps.zip exps := ha'.left
        have hp₂k₂zip : (p₂, k₂) ∈ ps.zip exps := hb'.left
        have hexistsidx1 := List.mem_iff_getElem?.mp hp₁k₁zip
        have hexistsidx2 := List.mem_iff_getElem?.mp hp₂k₂zip
        obtain ⟨i₁, hi₁⟩ := hexistsidx1
        obtain ⟨i₂, hi₂⟩ := hexistsidx2
        rw [List.getElem?_eq_some_iff] at hi₁ hi₂
        obtain ⟨h3, h33⟩ := hi₁
        obtain ⟨h4, h44⟩ := hi₂
        have hp1idx := List.mem_iff_getElem?.mp hp₁inps
        have hp2idx := List.mem_iff_getElem?.mp hp₂inps
        obtain ⟨j₁, hj₁⟩ := hp1idx
        obtain ⟨j₂, hj₂⟩ := hp2idx
        rw [List.getElem?_eq_some_iff] at hj₁ hj₂
        obtain ⟨h1, h11⟩ := hj₁
        obtain ⟨h2, h22⟩ := hj₂
        have hjeqj : j₁ = j₂ := by
          apply (List.Nodup.getElem_inj_iff hpsnodups).mp
          rw [h11, h22]
          exact hcon
        have hi₁valid : i₁ < ps.length := List.lt_length_left_of_zip h3
        have hi₂valid : i₂ < ps.length := List.lt_length_left_of_zip h4
        have hi₁valid2 : i₁ < exps.length := List.lt_length_right_of_zip h3
        have hi₂valid2 : i₂ < exps.length := List.lt_length_right_of_zip h4
        have hieqi : i₁ = i₂ := by
          have hpsi₁ : ps[i₁]'hi₁valid = p₁ := by
            rw [List.getElem_zip] at h33; exact (congrArg Prod.fst h33)
          have hpsi₂ : ps[i₂]'hi₂valid = p₂ := by
            rw [List.getElem_zip] at h44; exact (congrArg Prod.fst h44)
          rw [h11.symm] at hpsi₁
          rw [h22.symm] at hpsi₂
          have hi₁eqj₁ : i₁ = j₁ := (List.Nodup.getElem_inj_iff hpsnodups).mp hpsi₁
          have hi₂eqj₂ : i₂ = j₂ := (List.Nodup.getElem_inj_iff hpsnodups).mp hpsi₂
          rw [hi₁eqj₁, hi₂eqj₂]
          exact hjeqj
        rw [List.getElem_zip] at h33 h44
        have hei₁eqk₁ : exps[i₁]'hi₁valid2 = k₁ := congrArg Prod.snd h33
        have hei₂eqk₂ : exps[i₂]'hi₂valid2 = k₂ := congrArg Prod.snd h44
        have hkeqk : k₁ = k₂ := by
          rw [hei₁eqk₁.symm, hei₂eqk₂.symm]
          subst hieqi
          rfl
        have hcontra : p₁ ^ k₁ = p₂ ^ k₂ := by
          subst hcon
          subst hkeqk
          rfl
        contradiction

/-- We now prove that every odd number satisifies the equation. -/
theorem odd_k_satisfies (k : ℕ)
    (hkodd : k % 2 = 1) :
    (∃ n : ℕ, n ≠ 0 ∧ d (n ^ 2) = k * d n) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with (_ | k_minus_1)
      · contradiction
      · by_cases hk1 : k_minus_1 = 0
        · simp only [ne_eq, Nat.exists_ne_zero]
          use 0
          rw [hk1]
          simp
        · let kk := k_minus_1 + 1
          let t := (kk + 1).factorization 2
          have htpos : 0 < t := by
            apply Nat.Prime.factorization_pos_of_dvd Nat.prime_two
            · simp
            · dsimp [kk]; omega
          let j := (kk + 1) / (2 ^ t)
          have h_div : 2 ^ t ∣ (kk + 1) := Nat.ordProj_dvd (kk + 1) 2
          have hjodd : Odd j := by
            have hordcompl : j = ordCompl[2] (kk + 1) := rfl
            have htwondvd := @Nat.not_dvd_ordCompl (kk + 1) _ Nat.prime_two (Nat.succ_ne_zero kk)
            have htwondvdj : ¬ 2 ∣ j := by rw [hordcompl]; exact htwondvd
            exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp htwondvdj)
          have hkkeqjt : kk + 1 = j * 2 ^ t := Nat.eq_mul_of_div_eq_left h_div rfl
          have hjltkk : j < kk := by
            have hkkge2 : kk ≥ 2 := by
              dsimp [kk]
              have hpos : 0 < k_minus_1 := Nat.pos_of_ne_zero hk1
              linarith
            have h2le2t : 2 ≤ 2 ^ t := by
              refine Nat.le_self_pow ?_ 2; linarith
            have hbound : kk + 1 ≥ 2 * j := calc
              kk + 1 = j * 2^t := hkkeqjt
              _      ≥ j * 2   := Nat.mul_le_mul_left j h2le2t
              _      = 2 * j   := mul_comm _ _
            omega
          have hjworks := ih j hjltkk (Nat.odd_iff.mp hjodd)
          obtain ⟨nⱼ, hnⱼ⟩ := hjworks
          let kfac := kk.factorization
          obtain ⟨ps, hps⟩ := exists_distinct_primes t nⱼ hnⱼ.left kfac.support.toList
          let C := j * (2^t - 1) - 1
          have hCpos : C > 0 := by
            have ht : t > 0 := htpos
            have hj : j > 0 := hjodd.pos
            dsimp [C]
            rw [Nat.mul_sub_left_distrib, Nat.mul_one]
            rw [Nat.sub_sub]
            rw [←hkkeqjt]
            rw [Nat.add_sub_add_right]
            apply Nat.sub_pos_of_lt
            exact hjltkk
          let exps := (List.range t).map (fun i ↦ C * 2^i)
          let x := ((ps.zip exps).map (fun (p, e) ↦ p ^ e)).prod
          have hxnⱼcoprime : Nat.Coprime x nⱼ := by
            dsimp only [x]
            apply Nat.coprime_list_prod_left_iff.mpr
            intro n hnin
            simp only [List.mem_map, Prod.exists] at hnin
            obtain ⟨p, k, hpk⟩ := hnin
            have hpinps : p ∈ ps := (List.of_mem_zip hpk.left).left
            have hpcoprime : Nat.Coprime p nⱼ := (hps.left p hpinps).right.right
            rw [←hpk.right]
            apply Nat.Coprime.pow_left
            exact hpcoprime
          have hxneq0 : x ≠ 0 := by
            dsimp only [x]
            apply List.prod_ne_zero
            apply mt List.mem_map.mp
            simp only [not_exists, not_and]
            intro (p, k) hpk
            apply pow_ne_zero
            apply Nat.Prime.ne_zero
            exact (hps.left (p, k).1 (List.of_mem_zip hpk).left).left
          have hallp : ∀ i ∈ ps, Nat.Prime i := by intro i hi; exact (hps.left i hi).left
          have hneqdx : d x = ((List.range t).map
              (fun i ↦ (2 ^ (t + i)) * j - 2 ^ i * (j + 1) + 1)).prod := by
            dsimp only [x]
            have hexpsgt0 : (∀ i ∈ exps, i > 0) := by
              dsimp [exps]
              intro i hi
              simp only [List.mem_map, List.mem_range] at hi
              obtain ⟨a, ha⟩ := hi
              rw [ha.right.symm]
              exact Nat.mul_pos hCpos (Nat.two_pow_pos a)
            have hlent : exps.length = t := by
              dsimp [exps]; rw [List.length_map, List.length_range]
            have hlen : ps.length = exps.length := by
              rw [hps.right.left]; exact hlent.symm
            rw [d_of_factorization t ps exps hlen hlent hallp hps.right.right hexpsgt0]
            dsimp [exps]
            rw [List.map_map]
            apply congrArg List.prod
            apply List.map_congr_left
            intro i hi
            simp only [Function.comp_apply, Nat.add_right_cancel_iff]
            dsimp [C]
            rw [Nat.mul_sub_right_distrib, Nat.mul_sub_left_distrib, Nat.mul_one]
            rw [Nat.mul_sub_right_distrib, mul_assoc j, ←pow_add]
            rw [Nat.mul_add, Nat.mul_one]
            rw [mul_comm (2^i) j]
            grind
          have hneqdx2 : d (x ^ 2) = ((List.range t).map
              (fun i ↦ (2 ^ (t + i + 1) * j - 2 ^ (i + 1) * (j + 1) + 1))).prod := by
            dsimp only [x]
            have hsqdistr : (List.map (fun x ↦ x.1 ^ x.2) (ps.zip exps)).prod ^ 2
                        = (List.map (fun x ↦ x.1 ^ (2 * x.2)) (ps.zip exps)).prod := by
              induction (ps.zip exps) with
              | nil => simp
              | cons head tail ih =>
                simp only [List.map_cons, List.prod_cons]
                rw [Nat.mul_pow, ih, mul_comm 2 head.2, pow_mul]
            rw [hsqdistr]
            have hexp2 : (List.map (fun x ↦ x.1 ^ (2 * x.2)) (ps.zip exps)) =
                    (List.map (fun x ↦ x.1 ^ x.2)
                      (ps.zip ((List.map (fun y ↦ 2 * y) exps)))) := by
              nth_rw 2 [List.zip_map_right]
              rw [List.map_map]
              simp
            rw [hexp2]
            have hexpsgt0 : (∀ i ∈ (List.map (fun y ↦ 2 * y) exps), i > 0) := by
              dsimp [exps]
              intro i hi
              simp only [List.map_map, List.mem_map, List.mem_range, Function.comp_apply] at hi
              obtain ⟨a, ha⟩ := hi
              rw [ha.right.symm]
              exact Nat.mul_pos (by decide) (Nat.mul_pos hCpos (Nat.two_pow_pos a))
            have hlent : (List.map (fun y ↦ 2 * y) exps).length = t := by
              dsimp [exps]; rw [List.length_map, List.length_map, List.length_range]
            have hlen : ps.length = (List.map (fun y ↦ 2 * y) exps).length := by
              rw [hps.right.left]; exact hlent.symm
            rw [d_of_factorization t ps (List.map (fun y ↦ 2 * y) exps)
              hlen hlent hallp hps.right.right hexpsgt0]
            dsimp [exps]
            rw [List.map_map, List.map_map]
            apply congrArg List.prod
            apply List.map_congr_left
            intro i hi
            simp only [Function.comp_apply, Nat.add_right_cancel_iff]
            dsimp [C]
            rw [mul_comm 2, mul_assoc, mul_comm (2 ^ i) 2, (pow_succ' 2 i).symm]
            rw [Nat.mul_sub_right_distrib, Nat.mul_sub_left_distrib, Nat.mul_one]
            rw [Nat.mul_sub_right_distrib, mul_assoc j, ←pow_add]
            grind
          have htelescopes : d (x ^ 2) * j = d x * (2 ^ t * j - 1) := by
            have h : d (x ^ 2) * (2 ^ t * j - (j + 1) + 1) =
              d x * (2 ^ (2 * t) * j - 2 ^ t * (j + 1) + 1) := by
              let f := fun i ↦ 2 ^ (t + i) * j - 2 ^ i * (j + 1) + 1
              have h1 : (List.map (f ∘ Nat.succ) (List.range t)).prod * f 0 =
                    d (x ^ 2) * (2 ^ t * j - (j + 1) + 1) := by
                    simp only [add_zero, pow_zero, one_mul, hneqdx2, mul_eq_mul_right_iff,
                      Nat.add_eq_zero_iff, one_ne_zero, and_false, or_false, f]
                    apply congrArg List.prod
                    apply List.map_congr_left
                    intro i hi
                    simp
                    rfl
              have h2 : (List.map f (List.range t)).prod * f t =
                  d x * (2 ^ (2 * t) * j - 2 ^ t * (j + 1) + 1) := by
                simp only [hneqdx, mul_eq_mul_left_iff, Nat.add_right_cancel_iff,
                  List.prod_eq_zero_iff, List.mem_map, List.mem_range, Nat.add_eq_zero_iff,
                  one_ne_zero, and_false, exists_const, or_false, f]
                rw [two_mul]
              rw [h1.symm, h2.symm]
              rw [mul_comm _ (f 0)]
              rw [←List.prod_cons]
              have hlhs : f 0 :: List.map (f ∘ Nat.succ) (List.range t) =
                        List.map f (List.range (t + 1)) := by
                rw [List.range_succ_eq_map, List.map_cons, List.map_map]
              have hrhs : (List.map f (List.range t)).prod * f t =
                        (List.map f (List.range (t + 1))).prod := by
                rw [List.range_succ, List.map_append, List.prod_append]; simp
              rw [hlhs, hrhs]
            have hfactor : (2 ^ (2 * t) * j - 2 ^ t * (j + 1) + 1) =
              (2 ^ t * j - 1) * (2 ^ t - 1) := by
              have h1 : 1 ≤ 2^t := by
                apply Nat.succ_le_of_lt
                apply Nat.lt_of_succ_lt
                apply Nat.one_lt_two_pow
                exact Nat.ne_of_gt htpos
              have h2 : 1 ≤ 2^t * j := by linarith [h1, hjodd.pos]
              have h3 : 2 ^ t * (j + 1) ≤ 2 ^ (2 * t) * j := by
                rw [Nat.mul_add, two_mul, pow_add, (Nat.mul_add (2 ^ t) j 1).symm]
                rw [mul_assoc (2 ^ t)]
                apply Nat.mul_le_mul_left
                calc j + 1 ≤ 2 * j     := by linarith [hjodd.pos]
                     _     ≤ 2 ^ t * j := by
                            apply Nat.mul_le_mul_right j
                            apply Nat.succ_le_of_lt
                            apply Nat.one_lt_two_pow
                            exact Nat.ne_of_gt htpos
              zify
              rw [Nat.cast_sub h3]
              zify [h1, h2]
              ring
            have hden : 2 ^ t * j - (j + 1) + 1 = j * (2 ^ t - 1) := by grind
            rw [hfactor, hden] at h
            rw [←mul_assoc, ←mul_assoc] at h
            apply Nat.eq_of_mul_eq_mul_right _
            · exact h
            · apply Nat.sub_pos_of_lt
              apply Nat.one_lt_two_pow
              exact Nat.ne_of_gt htpos
          use nⱼ * x
          have hnⱼprodxneq0 : nⱼ * x ≠ 0 := by
            rw [mul_ne_zero_iff]; exact And.intro hnⱼ.left hxneq0
          refine ⟨hnⱼprodxneq0, ?_⟩
          have hdx2 : d ((nⱼ * x) ^ 2) = (d (nⱼ ^ 2)) * (d (x ^ 2)) := by
            have hmulexp : (nⱼ * x) ^ 2 = nⱼ ^ 2 * x ^ 2 := Nat.mul_pow nⱼ x 2
            rw [hmulexp]
            apply d_multiplicative (nⱼ ^ 2) (x ^ 2)
            exact Nat.Coprime.pow 2 2 hxnⱼcoprime.symm
          have hdx : d (nⱼ * x) = (d nⱼ) * (d x) := by
            apply d_multiplicative nⱼ x; exact hxnⱼcoprime.symm
          rw [hdx2, hdx]
          have hkj : k_minus_1 + 1 = (2 ^ t) * j - 1 := by
            simp only [j, kk]
            have hkj2 : 2 ^ t * ((k_minus_1 + 2) / 2 ^ t) = (k_minus_1 + 1 + 1) :=
              Nat.mul_div_cancel' h_div
            rw [hkj2]
            simp
          rw [hkj, mul_comm (2 ^ t * j - 1), mul_assoc, mul_comm (d nⱼ)]
          rw [htelescopes.symm, hnⱼ.right, mul_comm, mul_assoc]

/-- Finally, we put it all together. -/
theorem imo1998_q3 (k : ℕ) : (k % 2 = 1 ↔ ∃ n : ℕ, n ≠ 0 ∧ d (n ^ 2) = k * d n) :=
  Iff.intro (odd_k_satisfies k) (k_is_odd k)

end Imo1998Q3
