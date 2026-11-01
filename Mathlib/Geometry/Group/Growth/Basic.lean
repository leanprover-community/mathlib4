/-
Copyright (c) 2026 Ezequiel Souza dos Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel Souza dos Santos
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Geometry.Group.WordMetric

import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Finite.Range
import Mathlib.Order.Lattice.Nat

/-!
# Growth function of a finitely generated group

The growth of a group `G` with respect to a generating family `P` is the function sending `n` to
the number of elements of word length at most `n`.

## Main definitions

* `Group.Generators.wordBall`: the closed ball of radius `n` in the word metric.
* `Group.Generators.growth`: the growth function `n ↦ #(wordBall n)`.
* `Function.GrowthDominates`: `f` dominates `g` if `g n ≤ C * f (α * n)` for some `C, α`.
* `Function.GrowthEquivalent`: mutual domination of two functions.
* `Function.HasPolynomialGrowth`: `f` is dominated by `n ↦ (n + 1)^d` for some `d`.
* `Function.HasExponentialGrowth`: `f` dominates `n ↦ 2^n`.
* `Function.HasSuperpolynomialGrowth`: `f` eventually exceeds every polynomial.
* `Function.HasSubexponentialGrowth`: `log f n / n → 0`, stated with natural numbers.
* `Function.HasIntermediateGrowth`: superpolynomial and subexponential growth.
* `Group.Generators.growth_growthEquivalent`: the growth function is independent of the
  finite generating family, up to `GrowthEquivalent`.

## Implementation notes

* `wordBall` is defined via `wordLength`, so it is compatible with the existing word metric API.
* When the index type is finite, `wordBall n` is a finite set, hence `growth n` is the actual
  cardinality.
* Growth comparison uses natural coefficients, which is enough for cardinalities. Open the `Growth`
  locale for the notations `f ≽ᵍ g` and `f ∼ᵍ g`.

## Tags

growth of groups, word ball, geometric group theory
-/

@[expose] public section

open Set

/-- `f` dominates `g` (written `f ≽ᵍ g`) if `g` is bounded by a rescaling of `f`. -/
def Function.GrowthDominates (f g : ℕ → ℕ) : Prop :=
  ∃ C α : ℕ, ∀ n, g n ≤ C * f (α * n)

/-- Two functions are growth-equivalent (written `f ∼ᵍ g`) if each dominates the other. -/
def Function.GrowthEquivalent (f g : ℕ → ℕ) : Prop :=
  f.GrowthDominates g ∧ g.GrowthDominates f

@[inherit_doc Function.GrowthDominates]
scoped[Growth] infix:50 " ≽ᵍ " => Function.GrowthDominates

@[inherit_doc Function.GrowthEquivalent]
scoped[Growth] infix:50 " ∼ᵍ " => Function.GrowthEquivalent

namespace Function

lemma GrowthDominates.refl (f : ℕ → ℕ) : f.GrowthDominates f :=
  ⟨1, 1, by simp⟩

lemma GrowthDominates.trans {f g h : ℕ → ℕ} (hfg : f.GrowthDominates g)
    (hgh : g.GrowthDominates h) : f.GrowthDominates h := by
  obtain ⟨C₁, α₁, h₁⟩ := hfg
  obtain ⟨C₂, α₂, h₂⟩ := hgh
  refine ⟨C₂ * C₁, α₁ * α₂, fun n ↦ ?_⟩
  grw [h₂ n, h₁ (α₂ * n), mul_assoc, mul_assoc]

lemma GrowthEquivalent.refl (f : ℕ → ℕ) : f.GrowthEquivalent f :=
  ⟨.refl f, .refl f⟩

lemma GrowthEquivalent.symm {f g : ℕ → ℕ} (h : f.GrowthEquivalent g) : g.GrowthEquivalent f :=
  ⟨h.2, h.1⟩

lemma GrowthEquivalent.trans {f g h : ℕ → ℕ} (hfg : f.GrowthEquivalent g)
    (hgh : g.GrowthEquivalent h) : f.GrowthEquivalent h :=
  ⟨hfg.1.trans hgh.1, hgh.2.trans hfg.2⟩

lemma GrowthEquivalent.equivalence : Equivalence GrowthEquivalent :=
  ⟨GrowthEquivalent.refl, GrowthEquivalent.symm, GrowthEquivalent.trans⟩

/-- `f` has polynomial growth if it is dominated by `n ↦ (n + 1) ^ d` for some `d`.
We use `n + 1` so that the bound is positive at `n = 0`. -/
def HasPolynomialGrowth (f : ℕ → ℕ) : Prop :=
  ∃ d : ℕ, (fun n ↦ (n + 1) ^ d).GrowthDominates f

/-- `f` has exponential growth if it dominates `n ↦ 2 ^ n`. -/
def HasExponentialGrowth (f : ℕ → ℕ) : Prop :=
  f.GrowthDominates (2 ^ ·)

/-- `f` has superpolynomial growth if it eventually exceeds every polynomial bound. -/
def HasSuperpolynomialGrowth (f : ℕ → ℕ) : Prop :=
  ∀ d : ℕ, ∃ n₀, ∀ n ≥ n₀, (n + 1) ^ d < f n

/-- `f` has subexponential growth if `log (f n) / n → 0`. Equivalently, for every `k`
we have `f n ^ k ≤ 2 ^ n` for all sufficiently large `n`. -/
def HasSubexponentialGrowth (f : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ n₀, ∀ n ≥ n₀, f n ^ k ≤ 2 ^ n

/-- `f` has intermediate growth if it is both superpolynomial and subexponential. -/
def HasIntermediateGrowth (f : ℕ → ℕ) : Prop :=
  f.HasSuperpolynomialGrowth ∧ f.HasSubexponentialGrowth

lemma HasPolynomialGrowth.of_growthDominates {f g : ℕ → ℕ} (hf : f.HasPolynomialGrowth)
    (hfg : f.GrowthDominates g) : g.HasPolynomialGrowth :=
  hf.imp fun _ hd ↦ hd.trans hfg

lemma HasPolynomialGrowth.of_growthEquivalent {f g : ℕ → ℕ} (h : f.GrowthEquivalent g)
    (hf : f.HasPolynomialGrowth) : g.HasPolynomialGrowth :=
  hf.of_growthDominates h.1

lemma HasExponentialGrowth.of_growthDominates {f g : ℕ → ℕ} (hf : f.HasExponentialGrowth)
    (hgf : g.GrowthDominates f) : g.HasExponentialGrowth :=
  hgf.trans hf

lemma HasExponentialGrowth.of_growthEquivalent {f g : ℕ → ℕ} (h : f.GrowthEquivalent g)
    (hf : f.HasExponentialGrowth) : g.HasExponentialGrowth :=
  hf.of_growthDominates h.2

/-- Superpolynomial growth is inherited by any monotone function that dominates a
superpolynomial function. -/
lemma HasSuperpolynomialGrowth.of_growthDominates {f g : ℕ → ℕ} (hg : Monotone g)
    (hf : f.HasSuperpolynomialGrowth) (hgf : g.GrowthDominates f) :
    g.HasSuperpolynomialGrowth := by
  obtain ⟨C, α, hCf⟩ := hgf
  intro d
  obtain ⟨n₀, hn₀⟩ := hf (d + 1)
  let N := max (n₀ * (α + 1) + 1) ((C * (α + 1) ^ d + 1) * (α + 1))
  refine ⟨N, fun n hn ↦ ?_⟩
  set m := n / (α + 1)
  have hm : n₀ ≤ m := by
    have : n₀ * (α + 1) ≤ n := by
      have : n₀ * (α + 1) + 1 ≤ n := le_trans (le_max_left _ _) hn
      omega
    exact (Nat.le_div_iff_mul_le (Nat.succ_pos α)).2 this
  have hf' : (m + 1) ^ (d + 1) < f m := hn₀ m hm
  have hfg : f m ≤ C * g (α * m) := hCf m
  have hαm : α * m ≤ n :=
    calc
      α * m ≤ (α + 1) * m := Nat.mul_le_mul_right m (Nat.le_succ α)
      _ ≤ n := Nat.mul_div_le n (α + 1)
  have hCg : C * g (α * m) ≤ C * g n := Nat.mul_le_mul_left C (hg hαm)
  have hlt : (m + 1) ^ (d + 1) < C * g n := hf'.trans_le (hfg.trans hCg)
  have hn1 : n + 1 ≤ (α + 1) * (m + 1) :=
    Nat.succ_le_of_lt (Nat.lt_mul_div_succ n (Nat.succ_pos α))
  have hpow : (n + 1) ^ d ≤ (α + 1) ^ d * (m + 1) ^ d := by
    simpa [mul_pow] using Nat.pow_le_pow_left hn1 d
  by_cases hC0 : C = 0
  · subst hC0
    have : f m = 0 := Nat.eq_zero_of_le_zero (by simpa using hCf m)
    have : 0 < f m := Nat.zero_lt_of_lt hf'
    omega
  have hm1 : C * (α + 1) ^ d < m + 1 := by
    have : (C * (α + 1) ^ d + 1) * (α + 1) ≤ n := le_trans (le_max_right _ _) hn
    have : C * (α + 1) ^ d + 1 ≤ m := (Nat.le_div_iff_mul_le (Nat.succ_pos α)).2 this
    omega
  have : (n + 1) ^ d * C < (m + 1) ^ (d + 1) := by
    have h1 : (n + 1) ^ d * C ≤ (α + 1) ^ d * (m + 1) ^ d * C :=
      Nat.mul_le_mul_right C hpow
    have hαC : (α + 1) ^ d * C < m + 1 := by rwa [Nat.mul_comm]
    have h1' : (n + 1) ^ d * C ≤ ((α + 1) ^ d * C) * (m + 1) ^ d := by
      convert h1 using 1; ring
    have h2 : ((α + 1) ^ d * C) * (m + 1) ^ d < (m + 1) * (m + 1) ^ d :=
      Nat.mul_lt_mul_of_pos_right hαC (Nat.pow_pos (Nat.succ_pos m))
    exact h1'.trans_lt (h2.trans_eq (pow_succ' (m + 1) d).symm)
  have hCg' : (n + 1) ^ d * C < C * g n := this.trans hlt
  exact Nat.lt_of_mul_lt_mul_left (a := C) (by
    rw [Nat.mul_comm C]; exact hCg')

lemma HasSuperpolynomialGrowth.of_growthEquivalent {f g : ℕ → ℕ} (hg : Monotone g)
    (h : f.GrowthEquivalent g) (hf : f.HasSuperpolynomialGrowth) :
    g.HasSuperpolynomialGrowth :=
  hf.of_growthDominates hg h.2

/-- Squares grow slower than powers of two for exponents at least 5. -/
lemma sq_lt_two_pow {k : ℕ} (hk : 5 ≤ k) : k ^ 2 < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hlin : 2 * k + 1 < 2 ^ k := by
      have : 2 * k + 1 ≤ k * k := by
        have hk3 : 3 ≤ k := hk.trans' (by decide)
        nlinarith
      exact this.trans_lt (by simpa [pow_two] using ih)
    calc
      (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
      _ < 2 ^ k + 2 * k + 1 := by nlinarith
      _ = 2 ^ k + (2 * k + 1) := by ring
      _ < 2 ^ k + 2 ^ k := Nat.add_lt_add_left hlin _
      _ = 2 ^ (k + 1) := by rw [← two_mul, mul_comm, pow_succ]

/-- Superpolynomial growth follows from a quadratic self-lower-bound
`f n ^ 2 ≤ C * f (α * n)` along a monotone unbounded function. -/
lemma HasSuperpolynomialGrowth.of_sq_mul {f : ℕ → ℕ} (hf : Monotone f)
    (hunb : ∀ N, ∃ n, N < f n) {C α : ℕ} (hC : 0 < C) (hα : 2 ≤ α)
    (hsq : ∀ n, f n * f n ≤ C * f (α * n)) : f.HasSuperpolynomialGrowth := by
  obtain ⟨nraw, hnraw⟩ := hunb (2 * C)
  let n₁ := max nraw 1
  have hn₁ : 2 * C < f n₁ := lt_of_lt_of_le hnraw (hf (le_max_left _ _))
  have hn₁pos : 0 < n₁ := lt_of_lt_of_le (Nat.succ_pos 0) (le_max_right _ _)
  have hbase : C * 2 ≤ f n₁ := le_of_lt (by rwa [mul_comm] at hn₁)
  have hiter : ∀ k, C * 2 ^ (2 ^ k) ≤ f (α ^ k * n₁) := by
    intro k
    induction k with
    | zero => simpa [pow_zero, pow_one] using hbase
    | succ k ih =>
      have hαk : α * (α ^ k * n₁) = α ^ (k + 1) * n₁ := by
        rw [← mul_assoc, ← pow_succ']
      have hsq' := hsq (α ^ k * n₁)
      rw [hαk] at hsq'
      have hsqid : 2 ^ (2 ^ (k + 1)) = 2 ^ (2 ^ k) * 2 ^ (2 ^ k) := by
        rw [← pow_add, ← two_mul, mul_comm, pow_succ]
      have hgoal : C * 2 ^ (2 ^ (k + 1)) * C =
          (C * 2 ^ (2 ^ k)) * (C * 2 ^ (2 ^ k)) := by
        rw [hsqid]; ring
      have hdiv : C * 2 ^ (2 ^ (k + 1)) ≤
          f (α ^ k * n₁) * f (α ^ k * n₁) / C :=
        (Nat.le_div_iff_mul_le hC).2 (by rw [hgoal]; exact Nat.mul_le_mul ih ih)
      exact hdiv.trans (Nat.div_le_of_le_mul (by rwa [mul_comm] at hsq'))
  have hα1 : 1 < α := lt_of_lt_of_le (by decide : 1 < 2) hα
  intro d
  let B := α + n₁ + 1
  have hB2 : 2 ≤ B := by
    have : 2 ≤ α := hα
    omega
  have hB1 : 1 < B := lt_of_lt_of_le (by decide : 1 < 2) hB2
  let L := Nat.log 2 B + 1
  have hLpos : 0 < L := Nat.succ_pos _
  have hex : ∃ K, ∀ k ≥ K, (α ^ (k + 1) * n₁ + 1) ^ d < C * 2 ^ (2 ^ k) := by
    cases d with
    | zero =>
      refine ⟨0, fun k _ ↦ ?_⟩
      have : (1 : ℕ) < C * 2 ^ (2 ^ k) := by
        have h2 : (2 : ℕ) ≤ 2 ^ (2 ^ k) :=
          Nat.le_self_pow (Nat.pow_pos (by decide : (0 : ℕ) < 2)).ne' 2
        have : 2 ≤ C * 2 ^ (2 ^ k) := h2.trans (Nat.le_mul_of_pos_left _ hC)
        omega
      simpa using this
    | succ d' =>
      let M := L * d'.succ + 1
      refine ⟨max 5 (2 * M), fun k hk ↦ ?_⟩
      have hk5 : 5 ≤ k := le_trans (le_max_left _ _) hk
      have hkM : 2 * M ≤ k := le_trans (le_max_right _ _) hk
      have hbound : α ^ (k + 1) * n₁ + 1 ≤ B ^ (k + 2) := by
        have h1 : 1 ≤ α ^ (k + 1) := Nat.one_le_pow _ _ (Nat.zero_lt_of_lt hα1)
        have hstep : α ^ (k + 1) * n₁ + 1 ≤ α ^ (k + 1) * (n₁ + 1) := by
          calc
            α ^ (k + 1) * n₁ + 1 ≤ α ^ (k + 1) * n₁ + α ^ (k + 1) :=
              Nat.add_le_add_left h1 _
            _ = α ^ (k + 1) * (n₁ + 1) := by rw [Nat.mul_succ]
        have hαB : α ≤ B := by omega
        have hnB : n₁ + 1 ≤ B := by omega
        have : α ^ (k + 1) * (n₁ + 1) ≤ B ^ (k + 1) * B :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hαB _) hnB
        exact hstep.trans (this.trans_eq (pow_succ B (k + 1)).symm)
      have hBm : B ^ (k + 2) < 2 ^ (L * (k + 2)) := by
        have hBlt : B < 2 ^ L := Nat.lt_pow_succ_log_self (by decide : 1 < 2) B
        simpa [← pow_mul] using Nat.pow_lt_pow_left hBlt (Nat.succ_ne_zero (k + 1))
      have hpoly : (α ^ (k + 1) * n₁ + 1) ^ d'.succ ≤ (B ^ (k + 2)) ^ d'.succ :=
        Nat.pow_le_pow_left hbound _
      have hpoly' : (B ^ (k + 2)) ^ d'.succ < 2 ^ (L * (k + 2) * d'.succ) := by
        simpa [← pow_mul, ← pow_mul] using
          Nat.pow_lt_pow_left hBm (Nat.succ_ne_zero d')
      have hexp : L * (k + 2) * d'.succ < 2 ^ k := by
        have hsqk : k ^ 2 < 2 ^ k := sq_lt_two_pow hk5
        have hMk : M * (k + 2) ≤ k * k := by
          have : M * (k + 2) ≤ 2 * M * k := by
            have : k + 2 ≤ 2 * k := by omega
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              Nat.mul_le_mul_left M this
          have : 2 * M * k ≤ k * k := Nat.mul_le_mul_right k hkM
          exact this.trans' ‹M * (k + 2) ≤ 2 * M * k›
        have hLd : L * (k + 2) * d'.succ ≤ M * (k + 2) := by
          have : L * d'.succ ≤ M := Nat.le_add_right _ 1
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            Nat.mul_le_mul_right (k + 2) this
        exact (hLd.trans hMk).trans_lt (by simpa [pow_two] using hsqk)
      have h2 : 2 ^ (L * (k + 2) * d'.succ) ≤ 2 ^ (2 ^ k) :=
        Nat.pow_le_pow_right (by decide : 1 ≤ 2) (le_of_lt hexp)
      have hC2 : 2 ^ (2 ^ k) ≤ C * 2 ^ (2 ^ k) :=
        Nat.le_mul_of_pos_left _ hC
      exact (hpoly.trans_lt hpoly').trans_le (h2.trans hC2)
  obtain ⟨K, hK⟩ := hex
  refine ⟨α ^ K * n₁, fun n hn ↦ ?_⟩
  have hdiv : n₁ ≤ n := by
    have : n₁ ≤ α ^ K * n₁ :=
      Nat.le_mul_of_pos_left _ (Nat.pow_pos (Nat.zero_lt_of_lt hα1))
    exact this.trans hn
  have hndiv : n / n₁ ≠ 0 := (Nat.div_pos hdiv hn₁pos).ne'
  set k := Nat.log α (n / n₁)
  have hkK : K ≤ k := by
    have : α ^ K ≤ n / n₁ := (Nat.le_div_iff_mul_le hn₁pos).2 hn
    exact (Nat.le_log_iff_pow_le hα1 hndiv).2 this
  have hαk : α ^ k * n₁ ≤ n := by
    have : α ^ k ≤ n / n₁ := Nat.pow_log_le_self _ hndiv
    exact (Nat.le_div_iff_mul_le hn₁pos).1 this
  have hfkn : C * 2 ^ (2 ^ k) ≤ f n := (hiter k).trans (hf hαk)
  have hnup : n + 1 ≤ α ^ (k + 1) * n₁ + 1 := by
    have hlog : n / n₁ < α ^ (k + 1) := Nat.lt_pow_succ_log_self hα1 (n / n₁)
    have : n < α ^ (k + 1) * n₁ :=
      calc
        n < n₁ * (n / n₁ + 1) := Nat.lt_mul_div_succ n hn₁pos
        _ ≤ n₁ * α ^ (k + 1) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hlog)
        _ = α ^ (k + 1) * n₁ := Nat.mul_comm _ _
    exact Nat.succ_le_of_lt (this.trans_le (Nat.le_add_right _ _))
  have hpoly : (n + 1) ^ d ≤ (α ^ (k + 1) * n₁ + 1) ^ d :=
    Nat.pow_le_pow_left hnup d
  exact hpoly.trans_lt ((hK k hkK).trans_le hfkn)

end Function

namespace Group.Generators

variable {G ι ι' : Type*} [Group G] (P : Group.Generators G ι)

/-- The closed ball of radius `n` in the word metric: elements of word length at most `n`. -/
@[to_additive /-- The closed ball of radius `n` in the word metric: elements of word length at most
`n`. -/]
def wordBall (n : ℕ) : Set G := {g | P.wordLength g ≤ n}

@[to_additive (attr := simp)]
lemma mem_wordBall {n : ℕ} {g : G} : g ∈ P.wordBall n ↔ P.wordLength g ≤ n :=
  Iff.rfl

@[to_additive]
lemma wordBall_eq_image (n : ℕ) :
    P.wordBall n = P.wordProd '' {l : List (ι × Bool) | l.length ≤ n} := by
  ext g
  simp [mem_image, P.wordLength_le_iff]

@[to_additive]
lemma one_mem_wordBall (n : ℕ) : 1 ∈ P.wordBall n := by
  simp

@[to_additive (attr := simp)]
lemma wordBall_zero : P.wordBall 0 = {1} := by
  ext g
  simp [wordLength_eq_zero_iff]

/-- If the generating family is finite, then the word ball of any finite radius is finite. -/
@[to_additive /-- If the generating family is finite, then the word ball of any finite radius is
finite. -/]
lemma finite_wordBall [Finite ι] (n : ℕ) : (P.wordBall n).Finite := by
  rw [wordBall_eq_image]
  exact (List.finite_length_le (ι × Bool) n).image _

/-- The growth function of `G` with respect to the generating family `P`: the number of elements
of word length at most `n`. -/
@[to_additive /-- The growth function of `G` with respect to the generating family `P`: the number
of elements of word length at most `n`. -/]
noncomputable def growth (n : ℕ) : ℕ := (P.wordBall n).ncard

@[to_additive]
lemma growth_eq_ncard (n : ℕ) : P.growth n = (P.wordBall n).ncard :=
  rfl

@[to_additive (attr := simp)]
lemma growth_zero : P.growth 0 = 1 := by
  simp [growth]

@[to_additive]
lemma monotone_growth [Finite ι] : Monotone P.growth := by
  intro m n hmn
  refine ncard_le_ncard (fun g hg ↦ ?_) (P.finite_wordBall n)
  exact hg.trans hmn

@[to_additive]
lemma exists_one_lt_growth [Infinite G] [Finite ι] : ∃ n, 1 < P.growth n := by
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  refine ⟨P.wordLength g, ?_⟩
  have hsubset : ({1, g} : Set G) ⊆ P.wordBall (P.wordLength g) := by
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact P.one_mem_wordBall _
    · simp [wordBall]
  have : 2 ≤ ({1, g} : Set G).ncard := by
    rw [ncard_insert_of_notMem (by simp [hg.symm]), ncard_singleton]
  exact lt_of_lt_of_le (by decide : 1 < 2)
    (this.trans (ncard_le_ncard hsubset (P.finite_wordBall _)))

/-- The growth function of an infinite finitely generated group is unbounded. -/
@[to_additive]
lemma exists_lt_growth [Infinite G] [Finite ι] (N : ℕ) : ∃ n, N < P.growth n := by
  by_contra! h
  have hr : (Set.range P.growth).Nonempty := ⟨P.growth 0, 0, rfl⟩
  have hf : (Set.range P.growth).Finite :=
    (Set.finite_Iic N).subset fun x hx ↦ by
      obtain ⟨n, rfl⟩ := hx
      exact h n
  obtain ⟨n, hn⟩ : ∃ n, P.growth n = sSup (Set.range P.growth) := by
    have : sSup (Set.range P.growth) ∈ Set.range P.growth := Nat.sSup_mem hr hf.bddAbove
    simpa [Set.mem_range] using this
  have hEq : ∀ m ≥ n, P.wordBall m = P.wordBall n := by
    intro m hm
    refine (eq_of_subset_of_ncard_le (fun g hg ↦ (hg : P.wordLength g ≤ n).trans hm)
      ?_ (P.finite_wordBall m)).symm
    have hle : P.growth m ≤ P.growth n := by
      rw [hn]
      exact le_csSup hf.bddAbove ⟨m, rfl⟩
    have hge : P.growth n ≤ P.growth m := P.monotone_growth hm
    simpa [growth] using (hle.antisymm hge).le
  have huniv : (Set.univ : Set G) = P.wordBall n := by
    ext g
    constructor
    · intro _
      by_cases hg : P.wordLength g ≤ n
      · exact hg
      · have : g ∈ P.wordBall (P.wordLength g) := by simp [wordBall]
        rwa [hEq _ (le_of_not_ge hg)] at this
    · intro; trivial
  have hfin : (Set.univ : Set G).Finite := huniv ▸ P.finite_wordBall n
  exact hfin.not_infinite Set.infinite_univ

@[to_additive]
lemma wordLength_wordProd_le_mul {Q : Group.Generators G ι'} {α : ℕ}
    (hα : ∀ j, P.wordLength (Q.val j) ≤ α) (l : List (ι' × Bool)) :
    P.wordLength (Q.wordProd l) ≤ α * l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rcases x with ⟨j, b⟩
    have hj : P.wordLength (cond b (Q.val j) (Q.val j)⁻¹) ≤ α := by
      cases b <;> simpa [wordLength_inv] using hα j
    calc
      P.wordLength (Q.wordProd ((j, b) :: l))
          = P.wordLength (cond b (Q.val j) (Q.val j)⁻¹ * Q.wordProd l) := by
            rw [wordProd_cons]
      _ ≤ P.wordLength (cond b (Q.val j) (Q.val j)⁻¹) + P.wordLength (Q.wordProd l) :=
            P.wordLength_mul_le _ _
      _ ≤ α + α * l.length := Nat.add_le_add hj ih
      _ = α * ((j, b) :: l).length := by simp [Nat.mul_succ, Nat.add_comm]

/-- Any two finite generating families yield comparable word lengths. -/
@[to_additive /-- Any two finite generating families yield comparable word lengths. -/]
lemma exists_mul_le_wordLength [Finite ι'] (Q : Group.Generators G ι') :
    ∃ α, ∀ g, P.wordLength g ≤ α * Q.wordLength g := by
  obtain ⟨α, hα⟩ := (finite_range fun j : ι' ↦ P.wordLength (Q.val j)).bddAbove
  refine ⟨α, fun g ↦ ?_⟩
  obtain ⟨l, hl, rfl⟩ := Q.exists_isGeodesic g
  simpa [hl.eq] using P.wordLength_wordProd_le_mul (fun j ↦ hα ⟨j, rfl⟩) l

/-- The growth function of a finite generating family dominates that of any other finite
generating family. -/
@[to_additive /-- The growth function of a finite generating family dominates that of any other
finite generating family. -/]
lemma growthDominates_growth [Finite ι] [Finite ι'] (Q : Group.Generators G ι') :
    P.growth.GrowthDominates Q.growth := by
  obtain ⟨α, hα⟩ := P.exists_mul_le_wordLength Q
  refine ⟨1, α, fun n ↦ ?_⟩
  rw [one_mul]
  refine ncard_le_ncard (fun g hg ↦ ?_) (P.finite_wordBall (α * n))
  exact (hα g).trans (Nat.mul_le_mul_left α hg)

/-- The growth of a finitely generated group is independent of the finite generating family. -/
@[to_additive /-- The growth of a finitely generated group is independent of the finite generating
family. -/]
theorem growth_growthEquivalent [Finite ι] [Finite ι'] (Q : Group.Generators G ι') :
    P.growth.GrowthEquivalent Q.growth :=
  ⟨P.growthDominates_growth Q, Q.growthDominates_growth P⟩

/-- A generating family has polynomial growth if its growth function does. -/
@[to_additive /-- A generating family has polynomial growth if its growth function does. -/]
def HasPolynomialGrowth : Prop := Function.HasPolynomialGrowth P.growth

/-- A generating family has exponential growth if its growth function does. -/
@[to_additive /-- A generating family has exponential growth if its growth function does. -/]
def HasExponentialGrowth : Prop := Function.HasExponentialGrowth P.growth

/-- A generating family has superpolynomial growth if its growth function does. -/
@[to_additive /-- A generating family has superpolynomial growth if its growth function does. -/]
def HasSuperpolynomialGrowth : Prop := Function.HasSuperpolynomialGrowth P.growth

/-- A generating family has subexponential growth if its growth function does. -/
@[to_additive /-- A generating family has subexponential growth if its growth function does. -/]
def HasSubexponentialGrowth : Prop := Function.HasSubexponentialGrowth P.growth

/-- A generating family has intermediate growth if its growth function does. -/
@[to_additive /-- A generating family has intermediate growth if its growth function does. -/]
def HasIntermediateGrowth : Prop := Function.HasIntermediateGrowth P.growth

end Group.Generators
