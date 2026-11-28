/-
Copyright (c) 2026 Ezequiel Souza dos Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel Souza dos Santos
-/
module

public import Mathlib.Geometry.Group.Growth.Basic

import Mathlib.Data.Nat.Log

/-!
# Growth classes for functions and finitely generated groups

This file defines the standard growth classes in terms of GrowthDominates /
GrowthEquivalent, and transfers them to Group.Generators.

## Main definitions

* Function.HasPolynomialGrowth
* Function.HasExponentialGrowth
* Function.HasSuperpolynomialGrowth
* Function.HasSubexponentialGrowth
* Function.HasIntermediateGrowth
* the corresponding predicates on Group.Generators

## Tags

growth of groups, geometric group theory
-/

@[expose] public section

namespace Function

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

/-- A constant is eventually dominated by any positive exponential. -/
lemma exists_const_le_two_pow (M : ℕ) : ∃ n₀, ∀ n ≥ n₀, M ≤ 2 ^ n := by
  refine ⟨M, fun n hn ↦ ?_⟩
  have : M ≤ 2 ^ M := Nat.lt_two_pow_self.le
  exact this.trans (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn)

/-- Subexponential growth is inherited by any function dominated by a subexponential
function. -/
lemma HasSubexponentialGrowth.of_growthDominates {f g : ℕ → ℕ}
    (hf : f.HasSubexponentialGrowth) (hfg : f.GrowthDominates g) :
    g.HasSubexponentialGrowth := by
  obtain ⟨C, α, hCg⟩ := hfg
  intro k
  cases k with
  | zero =>
    exact ⟨0, fun n _ ↦ Nat.one_le_two_pow⟩
  | succ k =>
    cases α with
    | zero =>
      obtain ⟨n₀, hn₀⟩ := exists_const_le_two_pow ((C * f 0) ^ k.succ)
      refine ⟨n₀, fun n hn ↦ ?_⟩
      have hg : g n ≤ C * f 0 := by simpa using hCg n
      exact (Nat.pow_le_pow_left hg _).trans (hn₀ n hn)
    | succ α =>
      obtain ⟨n₁, hn₁⟩ := hf (2 * k.succ * α.succ)
      obtain ⟨n₂, hn₂⟩ := exists_const_le_two_pow (C ^ (2 * k.succ))
      refine ⟨max n₁ n₂, fun n hn ↦ ?_⟩
      have hαn : n₁ ≤ α.succ * n :=
        le_trans (le_trans (le_max_left _ _) hn)
          (Nat.le_mul_of_pos_left _ (Nat.succ_pos α))
      have hf' : f (α.succ * n) ^ (2 * k.succ * α.succ) ≤ 2 ^ (α.succ * n) :=
        hn₁ _ hαn
      have hg : g n ≤ C * f (α.succ * n) := hCg n
      have hpow : g n ^ (2 * k.succ) ≤
          C ^ (2 * k.succ) * f (α.succ * n) ^ (2 * k.succ) := by
        simpa [mul_pow] using Nat.pow_le_pow_left hg (2 * k.succ)
      have hα : 0 < α.succ := Nat.succ_pos _
      have hsq : (g n ^ k.succ) ^ 2 ≤ C ^ (2 * k.succ) * 2 ^ n := by
        have hleft : (g n ^ (2 * k.succ)) ^ α.succ ≤
            (C ^ (2 * k.succ) * f (α.succ * n) ^ (2 * k.succ)) ^ α.succ :=
          Nat.pow_le_pow_left hpow _
        have hrewrite :
            (C ^ (2 * k.succ) * f (α.succ * n) ^ (2 * k.succ)) ^ α.succ =
              C ^ (2 * k.succ * α.succ) *
                f (α.succ * n) ^ (2 * k.succ * α.succ) := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
        have hright :
            C ^ (2 * k.succ * α.succ) * f (α.succ * n) ^ (2 * k.succ * α.succ) ≤
              C ^ (2 * k.succ * α.succ) * 2 ^ (α.succ * n) :=
          Nat.mul_le_mul_left _ hf'
        have hC2 : C ^ (2 * k.succ * α.succ) * 2 ^ (α.succ * n) =
            (C ^ (2 * k.succ) * 2 ^ n) ^ α.succ := by
          rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n]
        have : (g n ^ (2 * k.succ)) ^ α.succ ≤
            (C ^ (2 * k.succ) * 2 ^ n) ^ α.succ :=
          (hleft.trans_eq hrewrite).trans (hright.trans_eq hC2)
        have hred : g n ^ (2 * k.succ) ≤ C ^ (2 * k.succ) * 2 ^ n :=
          (Nat.pow_le_pow_iff_left hα.ne').1 this
        have hsqid : g n ^ (2 * k.succ) = (g n ^ k.succ) ^ 2 := by
          rw [Nat.mul_comm, pow_mul, pow_two]
        rwa [← hsqid]
      have hC : C ^ (2 * k.succ) ≤ 2 ^ n := hn₂ n (le_trans (le_max_right _ _) hn)
      have : (g n ^ k.succ) ^ 2 ≤ (2 ^ n) ^ 2 :=
        hsq.trans (by
          have : C ^ (2 * k.succ) * 2 ^ n ≤ 2 ^ n * 2 ^ n :=
            Nat.mul_le_mul_right _ hC
          rwa [pow_two, Nat.mul_comm (2 ^ n)])
      exact (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).1 this

lemma HasSubexponentialGrowth.of_growthEquivalent {f g : ℕ → ℕ}
    (h : f.GrowthEquivalent g) (hf : f.HasSubexponentialGrowth) :
    g.HasSubexponentialGrowth :=
  hf.of_growthDominates h.1

lemma HasIntermediateGrowth.of_growthEquivalent {f g : ℕ → ℕ} (hg : Monotone g)
    (h : f.GrowthEquivalent g) (hf : f.HasIntermediateGrowth) :
    g.HasIntermediateGrowth :=
  ⟨hf.1.of_growthEquivalent hg h, hf.2.of_growthEquivalent h⟩

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

variable {G ι : Type*} [Group G] (P : Group.Generators G ι)

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
