import Mathlib.Algebra.Group.Subgroup.ZPowers
import Mathlib.Tactic
import MIL.common
import Mathlib.Algebra.BigOperators.Basic



noncomputable section Special_Example_070801

open Classical Set Function


variable {α β : Type*} [Nonempty β] (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n

def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x

theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  dsimp [invFun]
  have : ∀ i :ℕ ,x ∉ sbAux f g i := by
    by_contra nh; push_neg at nh
    rcases nh with ⟨i, ih⟩
    have : x ∈ ⋃ n, sbAux f g n := mem_iUnion_of_mem i ih
    contradiction
  have : x ∈ g '' univ := by
    by_contra nh; push_neg at nh
    have : x ∉ univ \ g '' univ := this 0
    have : x ∉ (univ \ g '' univ) ∪ g '' univ := by tauto
    simp only [image_univ, diff_union_self, univ_union, mem_univ, not_true_eq_false] at this
  have : ∃ y, g y = x := by
    simp at this
    assumption
  exact invFun_eq this

theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂
  intro (hxeq : h x₁ = h x₂)
  show x₁ = x₂
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      apply _root_.not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by
        rw [← (sb_right_inv f g x₂nA)]
        congr 1
        exact id (Eq.symm hxeq)
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, hn, x₂eq.symm⟩
    rw [if_pos x₁A, if_pos x₂A] at hxeq
    exact hf hxeq
  push_neg at xA
  rw [if_neg xA.1 , if_neg xA.2] at hxeq
  rw [← (sb_right_inv f g xA.1), ← (sb_right_inv f g xA.2)]
  congr 1

end Special_Example_070801



section Special_Example_070802
/-
Given an nature number $n$ which is not less than 2, prove either it is a prime or it can be divided by a prime nature number.
-/
theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  have : m < 2 := by linarith
  have : m ≤ 1 := by exact Nat.le_of_lt_succ this
  have : m < 1 := by exact Nat.lt_of_le_of_ne this h1
  have : m ≤ 0 := by exact Nat.le_of_lt_succ this
  have : m = 0 := by exact Nat.eq_zero_of_le_zero this
  contradiction

#check Nat.strong_induction_on
example {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  induction' n using Nat.strong_induction_on with n hn
  by_cases np : n.Prime
  · use n
  · rw [Nat.prime_def_lt] at np
    push_neg at np
    rcases np h with ⟨m, ⟨mltn, ⟨mdvdn, mne1⟩⟩⟩
    have : m ≠ 0 := by
      intro mz
      rw [mz, zero_dvd_iff] at mdvdn
      linarith
    have mge2 : 2 ≤ m := two_le this mne1
    rcases hn m mltn mge2 with ⟨p, ⟨pprime, pdvdm⟩⟩
    use p
    constructor
    · exact pprime
    · exact Nat.dvd_trans pdvdm mdvdn

end Special_Example_070802



section Special_Example_070803
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

lemma fac_pos(n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · exact Nat.zero_lt_succ 0
  · rw [fac]
    exact Nat.succ_mul_pos n ih

example (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · simp [fac]
  · induction' n with n ih
    · simp [fac]
    · calc
        _ = 2 * 2 ^ n := by exact Nat.pow_succ'
        _ ≤ 2 * fac (n + 1) := by apply mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ (n + 2) * fac (n + 1):= by
          apply mul_le_mul_of_nonneg_right (by linarith) (by linarith[fac_pos])
        _ = fac (n + 1 + 1) := by rfl

end Special_Example_070803



section Special_Example_070804
open BigOperators
open Finset

/-
$1 ^ 2 + 2 ^ 2 + \cdots + n ^ 2 = \dfrac{n * (n + 1) * (2 * n + 1)}{6}$
-/
example (n : ℕ) : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 6)
  induction' n with n ih
  · simp
  · rw [Finset.sum_range_succ, mul_add 6, ← ih]
    ring

end Special_Example_070804



section Special_Example_070805
open BigOperators
open Finset
def fac₁ : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac₁ n


example (n : ℕ) : fac₁ n = ∏ i in range n, (i + 1) := by
  induction' n with n ih
  · rfl
  · rw [Finset.prod_range_succ, ←ih]
    nth_rw 1 [fac₁]
    exact Nat.mul_comm (n + 1) (fac₁ n)

end Special_Example_070805



section Special_Example_070806
open BigOperators
open Finset
/-
$1 + 3 + \cdots + (2 * n - 1) = n ^ 2$
-/
def p : ℕ → Prop := fun n ↦ Odd n

noncomputable instance : DecidablePred p := fun n ↦ Classical.propDecidable (p n)

#check Finset.sum_filter
#check Finset.sum_range_succ
#check if_pos
#check if_neg

example (n : ℕ) : ∑ i ∈ range (2 * n) with p i, i = n * n := by
  --By induction
  induction' n with n ih
  · --Base case is trivial
    simp only [mul_zero, range_zero, filter_empty, sum_empty]
  · rw [Finset.sum_filter] at ih
    rw [Finset.sum_filter]
    show (∑ a ∈ range (2 * n + 1 + 1), if p a then a else 0) = (n + 1) * (n + 1)
    rw [Finset.sum_range_succ]
    have : p (2 * n + 1) = True := by
      unfold p
      unfold Odd
      simp only [add_left_inj, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, exists_eq']
    have : (if p (2 * n + 1) then (2 * n + 1) else 0) = 2 * n + 1 := ite_cond_eq_true (2 * n + 1) 0 this
    rw [this]
    rw [Finset.sum_range_succ]
    have : p (2 * n) = False := by
      unfold p
      unfold Odd
      simp only [eq_iff_iff, iff_false, not_exists]
      intro _
      exact Nat.two_mul_ne_two_mul_add_one
    have : (if p (2 * n) then 2 * n else 0) = 0 := ite_cond_eq_false (2 * n) 0 this
    --Use induction hypothesis and we simplifacte the equation ,we are done
    rw [this, ih]
    ring

end Special_Example_070806



section Special_Example_070807

variable {X : Type*} [MetricSpace X]
open Set Filter
open Topology Filter
open Finset Filter Topology Filter BigOperators

example {u : ℕ → X} (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by
    have : ∃ N : ℕ , 2 ^ N > 2 / ε := pow_unbounded_of_one_lt (2 / ε) (by norm_num)
    rcases this with ⟨N, hn⟩
    use N
    have : 1 / (2 ^ N) < 1 / (2 / ε) := by
      have h2 : 2 / ε > 0 := div_pos (by norm_num) ε_pos
      exact one_div_lt_one_div_of_lt h2 hn
    calc
      _ < 1 / (2 / ε) * 2 := by linarith
      _ = ε := by simp only [one_div, inv_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.div_mul_cancel]
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := PseudoMetricSpace.dist_comm (u (N + k)) (u N)
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) := by
      induction' k with k ih
      · simp only [add_zero, dist_self, range_zero, sum_empty, le_refl]
      · have : N + k ≥ N := by linarith
        have step1 : dist (u (N + 0)) (u (N + k)) ≤ ∑ i ∈ Finset.range k, dist (u (N + i)) (u (N + (i + 1))) :=
          ih this
        have step2 : dist (u (N + 0)) (u (N + (k + 1))) ≤ dist (u (N + 0)) (u (N + (k))) + dist (u (N + k)) (u (N + (k + 1))) :=
          dist_triangle (u (N + 0)) (u (N + k)) (u (N + (k + 1)))
        have step3 : ∑ i ∈ Finset.range k, dist (u (N + i)) (u (N + (i + 1))) + dist (u (N + k)) (u (N + (k + 1))) =
                      ∑ i ∈ Finset.range (k + 1), dist (u (N + i)) (u (N + (i + 1))) := by
          rw [sum_range_succ]
        linarith
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) := GCongr.sum_le_sum fun i _ => hu (N + i)
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := by simp_rw [← one_div_pow, pow_add, ← mul_sum]
    _ ≤ 1 / 2 ^ N * 2 :=
      (mul_le_mul_of_nonneg_left (sum_geometric_two_le _)
        (one_div_nonneg.mpr (pow_nonneg (zero_le_two : (0 : ℝ) ≤ 2) _)))
    _ < ε := hN

end Special_Example_070807
