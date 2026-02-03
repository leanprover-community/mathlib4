/-
Copyright (c) 2026 Semar Augusto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Semar Augusto
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Probability.Distributions.Uniform

/-!
# Shannon Entropy for Discrete Random Variables

This file defines the Shannon entropy (in nats) for discrete random variables represented
as probability mass functions (PMFs).

## Main Definitions

* `entropy p`: the Shannon entropy (in nats) of a PMF `p`,
  `∑' a, Real.negMulLog (ENNReal.toReal (p a))`.

## Main Results

* `entropy_nonneg`: Entropy is nonnegative
* `entropy_eq_zero_iff`: Entropy is zero if and only if the distribution is deterministic
* `entropy_bernoulli_eq_binEntropy`: Connection to binary entropy function
* `entropy_uniformOfFinset`: Entropy of uniform distribution on n elements equals `log n`

## Tags

entropy, Shannon, information theory, discrete random variable, PMF
-/

public section

open scoped Finset MeasureTheory NNReal ENNReal

namespace InformationTheory

variable {α β : Type*}

/-! ### Basic Definitions -/

/-- Shannon entropy (in nats) of a probability mass function.

We use `Real.negMulLog` so the summand is well-behaved at probability `0`.
The PMF values live in `ENNReal`, so we convert to `ℝ` with `ENNReal.toReal`.

The entropy is defined as `H(X) = ∑_{x ∈ 𝒳} p(x) · log(p(x))` where the sum
is over all possible outcomes and we use the convention `0 · log(0) = 0`. -/
noncomputable def entropy (p : PMF α) : ℝ :=
  ∑' a : α, Real.negMulLog (ENNReal.toReal (p a))

/-! ### Basic Properties -/

/-- Entropy of a deterministic distribution (pure) is zero. -/
@[simp] lemma entropy_pure (a : α) : entropy (PMF.pure a) = 0 := by
  classical
  simp only [entropy, PMF.pure_apply]
  have h : (fun a' : α => Real.negMulLog (ENNReal.toReal (if a' = a then 1 else 0)))
      = (fun _ : α => (0 : ℝ)) := by
    funext a'
    by_cases ha : a' = a <;> simp [ha, Real.negMulLog_one, Real.negMulLog_zero]
  simp [h, tsum_zero]

/-- Entropy of a PMF is non negative. -/
@[simp] lemma entropy_nonneg (p : PMF α) : 0 ≤ entropy p := by
  simp only [entropy]
  refine tsum_nonneg (fun a => ?_)
  refine Real.negMulLog_nonneg ENNReal.toReal_nonneg ?_
  exact ENNReal.toReal_le_of_le_ofReal (by simp) (by
      simpa only [ENNReal.ofReal_one] using (PMF.coe_le_one p a))

/-!
### Helper lemmas for `entropy_eq_zero_iff`

The proof that entropy is strictly positive for a non-pure distribution proceeds by extracting two
distinct elements of the support, showing both summands are strictly positive,
and then comparing the full sum to a partial sum that includes at least one of those positive terms.

The following helper lemmas isolate the fiddly support / `toReal` / `tsum` plumbing so that the main
proof reads at a higher level.
-/

/-- If a PMF is not pure, then its support contains at least two points. -/
private lemma support_nontrivial_of_not_pure (p : PMF α) (h : ¬ ∃ a : α, p = PMF.pure a) :
    Set.Nontrivial p.support := by
  obtain ⟨a0, ha0⟩ := p.support_nonempty
  rw [Set.nontrivial_iff_ne_singleton ha0]
  intro heq
  have h1 : p a0 = 1 := (p.apply_eq_one_iff a0).2 heq
  have : p = PMF.pure a0 := PMF.ext fun x => by
    by_cases hx : x = a0
    · subst hx;
      simpa only [PMF.pure_apply, ↓reduceIte] using h1
    · have : (PMF.pure a0) x = 0 := by simp only [PMF.pure_apply, if_neg hx]
      simpa [this] using (p.apply_eq_zero_iff x).mpr (by simp [heq, hx])
  exact h ⟨a0, this⟩

/-- If `x ∈ support p` and `p` is not pure, then `(p x).toReal < 1`. -/
private lemma toReal_lt_one_of_mem_support_of_not_pure (p : PMF α) (x : α) (hx : x ∈ p.support)
    (h : ¬ ∃ a : α, p = PMF.pure a) : (p x).toReal < 1 := by
  by_contra h_not
  push_neg at h_not
  have hx_le_one : (p x).toReal ≤ 1 := by
    have hpx : p x ≤ (1 : ENNReal) := PMF.coe_le_one p x
    exact ENNReal.toReal_le_of_le_ofReal (by simp) (by simpa using hpx)
  have hx_toReal_eq_one : (p x).toReal = 1 := le_antisymm hx_le_one h_not
  have hx_eq_one : p x = 1 := (ENNReal.toReal_eq_one_iff (p x)).1 hx_toReal_eq_one
  have hsupp : p.support = {x} := (p.apply_eq_one_iff x).1 hx_eq_one
  have hpure : p = PMF.pure x := PMF.ext fun y => by
    by_cases hy : y = x
    · subst hy;
      simpa only [PMF.pure_apply, ↓reduceIte] using hx_eq_one
    · have : (PMF.pure x) y = 0 := by simp only [PMF.pure_apply, if_neg hy]
      simpa [this] using (p.apply_eq_zero_iff y).mpr (by simp [hsupp, hy])
  exact h ⟨x, hpure⟩

/-- A pointwise nonnegativity lemma for the “remove one term from the entropy sum” trick. -/
private lemma negMulLog_ite_nonneg (p : PMF α) (a b : α) [DecidableEq α] :
    0 ≤ (if b = a then 0 else Real.negMulLog ((p b).toReal)) := by
  by_cases hb : b = a
  · simpa only [hb, ite_true] using le_rfl
    -- `negMulLog` is nonnegative on `[0,1]`.
  · simpa only [hb, ite_false] using Real.negMulLog_nonneg ENNReal.toReal_nonneg (by
      have hpb : p b ≤ (1 : ENNReal) := PMF.coe_le_one p b
      exact ENNReal.toReal_le_of_le_ofReal (by simp only [zero_le_one]) (
        by simpa only [ENNReal.ofReal_one] using hpb)
      )

/-- A one-term lower bound on the “rest” of the entropy sum.
This is used to compare the total entropy to the sum with one index removed, ensuring a positive
contribution remains when the support has at least two points. -/
private lemma entropy_tsum_ite_ge (p : PMF α) [Finite α] [DecidableEq α] (a a' : α) (ha' : a' ≠ a) :
    Real.negMulLog ((p a').toReal) ≤
      ∑' b : α, if b = a then 0 else Real.negMulLog ((p b).toReal) := by
  have h_rest_summable : Summable (fun b => if b = a then 0 else Real.negMulLog ((p b).toReal)) :=
    Summable.of_finite
  have h_nonneg' : ∀ j : α, j ≠ a' → 0 ≤ (if j = a then 0 else Real.negMulLog ((p j).toReal)) :=
    fun j _ => negMulLog_ite_nonneg p a j
  have hle := Summable.le_tsum h_rest_summable a' h_nonneg'
  simpa [ha'] using hle

/-- Entropy is zero iff the distribution is deterministic (`PMF.pure`). -/
lemma entropy_eq_zero_iff (p : PMF α) [Finite α] :
  entropy p = 0 ↔ ∃ a : α, p = PMF.pure a := by
  classical
  constructor
  · intro hE
    by_contra h
    obtain ⟨a, ha, a', ha', haa'⟩ := support_nontrivial_of_not_pure p h
    have ha_pos : 0 < (p a).toReal :=
      ENNReal.toReal_pos ((p.mem_support_iff a).1 ha) (p.apply_ne_top a)
    have ha'_pos : 0 < (p a').toReal :=
      ENNReal.toReal_pos ((p.mem_support_iff a').1 ha') (p.apply_ne_top a')
    have ha_lt_one : (p a).toReal < 1 := toReal_lt_one_of_mem_support_of_not_pure p a ha h
    have ha'_lt_one : (p a').toReal < 1 := toReal_lt_one_of_mem_support_of_not_pure p a' ha' h
    have h1 : 0 < Real.negMulLog ((p a).toReal) :=
      Real.negMulLog_pos_of_pos_lt_one ha_pos ha_lt_one
    have h2 : 0 < Real.negMulLog ((p a').toReal) :=
      Real.negMulLog_pos_of_pos_lt_one ha'_pos ha'_lt_one
    have h_sum := entropy_tsum_ite_ge p a a' (ne_comm.1 haa')
    have h_summable : Summable (fun b : α => Real.negMulLog (ENNReal.toReal (p b))) :=
      Summable.of_finite
    rw [entropy, (h_summable.tsum_eq_add_tsum_ite a)] at hE
    linarith [h1, h2, h_sum]
  · rintro ⟨a, rfl⟩
    simp only [entropy_pure]

/-- If a PMF is not pure, then its entropy is strictly positive. -/
lemma entropy_pos_of_not_pure (p : PMF α) [Finite α]
    (hp : ¬ ∃ a : α, p = PMF.pure a) :
    0 < entropy p := by
  have hnonneg : 0 ≤ entropy p := entropy_nonneg (α := α) p
  have hne : entropy p ≠ 0 := by
    intro h0
    exact hp ((entropy_eq_zero_iff p).1 h0)
  -- nonneg + ≠0 gives strict positivity in ℝ
  exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using hne)

/-! ### Connection to Binary Entropy -/

/-- The entropy of a Bernoulli PMF equals the binary entropy function. -/
theorem entropy_bernoulli_eq_binEntropy (p : ℝ≥0) (h : p ≤ 1) :
    entropy (PMF.bernoulli p h) = Real.binEntropy (p : ℝ) := by
  simp only [entropy, PMF.bernoulli_apply]
  simp_all [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, ENNReal.toReal]

/-! ### Uniform distributions -/

/-- A helper identity used to compute entropy of the uniform distribution. -/
lemma nat_mul_negMulLog_inv_eq_log (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.negMulLog (((n : ENNReal)⁻¹).toReal) = Real.log n := by
  -- set up positivity / nonzero facts for coercions
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have htoReal : (((n : ENNReal)⁻¹).toReal) = (n : ℝ)⁻¹ := by
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  calc
    (n : ℝ) * Real.negMulLog (((n : ENNReal)⁻¹).toReal)
        = (n : ℝ) * (-( ((n : ENNReal)⁻¹).toReal * Real.log (((n : ENNReal)⁻¹).toReal) )) := by
          simp [htoReal, Real.negMulLog]
    _ = -((n : ℝ) * ((n : ENNReal)⁻¹).toReal) * Real.log (((n : ENNReal)⁻¹).toReal) := by
          ring
    _ = -(1 : ℝ) * Real.log (((n : ENNReal)⁻¹).toReal) := by
          simp [htoReal, hn0]
    _ = - Real.log (((n : ENNReal)⁻¹).toReal) := by simp
    _ = Real.log n := by
          simp [htoReal, Real.log_inv]

/-- Entropy of the uniform distribution on a finite nonempty type is `log (card α)`. -/
lemma entropy_uniformOfFintype (α : Type*) [Fintype α] [Nonempty α] :
    entropy (PMF.uniformOfFintype α) = Real.log (Fintype.card α) := by
  classical
  -- unfold entropy and use that the summand is constant
  simp [entropy, PMF.uniformOfFintype_apply, tsum_fintype, Finset.sum_const, nsmul_eq_mul]
  -- goal is now `card * negMulLog(1/card) = log card`
  simpa using nat_mul_negMulLog_inv_eq_log (Fintype.card α) (Fintype.card_pos)


/-- Entropy of the uniform distribution on a nonempty finset is `log (card s)`.

This works over an arbitrary type `α` (possibly infinite), because the uniform distribution on a
finset has finite support. -/
lemma entropy_uniformOfFinset
    (s : Finset α) (hs : s.Nonempty) :
    entropy (PMF.uniformOfFinset s hs : PMF α) = Real.log s.card := by
  classical
  set p : PMF α := (PMF.uniformOfFinset s hs : PMF α)
  set f : α → ℝ := fun a => Real.negMulLog (ENNReal.toReal (p a))
  -- reduce the tsum to a finset sum using `tsum_eq_sum`
  have htsum : (∑' a : α, f a) = ∑ a ∈ s, f a := by
    refine tsum_eq_sum (s := s) ?_
    intro a ha
    simp [f, p, PMF.uniformOfFinset, ha]
  -- unfold entropy and use htsum
  simp only [entropy, f, htsum]
  have hcard : 0 < s.card := hs.card_pos
  calc
    ∑ a ∈ s, Real.negMulLog (ENNReal.toReal (p a))
        = (s.card : ℝ) * Real.negMulLog (((s.card : ENNReal)⁻¹).toReal) := by
      have : (∑ a ∈ s, Real.negMulLog (ENNReal.toReal (p a)))
              =
            ∑ a ∈ s, Real.negMulLog (((s.card : ENNReal)⁻¹).toReal) := by
        refine Finset.sum_congr rfl ?_
        intro a ha_mem
        -- inside s: p a = (card s)⁻¹
        simp [p, PMF.uniformOfFinset, ha_mem]
      simp [this, Finset.sum_const, nsmul_eq_mul]
    _ = Real.log s.card := by
      have h := nat_mul_negMulLog_inv_eq_log s.card hcard
      simpa only [ENNReal.toReal_inv, ENNReal.toReal_natCast] using h

/-! ### Examples -/

/-- Entropy of a deterministic distribution is zero. -/
example : entropy (PMF.pure ()) = 0 := by simp only [entropy_pure]

/-- Entropy of another deterministic distribution is zero. -/
example : entropy (PMF.pure true) = 0 := by simp only [entropy_pure]

/-- Entropy of the uniform distribution on `{0,1, ..., n}` is `log n`. -/
example (n : ℕ) [NeZero n] : entropy (PMF.uniformOfFintype (Fin n)) = Real.log n := by
  simpa using (entropy_uniformOfFintype (α := Fin n))

/-- Entropy of the uniform distribution on `{0,1}` is `log 2`. -/
example : entropy (PMF.uniformOfFinset ({0, 1} : Finset ℕ) (by simp) : PMF ℕ) = Real.log 2 := by
  simpa using
    (entropy_uniformOfFinset (α := ℕ) ({0, 1} : Finset ℕ) (by simp))

end InformationTheory
