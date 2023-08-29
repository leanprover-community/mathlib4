/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jujian Zhang
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Data.Polynomial.DenomsClearable
import Mathlib.Data.Real.Irrational
import Mathlib.Topology.Algebra.Polynomial

#align_import number_theory.liouville.basic from "leanprover-community/mathlib"@"04e80bb7e8510958cd9aacd32fe2dc147af0b9f1"

/-!

# Liouville's theorem

This file contains a proof of Liouville's theorem stating that all Liouville numbers are
transcendental.

To obtain this result, there is first a proof that Liouville numbers are irrational and two
technical lemmas.  These lemmas exploit the fact that a polynomial with integer coefficients
takes integer values at integers.  When evaluating at a rational number, we can clear denominators
and obtain precise inequalities that ultimately allow us to prove transcendence of
Liouville numbers.
-/


/-- A Liouville number is a real number `x` such that for every natural number `n`, there exist
`a, b ∈ ℤ` with `1 < b` such that `0 < |x - a/b| < 1/bⁿ`.
In the implementation, the condition `x ≠ a/b` replaces the traditional equivalent `0 < |x - a/b|`.
-/
def Liouville (x : ℝ) :=
  ∀ n : ℕ, ∃ a b : ℤ, 1 < b ∧ x ≠ a / b ∧ |x - a / b| < 1 / (b : ℝ) ^ n
#align liouville Liouville

namespace Liouville

protected theorem irrational {x : ℝ} (h : Liouville x) : Irrational x := by
  -- By contradiction, `x = a / b`, with `a ∈ ℤ`, `0 < b ∈ ℕ` is a Liouville number,
  rintro ⟨⟨a, b, bN0, cop⟩, rfl⟩
  -- ⊢ False
  -- clear up the mess of constructions of rationals
  rw [Rat.cast_mk', ← div_eq_mul_inv] at h
  -- ⊢ False
  -- Since `a / b` is a Liouville number, there are `p, q ∈ ℤ`, with `q1 : 1 < q`,
  -- `a0 : a / b ≠ p / q` and `a1 : |a / b - p / q| < 1 / q ^ (b + 1)`
  rcases h (b + 1) with ⟨p, q, q1, a0, a1⟩
  -- ⊢ False
  -- A few useful inequalities
  have qR0 : (0 : ℝ) < q := Int.cast_pos.mpr (zero_lt_one.trans q1)
  -- ⊢ False
  have b0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr bN0
  -- ⊢ False
  have bq0 : (0 : ℝ) < b * q := mul_pos (Nat.cast_pos.mpr bN0.bot_lt) qR0
  -- ⊢ False
  -- At a1, clear denominators...
  replace a1 : |a * q - b * p| * q ^ (b + 1) < b * q
  -- ⊢ |a * q - ↑b * p| * q ^ (b + 1) < ↑b * q
  · rw [div_sub_div _ _ b0 qR0.ne', abs_div, div_lt_div_iff (abs_pos.mpr bq0.ne') (pow_pos qR0 _),
      abs_of_pos bq0, one_mul] at a1
    exact_mod_cast a1
    -- 🎉 no goals
  -- At a0, clear denominators...
  replace a0 : a * q - ↑b * p ≠ 0;
  -- ⊢ a * q - ↑b * p ≠ 0
  · rw [Ne.def, div_eq_div_iff b0 qR0.ne', mul_comm (p : ℝ), ← sub_eq_zero] at a0
    -- ⊢ a * q - ↑b * p ≠ 0
    exact_mod_cast a0
    -- 🎉 no goals
  -- Actually, `q` is a natural number
  lift q to ℕ using (zero_lt_one.trans q1).le
  -- ⊢ False
  -- Looks innocuous, but we now have an integer with non-zero absolute value: this is at
  -- least one away from zero.  The gain here is what gets the proof going.
  have ap : 0 < |a * ↑q - ↑b * p| := abs_pos.mpr a0
  -- ⊢ False
  -- Actually, the absolute value of an integer is a natural number
  lift |a * ↑q - ↑b * p| to ℕ using abs_nonneg (a * ↑q - ↑b * p) with e he
  -- ⊢ False
  -- At a1, revert to natural numbers
  rw [← Int.ofNat_mul, ← Int.coe_nat_pow, ← Int.ofNat_mul, Int.ofNat_lt] at a1
  -- ⊢ False
  -- Recall this is by contradiction: we obtained the inequality `b * q ≤ x * q ^ (b + 1)`, so
  -- we are done.
  exact not_le.mpr a1 (Nat.mul_lt_mul_pow_succ (Int.coe_nat_pos.mp ap) (Int.ofNat_lt.mp q1)).le
  -- 🎉 no goals
#align liouville.irrational Liouville.irrational

open Polynomial Metric Set Real RingHom

open scoped Polynomial

/-- Let `Z, N` be types, let `R` be a metric space, let `α : R` be a point and let
`j : Z → N → R` be a function.  We aim to estimate how close we can get to `α`, while staying
in the image of `j`.  The points `j z a` of `R` in the image of `j` come with a "cost" equal to
`d a`.  As we get closer to `α` while staying in the image of `j`, we are interested in bounding
the quantity `d a * dist α (j z a)` from below by a strictly positive amount `1 / A`: the intuition
is that approximating well `α` with the points in the image of `j` should come at a high cost.  The
hypotheses on the function `f : R → R` provide us with sufficient conditions to ensure our goal.
The first hypothesis is that `f` is Lipschitz at `α`: this yields a bound on the distance.
The second hypothesis is specific to the Liouville argument and provides the missing bound
involving the cost function `d`.

This lemma collects the properties used in the proof of `exists_pos_real_of_irrational_root`.
It is stated in more general form than needed: in the intended application, `Z = ℤ`, `N = ℕ`,
`R = ℝ`, `d a = (a + 1) ^ f.nat_degree`, `j z a = z / (a + 1)`, `f ∈ ℤ[x]`, `α` is an irrational
root of `f`, `ε` is small, `M` is a bound on the Lipschitz constant of `f` near `α`, `n` is
the degree of the polynomial `f`.
-/
theorem exists_one_le_pow_mul_dist {Z N R : Type*} [PseudoMetricSpace R] {d : N → ℝ}
    {j : Z → N → R} {f : R → R} {α : R} {ε M : ℝ}
    -- denominators are positive
    (d0 : ∀ a : N, 1 ≤ d a)
    (e0 : 0 < ε)
    -- function is Lipschitz at α
    (B : ∀ ⦃y : R⦄, y ∈ closedBall α ε → dist (f α) (f y) ≤ dist α y * M)
    -- clear denominators
    (L : ∀ ⦃z : Z⦄, ∀ ⦃a : N⦄, j z a ∈ closedBall α ε → 1 ≤ d a * dist (f α) (f (j z a))) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : Z, ∀ a : N, 1 ≤ d a * (dist α (j z a) * A) := by
  -- A useful inequality to keep at hand
  have me0 : 0 < max (1 / ε) M := lt_max_iff.mpr (Or.inl (one_div_pos.mpr e0))
  -- ⊢ ∃ A, 0 < A ∧ ∀ (z : Z) (a : N), 1 ≤ d a * (dist α (j z a) * A)
  -- The maximum between `1 / ε` and `M` works
  refine' ⟨max (1 / ε) M, me0, fun z a => _⟩
  -- ⊢ 1 ≤ d a * (dist α (j z a) * max (1 / ε) M)
  -- First, let's deal with the easy case in which we are far away from `α`
  by_cases dm1 : 1 ≤ dist α (j z a) * max (1 / ε) M
  -- ⊢ 1 ≤ d a * (dist α (j z a) * max (1 / ε) M)
  · exact one_le_mul_of_one_le_of_one_le (d0 a) dm1
    -- 🎉 no goals
  · -- `j z a = z / (a + 1)`: we prove that this ratio is close to `α`
    have : j z a ∈ closedBall α ε := by
      refine' mem_closedBall'.mp (le_trans _ ((one_div_le me0 e0).mpr (le_max_left _ _)))
      exact (le_div_iff me0).mpr (not_le.mp dm1).le
    -- use the "separation from `1`" (assumption `L`) for numerators,
    refine' (L this).trans _
    -- ⊢ d a * dist (f α) (f (j z a)) ≤ d a * (dist α (j z a) * max (1 / ε) M)
    -- remove a common factor and use the Lipschitz assumption `B`
    refine' mul_le_mul_of_nonneg_left ((B this).trans _) (zero_le_one.trans (d0 a))
    -- ⊢ dist α (j z a) * M ≤ dist α (j z a) * max (1 / ε) M
    exact mul_le_mul_of_nonneg_left (le_max_right _ M) dist_nonneg
    -- 🎉 no goals
#align liouville.exists_one_le_pow_mul_dist Liouville.exists_one_le_pow_mul_dist

theorem exists_pos_real_of_irrational_root {α : ℝ} (ha : Irrational α) {f : ℤ[X]} (f0 : f ≠ 0)
    (fa : eval α (map (algebraMap ℤ ℝ) f) = 0) :
    ∃ A : ℝ, 0 < A ∧ ∀ a : ℤ, ∀ b : ℕ,
      (1 : ℝ) ≤ ((b : ℝ) + 1) ^ f.natDegree * (|α - a / (b + 1)| * A) := by
  -- `fR` is `f` viewed as a polynomial with `ℝ` coefficients.
  set fR : ℝ[X] := map (algebraMap ℤ ℝ) f
  -- ⊢ ∃ A, 0 < A ∧ ∀ (a : ℤ) (b : ℕ), 1 ≤ (↑b + 1) ^ natDegree f * (|α - ↑a / (↑b  …
  -- `fR` is non-zero, since `f` is non-zero.
  obtain fR0 : fR ≠ 0 := fun fR0 =>
    (map_injective (algebraMap ℤ ℝ) fun _ _ A => Int.cast_inj.mp A).ne f0
      (fR0.trans (Polynomial.map_zero _).symm)
  -- reformulating assumption `fa`: `α` is a root of `fR`.
  have ar : α ∈ (fR.roots.toFinset : Set ℝ) :=
    Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr ((mem_roots fR0).mpr (IsRoot.def.mpr fa)))
  -- Since the polynomial `fR` has finitely many roots, there is a closed interval centered at `α`
  -- such that `α` is the only root of `fR` in the interval.
  obtain ⟨ζ, z0, U⟩ : ∃ ζ > 0, closedBall α ζ ∩ fR.roots.toFinset = {α} :=
    @exists_closedBall_inter_eq_singleton_of_discrete _ _ _ discrete_of_t1_of_finite _ ar
  -- Since `fR` is continuous, it is bounded on the interval above.
  obtain ⟨xm, -, hM⟩ : ∃ xm : ℝ, xm ∈ Icc (α - ζ) (α + ζ) ∧
      IsMaxOn (|fR.derivative.eval ·|) (Icc (α - ζ) (α + ζ)) xm :=
    IsCompact.exists_isMaxOn isCompact_Icc
      ⟨α, (sub_lt_self α z0).le, (lt_add_of_pos_right α z0).le⟩
      (continuous_abs.comp fR.derivative.continuous_aeval).continuousOn
  -- Use the key lemma `exists_one_le_pow_mul_dist`: we are left to show that ...
  refine'
    @exists_one_le_pow_mul_dist ℤ ℕ ℝ _ _ _ (fun y => fR.eval y) α ζ |fR.derivative.eval xm| _ z0
      (fun y hy => _) fun z a hq => _
  -- 1: the denominators are positive -- essentially by definition;
  · exact fun a => one_le_pow_of_one_le ((le_add_iff_nonneg_left 1).mpr a.cast_nonneg) _
    -- 🎉 no goals
  -- 2: the polynomial `fR` is Lipschitz at `α` -- as its derivative continuous;
  · rw [mul_comm]
    -- ⊢ dist ((fun y => eval y fR) α) ((fun y => eval y fR) y) ≤ |eval xm (↑derivati …
    rw [Real.closedBall_eq_Icc] at hy
    -- ⊢ dist ((fun y => eval y fR) α) ((fun y => eval y fR) y) ≤ |eval xm (↑derivati …
    -- apply the Mean Value Theorem: the bound on the derivative comes from differentiability.
    refine'
      Convex.norm_image_sub_le_of_norm_deriv_le (fun _ _ => fR.differentiableAt)
        (fun y h => by rw [fR.deriv]; exact hM h) (convex_Icc _ _) hy (mem_Icc_iff_abs_le.mp _)
    exact @mem_closedBall_self ℝ _ α ζ (le_of_lt z0)
    -- 🎉 no goals
  -- 3: the weird inequality of Liouville type with powers of the denominators.
  · show 1 ≤ (a + 1 : ℝ) ^ f.natDegree * |eval α fR - eval ((z : ℝ) / (a + 1)) fR|
    -- ⊢ 1 ≤ (↑a + 1) ^ natDegree f * |eval α fR - eval (↑z / (↑a + 1)) fR|
    rw [fa, zero_sub, abs_neg]
    -- ⊢ 1 ≤ (↑a + 1) ^ natDegree f * |eval (↑z / (↑a + 1)) fR|
    rw [show (a + 1 : ℝ) = ((a + 1 : ℕ) : ℤ) by norm_cast] at hq ⊢
    -- ⊢ 1 ≤ ↑↑(a + 1) ^ natDegree f * |eval (↑z / ↑↑(a + 1)) fR|
    -- key observation: the right-hand side of the inequality is an *integer*.  Therefore,
    -- if its absolute value is not at least one, then it vanishes.  Proceed by contradiction
    refine' one_le_pow_mul_abs_eval_div (Int.coe_nat_succ_pos a) fun hy => _
    -- ⊢ False
    -- As the evaluation of the polynomial vanishes, we found a root of `fR` that is rational.
    -- We know that `α` is the only root of `fR` in our interval, and `α` is irrational:
    -- follow your nose.
    refine' (irrational_iff_ne_rational α).mp ha z (a + 1) (mem_singleton_iff.mp _).symm
    -- ⊢ ↑z / ↑(↑a + 1) ∈ {α}
    refine' U.subset _
    -- ⊢ ↑z / ↑(↑a + 1) ∈ closedBall α ζ ∩ ↑(Multiset.toFinset (roots fR))
    refine' ⟨hq, Finset.mem_coe.mp (Multiset.mem_toFinset.mpr _)⟩
    -- ⊢ ↑z / ↑(↑a + 1) ∈ roots fR
    exact (mem_roots fR0).mpr (IsRoot.def.mpr hy)
    -- 🎉 no goals
#align liouville.exists_pos_real_of_irrational_root Liouville.exists_pos_real_of_irrational_root

/-- **Liouville's Theorem** -/
protected theorem transcendental {x : ℝ} (lx : Liouville x) : Transcendental ℤ x := by
  -- Proceed by contradiction: if `x` is algebraic, then `x` is the root (`ef0`) of a
  -- non-zero (`f0`) polynomial `f`
  rintro ⟨f : ℤ[X], f0, ef0⟩
  -- ⊢ False
  -- Change `aeval x f = 0` to `eval (map _ f) = 0`, who knew.
  replace ef0 : (f.map (algebraMap ℤ ℝ)).eval x = 0;
  -- ⊢ eval x (map (algebraMap ℤ ℝ) f) = 0
  · rwa [aeval_def, ← eval_map] at ef0
    -- 🎉 no goals
  -- There is a "large" real number `A` such that `(b + 1) ^ (deg f) * |f (x - a / (b + 1))| * A`
  -- is at least one.  This is obtained from lemma `exists_pos_real_of_irrational_root`.
  obtain ⟨A, hA, h⟩ : ∃ A : ℝ, 0 < A ∧ ∀ (a : ℤ) (b : ℕ),
      (1 : ℝ) ≤ ((b : ℝ) + 1) ^ f.natDegree * (|x - a / (b + 1)| * A) :=
    exists_pos_real_of_irrational_root lx.irrational f0 ef0
  -- Since the real numbers are Archimedean, a power of `2` exceeds `A`: `hn : A < 2 ^ r`.
  rcases pow_unbounded_of_one_lt A (lt_add_one 1) with ⟨r, hn⟩
  -- ⊢ False
  -- Use the Liouville property, with exponent `r + deg f`.
  obtain ⟨a, b, b1, -, a1⟩ : ∃ a b : ℤ, 1 < b ∧ x ≠ a / b ∧
      |x - a / b| < 1 / (b : ℝ) ^ (r + f.natDegree) :=
    lx (r + f.natDegree)
  have b0 : (0 : ℝ) < b := zero_lt_one.trans (by rw [← Int.cast_one]; exact Int.cast_lt.mpr b1)
  -- ⊢ False
  -- Prove that `b ^ f.nat_degree * abs (x - a / b)` is strictly smaller than itself
  -- recall, this is a proof by contradiction!
  refine' lt_irrefl ((b : ℝ) ^ f.natDegree * |x - ↑a / ↑b|) _
  -- ⊢ ↑b ^ natDegree f * |x - ↑a / ↑b| < ↑b ^ natDegree f * |x - ↑a / ↑b|
  -- clear denominators at `a1`
  rw [lt_div_iff' (pow_pos b0 _), pow_add, mul_assoc] at a1
  -- ⊢ ↑b ^ natDegree f * |x - ↑a / ↑b| < ↑b ^ natDegree f * |x - ↑a / ↑b|
  -- split the inequality via `1 / A`.
  refine' (_ : (b : ℝ) ^ f.natDegree * |x - a / b| < 1 / A).trans_le _
  -- ⊢ ↑b ^ natDegree f * |x - ↑a / ↑b| < 1 / A
  -- This branch of the proof uses the Liouville condition and the Archimedean property
  · refine' (lt_div_iff' hA).mpr _
    -- ⊢ A * (↑b ^ natDegree f * |x - ↑a / ↑b|) < 1
    refine' lt_of_le_of_lt _ a1
    -- ⊢ A * (↑b ^ natDegree f * |x - ↑a / ↑b|) ≤ ↑b ^ r * (↑b ^ natDegree f * |x - ↑ …
    gcongr
    -- ⊢ A ≤ ↑b ^ r
    refine' hn.le.trans _
    -- ⊢ (1 + 1) ^ r ≤ ↑b ^ r
    rw [one_add_one_eq_two]
    -- ⊢ 2 ^ r ≤ ↑b ^ r
    gcongr
    -- ⊢ 2 ≤ ↑b
    exact Int.cast_two.symm.le.trans (Int.cast_le.mpr (Int.add_one_le_iff.mpr b1))
    -- 🎉 no goals
  -- this branch of the proof exploits the "integrality" of evaluations of polynomials
  -- at ratios of integers.
  · lift b to ℕ using zero_le_one.trans b1.le
    -- ⊢ 1 / A ≤ ↑↑b ^ natDegree f * |x - ↑a / ↑↑b|
    specialize h a b.pred
    -- ⊢ 1 / A ≤ ↑↑b ^ natDegree f * |x - ↑a / ↑↑b|
    rwa [← Nat.cast_succ, Nat.succ_pred_eq_of_pos (zero_lt_one.trans _), ← mul_assoc, ←
      div_le_iff hA] at h
    exact Int.ofNat_lt.mp b1
    -- 🎉 no goals
#align liouville.transcendental Liouville.transcendental

end Liouville
