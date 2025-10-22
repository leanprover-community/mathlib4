/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Analysis.Polynomial.Factorization
import Mathlib.Analysis.Normed.Algebra.Basic

/-!
# A (new?) proof of the Gelfand-Mazur Theorem

We provide a formalization of proofs of the following versions of the *Gelfand-Mazur* *Theorem*.

* `NormedAlgebra.Complex.algEquivOfNormMul`: if `F` is a nontrivial normed `ℂ`-algebra
  with multiplicative norm, then we obtain a `ℂ`-algebra equivalence with `ℂ`.

  This differs from `NormedRing.algEquivComplexOfComplete` in the assumptions: there,
  * `F` is assumed to be complete,
  * `F` is assumed to be a (nontrivial) division ring,
  * but the norm is only required to be submultiplicative.
* `NormedAlgebra.Complex.nonempty_algEquiv`: A nontrivial normed `ℂ`-algebra
  with multiplicative norm is isomorphic to `ℂ` as a `ℂ`-algebra.
* `NormedAlgebra.Real.nonempty_algEquiv_or`: if a field `F` is a normed `ℝ`-algebra,
  then `F` is isomorphic as an `ℝ`-algebra either to `ℝ` or to `ℂ`.

### The complex case

The proof we use here is a variant of a proof for the complex case (any normed `ℂ`-algebra
is isomorphic to `ℂ`) that is originally due to Ostrowski
[A. Ostrowski, *Über einige Lösungen der Funktionalgleichung φ(x)⋅φ(y)=φ(xy)*
  (Section 7)][ostrowski1916].
See also the concise version provided by Peter Scholze on
[Math Overflow](https://mathoverflow.net/questions/10535/ways-to-prove-the-fundamental-theorem-of-algebra/420803#420803).

This proof goes as follows. Let `x : F` be arbitrary; we need to show that `x = z • 1`
for some `z : ℂ`. We consider the function `z ↦ ‖x - z • 1‖`. It has a minimum `M`,
which it attains at some point `z₀`, which (upon replacing `x` by `x - z₀ • 1`) we can
assume to be zero. If `M = 0`, we are done, so assume not. For `n : ℕ`,
a primitive `n`th root of unity `ζ : ℂ`, and `z : ℂ` with `|z| < M = ‖x‖` we then have that
`M ≤ ‖x - z • 1‖ = ‖x ^ n - z ^ n • 1‖ / ∏ 0 < k < n, ‖x - (ζ ^ k * z) • 1‖`,
which is bounded by `(M ^ n + |z| ^ n) / M ^ (n - 1) = M * (1 + (|z| / M) ^ n)`.
Letting `n` tend to infinity then shows that `‖x - z • 1‖ = M` (see `NormedAlgebra.aux`).
This implies that the set of `z` such that `‖x - z • 1‖ = M` is closed and open
(and nonempty), so it is all of `ℂ`, which contradicts `‖x - z • 1‖ ≥ |z| - M`
when `|z|` is sufficiently large.

### The real case

THe usual proof for the real case is "either `F` contains a square root of `-1`;
then `F` is in fact a normed `ℂ`-agebra and we can use the result above, or else
we adjoin a square root of `-1` to `F` to obtain a normed `ℂ`-agebra `F'` and
apply the result to `F'`". The difficulty with formalizing this is that
Mathlib does not provide a normed `ℂ`-algebra instance for `F'` (neither for
`F' := AdjoinRoot (X ^ 2 + 1 : F[X])` nor for `F' := TensorProduct ℝ ℂ F`),
and it is not so straight-forward to set this up. So we take inspiration from the
proof sketched above for the complex case to obtain a direct proof.

Since irreducible polynomials over `ℝ` have degree at most `2`, it must be the case
that each element is annihilated by a monic polynomial of degree `2`.
We fix `x : F` in the following.

The space `ℝ²` of monic polynomials of degree `2` is complete and locally compact
and hence `‖aeval x p‖` gets large when `p` has large coefficients.
This is actually slightly subtle. It is certainly true for `‖x - r • 1‖` with `r : ℝ`.
If the minimum of this is zero, then the minimum for monic polynomials of degree `2`
will also be zero (and is attained on a one-dimensional subset). Otherwise, one can
indeed show that a bound on `‖x ^ 2 - a • x + b • 1‖` implies bounds on `|a|` and `|b|`.

By the first sentence of the previous paragraph, there will be some `p₀`
such that `‖aeval x p₀‖` attains a minimum (see `NormedAlgebra.Real.exists_min_norm_φ`).
We assume that this is positive and derive a contradiction. Let `M := ‖aeval x p₀‖ > 0`
be the minimal value.
Since every monic polynomial `f : ℝ[X]` of even degree can be written as a product
of monic polynomials of degree `2`
(see `Polynomial.IsMonicOfDegree.eq_isMonicOfDegree_two_mul_isMonicOfDegree`),
it follows that `‖aeval x f‖ ≥ M ^ (f.natDegree / 2)`.

The goal is now to show that when `a` and `b` achieve the minimum `M` of `‖x ^ 2 - a • x + b • 1‖`,
and `M > 0`, then we can find some neighborhood `U` of `(a, b)` in `ℝ × ℝ`
such that `‖x ^ 2 - a' • x + b' • 1‖ = M` for all `(a', b') ∈ U`
Then the set `S = {(a', b') | ‖x ^ 2 - a' • x + b' • 1‖ = M}` must be all of `ℝ × ℝ` (as it is
closed, open, and nonempty). (see `NormedAlgebra.Real.is_const_norm_sq_sub_add`).
This will lead to a contradiction with the growth of `‖x ^ 2 - a • x‖` as `|a|` gets large.

To get there, the idea is, similarly to the complex case, to use the fact that
`X ^ 2 - a' * X + b'` divides the difference
`(X ^ 2 - a * X + b) ^ n - ((a' - a) * X - (b' - b)) ^ n`;
this gives us a monic polynomial `p` of degree `2 * (n - 1)` such that `(X ^ 2 - a' * X + b') * p`
equals this difference. By the above, `‖aeval x p‖ ≥ M ^ (n - 1)`.

Since `(a', b') ↦ x ^ 2 - a' • x + b' • 1` is continuous, there will be a neighborhood `U`
of `(a, b)` such that
`‖(a' - a) • x - (b' - b) • 1‖ = ‖(x ^ 2 - a • x + b • 1) - (x ^ 2 -a' • x + b' • 1)‖`
is less than `M` for `(a', b') ∈ U`. For such `(a', b')`, it follows that
`‖x ^ 2 - a' • x + b' • 1‖ ≤ ‖(x ^ 2 - a • x + b • 1) ^ n - ((a' - a) • x - (b' - b) • 1) ^ n‖ /`
`‖aeval x p‖`,
which is bounded by `(M ^ n + c ^ n) / M ^ (n - 1) = M * (1 + (c / M) ^ n)`, where
`c = ‖(a' - a) • x - (b' - b) • 1‖ < M`. So, letting `n` tend to infinity, we obtain that
`M ≤ ‖x ^ 2 - a' • x + b' • 1‖ ≤ M`, as desired.
-/

/-!
### Auxiliary results used in both cases
-/

open Polynomial

namespace NormedAlgebra

open Filter Topology in
/- The key step: show that the norm of a suitable function is constant if the norm takes
a positive minimum and condition `H` below is satisfied. -/
private lemma aux {X E : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [SeminormedAddCommGroup E] {f : X → E} {M : ℝ} {x : X} (hM : 0 < M) (hx : ‖f x‖ = M)
    (h : ∀ y, M ≤ ‖f y‖) (hf : Continuous f)
    (H : ∀ {y} z, ‖f y‖ = M → ∀ n > 0, ‖f z‖ ≤ M * (1 + (‖f z - f y‖ / M) ^ n)) (y : X) :
    ‖f y‖ = M := by
  suffices {y | ‖f y‖ = M} = Set.univ by simpa only [← this, hx] using Set.mem_univ y
  refine IsClopen.eq_univ ⟨isClosed_eq (by fun_prop) (by fun_prop), ?_⟩ <| Set.nonempty_of_mem hx
  rw [isOpen_iff_eventually]
  intro w hw
  filter_upwards [mem_map.mp <| hf.tendsto w (Metric.ball_mem_nhds (f w) hM)] with u hu
  simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, ← div_lt_one₀ hM] at hu
  apply le_antisymm ?_ (h u)
  suffices Tendsto (fun n : ℕ ↦ M * (1 + (‖f u - f w‖ / M) ^ n)) atTop (𝓝 (M * (1 + 0))) by
    refine ge_of_tendsto (by simpa) ?_
    filter_upwards [Filter.Ioi_mem_atTop 0] with n hn
    exact H u hw n hn
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hu |>.const_add 1 |>.const_mul M

open Filter Bornology in
/-- In a normed algebra `F` over a normed field `𝕜` that is a proper space, the function
`z : 𝕜 ↦ ‖x - z • 1‖` achieves a global minimum for every `x : F`. -/
lemma exists_min_norm_sub_smul (𝕜 : Type*) {F : Type*} [NormedField 𝕜]
    [ProperSpace 𝕜] [SeminormedRing F] [NormedAlgebra 𝕜 F] [NormOneClass F] (x : F) :
  ∃ z : 𝕜, IsMinOn (‖x - · • 1‖) Set.univ z := by
  have : Tendsto (‖x - · • 1‖) (cobounded 𝕜) atTop := by
    simp only [← Algebra.algebraMap_eq_smul_one]
    exact tendsto_norm_cobounded_atTop |>.comp <| tendsto_const_sub_cobounded x |>.comp <| by simp
  have hf : Continuous fun z : 𝕜 ↦ ‖x - z • 1‖ := by fun_prop
  simp only [isMinOn_univ_iff]
  refine hf.exists_forall_le_of_isBounded 0 ?_
  simpa [isBounded_def, Set.compl_setOf, Set.Ioi] using this (Ioi_mem_atTop (‖x - (0 : 𝕜) • 1‖))

/-!
### The complex case
-/

namespace Complex

variable {F : Type*} [NormedRing F] [NormOneClass F] [NormMulClass F] [NormedAlgebra ℂ F]

private lemma le_aeval_of_isMonicOfDegree (x : F) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ z' : ℂ, M ≤ ‖x - z' • 1‖) {p : ℂ[X]} {n : ℕ} (hp : IsMonicOfDegree p n) (c : ℂ) :
    M ^ n ≤ ‖aeval (x - c • 1) p‖ := by
  induction n generalizing p with
  | zero => simp [isMonicOfDegree_zero_iff.mp hp]
  | succ n ih =>
    obtain ⟨f₁, f₂, hf₁, hf₂, H⟩ := hp.eq_isMonicOfDegree_one_mul_isMonicOfDegree
    obtain ⟨r, rfl⟩ := isMonicOfDegree_one_iff.mp hf₁
    have H' (y : F) : aeval y (X + C r) = y + r • 1 := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [H, aeval_mul, norm_mul, mul_comm, pow_succ, H', sub_add, ← sub_smul]
    exact mul_le_mul (ih hf₂) (h (c - r)) hM (norm_nonneg _)

private lemma norm_sub_is_constant {x : F} {z : ℂ} (hz : ∀ z' : ℂ, ‖x - z • 1‖ ≤ ‖x - z' • 1‖)
    (H : ∀ z' : ℂ, ‖x - z' • 1‖ ≠ 0) (c : ℂ) :
    ‖x - c • 1‖ = ‖x - z • 1‖ := by
  set M := ‖x - z • 1‖ with hMdef
  have hM₀ : 0 < M := by have := H z; positivity
  refine aux (f := (x - · • 1)) hM₀ hMdef.symm hz (by fun_prop) (fun {y} w hy n hn ↦ ?_) c
  dsimp only at hy ⊢
  rw [sub_sub_sub_cancel_left, ← sub_smul, Algebra.norm_smul_one_eq_norm, norm_sub_rev y w,
    show M * (1 + (‖w - y‖ / M) ^ n) = (M ^ n + ‖w - y‖ ^ n) / M ^ (n - 1) by
      simp only [field, div_pow, ← pow_succ', Nat.sub_add_cancel hn],
    le_div_iff₀ (by positivity)]
  obtain ⟨p, hp, hrel⟩ :=
    (isMonicOfDegree_X_pow ℂ n).of_dvd_sub (by grind)
      (isMonicOfDegree_X_sub_one (w - y)) (by compute_degree!) <| sub_dvd_pow_sub_pow X _ n
  grw [le_aeval_of_isMonicOfDegree x hM₀.le hz hp y]
  rw [eq_comm, ← eq_sub_iff_add_eq, mul_comm] at hrel
  apply_fun (‖aeval (x - y • 1) ·‖) at hrel
  simp only [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, norm_mul,
    map_pow, sub_sub_sub_cancel_right] at hrel
  rw [hrel]
  exact (norm_sub_le ..).trans <| by simp [hy, ← sub_smul]

lemma exists_norm_sub_smul_one_eq_zero (x : F) :
    ∃ z : ℂ, ‖x - z • 1‖ = 0 := by
  obtain ⟨z, hz⟩ := exists_min_norm_sub_smul ℂ x
  rw [isMinOn_univ_iff] at hz
  set M := ‖x - z • 1‖ with hM
  rcases eq_or_lt_of_le (show 0 ≤ M from norm_nonneg _) with hM₀ | hM₀
  · exact ⟨z, hM₀.symm⟩
  by_contra! H
  have key := norm_sub_is_constant hz H (‖x‖ + M + 1)
  rw [← hM, norm_sub_rev] at key
  replace key := (norm_sub_norm_le ..).trans_eq key
  rw [Algebra.norm_smul_one_eq_norm] at key
  norm_cast at key
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at key
  linarith

variable (F) [Nontrivial F]

open Algebra in
/-- A version of the **Gelfand-Mazur Theorem**.

If `F` is a nontrivial normed `ℂ`-algebra with multiplicative norm, then we obtain a
`ℂ`-algebra equivalence with `ℂ`. -/
noncomputable
def algEquivOfNormMul : ℂ ≃ₐ[ℂ] F :=
  .ofBijective (ofId ℂ F) <| by
    refine ⟨FaithfulSMul.algebraMap_injective ℂ F, fun x ↦ ?_⟩
    obtain ⟨z, hz⟩ := exists_norm_sub_smul_one_eq_zero x
    refine ⟨z, ?_⟩
    rwa [norm_eq_zero, sub_eq_zero, ← algebraMap_eq_smul_one, eq_comm, ← ofId_apply] at hz

/-- A version of the **Gelfand-Mazur Theorem** for nontrivial normed `ℂ`-algebras `F`
with multiplicative norm. -/
theorem nonempty_algEquiv : Nonempty (ℂ ≃ₐ[ℂ] F) := ⟨algEquivOfNormMul F⟩

end Complex


/-!
### The real case
-/

namespace Real

variable {F : Type*} [NormedRing F] [NormedAlgebra ℝ F]

/- An abbreviation introduced for conciseness below. -/
private abbrev φ (x : F) (u : ℝ × ℝ) : F := x ^ 2 - u.1 • x + u.2 • 1

private lemma continuous_φ (x : F) : Continuous (φ x) := by fun_prop

private lemma aeval_eq_φ (x : F) (u : ℝ × ℝ) : aeval x (X ^ 2 - C u.1 * X + C u.2) = φ x u := by
  simp [Algebra.algebraMap_eq_smul_one]

variable [NormOneClass F] [NormMulClass F]

private lemma le_aeval_of_isMonicOfDegree {x : F} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ z : ℝ × ℝ, M ≤ ‖φ x z‖) {p : ℝ[X]} {n : ℕ} (hp : IsMonicOfDegree p (2 * n)) :
    M ^ n ≤ ‖aeval x p‖ := by
  induction n generalizing p with
  | zero => simp_all
  | succ n ih =>
    rw [mul_add, mul_one] at hp
    obtain ⟨f₁, f₂, hf₁, hf₂, H⟩ := hp.eq_isMonicOfDegree_two_mul_isMonicOfDegree
    obtain ⟨a, b, hab⟩ := isMonicOfDegree_two_iff'.mp hf₁
    rw [H, aeval_mul, norm_mul, mul_comm, pow_succ, hab, aeval_eq_φ x (a, b)]
    exact mul_le_mul (ih hf₂) (h (a, b)) hM (norm_nonneg _)

/- The key step in the proof: if `a` and `b` are real numbers minimizing `‖x ^ 2 - a • x + b • 1‖`,
and the minimal value is strictly positive, then the function `(s, t) ↦ ‖x ^ 2 - s • x + t • 1‖`
is constant. -/
private lemma is_const_norm_φ {x : F} {z : ℝ × ℝ} (h : ∀ w, ‖φ x z‖ ≤ ‖φ x w‖) (H : ‖φ x z‖ ≠ 0)
    (w : ℝ × ℝ) :
    ‖φ x w‖ = ‖φ x z‖ := by
  set M : ℝ := ‖φ x z‖ with hMdef
  have hM₀ : 0 < M := by positivity
  refine aux hM₀ hMdef.symm h (continuous_φ x) (fun {w} u hw n hn ↦ ?_) w
  have HH : M * (1 + (‖φ x u - φ x w‖ / M) ^ n) = (M ^ n + ‖φ x u - φ x w‖ ^ n) / M ^ (n - 1) := by
    simp only [field, div_pow, ← pow_succ', Nat.sub_add_cancel hn]
  rw [HH, le_div_iff₀ (by positivity)]; clear HH
  let q (y : ℝ × ℝ) : ℝ[X] := X ^ 2 - C y.1 * X + C y.2
  have hq (y : ℝ × ℝ) : IsMonicOfDegree (q y) 2 := isMonicOfDegree_sub_add_two ..
  have hsub : q w - q u = (C u.1 - C w.1) * X + C w.2 - C u.2 := by simp only [q]; ring
  have hdvd : q u ∣ q w ^ n - (q w - q u) ^ n := by
    nth_rewrite 1 [← sub_sub_self (q w) (q u)]
    exact sub_dvd_pow_sub_pow ..
  have H' : ((q w - q u) ^ n).natDegree < 2 * n := by rw [hsub]; compute_degree; grind
  obtain ⟨p, hp, hrel⟩ := ((hq w).pow n).of_dvd_sub (by grind) (hq u) H' hdvd; clear H' hdvd hsub
  rw [show 2 * n - 2 = 2 * (n - 1) by grind] at hp
  grw [le_aeval_of_isMonicOfDegree hM₀.le h hp]
  rw [← sub_eq_iff_eq_add, eq_comm, mul_comm] at hrel
  apply_fun (‖aeval x ·‖) at hrel
  rw [map_mul, norm_mul, map_sub, aeval_eq_φ x u] at hrel
  rw [hrel, norm_sub_rev (φ ..)]
  exact (norm_sub_le ..).trans <| by simp [q, aeval_eq_φ, hw]

/- Existence of a minimizing monic polynomial of degree 2 -/

private lemma a_bound {x : F} {c : ℝ} (hc₀ : 0 < c) (hbd : ∀ r : ℝ, c ≤ ‖x - r • 1‖) {a b : ℝ}
    (h : ‖x ^ 2 - a • x + b • 1‖ ≤ ‖x‖ ^ 2) :
    |a| ≤ 2 * ‖x‖ ^ 2 / c := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [abs_zero]
    positivity
  rw [le_div_iff₀ hc₀]
  calc |a| * c
  _ ≤ |a| * ‖x - (b / a) • 1‖ := by gcongr; exact hbd _
  _ = ‖a • x - b • 1‖ := by
      rw [← Real.norm_eq_abs, ← norm_smul, smul_sub, smul_smul, mul_div_cancel₀ _ ha]
  _ ≤ ‖x‖ ^ 2 + ‖x ^ 2 - a • x + b • 1‖ := by
      simpa only [← norm_pow, sub_add, norm_sub_rev (x ^ 2)] using norm_le_norm_add_norm_sub' ..
  _ ≤ _ := by rw [two_mul]; exact add_le_add_left h _

private lemma exists_min_norm_φ (x : F) : ∃ z : ℝ × ℝ, IsMinOn (‖φ x ·‖) Set.univ z := by
  obtain ⟨u, hu⟩ := exists_min_norm_sub_smul ℝ x
  rw [isMinOn_univ_iff] at hu
  rcases eq_or_lt_of_le (norm_nonneg (x - u • 1)) with hc₀ | hc₀
  · rw [eq_comm, norm_eq_zero, sub_eq_zero] at hc₀
    exact ⟨(u, 0), fun z' ↦ by simp [φ, hc₀, sq]⟩
  set c := ‖x - u • 1‖
  simp only [isMinOn_univ_iff]
  refine (continuous_φ x).norm.exists_forall_le_of_isBounded (0, 0) ?_
  simp only [φ, zero_smul, sub_zero, add_zero, norm_pow]
  refine ((Metric.isBounded_of_abs_le (2 * ‖x‖ ^ 2 / c)).prod
    (Metric.isBounded_of_abs_le (2 * ‖x‖ ^ 2 + 2 * ‖x‖ ^ 3 / c))).subset fun (a, b) hab ↦ ?_
  simp only [Set.mem_prod, Set.mem_setOf] at hab ⊢
  have ha : |a| ≤ 2 * ‖x‖ ^ 2 / c := a_bound hc₀ hu hab
  refine ⟨ha, ?_⟩
  rw [two_mul, add_assoc, ← sub_le_iff_le_add, ← sub_sub]
  calc |b| - ‖x‖ ^ 2 - 2 * ‖x‖ ^ 3 / c
  _ = |b| - ‖x‖ ^ 2 - 2 * ‖x‖ ^ 2 / c * ‖x‖ := by ring
  _ ≤ |b| - ‖x‖ ^ 2 - |a| * ‖x‖ := by gcongr
  _ = ‖b • (1 : F)‖ - ‖a • x‖ - ‖x ^ 2‖ := by rw [sub_right_comm, norm_smul a]; simp
  _ ≤ ‖b • 1 - a • x‖ - ‖x ^ 2‖ := by gcongr; exact norm_sub_norm_le ..
  _ ≤ ‖x ^ 2 - a • x + b • 1‖ := by rw [sub_add_comm]; exact norm_sub_le_norm_add ..
  _ ≤ ‖x‖ ^ 2 := hab

open Algebra in
/-- If `F` is a normed `ℝ`-algebra with a multiplicative norm (and such that `‖1‖ = 1`),
e.g., a normed division ring, then every `x : F` is the root of a monic quadratic polynomial
with real coefficients. -/
lemma exists_isMonicOfDegree_two_and_aeval_eq_zero (x : F) :
    ∃ p : ℝ[X], IsMonicOfDegree p 2 ∧ aeval x p = 0 := by
  obtain ⟨z, h⟩ := exists_min_norm_φ x
  rw [isMinOn_univ_iff] at h
  suffices φ x z = 0 from ⟨_, isMonicOfDegree_sub_add_two z.1 z.2, by rwa [aeval_eq_φ]⟩
  by_contra! H
  set M := ‖φ x z‖
  have hM₀ : 0 ≤ M := norm_nonneg _
  -- use that `f x t` is constant to produce an inequality that is false for `c` large enough
  suffices |2 * (‖x‖ ^ 2 / √M + 1)| ≤ 2 * ‖x‖ ^ 2 / √M by
    rw [abs_of_pos <| by positivity, mul_div_assoc] at this
    linarith
  refine a_bound (x := x) (c := √M) (by positivity) (fun r ↦ ?_) (b := 0) ?_
  · rw [← sq_le_sq₀ (Real.sqrt_nonneg M) (norm_nonneg _), Real.sq_sqrt hM₀, ← norm_pow,
      Commute.sub_sq <| algebraMap_eq_smul_one (A := F) r ▸ commute_algebraMap_right r x]
    convert h (2 * r, r ^ 2) using 4 <;> simp [two_mul, add_smul, _root_.smul_pow]
  · nth_rewrite 2 [show ‖x‖ ^ 2 = ‖x ^ 2 - (0 : ℝ) • x + (0 : ℝ) • 1‖ by simp]
    rw [is_const_norm_φ h (norm_ne_zero_iff.mpr H) (2 * (‖x‖ ^ 2 / √M + 1), 0)]
    exact h (0, 0)

/-- A version of the **Gelfand-Mazur Theorem** over `ℝ`.

If a field `F` is a normed `ℝ`-algebra, then `F` is isomorphic as an `ℝ`-algebra
either to `ℝ` or to `ℂ`. -/
theorem nonempty_algEquiv_or (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) := by
  have : Algebra.IsAlgebraic ℝ F := by
    refine ⟨fun x ↦ IsIntegral.isAlgebraic ?_⟩
    obtain ⟨f, hf, hfx⟩ := exists_isMonicOfDegree_two_and_aeval_eq_zero x
    exact (hfx ▸ isIntegral_zero).of_aeval_monic hf.monic <| hf.natDegree_eq.trans_ne two_ne_zero
  exact _root_.Real.nonempty_algEquiv_or F

-- without going via `IsIntegral` (missing API for `IsAlgebraic`?):
/-
  have : Algebra.IsAlgebraic ℝ F := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨f, hf, hfx⟩ := exists_isMonicOfDegree_two_and_aeval_eq_zero x
    refine (hfx ▸ isAlgebraic_zero).of_aeval f ?_ ?_
    · exact hf.natDegree_eq.trans_ne two_ne_zero
    · rw [hf.monic.leadingCoeff]
      exact Submonoid.one_mem (nonZeroDivisors ℝ)
-/

end Real

end NormedAlgebra
