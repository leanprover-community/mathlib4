/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Polynomial.Factorization

/-!
# A (new?) proof of the Gelfand-Mazur Theorem

We provide a formalization of proofs of the following versions of the *Gelfand-Mazur Theorem*.

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

  With some additional work (TODO), this implies a
  [Theorem of Ostrowski](https://en.wikipedia.org/wiki/Ostrowski%27s_theorem#Another_Ostrowski's_theorem),
  which says that any field that is complete with respect to an archimedean absolute value
  is isomorphic to either `ℝ` or `ℂ` as a field with absolute value. The additional input needed
  for this is to show that any such field is in fact a normed `ℝ`-algebra.

### The complex case

The proof we use here is a variant of a proof for the complex case (any normed `ℂ`-algebra
is isomorphic to `ℂ`) that is originally due to Ostrowski
[A. Ostrowski, *Über einige Lösungen der Funktionalgleichung φ(x)⋅φ(y)=φ(xy)*
  (Section 7)][ostrowski1916].
See also the concise version provided by Peter Scholze on
[Math Overflow](https://mathoverflow.net/questions/10535/ways-to-prove-the-fundamental-theorem-of-algebra/420803#420803).

(In the following, we write `a • 1` instead of `algebraMap _ F a` for easier reading.
In the code, we use `algebraMap`.)

This proof goes as follows. Let `x : F` be arbitrary; we need to show that `x = z • 1`
for some `z : ℂ`. We consider the function `z ↦ ‖x - z • 1‖`. It has a minimum `M`,
which it attains at some point `z₀`, which (upon replacing `x` by `x - z₀ • 1`) we can
assume to be zero. If `M = 0`, we are done, so assume not. For `n : ℕ`,
a primitive `n`th root of unity `ζ : ℂ`, and `z : ℂ` with `|z| < M = ‖x‖` we then have that
`M ≤ ‖x - z • 1‖ = ‖x ^ n - z ^ n • 1‖ / ∏ 0 < k < n, ‖x - (ζ ^ k * z) • 1‖`,
which is bounded by `(M ^ n + |z| ^ n) / M ^ (n - 1) = M * (1 + (|z| / M) ^ n)`.
Letting `n` tend to infinity then shows that `‖x - z • 1‖ = M`
(see `NormedAlgebra.norm_eq_of_isMinOn_of_forall_le`).
This implies that the set of `z` such that `‖x - z • 1‖ = M` is closed and open
(and nonempty), so it is all of `ℂ`, which contradicts `‖x - z • 1‖ ≥ |z| - M`
when `|z|` is sufficiently large.

### The real case

The usual proof for the real case is "either `F` contains a square root of `-1`;
then `F` is in fact a normed `ℂ`-algebra and we can use the result above, or else
we adjoin a square root of `-1` to `F` to obtain a normed `ℂ`-algebra `F'` and
apply the result to `F'`". The difficulty with formalizing this is that (as of October 2025)
Mathlib does not provide a normed `ℂ`-algebra instance for `F'` (neither for
`F' := AdjoinRoot (X ^ 2 + 1 : F[X])` nor for `F' := TensorProduct ℝ ℂ F`),
and it is not so straight-forward to set this up. So we take inspiration from the
proof sketched above for the complex case to obtain a direct proof.
An additional benefit is that this approach minimizes imports.

Since irreducible polynomials over `ℝ` have degree at most `2`, it must be the case
that each element is annihilated by a monic polynomial of degree `2`.
We fix `x : F` in the following.

The space `ℝ × ℝ` of monic polynomials of degree `2` is complete and locally compact
and hence `‖aeval x p‖` gets large when `p` has large coefficients.
This is actually slightly subtle. It is certainly true for `‖x - r • 1‖` with `r : ℝ`.
If the minimum of this is zero, then the minimum for monic polynomials of degree `2`
will also be zero (and is attained on a one-dimensional subset). Otherwise, one can
indeed show that a bound on `‖x ^ 2 - a • x + b • 1‖` implies bounds on `|a|` and `|b|`.

By the first sentence of the previous paragraph, there will be some `p₀`
such that `‖aeval x p₀‖` attains a minimum (see `NormedAlgebra.Real.exists_isMinOn_norm_φ`).
We assume that this is positive and derive a contradiction. Let `M := ‖aeval x p₀‖ > 0`
be the minimal value.
Since every monic polynomial `f : ℝ[X]` of even degree can be written as a product
of monic polynomials of degree `2`
(see `Polynomial.IsMonicOfDegree.eq_isMonicOfDegree_two_mul_isMonicOfDegree`),
it follows that `‖aeval x f‖ ≥ M ^ (f.natDegree / 2)`.

The goal is now to show that when `a` and `b` achieve the minimum `M` of `‖x ^ 2 - a • x + b • 1‖`
and `M > 0`, then we can find some neighborhood `U` of `(a, b)` in `ℝ × ℝ`
such that `‖x ^ 2 - a' • x + b' • 1‖ = M` for all `(a', b') ∈ U`
Then the set `S = {(a', b') | ‖x ^ 2 - a' • x + b' • 1‖ = M}` must be all of `ℝ × ℝ` (as it is
closed, open, and nonempty). (see `NormedAlgebra.Real.norm_φ_eq_norm_φ_of_isMinOn`).
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

@[expose] public section

/-!
### Auxiliary results used in both cases
-/

open Polynomial

namespace NormedAlgebra

open Filter Topology Set in
/- The key step: show that the norm of a suitable function is constant if the norm takes
a positive minimum and condition `H` below is satisfied. -/
private lemma norm_eq_of_isMinOn_of_forall_le {X E : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [SeminormedAddCommGroup E] {f : X → E} {M : ℝ} {x : X} (hM : 0 < M)
    (hx : ‖f x‖ = M) (h : IsMinOn (‖f ·‖) univ x) (hf : Continuous f)
    (H : ∀ {y} z, ‖f y‖ = M → ∀ n > 0, ‖f z‖ ≤ M * (1 + (‖f z - f y‖ / M) ^ n)) (y : X) :
    ‖f y‖ = M := by
  suffices {y | ‖f y‖ = M} = univ by simpa only [← this, hx] using mem_univ y
  refine IsClopen.eq_univ ⟨isClosed_eq (by fun_prop) (by fun_prop), ?_⟩ <| nonempty_of_mem hx
  rw [isOpen_iff_eventually]
  intro w hw
  filter_upwards [mem_map.mp <| hf.tendsto w (Metric.ball_mem_nhds (f w) hM)] with u hu
  simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, ← div_lt_one₀ hM] at hu
  refine le_antisymm ?_ (hx ▸ isMinOn_univ_iff.mp h u)
  suffices Tendsto (fun n : ℕ ↦ M * (1 + (‖f u - f w‖ / M) ^ n)) atTop (𝓝 (M * (1 + 0))) by
    refine ge_of_tendsto (by simpa) ?_
    filter_upwards [Ioi_mem_atTop 0] with n hn
    exact H u hw n hn
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hu |>.const_add 1 |>.const_mul M

open Filter Bornology Set in
/-- In a normed algebra `F` over a normed field `𝕜` that is a proper space, the function
`z : 𝕜 ↦ ‖x - algebraMap 𝕜 F z‖` achieves a global minimum for every `x : F`. -/
lemma exists_isMinOn_norm_sub_smul (𝕜 : Type*) {F : Type*} [NormedField 𝕜] [ProperSpace 𝕜]
    [SeminormedRing F] [NormedAlgebra 𝕜 F] [NormOneClass F] (x : F) :
    ∃ z : 𝕜, IsMinOn (‖x - algebraMap 𝕜 F ·‖) univ z := by
  have : Tendsto (‖x - algebraMap 𝕜 F ·‖) (cobounded 𝕜) atTop := by
    exact tendsto_norm_cobounded_atTop |>.comp <| tendsto_const_sub_cobounded x |>.comp <| by simp
  simp only [isMinOn_univ_iff]
  refine (show Continuous fun z : 𝕜 ↦ ‖x - algebraMap 𝕜 F z‖ by fun_prop)
    |>.exists_forall_le_of_isBounded 0 ?_
  simpa [isBounded_def, compl_setOf, Ioi] using this (Ioi_mem_atTop ‖x - (0 : 𝕜) • 1‖)

/-!
### The complex case
-/

namespace Complex

variable {F : Type*} [NormedRing F] [NormOneClass F] [NormMulClass F] [NormedAlgebra ℂ F]

/- If the norm of every monic linear polynomial over `ℂ`, evaluated at some `x : F`,
is bounded below by `M`, then the norm of the value at `x - algebraMap ℂ F c` of a monic polynomial
of degree `n` is bounded below by `M ^ n`. This follows by induction from the fact that
every monic polynomial over `ℂ` factors as a product of monic linear polynomials. -/
private lemma le_aeval_of_isMonicOfDegree (x : F) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ z' : ℂ, M ≤ ‖x - algebraMap ℂ F z'‖) {p : ℂ[X]} {n : ℕ} (hp : IsMonicOfDegree p n)
    (c : ℂ) :
    M ^ n ≤ ‖aeval (x - algebraMap ℂ F c) p‖ := by
  induction n generalizing p with
  | zero => simp [isMonicOfDegree_zero_iff.mp hp]
  | succ n ih =>
    obtain ⟨f₁, f₂, hf₁, hf₂, H⟩ := hp.eq_isMonicOfDegree_one_mul_isMonicOfDegree
    obtain ⟨r, rfl⟩ := isMonicOfDegree_one_iff.mp hf₁
    have H' (y : F) : aeval y (X + C r) = y + algebraMap ℂ F r := by simp
    simpa only [pow_succ, mul_comm, H, aeval_mul, H', sub_add, ← map_sub, norm_mul]
      using mul_le_mul (ih hf₂) (h (c - r)) hM (norm_nonneg _)

open Set in
/- We show that when `z ↦ ‖x - algebraMap ℂ F z‖` is never zero (and attains a minimum), then
it is constant. This uses the auxiliary result `norm_eq_of_isMinOn_of_forall_le`. -/
private lemma norm_sub_eq_norm_sub_of_isMinOn {x : F} {z : ℂ}
    (hz : IsMinOn (‖x - algebraMap ℂ F ·‖) univ z) (H : ∀ z' : ℂ, ‖x - algebraMap ℂ F z'‖ ≠ 0)
    (c : ℂ) :
    ‖x - algebraMap ℂ F c‖ = ‖x - algebraMap ℂ F z‖ := by
  set M := ‖x - algebraMap ℂ F z‖ with hMdef
  have hM₀ : 0 < M := by have := H z; positivity
  refine norm_eq_of_isMinOn_of_forall_le (f := (x - algebraMap ℂ F ·)) hM₀ hMdef.symm hz
    (by fun_prop) (fun {y} w hy n hn ↦ ?_) c
  dsimp only at hy ⊢
  -- show
  --  `‖x - algebraMap ℂ F w‖ ≤ M * (1 + (‖x - algebraMap ℂ F w - (x - algebraMap ℂ F y)‖ / M) ^ n)`
  rw [sub_sub_sub_cancel_left, ← map_sub, norm_algebraMap, norm_sub_rev y w, norm_one, mul_one,
    show M * (1 + (‖w - y‖ / M) ^ n) = (M ^ n + ‖w - y‖ ^ n) / M ^ (n - 1) by
      simp only [field, div_pow, ← pow_succ', Nat.sub_add_cancel hn],
    le_div_iff₀ (by positivity)]
  obtain ⟨p, hp, hrel⟩ :=
    (isMonicOfDegree_X_pow ℂ n).of_dvd_sub (by grind)
      (isMonicOfDegree_X_sub_one (w - y)) (by compute_degree!) <| sub_dvd_pow_sub_pow X _ n
  grw [le_aeval_of_isMonicOfDegree x hM₀.le (isMinOn_univ_iff.mp hz) hp y]
  rw [eq_comm, ← eq_sub_iff_add_eq, mul_comm] at hrel
  apply_fun (‖aeval (x - algebraMap ℂ F y) ·‖) at hrel
  simp only [map_sub, map_mul, aeval_X, aeval_C, sub_sub_sub_cancel_right, norm_mul, map_pow]
    at hrel
  rw [hrel]
  exact (norm_sub_le ..).trans <| by simp [hy, ← map_sub]

/-- If `F` is a normed `ℂ`-algebra and `x : F`, then there is a complex number `z` such that
`‖x - algebraMap ℂ F z‖ = 0` (whence `x = algebraMap ℂ F z`). -/
lemma exists_norm_sub_smul_one_eq_zero (x : F) :
    ∃ z : ℂ, ‖x - algebraMap ℂ F z‖ = 0 := by
  -- there is a minimizing `z : ℂ`; get it.
  obtain ⟨z, hz⟩ := exists_isMinOn_norm_sub_smul ℂ x
  set M := ‖x - algebraMap ℂ F z‖ with hM
  rcases eq_or_lt_of_le (show 0 ≤ M from norm_nonneg _) with hM₀ | hM₀
    -- minimum is zero: nothing to do
  · exact ⟨z, hM₀.symm⟩
  -- otherwise, use the result from above that `z ↦ ‖x - algebraMap ℂ F z‖` is constant
  -- to derive a contradiction.
  by_contra! H
  have key := norm_sub_eq_norm_sub_of_isMinOn hz H (‖x‖ + M + 1)
  rw [← hM, norm_sub_rev] at key
  replace key := (norm_sub_norm_le ..).trans_eq key
  rw [norm_algebraMap, norm_one, mul_one] at key
  norm_cast at key
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at key
  linarith only [key]

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
    rwa [norm_eq_zero, sub_eq_zero, eq_comm, ← ofId_apply] at hz

/-- A version of the **Gelfand-Mazur Theorem** for nontrivial normed `ℂ`-algebras `F`
with multiplicative norm: any such `F` is isomorphic to `ℂ` as a `ℂ`-algebra. -/
theorem nonempty_algEquiv : Nonempty (ℂ ≃ₐ[ℂ] F) := ⟨algEquivOfNormMul F⟩

end Complex


/-!
### The real case
-/

namespace Real

variable {F : Type*} [NormedRing F] [NormedAlgebra ℝ F]

/- A (private) abbreviation introduced for conciseness below.
We will show that for every `x : F`, `φ x` takes the value zero. -/
private noncomputable abbrev φ (x : F) (u : ℝ × ℝ) : F := x ^ 2 - u.1 • x + algebraMap ℝ F u.2

private lemma continuous_φ (x : F) : Continuous (φ x) := by fun_prop

private lemma aeval_eq_φ (x : F) (u : ℝ × ℝ) : aeval x (X ^ 2 - C u.1 * X + C u.2) = φ x u := by
  simp [Algebra.smul_def]

variable [NormOneClass F] [NormMulClass F]

/- If, for some `x : F`, `‖φ x ·‖` is bounded below by `M`, then the value at `x` of any monic
polynomial over `ℝ` of degree `2 * n` has norm bounded below by `M ^ n`. This follows by
induction from the fact that a real monic polynomial of even degree is a product of monic
polynomials of degree `2`. -/
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

/- The key step in the proof: if `a` and `b` are real numbers minimizing `‖φ x (a, b)‖`,
and the minimal value is strictly positive, then the function `(s, t) ↦ ‖φ x (s, t)‖`
is constant. -/
private lemma norm_φ_eq_norm_φ_of_isMinOn {x : F} {z : ℝ × ℝ} (h : IsMinOn (‖φ x ·‖) Set.univ z)
    (H : ‖φ x z‖ ≠ 0) (w : ℝ × ℝ) :
    ‖φ x w‖ = ‖φ x z‖ := by
  set M : ℝ := ‖φ x z‖ with hM
  have hM₀ : 0 < M := by positivity
  -- we use the key result `norm_eq_of_isMinOn_of_forall_le`
  refine norm_eq_of_isMinOn_of_forall_le hM₀ hM.symm h (continuous_φ x) (fun {w} u hw n hn ↦ ?_) w
  -- show `‖φ x u‖ ≤ M * (1 + (‖φ x u - φ x w‖ / M) ^ n)`
  have HH : M * (1 + (‖φ x u - φ x w‖ / M) ^ n) = (M ^ n + ‖φ x u - φ x w‖ ^ n) / M ^ (n - 1) := by
    simp only [field, div_pow, ← pow_succ', Nat.sub_add_cancel hn]
  rw [HH, le_div_iff₀ (by positivity)]; clear HH
  -- show `‖φ x u‖ * M ^ (n - 1) ≤ M ^ n + ‖φ x u - φ x w‖ ^ n`
  let q (y : ℝ × ℝ) : ℝ[X] := X ^ 2 - C y.1 * X + C y.2
  have hq (y : ℝ × ℝ) : IsMonicOfDegree (q y) 2 := isMonicOfDegree_sub_add_two ..
  have hsub : q w - q u = (C u.1 - C w.1) * X + C w.2 - C u.2 := by simp only [q]; ring
  have hdvd : q u ∣ q w ^ n - (q w - q u) ^ n := by
    nth_rewrite 1 [← sub_sub_self (q w) (q u)]
    exact sub_dvd_pow_sub_pow ..
  have H' : ((q w - q u) ^ n).natDegree < 2 * n := by rw [hsub]; compute_degree; grind
  -- write `q w ^ n = p * q u + (q w - q u) ^ n` with a monic polynomial `p` of deg. `2 * (n - 1)`,
  -- where `aeval x (q u) = φ x u` (*).
  obtain ⟨p, hp, hrel⟩ := ((hq w).pow n).of_dvd_sub (by grind) (hq u) H' hdvd; clear H' hdvd hsub
  rw [show 2 * n - 2 = 2 * (n - 1) by grind] at hp
  -- use that `‖aeval p x‖ ≥ M ^ (n - 1)`.
  grw [le_aeval_of_isMonicOfDegree hM₀.le (isMinOn_univ_iff.mp h) hp]
  -- from (*) above, deduce
  -- `‖φ x u‖ * ‖(aeval x) p‖ = ‖(aeval x) (q w ^ n) - (aeval x) ((q w - q u) ^ n)‖`
  -- and use that.
  rw [← sub_eq_iff_eq_add, eq_comm, mul_comm] at hrel
  apply_fun (‖aeval x ·‖) at hrel
  rw [map_mul, norm_mul, map_sub, aeval_eq_φ x u] at hrel
  rw [hrel, norm_sub_rev (φ ..)]
  exact (norm_sub_le ..).trans <| by simp [q, aeval_eq_φ, hw]

open Filter Topology Bornology in
omit [NormMulClass F] in
/- Assuming that `‖x - algebraMap ℝ F ·‖` is bounded below by a positive constant, we show that
`φ x w` grows unboundedly as `w : ℝ × ℝ` does. We will use this to obtain a contradiction
when `φ x` does not attain the value zero. -/
private lemma tendsto_φ_cobounded {x : F} {c : ℝ} (hc₀ : 0 < c)
    (hbd : ∀ r : ℝ, c ≤ ‖x - algebraMap ℝ F r‖) :
    Tendsto (φ x ·) (cobounded (ℝ × ℝ)) (cobounded F) := by
  simp_rw [φ, sub_add]
  refine tendsto_const_sub_cobounded _ |>.comp ?_
  rw [← tendsto_norm_atTop_iff_cobounded]
  -- split into statements involving each of the two components separately.
  refine Tendsto.coprod_of_prod_top_right (α := ℝ) (fun s hs ↦ ?_) ?_
    -- the first component is bounded and the second one is unbounded
  · rw [← isCobounded_def, ← isBounded_compl_iff] at hs
    obtain ⟨M, hM_pos, hM⟩ : ∃ M > 0, ∀ y ∈ sᶜ, ‖y‖ ≤ M := hs.exists_pos_norm_le
    suffices Tendsto (‖algebraMap ℝ F ·.2‖ - M * ‖x‖) (𝓟 sᶜ ×ˢ cobounded ℝ) atTop by
      refine tendsto_atTop_mono' _ ?_ this
      filter_upwards [prod_mem_prod (mem_principal_self sᶜ) univ_mem] with w hw
      rw [norm_sub_rev]
      refine le_trans ?_ (norm_sub_norm_le ..)
      specialize hM _ (Set.mem_prod.mp hw).1
      simp only [norm_algebraMap', norm_smul]
      gcongr
    simp only [norm_algebraMap', sub_eq_add_neg]
    exact tendsto_atTop_add_const_right _ _ <| tendsto_norm_atTop_iff_cobounded.mpr tendsto_snd
    -- the first component is unbounded and the second one is arbitrary
  · suffices Tendsto (fun y : ℝ × ℝ ↦ ‖y.1‖ * c) (cobounded ℝ ×ˢ ⊤) atTop by
      refine tendsto_atTop_mono' _ ?_ this
      filter_upwards [prod_mem_prod (isBounded_singleton (x := 0)) univ_mem] with y hy
      calc ‖y.1‖ * c
        _ ≤ ‖y.1‖ * ‖x - algebraMap ℝ F (y.1⁻¹ * y.2)‖ := by gcongr; exact hbd _
        _ = ‖y.1 • x - algebraMap ℝ F y.2‖ := by
          simp only [← norm_smul, smul_sub, smul_smul, Algebra.algebraMap_eq_smul_one]
          simp_all
    rw [tendsto_mul_const_atTop_of_pos hc₀, tendsto_norm_atTop_iff_cobounded]
    exact tendsto_fst

open Bornology Filter Set in
omit [NormMulClass F] in
/- The norm of `‖φ x ·‖` attains a minimum on `ℝ × ℝ`. -/
private lemma exists_isMinOn_norm_φ (x : F) : ∃ z : ℝ × ℝ, IsMinOn (‖φ x ·‖) univ z := by
  -- use that `‖x - algebraMap ℝ F ·‖` has a minimum.
  obtain ⟨u, hu⟩ := exists_isMinOn_norm_sub_smul ℝ x
  rcases eq_or_lt_of_le (norm_nonneg (x - algebraMap ℝ F u)) with hc₀ | hc₀
    -- if this minimum is zero, use `(u, 0)`.
  · rw [eq_comm, norm_eq_zero, sub_eq_zero] at hc₀
    exact ⟨(u, 0), fun _ ↦ by simp [φ, hc₀, sq, Algebra.smul_def]⟩
  -- otherwise, use `tendsto_φ_cobounded`.
  simp only [isMinOn_univ_iff] at hu ⊢
  refine (continuous_φ x).norm.exists_forall_le_of_isBounded (0, 0) ?_
  simpa [isBounded_def, compl_setOf, Ioi]
    using tendsto_norm_cobounded_atTop.comp (tendsto_φ_cobounded hc₀ hu) (Ioi_mem_atTop _)

open Algebra in
/-- If `F` is a normed `ℝ`-algebra with a multiplicative norm (and such that `‖1‖ = 1`),
e.g., a normed division ring, then every `x : F` is the root of a monic quadratic polynomial
with real coefficients. -/
lemma exists_isMonicOfDegree_two_and_aeval_eq_zero (x : F) :
    ∃ p : ℝ[X], IsMonicOfDegree p 2 ∧ aeval x p = 0 := by
  -- take the minimizer of `‖φ x ·‖` ...
  obtain ⟨z, h⟩ := exists_isMinOn_norm_φ x
  -- ... and show that the minimum is zero.
  suffices φ x z = 0 from ⟨_, isMonicOfDegree_sub_add_two z.1 z.2, by rwa [aeval_eq_φ]⟩
  by_contra! H
  set M := ‖φ x z‖
  -- use that `‖φ x ·‖` is constant *and* is unbounded to produce a contradiction.
  have h' (r : ℝ) : √M ≤ ‖x - algebraMap ℝ F r‖ := by
    rw [← sq_le_sq₀ M.sqrt_nonneg (norm_nonneg _), Real.sq_sqrt (norm_nonneg _), ← norm_pow,
      Commute.sub_sq <| algebraMap_eq_smul_one (A := F) r ▸ commute_algebraMap_right r x]
    convert isMinOn_univ_iff.mp h (2 * r, r ^ 2) using 4 <;>
      simp [two_mul, add_mul, ← commutes, smul_def, mul_add]
  have := tendsto_norm_atTop_iff_cobounded.mpr <| tendsto_φ_cobounded (by positivity) h'
  simp only [norm_φ_eq_norm_φ_of_isMinOn h (norm_ne_zero_iff.mpr H)] at this
  exact Filter.not_tendsto_const_atTop _ _ this

/-- A version of the **Gelfand-Mazur Theorem** over `ℝ`.

If a field `F` is a normed `ℝ`-algebra, then `F` is isomorphic as an `ℝ`-algebra
either to `ℝ` or to `ℂ`. -/
theorem nonempty_algEquiv_or (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    Nonempty (F ≃ₐ[ℝ] ℝ) ∨ Nonempty (F ≃ₐ[ℝ] ℂ) := by
  have : Algebra.IsAlgebraic ℝ F := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨f, hf, hfx⟩ := exists_isMonicOfDegree_two_and_aeval_eq_zero x
    exact ⟨f, hf.ne_zero, hfx⟩
  exact _root_.Real.nonempty_algEquiv_or F

end Real

end NormedAlgebra
