/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Data.ENat.Lattice

/-!
# Iterated derivatives of a function

In this file, we define iteratively the `n+1`-th derivative of a function as the
derivative of the `n`-th derivative. It is called `iteratedFDeriv 𝕜 n f x` where `𝕜` is the
field, `n` is the number of iterations, `f` is the function and `x` is the point, and it is given
as an `n`-multilinear map. We also define a version `iteratedFDerivWithin` relative to a domain.
Note that, in domains, there may be several choices of possible derivative, so we make some
arbitrary choice in the definition.

We also define a predicate `HasFTaylorSeriesUpTo` (and its localized version
`HasFTaylorSeriesUpToOn`), saying that a sequence of multilinear maps is *a* sequence of
derivatives of `f`. Contrary to `iteratedFDerivWithin`, it accommodates well the
non-uniqueness of derivatives.

## Main definitions and results

Let `f : E → F` be a map between normed vector spaces over a nontrivially normed field `𝕜`.

* `HasFTaylorSeriesUpTo n f p`: expresses that the formal multilinear series `p` is a sequence
  of iterated derivatives of `f`, up to the `n`-th term (where `n` is a natural number or `∞`).
* `HasFTaylorSeriesUpToOn n f p s`: same thing, but inside a set `s`. The notion of derivative
  is now taken inside `s`. In particular, derivatives don't have to be unique.

* `iteratedFDerivWithin 𝕜 n f s x` is an `n`-th derivative of `f` over the field `𝕜` on the
  set `s` at the point `x`. It is a continuous multilinear map from `E^n` to `F`, defined as a
  derivative within `s` of `iteratedFDerivWithin 𝕜 (n-1) f s` if one exists, and `0` otherwise.
* `iteratedFDeriv 𝕜 n f x` is the `n`-th derivative of `f` over the field `𝕜` at the point `x`.
  It is a continuous multilinear map from `E^n` to `F`, defined as a derivative of
  `iteratedFDeriv 𝕜 (n-1) f` if one exists, and `0` otherwise.


### Side of the composition, and universe issues

With a naïve direct definition, the `n`-th derivative of a function belongs to the space
`E →L[𝕜] (E →L[𝕜] (E ... F)...)))` where there are n iterations of `E →L[𝕜]`. This space
may also be seen as the space of continuous multilinear functions on `n` copies of `E` with
values in `F`, by uncurrying. This is the point of view that is usually adopted in textbooks,
and that we also use. This means that the definition and the first proofs are slightly involved,
as one has to keep track of the uncurrying operation. The uncurrying can be done from the
left or from the right, amounting to defining the `n+1`-th derivative either as the derivative of
the `n`-th derivative, or as the `n`-th derivative of the derivative.
For proofs, it would be more convenient to use the latter approach (from the right),
as it means to prove things at the `n+1`-th step we only need to understand well enough the
derivative in `E →L[𝕜] F` (contrary to the approach from the left, where one would need to know
enough on the `n`-th derivative to deduce things on the `n+1`-th derivative).

However, the definition from the right leads to a universe polymorphism problem: if we define
`iteratedFDeriv 𝕜 (n + 1) f x = iteratedFDeriv 𝕜 n (fderiv 𝕜 f) x` by induction, we need to
generalize over all spaces (as `f` and `fderiv 𝕜 f` don't take values in the same space). It is
only possible to generalize over all spaces in some fixed universe in an inductive definition.
For `f : E → F`, then `fderiv 𝕜 f` is a map `E → (E →L[𝕜] F)`. Therefore, the definition will only
work if `F` and `E →L[𝕜] F` are in the same universe.

This issue does not appear with the definition from the left, where one does not need to generalize
over all spaces. Therefore, we use the definition from the left. This means some proofs later on
become a little bit more complicated: to prove that a function is `C^n`, the most efficient approach
is to exhibit a formula for its `n`-th derivative and prove it is continuous (contrary to the
inductive approach where one would prove smoothness statements without giving a formula for the
derivative). In the end, this approach is still satisfactory as it is good to have formulas for the
iterated derivatives in various constructions.

One point where this explicit approach is particularly delicate is in the proof of smoothness of a
composition: there is a formula for the `n`-th derivative of a composition (Faà di Bruno's formula),
but it is very complicated, while the inductive proof is very simple. The inductive proof would
be good enough for `C^n` functions with `n ∈ ℕ ∪ {∞}` (modulo polymorphism issues, i.e., one would
need to first prove inductively the result when all spaces belong to the same universe, and then
prove the general result by lifting all the spaces to a common universe). However, it would not
work for `C^ω` functions. Therefore, we give the proof based on Faà di Bruno's formula, which is
more complicated but more general.

### Variables management

The textbook definitions and proofs use various identifications and abuse of notations, for instance
when saying that the natural space in which the derivative lives, i.e.,
`E →L[𝕜] (E →L[𝕜] ( ... →L[𝕜] F))`, is the same as a space of multilinear maps. When doing things
formally, we need to provide explicit maps for these identifications, and chase some diagrams to see
everything is compatible with the identifications. In particular, one needs to check that taking the
derivative and then doing the identification, or first doing the identification and then taking the
derivative, gives the same result. The key point for this is that taking the derivative commutes
with continuous linear equivalences. Therefore, we need to implement all our identifications with
continuous linear equivs.

## Notation

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `⊤ : ℕ∞` with `∞`.
-/


noncomputable section

open ENat NNReal Topology Filter Set Fin Filter Function

/-- Smoothness exponent for analytic functions. -/
scoped[ContDiff] notation3 "ω" => (⊤ : WithTop ℕ∞)
/-- Smoothness exponent for infinitely differentiable functions. -/
scoped[ContDiff] notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

open scoped ContDiff Pointwise

universe u uE uF

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {s t u : Set E} {f f₁ : E → F} {x : E} {m n N : WithTop ℕ∞}
  {p : E → FormalMultilinearSeries 𝕜 E F}

/-! ### Functions with a Taylor series on a domain -/

/-- `HasFTaylorSeriesUpToOn n f p s` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`HasFDerivWithinAt` but for higher-order derivatives.

Notice that `p` does not sum up to `f` on the diagonal (`FormalMultilinearSeries.sum`), even if
`f` is analytic and `n = ∞`: an additional `1/m!` factor on the `m`th term is necessary for that. -/
structure HasFTaylorSeriesUpToOn
  (n : WithTop ℕ∞) (f : E → F) (p : E → FormalMultilinearSeries 𝕜 E F) (s : Set E) : Prop where
  zero_eq : ∀ x ∈ s, (p x 0).curry0 = f x
  protected fderivWithin : ∀ m : ℕ, m < n → ∀ x ∈ s,
    HasFDerivWithinAt (p · m) (p x m.succ).curryLeft s x
  cont : ∀ m : ℕ, m ≤ n → ContinuousOn (p · m) s

theorem HasFTaylorSeriesUpToOn.zero_eq' (h : HasFTaylorSeriesUpToOn n f p s) {x : E} (hx : x ∈ s) :
    p x 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (f x) := by
  rw [← h.zero_eq x hx]
  exact (p x 0).uncurry0_curry0.symm

/-- If two functions coincide on a set `s`, then a Taylor series for the first one is as well a
Taylor series for the second one. -/
theorem HasFTaylorSeriesUpToOn.congr (h : HasFTaylorSeriesUpToOn n f p s)
    (h₁ : ∀ x ∈ s, f₁ x = f x) : HasFTaylorSeriesUpToOn n f₁ p s := by
  refine ⟨fun x hx => ?_, h.fderivWithin, h.cont⟩
  rw [h₁ x hx]
  exact h.zero_eq x hx

theorem HasFTaylorSeriesUpToOn.congr_series {q} (hp : HasFTaylorSeriesUpToOn n f p s)
    (hpq : ∀ m : ℕ, m ≤ n → EqOn (p · m) (q · m) s) :
    HasFTaylorSeriesUpToOn n f q s where
  zero_eq x hx := by simp only [← (hpq 0 (zero_le n) hx), hp.zero_eq x hx]
  fderivWithin m hm x hx := by
    refine ((hp.fderivWithin m hm x hx).congr' (hpq m hm.le).symm hx).congr_fderiv ?_
    refine congrArg _ (hpq (m + 1) ?_ hx)
    exact ENat.add_one_natCast_le_withTop_of_lt hm
  cont m hm := (hp.cont m hm).congr (hpq m hm).symm

theorem HasFTaylorSeriesUpToOn.mono (h : HasFTaylorSeriesUpToOn n f p s) {t : Set E} (hst : t ⊆ s) :
    HasFTaylorSeriesUpToOn n f p t :=
  ⟨fun x hx => h.zero_eq x (hst hx), fun m hm x hx => (h.fderivWithin m hm x (hst hx)).mono hst,
    fun m hm => (h.cont m hm).mono hst⟩

theorem HasFTaylorSeriesUpToOn.of_le (h : HasFTaylorSeriesUpToOn n f p s) (hmn : m ≤ n) :
    HasFTaylorSeriesUpToOn m f p s :=
  ⟨h.zero_eq, fun k hk x hx => h.fderivWithin k (lt_of_lt_of_le hk hmn) x hx, fun k hk =>
    h.cont k (le_trans hk hmn)⟩

theorem HasFTaylorSeriesUpToOn.continuousOn (h : HasFTaylorSeriesUpToOn n f p s) :
    ContinuousOn f s := by
  have := (h.cont 0 bot_le).congr fun x hx => (h.zero_eq' hx).symm
  rwa [← (continuousMultilinearCurryFin0 𝕜 E F).symm.comp_continuousOn_iff]

theorem hasFTaylorSeriesUpToOn_zero_iff :
    HasFTaylorSeriesUpToOn 0 f p s ↔ ContinuousOn f s ∧ ∀ x ∈ s, (p x 0).curry0 = f x := by
  refine ⟨fun H => ⟨H.continuousOn, H.zero_eq⟩, fun H =>
      ⟨H.2, fun m hm => False.elim (not_le.2 hm bot_le), fun m hm ↦ ?_⟩⟩
  obtain rfl : m = 0 := mod_cast hm.antisymm (zero_le _)
  have : EqOn (p · 0) ((continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f) s := fun x hx ↦
    (continuousMultilinearCurryFin0 𝕜 E F).eq_symm_apply.2 (H.2 x hx)
  rw [continuousOn_congr this, LinearIsometryEquiv.comp_continuousOn_iff]
  exact H.1

theorem hasFTaylorSeriesUpToOn_top_iff_add (hN : ∞ ≤ N) (k : ℕ) :
    HasFTaylorSeriesUpToOn N f p s ↔ ∀ n : ℕ, HasFTaylorSeriesUpToOn (n + k : ℕ) f p s := by
  constructor
  · intro H n
    apply H.of_le (natCast_le_of_coe_top_le_withTop hN _)
  · intro H
    constructor
    · exact (H 0).zero_eq
    · intro m _
      apply (H m.succ).fderivWithin m (by norm_cast; cutsat)
    · intro m _
      apply (H m).cont m (by simp)

theorem hasFTaylorSeriesUpToOn_top_iff (hN : ∞ ≤ N) :
    HasFTaylorSeriesUpToOn N f p s ↔ ∀ n : ℕ, HasFTaylorSeriesUpToOn n f p s := by
  simpa using hasFTaylorSeriesUpToOn_top_iff_add hN 0

/-- In the case that `n = ∞` we don't need the continuity assumption in
`HasFTaylorSeriesUpToOn`. -/
theorem hasFTaylorSeriesUpToOn_top_iff' (hN : ∞ ≤ N) :
    HasFTaylorSeriesUpToOn N f p s ↔
      (∀ x ∈ s, (p x 0).curry0 = f x) ∧
        ∀ m : ℕ, ∀ x ∈ s, HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft s x := by
  -- Everything except for the continuity is trivial:
  refine ⟨fun h => ⟨h.1, fun m => h.2 m (natCast_lt_of_coe_top_le_withTop hN _)⟩, fun h =>
    ⟨h.1, fun m _ => h.2 m, fun m _ x hx =>
      -- The continuity follows from the existence of a derivative:
      (h.2 m x hx).continuousWithinAt⟩⟩

/-- If a function has a Taylor series at order at least `1`, then the term of order `1` of this
series is a derivative of `f`. -/
theorem HasFTaylorSeriesUpToOn.hasFDerivWithinAt (h : HasFTaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
    (hx : x ∈ s) : HasFDerivWithinAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) s x := by
  have A : ∀ y ∈ s, f y = (continuousMultilinearCurryFin0 𝕜 E F) (p y 0) := fun y hy ↦
    (h.zero_eq y hy).symm
  suffices H : HasFDerivWithinAt (continuousMultilinearCurryFin0 𝕜 E F ∘ (p · 0))
    (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) s x from H.congr A (A x hx)
  rw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff']
  have : ((0 : ℕ) : ℕ∞) < n := zero_lt_one.trans_le hn
  convert h.fderivWithin _ this x hx
  ext y v
  change (p x 1) (snoc 0 y) = (p x 1) (cons y v)
  congr with i
  rw [Unique.eq_default (α := Fin 1) i]
  rfl

theorem HasFTaylorSeriesUpToOn.differentiableOn (h : HasFTaylorSeriesUpToOn n f p s) (hn : 1 ≤ n) :
    DifferentiableOn 𝕜 f s := fun _x hx => (h.hasFDerivWithinAt hn hx).differentiableWithinAt

/-- If a function has a Taylor series at order at least `1` on a neighborhood of `x`, then the term
of order `1` of this series is a derivative of `f` at `x`. -/
theorem HasFTaylorSeriesUpToOn.hasFDerivAt (h : HasFTaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
    (hx : s ∈ 𝓝 x) : HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) x :=
  (h.hasFDerivWithinAt hn (mem_of_mem_nhds hx)).hasFDerivAt hx

/-- If a function has a Taylor series at order at least `1` on a neighborhood of `x`, then
in a neighborhood of `x`, the term of order `1` of this series is a derivative of `f`. -/
theorem HasFTaylorSeriesUpToOn.eventually_hasFDerivAt (h : HasFTaylorSeriesUpToOn n f p s)
    (hn : 1 ≤ n) (hx : s ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p y 1)) y :=
  (eventually_eventually_nhds.2 hx).mono fun _y hy => h.hasFDerivAt hn hy

/-- If a function has a Taylor series at order at least `1` on a neighborhood of `x`, then
it is differentiable at `x`. -/
theorem HasFTaylorSeriesUpToOn.differentiableAt (h : HasFTaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
    (hx : s ∈ 𝓝 x) : DifferentiableAt 𝕜 f x :=
  (h.hasFDerivAt hn hx).differentiableAt

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p` is a Taylor series up to `n`, and
`p (n + 1)` is a derivative of `p n`. -/
theorem hasFTaylorSeriesUpToOn_succ_iff_left {n : ℕ} :
    HasFTaylorSeriesUpToOn (n + 1) f p s ↔
      HasFTaylorSeriesUpToOn n f p s ∧
        (∀ x ∈ s, HasFDerivWithinAt (fun y => p y n) (p x n.succ).curryLeft s x) ∧
          ContinuousOn (fun x => p x (n + 1)) s := by
  constructor
  · exact fun h ↦ ⟨h.of_le (mod_cast Nat.le_succ n),
      h.fderivWithin _ (mod_cast lt_add_one n), h.cont (n + 1) le_rfl⟩
  · intro h
    constructor
    · exact h.1.zero_eq
    · intro m hm
      by_cases h' : m < n
      · exact h.1.fderivWithin m (mod_cast h')
      · have : m = n := Nat.eq_of_lt_succ_of_not_lt (mod_cast hm) h'
        rw [this]
        exact h.2.1
    · intro m hm
      by_cases h' : m ≤ n
      · apply h.1.cont m (mod_cast h')
      · have : m = n + 1 := le_antisymm (mod_cast hm) (not_le.1 h')
        rw [this]
        exact h.2.2

theorem HasFTaylorSeriesUpToOn.shift_of_succ
    {n : ℕ} (H : HasFTaylorSeriesUpToOn (n + 1 : ℕ) f p s) :
    (HasFTaylorSeriesUpToOn n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1))
      (fun x => (p x).shift)) s := by
  constructor
  · intro x _
    rfl
  · intro m (hm : (m : WithTop ℕ∞) < n) x (hx : x ∈ s)
    have A : (m.succ : WithTop ℕ∞) < n.succ := by
      rw [Nat.cast_lt] at hm ⊢
      exact Nat.succ_lt_succ hm
    change HasFDerivWithinAt (continuousMultilinearCurryRightEquiv' 𝕜 m E F ∘ (p · m.succ))
      (p x m.succ.succ).curryRight.curryLeft s x
    rw [(continuousMultilinearCurryRightEquiv' 𝕜 m E F).comp_hasFDerivWithinAt_iff']
    convert H.fderivWithin _ A x hx
    ext y v
    change p x (m + 2) (snoc (cons y (init v)) (v (last _))) = p x (m + 2) (cons y v)
    rw [← cons_snoc_eq_snoc_cons, snoc_init_self]
  · intro m (hm : (m : WithTop ℕ∞) ≤ n)
    suffices A : ContinuousOn (p · (m + 1)) s from
      (continuousMultilinearCurryRightEquiv' 𝕜 m E F).continuous.comp_continuousOn A
    refine H.cont _ ?_
    rw [Nat.cast_le] at hm ⊢
    exact Nat.succ_le_succ hm

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. Version for `n : ℕ`. -/
theorem hasFTaylorSeriesUpToOn_succ_nat_iff_right {n : ℕ} :
    HasFTaylorSeriesUpToOn (n + 1 : ℕ) f p s ↔
      (∀ x ∈ s, (p x 0).curry0 = f x) ∧
        (∀ x ∈ s, HasFDerivWithinAt (fun y => p y 0) (p x 1).curryLeft s x) ∧
          HasFTaylorSeriesUpToOn n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1))
            (fun x => (p x).shift) s := by
  constructor
  · intro H
    refine ⟨H.zero_eq, H.fderivWithin 0 (Nat.cast_lt.2 (Nat.succ_pos n)), ?_⟩
    exact H.shift_of_succ
  · rintro ⟨Hzero_eq, Hfderiv_zero, Htaylor⟩
    constructor
    · exact Hzero_eq
    · intro m (hm : (m : WithTop ℕ∞) < n.succ) x (hx : x ∈ s)
      rcases m with - | m
      · exact Hfderiv_zero x hx
      · have A : (m : WithTop ℕ∞) < n := by
          rw [Nat.cast_lt] at hm ⊢
          exact Nat.lt_of_succ_lt_succ hm
        have :
          HasFDerivWithinAt (𝕜 := 𝕜) (continuousMultilinearCurryRightEquiv' 𝕜 m E F ∘ (p · m.succ))
            ((p x).shift m.succ).curryLeft s x := Htaylor.fderivWithin _ A x hx
        rw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff'
            (f' := ((p x).shift m.succ).curryLeft)] at this
        convert this
        ext y v
        change
          (p x (Nat.succ (Nat.succ m))) (cons y v) =
            (p x m.succ.succ) (snoc (cons y (init v)) (v (last _)))
        rw [← cons_snoc_eq_snoc_cons, snoc_init_self]
    · intro m (hm : (m : WithTop ℕ∞) ≤ n.succ)
      rcases m with - | m
      · have : DifferentiableOn 𝕜 (fun x => p x 0) s := fun x hx =>
          (Hfderiv_zero x hx).differentiableWithinAt
        exact this.continuousOn
      · refine (continuousMultilinearCurryRightEquiv' 𝕜 m E F).comp_continuousOn_iff.mp ?_
        refine Htaylor.cont _ ?_
        rw [Nat.cast_le] at hm ⊢
        exact Nat.lt_succ_iff.mp hm

/-- `p` is a Taylor series of `f` up to `⊤` if and only if `p.shift` is a Taylor series up to `⊤`
for `p 1`, which is a derivative of `f`. -/
theorem hasFTaylorSeriesUpToOn_top_iff_right (hN : ∞ ≤ N) :
    HasFTaylorSeriesUpToOn N f p s ↔
      (∀ x ∈ s, (p x 0).curry0 = f x) ∧
        (∀ x ∈ s, HasFDerivWithinAt (fun y => p y 0) (p x 1).curryLeft s x) ∧
          HasFTaylorSeriesUpToOn N (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1))
            (fun x => (p x).shift) s := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [hasFTaylorSeriesUpToOn_top_iff_add hN 1] at h
    rw [hasFTaylorSeriesUpToOn_top_iff hN]
    exact ⟨(hasFTaylorSeriesUpToOn_succ_nat_iff_right.1 (h 1)).1,
      (hasFTaylorSeriesUpToOn_succ_nat_iff_right.1 (h 1)).2.1,
      fun n ↦ (hasFTaylorSeriesUpToOn_succ_nat_iff_right.1 (h n)).2.2⟩
  · apply (hasFTaylorSeriesUpToOn_top_iff_add hN 1).2 (fun n ↦ ?_)
    rw [hasFTaylorSeriesUpToOn_succ_nat_iff_right]
    exact ⟨h.1, h.2.1, (h.2.2).of_le (m := n) (natCast_le_of_coe_top_le_withTop hN n)⟩

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. Version for `n : WithTop ℕ∞`. -/
theorem hasFTaylorSeriesUpToOn_succ_iff_right :
    HasFTaylorSeriesUpToOn (n + 1) f p s ↔
      (∀ x ∈ s, (p x 0).curry0 = f x) ∧
        (∀ x ∈ s, HasFDerivWithinAt (fun y => p y 0) (p x 1).curryLeft s x) ∧
          HasFTaylorSeriesUpToOn n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1))
            (fun x => (p x).shift) s := by
  match n with
  | ⊤ => exact hasFTaylorSeriesUpToOn_top_iff_right (by simp)
  | (⊤ : ℕ∞) => exact hasFTaylorSeriesUpToOn_top_iff_right (by simp)
  | (n : ℕ) => exact hasFTaylorSeriesUpToOn_succ_nat_iff_right

/-! ### Iterated derivative within a set -/


variable (𝕜)

/-- The `n`-th derivative of a function along a set, defined inductively by saying that the `n+1`-th
derivative of `f` is the derivative of the `n`-th derivative of `f` along this set, together with
an uncurrying step to see it as a multilinear map in `n+1` variables..
-/
noncomputable def iteratedFDerivWithin (n : ℕ) (f : E → F) (s : Set E) : E → E[×n]→L[𝕜] F :=
  Nat.recOn n (fun x => ContinuousMultilinearMap.uncurry0 𝕜 E (f x)) fun _ rec x =>
    ContinuousLinearMap.uncurryLeft (fderivWithin 𝕜 rec s x)

/-- Formal Taylor series associated to a function within a set. -/
def ftaylorSeriesWithin (f : E → F) (s : Set E) (x : E) : FormalMultilinearSeries 𝕜 E F := fun n =>
  iteratedFDerivWithin 𝕜 n f s x

variable {𝕜}

@[simp]
theorem iteratedFDerivWithin_zero_apply (m : Fin 0 → E) :
    (iteratedFDerivWithin 𝕜 0 f s x : (Fin 0 → E) → F) m = f x :=
  rfl

theorem iteratedFDerivWithin_zero_eq_comp :
    iteratedFDerivWithin 𝕜 0 f s = (continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f :=
  rfl

@[simp]
theorem dist_iteratedFDerivWithin_zero (f : E → F) (s : Set E) (x : E)
    (g : E → F) (t : Set E) (y : E) :
    dist (iteratedFDerivWithin 𝕜 0 f s x) (iteratedFDerivWithin 𝕜 0 g t y) = dist (f x) (g y) := by
  simp only [iteratedFDerivWithin_zero_eq_comp, comp_apply, LinearIsometryEquiv.dist_map]

@[simp]
theorem norm_iteratedFDerivWithin_zero : ‖iteratedFDerivWithin 𝕜 0 f s x‖ = ‖f x‖ := by
  rw [iteratedFDerivWithin_zero_eq_comp, comp_apply, LinearIsometryEquiv.norm_map]

theorem iteratedFDerivWithin_succ_apply_left {n : ℕ} (m : Fin (n + 1) → E) :
    (iteratedFDerivWithin 𝕜 (n + 1) f s x : (Fin (n + 1) → E) → F) m =
      (fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s x : E → E[×n]→L[𝕜] F) (m 0) (tail m) :=
  rfl

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
theorem iteratedFDerivWithin_succ_eq_comp_left {n : ℕ} :
    iteratedFDerivWithin 𝕜 (n + 1) f s =
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F).symm ∘
        fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s :=
  rfl

theorem fderivWithin_iteratedFDerivWithin {s : Set E} {n : ℕ} :
    fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s =
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F) ∘
        iteratedFDerivWithin 𝕜 (n + 1) f s :=
  rfl

theorem norm_fderivWithin_iteratedFDerivWithin {n : ℕ} :
    ‖fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s x‖ =
      ‖iteratedFDerivWithin 𝕜 (n + 1) f s x‖ := by
  rw [iteratedFDerivWithin_succ_eq_comp_left, comp_apply, LinearIsometryEquiv.norm_map]

@[simp]
theorem dist_iteratedFDerivWithin_one (f g : E → F) {y}
    (hsx : UniqueDiffWithinAt 𝕜 s x) (hyt : UniqueDiffWithinAt 𝕜 t y) :
    dist (iteratedFDerivWithin 𝕜 1 f s x) (iteratedFDerivWithin 𝕜 1 g t y)
      = dist (fderivWithin 𝕜 f s x) (fderivWithin 𝕜 g t y) := by
  simp only [iteratedFDerivWithin_succ_eq_comp_left, comp_apply,
    LinearIsometryEquiv.dist_map, iteratedFDerivWithin_zero_eq_comp,
    LinearIsometryEquiv.comp_fderivWithin, hsx, hyt]
  apply (continuousMultilinearCurryFin0 𝕜 E F).symm.toLinearIsometry.postcomp.dist_map

@[simp]
theorem norm_iteratedFDerivWithin_one (f : E → F) (h : UniqueDiffWithinAt 𝕜 s x) :
    ‖iteratedFDerivWithin 𝕜 1 f s x‖ = ‖fderivWithin 𝕜 f s x‖ := by
  simp only [← norm_fderivWithin_iteratedFDerivWithin,
    iteratedFDerivWithin_zero_eq_comp, LinearIsometryEquiv.comp_fderivWithin _ h]
  apply (continuousMultilinearCurryFin0 𝕜 E F).symm.toLinearIsometry.norm_toContinuousLinearMap_comp

theorem iteratedFDerivWithin_succ_apply_right {n : ℕ} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s)
    (m : Fin (n + 1) → E) :
    (iteratedFDerivWithin 𝕜 (n + 1) f s x : (Fin (n + 1) → E) → F) m =
      iteratedFDerivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s x (init m) (m (last n)) := by
  induction n generalizing x with
  | zero =>
    rw [iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_zero_eq_comp,
      iteratedFDerivWithin_zero_apply, Function.comp_apply,
      LinearIsometryEquiv.comp_fderivWithin _ (hs x hx)]
    simp
  | succ n IH =>
    let I := (continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm
    have A : ∀ y ∈ s, iteratedFDerivWithin 𝕜 n.succ f s y =
        (I ∘ iteratedFDerivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) y := fun y hy ↦ by
      ext m
      simp [IH hy m, I]
    calc
      (iteratedFDerivWithin 𝕜 (n + 2) f s x : (Fin (n + 2) → E) → F) m =
          (fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n.succ f s) s x : E → E[×n + 1]→L[𝕜] F) (m 0)
            (tail m) := by
        simp [iteratedFDerivWithin_succ_eq_comp_left]
      _ = (fderivWithin 𝕜 (I ∘ iteratedFDerivWithin 𝕜 n (fderivWithin 𝕜 f s) s) s x :
              E → E[×n + 1]→L[𝕜] F) (m 0) (tail m) := by
        rw [fderivWithin_congr A (A x hx)]
      _ = (I ∘ fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n (fderivWithin 𝕜 f s) s) s x :
              E → E[×n + 1]→L[𝕜] F) (m 0) (tail m) := by
        simp [LinearIsometryEquiv.comp_fderivWithin _ (hs x hx)]
      _ = (fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) s x :
              E → E[×n]→L[𝕜] E →L[𝕜] F) (m 0) (init (tail m)) ((tail m) (last n)) := by
        simp [I]
      _ = iteratedFDerivWithin 𝕜 (Nat.succ n) (fun y => fderivWithin 𝕜 f s y) s x (init m)
            (m (last (n + 1))) := by
        rw [iteratedFDerivWithin_succ_apply_left, tail_init_eq_init_tail]
        simp [init, tail]

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the `n`-th derivative of the derivative. -/
theorem iteratedFDerivWithin_succ_eq_comp_right {n : ℕ} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFDerivWithin 𝕜 (n + 1) f s x =
      ((continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm ∘
          iteratedFDerivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s)
        x := by
  ext m; simp [iteratedFDerivWithin_succ_apply_right hs hx]

theorem norm_iteratedFDerivWithin_fderivWithin {n : ℕ} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    ‖iteratedFDerivWithin 𝕜 n (fderivWithin 𝕜 f s) s x‖ =
      ‖iteratedFDerivWithin 𝕜 (n + 1) f s x‖ := by
  rw [iteratedFDerivWithin_succ_eq_comp_right hs hx, comp_apply, LinearIsometryEquiv.norm_map]

@[simp]
theorem iteratedFDerivWithin_one_apply (h : UniqueDiffWithinAt 𝕜 s x) (m : Fin 1 → E) :
    iteratedFDerivWithin 𝕜 1 f s x m = fderivWithin 𝕜 f s x (m 0) := by
  simp [iteratedFDerivWithin_succ_apply_left, iteratedFDerivWithin_zero_eq_comp,
    (continuousMultilinearCurryFin0 𝕜 E F).symm.comp_fderivWithin h]

/-- On a set of unique differentiability, the second derivative is obtained by taking the
derivative of the derivative. -/
lemma iteratedFDerivWithin_two_apply (f : E → F) {z : E} (hs : UniqueDiffOn 𝕜 s) (hz : z ∈ s)
    (m : Fin 2 → E) :
    iteratedFDerivWithin 𝕜 2 f s z m = fderivWithin 𝕜 (fderivWithin 𝕜 f s) s z (m 0) (m 1) := by
  simp only [iteratedFDerivWithin_succ_apply_right hs hz]
  rfl

/-- On a set of unique differentiability, the second derivative is obtained by taking the
derivative of the derivative. -/
lemma iteratedFDerivWithin_two_apply' (f : E → F) {z : E} (hs : UniqueDiffOn 𝕜 s) (hz : z ∈ s)
    (v w : E) :
    iteratedFDerivWithin 𝕜 2 f s z ![v, w] = fderivWithin 𝕜 (fderivWithin 𝕜 f s) s z v w :=
  iteratedFDerivWithin_two_apply f hs hz _

theorem Filter.EventuallyEq.iteratedFDerivWithin' (h : f₁ =ᶠ[𝓝[s] x] f) (ht : t ⊆ s) (n : ℕ) :
    iteratedFDerivWithin 𝕜 n f₁ t =ᶠ[𝓝[s] x] iteratedFDerivWithin 𝕜 n f t := by
  induction n with
  | zero => exact h.mono fun y hy => DFunLike.ext _ _ fun _ => hy
  | succ n ihn =>
    have : fderivWithin 𝕜 _ t =ᶠ[𝓝[s] x] fderivWithin 𝕜 _ t := ihn.fderivWithin' ht
    refine this.mono fun y hy => ?_
    simp only [iteratedFDerivWithin_succ_eq_comp_left, hy, (· ∘ ·)]

protected theorem Filter.EventuallyEq.iteratedFDerivWithin (h : f₁ =ᶠ[𝓝[s] x] f) (n : ℕ) :
    iteratedFDerivWithin 𝕜 n f₁ s =ᶠ[𝓝[s] x] iteratedFDerivWithin 𝕜 n f s :=
  h.iteratedFDerivWithin' Subset.rfl n

/-- If two functions coincide in a neighborhood of `x` within a set `s` and at `x`, then their
iterated differentials within this set at `x` coincide. -/
theorem Filter.EventuallyEq.iteratedFDerivWithin_eq (h : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
    (n : ℕ) : iteratedFDerivWithin 𝕜 n f₁ s x = iteratedFDerivWithin 𝕜 n f s x :=
  have : f₁ =ᶠ[𝓝[insert x s] x] f := by simpa [EventuallyEq, hx]
  (this.iteratedFDerivWithin' (subset_insert _ _) n).self_of_nhdsWithin (mem_insert _ _)

/-- If two functions coincide on a set `s`, then their iterated differentials within this set
coincide. See also `Filter.EventuallyEq.iteratedFDerivWithin_eq` and
`Filter.EventuallyEq.iteratedFDerivWithin`. -/
theorem iteratedFDerivWithin_congr (hs : EqOn f₁ f s) (hx : x ∈ s) (n : ℕ) :
    iteratedFDerivWithin 𝕜 n f₁ s x = iteratedFDerivWithin 𝕜 n f s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).iteratedFDerivWithin_eq (hs hx) _

/-- If two functions coincide on a set `s`, then their iterated differentials within this set
coincide. See also `Filter.EventuallyEq.iteratedFDerivWithin_eq` and
`Filter.EventuallyEq.iteratedFDerivWithin`. -/
protected theorem Set.EqOn.iteratedFDerivWithin (hs : EqOn f₁ f s) (n : ℕ) :
    EqOn (iteratedFDerivWithin 𝕜 n f₁ s) (iteratedFDerivWithin 𝕜 n f s) s := fun _x hx =>
  iteratedFDerivWithin_congr hs hx n

theorem iteratedFDerivWithin_eventually_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) (n : ℕ) :
    iteratedFDerivWithin 𝕜 n f s =ᶠ[𝓝 x] iteratedFDerivWithin 𝕜 n f t := by
  induction n generalizing x with
  | zero => rfl
  | succ n ihn =>
    refine (eventually_nhds_nhdsWithin.2 h).mono fun y hy => ?_
    simp only [iteratedFDerivWithin_succ_eq_comp_left, (· ∘ ·)]
    rw [(ihn hy).fderivWithin_eq_of_nhds, fderivWithin_congr_set' _ hy]

theorem iteratedFDerivWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) (n : ℕ) :
    iteratedFDerivWithin 𝕜 n f s =ᶠ[𝓝 x] iteratedFDerivWithin 𝕜 n f t :=
  iteratedFDerivWithin_eventually_congr_set' x (h.filter_mono inf_le_left) n

/-- If two sets coincide in a punctured neighborhood of `x`,
then the corresponding iterated derivatives are equal.

Note that we also allow to puncture the neighborhood of `x` at `y`.
If `y ≠ x`, then this is a no-op. -/
theorem iteratedFDerivWithin_congr_set' {y} (h : s =ᶠ[𝓝[{y}ᶜ] x] t) (n : ℕ) :
    iteratedFDerivWithin 𝕜 n f s x = iteratedFDerivWithin 𝕜 n f t x :=
  (iteratedFDerivWithin_eventually_congr_set' y h n).self_of_nhds

@[simp]
theorem iteratedFDerivWithin_insert {n y} :
    iteratedFDerivWithin 𝕜 n f (insert x s) y = iteratedFDerivWithin 𝕜 n f s y :=
  iteratedFDerivWithin_congr_set' (y := x)
    (eventually_mem_nhdsWithin.mono <| by intros; simp_all).set_eq _

theorem iteratedFDerivWithin_congr_set (h : s =ᶠ[𝓝 x] t) (n : ℕ) :
    iteratedFDerivWithin 𝕜 n f s x = iteratedFDerivWithin 𝕜 n f t x :=
  (iteratedFDerivWithin_eventually_congr_set h n).self_of_nhds

@[simp]
theorem ftaylorSeriesWithin_insert :
    ftaylorSeriesWithin 𝕜 f (insert x s) = ftaylorSeriesWithin 𝕜 f s := by
  ext y n : 2
  apply iteratedFDerivWithin_insert

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x` within `s`. -/
theorem iteratedFDerivWithin_inter' {n : ℕ} (hu : u ∈ 𝓝[s] x) :
    iteratedFDerivWithin 𝕜 n f (s ∩ u) x = iteratedFDerivWithin 𝕜 n f s x :=
  iteratedFDerivWithin_congr_set (nhdsWithin_eq_iff_eventuallyEq.1 <| nhdsWithin_inter_of_mem' hu) _

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x`. -/
theorem iteratedFDerivWithin_inter {n : ℕ} (hu : u ∈ 𝓝 x) :
    iteratedFDerivWithin 𝕜 n f (s ∩ u) x = iteratedFDerivWithin 𝕜 n f s x :=
  iteratedFDerivWithin_inter' (mem_nhdsWithin_of_mem_nhds hu)

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with an open set containing `x`. -/
theorem iteratedFDerivWithin_inter_open {n : ℕ} (hu : IsOpen u) (hx : x ∈ u) :
    iteratedFDerivWithin 𝕜 n f (s ∩ u) x = iteratedFDerivWithin 𝕜 n f s x :=
  iteratedFDerivWithin_inter (hu.mem_nhds hx)

/-- On a set with unique differentiability, any choice of iterated differential has to coincide
with the one we have chosen in `iteratedFDerivWithin 𝕜 m f s`. -/
theorem HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (h : HasFTaylorSeriesUpToOn n f p s) {m : ℕ} (hmn : m ≤ n) (hs : UniqueDiffOn 𝕜 s)
    (hx : x ∈ s) : p x m = iteratedFDerivWithin 𝕜 m f s x := by
  induction m generalizing x with
  | zero => rw [h.zero_eq' hx, iteratedFDerivWithin_zero_eq_comp, comp_apply]
  | succ m IH =>
    have A : m < n := lt_of_lt_of_le (mod_cast lt_add_one m) hmn
    have :
      HasFDerivWithinAt (fun y : E => iteratedFDerivWithin 𝕜 m f s y)
        (ContinuousMultilinearMap.curryLeft (p x (Nat.succ m))) s x :=
      (h.fderivWithin m A x hx).congr (fun y hy => (IH (le_of_lt A) hy).symm)
        (IH (le_of_lt A) hx).symm
    rw [iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply, this.fderivWithin (hs x hx)]
    exact (ContinuousMultilinearMap.uncurry_curryLeft _).symm

/-- The iterated derivative commutes with shifting the function by a constant on the left. -/
lemma iteratedFDerivWithin_comp_add_left' (n : ℕ) (a : E) :
    iteratedFDerivWithin 𝕜 n (fun z ↦ f (a + z)) s =
      fun x ↦ iteratedFDerivWithin 𝕜 n f (a +ᵥ s) (a + x) := by
  induction n with
  | zero => simp [iteratedFDerivWithin]
  | succ n IH =>
    ext v
    rw [iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_succ_eq_comp_left]
    simp only [Nat.succ_eq_add_one, IH, comp_apply, continuousMultilinearCurryLeftEquiv_symm_apply]
    congr 2
    rw [fderivWithin_comp_add_left]

/-- The iterated derivative commutes with shifting the function by a constant on the left. -/
lemma iteratedFDerivWithin_comp_add_left (n : ℕ) (a : E) (x : E) :
    iteratedFDerivWithin 𝕜 n (fun z ↦ f (a + z)) s x =
      iteratedFDerivWithin 𝕜 n f (a +ᵥ s) (a + x) := by
  simp [iteratedFDerivWithin_comp_add_left']

/-- The iterated derivative commutes with shifting the function by a constant on the right. -/
lemma iteratedFDerivWithin_comp_add_right' (n : ℕ) (a : E) :
    iteratedFDerivWithin 𝕜 n (fun z ↦ f (z + a)) s =
      fun x ↦ iteratedFDerivWithin 𝕜 n f (a +ᵥ s) (x + a) := by
  simpa [add_comm a] using iteratedFDerivWithin_comp_add_left' n a

/-- The iterated derivative commutes with shifting the function by a constant on the right. -/
lemma iteratedFDerivWithin_comp_add_right (n : ℕ) (a : E) (x : E) :
    iteratedFDerivWithin 𝕜 n (fun z ↦ f (z + a)) s x =
      iteratedFDerivWithin 𝕜 n f (a +ᵥ s) (x + a) := by
  simp [iteratedFDerivWithin_comp_add_right']

/-- The iterated derivative commutes with subtracting a constant. -/
lemma iteratedFDerivWithin_comp_sub' (n : ℕ) (a : E) :
    iteratedFDerivWithin 𝕜 n (fun z ↦ f (z - a)) s =
      fun x ↦ iteratedFDerivWithin 𝕜 n f (-a +ᵥ s) (x - a) := by
  simpa [sub_eq_add_neg] using iteratedFDerivWithin_comp_add_right' n (-a)

/-- The iterated derivative commutes with subtracting a constant. -/
lemma iteratedFDerivWithin_comp_sub (n : ℕ) (a : E) :
    iteratedFDerivWithin 𝕜 n (fun z ↦ f (z - a)) s x =
      iteratedFDerivWithin 𝕜 n f (-a +ᵥ s) (x - a) := by
  simp [iteratedFDerivWithin_comp_sub']

/-! ### Functions with a Taylor series on the whole space -/

/-- `HasFTaylorSeriesUpTo n f p` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`HasFDerivAt` but for higher-order derivatives.

Notice that `p` does not sum up to `f` on the diagonal (`FormalMultilinearSeries.sum`), even if
`f` is analytic and `n = ∞`: an addition `1/m!` factor on the `m`th term is necessary for that. -/
structure HasFTaylorSeriesUpTo
  (n : WithTop ℕ∞) (f : E → F) (p : E → FormalMultilinearSeries 𝕜 E F) : Prop where
  zero_eq : ∀ x, (p x 0).curry0 = f x
  fderiv : ∀ m : ℕ, m < n → ∀ x, HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x
  cont : ∀ m : ℕ, m ≤ n → Continuous fun x => p x m

theorem HasFTaylorSeriesUpTo.zero_eq' (h : HasFTaylorSeriesUpTo n f p) (x : E) :
    p x 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (f x) := by
  rw [← h.zero_eq x]
  exact (p x 0).uncurry0_curry0.symm

theorem hasFTaylorSeriesUpToOn_univ_iff :
    HasFTaylorSeriesUpToOn n f p univ ↔ HasFTaylorSeriesUpTo n f p := by
  constructor
  · intro H
    constructor
    · exact fun x => H.zero_eq x (mem_univ x)
    · intro m hm x
      rw [← hasFDerivWithinAt_univ]
      exact H.fderivWithin m hm x (mem_univ x)
    · intro m hm
      rw [← continuousOn_univ]
      exact H.cont m hm
  · intro H
    constructor
    · exact fun x _ => H.zero_eq x
    · intro m hm x _
      rw [hasFDerivWithinAt_univ]
      exact H.fderiv m hm x
    · intro m hm
      rw [continuousOn_univ]
      exact H.cont m hm

theorem HasFTaylorSeriesUpTo.hasFTaylorSeriesUpToOn (h : HasFTaylorSeriesUpTo n f p) (s : Set E) :
    HasFTaylorSeriesUpToOn n f p s :=
  (hasFTaylorSeriesUpToOn_univ_iff.2 h).mono (subset_univ _)

theorem HasFTaylorSeriesUpTo.of_le (h : HasFTaylorSeriesUpTo n f p) (hmn : m ≤ n) :
    HasFTaylorSeriesUpTo m f p := by
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h ⊢; exact h.of_le hmn

theorem HasFTaylorSeriesUpTo.continuous (h : HasFTaylorSeriesUpTo n f p) : Continuous f := by
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h
  rw [← continuousOn_univ]
  exact h.continuousOn

theorem hasFTaylorSeriesUpTo_zero_iff :
    HasFTaylorSeriesUpTo 0 f p ↔ Continuous f ∧ ∀ x, (p x 0).curry0 = f x := by
  simp [hasFTaylorSeriesUpToOn_univ_iff.symm, continuousOn_univ,
    hasFTaylorSeriesUpToOn_zero_iff]

theorem hasFTaylorSeriesUpTo_top_iff (hN : ∞ ≤ N) :
    HasFTaylorSeriesUpTo N f p ↔ ∀ n : ℕ, HasFTaylorSeriesUpTo n f p := by
  simp only [← hasFTaylorSeriesUpToOn_univ_iff, hasFTaylorSeriesUpToOn_top_iff hN]

/-- In the case that `n = ∞` we don't need the continuity assumption in
`HasFTaylorSeriesUpTo`. -/
theorem hasFTaylorSeriesUpTo_top_iff' (hN : ∞ ≤ N) :
    HasFTaylorSeriesUpTo N f p ↔
      (∀ x, (p x 0).curry0 = f x) ∧
        ∀ (m : ℕ) (x), HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x := by
  simp only [← hasFTaylorSeriesUpToOn_univ_iff, hasFTaylorSeriesUpToOn_top_iff' hN, mem_univ,
    forall_true_left, hasFDerivWithinAt_univ]

/-- If a function has a Taylor series at order at least `1`, then the term of order `1` of this
series is a derivative of `f`. -/
theorem HasFTaylorSeriesUpTo.hasFDerivAt (h : HasFTaylorSeriesUpTo n f p) (hn : 1 ≤ n) (x : E) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) x := by
  rw [← hasFDerivWithinAt_univ]
  exact (hasFTaylorSeriesUpToOn_univ_iff.2 h).hasFDerivWithinAt hn (mem_univ _)

theorem HasFTaylorSeriesUpTo.differentiable (h : HasFTaylorSeriesUpTo n f p) (hn : 1 ≤ n) :
    Differentiable 𝕜 f := fun x => (h.hasFDerivAt hn x).differentiableAt

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. -/
theorem hasFTaylorSeriesUpTo_succ_nat_iff_right {n : ℕ} :
    HasFTaylorSeriesUpTo (n + 1 : ℕ) f p ↔
      (∀ x, (p x 0).curry0 = f x) ∧
        (∀ x, HasFDerivAt (fun y => p y 0) (p x 1).curryLeft x) ∧
          HasFTaylorSeriesUpTo n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1)) fun x =>
            (p x).shift := by
  simp only [hasFTaylorSeriesUpToOn_succ_nat_iff_right, ← hasFTaylorSeriesUpToOn_univ_iff, mem_univ,
    forall_true_left, hasFDerivWithinAt_univ]

/-! ### Iterated derivative -/


variable (𝕜)

/-- The `n`-th derivative of a function, as a multilinear map, defined inductively. -/
noncomputable def iteratedFDeriv (n : ℕ) (f : E → F) : E → E[×n]→L[𝕜] F :=
  Nat.recOn n (fun x => ContinuousMultilinearMap.uncurry0 𝕜 E (f x)) fun _ rec x =>
    ContinuousLinearMap.uncurryLeft (fderiv 𝕜 rec x)

/-- Formal Taylor series associated to a function. -/
def ftaylorSeries (f : E → F) (x : E) : FormalMultilinearSeries 𝕜 E F := fun n =>
  iteratedFDeriv 𝕜 n f x

variable {𝕜}

@[simp]
theorem iteratedFDeriv_zero_apply (m : Fin 0 → E) :
    (iteratedFDeriv 𝕜 0 f x : (Fin 0 → E) → F) m = f x :=
  rfl

theorem iteratedFDeriv_zero_eq_comp :
    iteratedFDeriv 𝕜 0 f = (continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f :=
  rfl

@[simp]
theorem norm_iteratedFDeriv_zero : ‖iteratedFDeriv 𝕜 0 f x‖ = ‖f x‖ := by
  rw [iteratedFDeriv_zero_eq_comp, comp_apply, LinearIsometryEquiv.norm_map]

theorem iteratedFDerivWithin_zero_eq : iteratedFDerivWithin 𝕜 0 f s = iteratedFDeriv 𝕜 0 f := rfl

theorem iteratedFDeriv_succ_apply_left {n : ℕ} (m : Fin (n + 1) → E) :
    (iteratedFDeriv 𝕜 (n + 1) f x : (Fin (n + 1) → E) → F) m =
      (fderiv 𝕜 (iteratedFDeriv 𝕜 n f) x : E → E[×n]→L[𝕜] F) (m 0) (tail m) :=
  rfl

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
theorem iteratedFDeriv_succ_eq_comp_left {n : ℕ} :
    iteratedFDeriv 𝕜 (n + 1) f =
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F).symm ∘
        fderiv 𝕜 (iteratedFDeriv 𝕜 n f) :=
  rfl

/-- Writing explicitly the derivative of the `n`-th derivative as the composition of a currying
linear equiv, and the `n + 1`-th derivative. -/
theorem fderiv_iteratedFDeriv {n : ℕ} :
    fderiv 𝕜 (iteratedFDeriv 𝕜 n f) =
      continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F ∘
        iteratedFDeriv 𝕜 (n + 1) f :=
  rfl

theorem tsupport_iteratedFDeriv_subset (n : ℕ) : tsupport (iteratedFDeriv 𝕜 n f) ⊆ tsupport f := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact closure_minimal ((support_comp_subset (LinearIsometryEquiv.map_zero _) _).trans
      subset_closure) isClosed_closure
  | succ n IH =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact closure_minimal ((support_comp_subset (LinearIsometryEquiv.map_zero _) _).trans
      ((support_fderiv_subset 𝕜).trans IH)) isClosed_closure

theorem support_iteratedFDeriv_subset (n : ℕ) : support (iteratedFDeriv 𝕜 n f) ⊆ tsupport f :=
  subset_closure.trans (tsupport_iteratedFDeriv_subset n)

theorem HasCompactSupport.iteratedFDeriv (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedFDeriv 𝕜 n f) :=
  hf.of_isClosed_subset isClosed_closure (tsupport_iteratedFDeriv_subset n)

theorem norm_fderiv_iteratedFDeriv {n : ℕ} :
    ‖fderiv 𝕜 (iteratedFDeriv 𝕜 n f) x‖ = ‖iteratedFDeriv 𝕜 (n + 1) f x‖ := by
  rw [iteratedFDeriv_succ_eq_comp_left, comp_apply, LinearIsometryEquiv.norm_map]

theorem iteratedFDerivWithin_univ {n : ℕ} :
    iteratedFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f := by
  induction n with
  | zero => ext x; simp
  | succ n IH =>
    ext x m
    rw [iteratedFDeriv_succ_apply_left, iteratedFDerivWithin_succ_apply_left, IH, fderivWithin_univ]

variable (𝕜) in
/-- If two functions agree in a neighborhood, then so do their iterated derivatives. -/
theorem Filter.EventuallyEq.iteratedFDeriv
    {f₁ f₂ : E → F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) (n : ℕ) :
    iteratedFDeriv 𝕜 n f₁ =ᶠ[𝓝 x] iteratedFDeriv 𝕜 n f₂ := by
  simp_all [← nhdsWithin_univ, ← iteratedFDerivWithin_univ,
    Filter.EventuallyEq.iteratedFDerivWithin]

theorem HasFTaylorSeriesUpTo.eq_iteratedFDeriv
    (h : HasFTaylorSeriesUpTo n f p) {m : ℕ} (hmn : m ≤ n) (x : E) :
    p x m = iteratedFDeriv 𝕜 m f x := by
  rw [← iteratedFDerivWithin_univ]
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h
  exact h.eq_iteratedFDerivWithin_of_uniqueDiffOn hmn uniqueDiffOn_univ (mem_univ _)

/-- In an open set, the iterated derivative within this set coincides with the global iterated
derivative. -/
theorem iteratedFDerivWithin_of_isOpen (n : ℕ) (hs : IsOpen s) :
    EqOn (iteratedFDerivWithin 𝕜 n f s) (iteratedFDeriv 𝕜 n f) s := by
  induction n with
  | zero =>
    intro x _
    ext1
    simp only [iteratedFDerivWithin_zero_apply, iteratedFDeriv_zero_apply]
  | succ n IH =>
    intro x hx
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDerivWithin_succ_eq_comp_left]
    dsimp
    congr 1
    rw [fderivWithin_of_isOpen hs hx]
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hs.mem_nhds hx]
    exact IH

theorem ftaylorSeriesWithin_univ : ftaylorSeriesWithin 𝕜 f univ = ftaylorSeries 𝕜 f := by
  ext1 x; ext1 n
  change iteratedFDerivWithin 𝕜 n f univ x = iteratedFDeriv 𝕜 n f x
  rw [iteratedFDerivWithin_univ]

theorem iteratedFDeriv_succ_apply_right {n : ℕ} (m : Fin (n + 1) → E) :
    (iteratedFDeriv 𝕜 (n + 1) f x : (Fin (n + 1) → E) → F) m =
      iteratedFDeriv 𝕜 n (fun y => fderiv 𝕜 f y) x (init m) (m (last n)) := by
  rw [← iteratedFDerivWithin_univ, ← iteratedFDerivWithin_univ, ← fderivWithin_univ]
  exact iteratedFDerivWithin_succ_apply_right uniqueDiffOn_univ (mem_univ _) _

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the `n`-th derivative of the derivative. -/
theorem iteratedFDeriv_succ_eq_comp_right {n : ℕ} :
    iteratedFDeriv 𝕜 (n + 1) f x =
      ((continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm ∘
          iteratedFDeriv 𝕜 n fun y => fderiv 𝕜 f y) x := by
  ext m
  rw [iteratedFDeriv_succ_apply_right, comp_apply, continuousMultilinearCurryRightEquiv_symm_apply']

theorem norm_iteratedFDeriv_fderiv {n : ℕ} :
    ‖iteratedFDeriv 𝕜 n (fderiv 𝕜 f) x‖ = ‖iteratedFDeriv 𝕜 (n + 1) f x‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, comp_apply, LinearIsometryEquiv.norm_map]

@[simp]
theorem iteratedFDeriv_one_apply (m : Fin 1 → E) :
    iteratedFDeriv 𝕜 1 f x m = fderiv 𝕜 f x (m 0) := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_zero_apply, last_zero]

lemma iteratedFDeriv_two_apply (f : E → F) (z : E) (m : Fin 2 → E) :
    iteratedFDeriv 𝕜 2 f z m = fderiv 𝕜 (fderiv 𝕜 f) z (m 0) (m 1) := by
  simp [iteratedFDeriv_succ_apply_right, init]

/-- The iterated derivative commutes with shifting the function by a constant on the left. -/
lemma iteratedFDeriv_comp_add_left' (n : ℕ) (a : E) :
    iteratedFDeriv 𝕜 n (fun z ↦ f (a + z)) = fun x ↦ iteratedFDeriv 𝕜 n f (a + x) := by
  simpa [← iteratedFDerivWithin_univ] using iteratedFDerivWithin_comp_add_left' n a (s := univ)

/-- The iterated derivative commutes with shifting the function by a constant on the left. -/
lemma iteratedFDeriv_comp_add_left (n : ℕ) (a : E) (x : E) :
    iteratedFDeriv 𝕜 n (fun z ↦ f (a + z)) x = iteratedFDeriv 𝕜 n f (a + x) := by
  simp [iteratedFDeriv_comp_add_left']

/-- The iterated derivative commutes with shifting the function by a constant on the right. -/
lemma iteratedFDeriv_comp_add_right' (n : ℕ) (a : E) :
    iteratedFDeriv 𝕜 n (fun z ↦ f (z + a)) = fun x ↦ iteratedFDeriv 𝕜 n f (x + a) := by
  simpa [add_comm a] using iteratedFDeriv_comp_add_left' n a

/-- The iterated derivative commutes with shifting the function by a constant on the right. -/
lemma iteratedFDeriv_comp_add_right (n : ℕ) (a : E) (x : E) :
    iteratedFDeriv 𝕜 n (fun z ↦ f (z + a)) x = iteratedFDeriv 𝕜 n f (x + a) := by
  simp [iteratedFDeriv_comp_add_right']

/-- The iterated derivative commutes with subtracting a constant. -/
lemma iteratedFDeriv_comp_sub' (n : ℕ) (a : E) :
    iteratedFDeriv 𝕜 n (fun z ↦ f (z - a)) = fun x ↦ iteratedFDeriv 𝕜 n f (x - a) := by
  simpa [sub_eq_add_neg] using iteratedFDeriv_comp_add_right' n (-a)

/-- The iterated derivative commutes with subtracting a constant. -/
lemma iteratedFDeriv_comp_sub (n : ℕ) (a : E) (x : E) :
    iteratedFDeriv 𝕜 n (fun z ↦ f (z - a)) x = iteratedFDeriv 𝕜 n f (x - a) := by
  simp [iteratedFDeriv_comp_sub']
