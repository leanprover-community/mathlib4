/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.calculus.cont_diff_def
! leanprover-community/mathlib commit 3a69562db5a458db8322b190ec8d9a8bbd8a5b14
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.Fderiv.Add
import Mathbin.Analysis.Calculus.Fderiv.Mul
import Mathbin.Analysis.Calculus.Fderiv.Equiv
import Mathbin.Analysis.Calculus.Fderiv.RestrictScalars
import Mathbin.Analysis.Calculus.FormalMultilinearSeries

/-!
# Higher differentiability

A function is `C^1` on a domain if it is differentiable there, and its derivative is continuous.
By induction, it is `C^n` if it is `C^{n-1}` and its (n-1)-th derivative is `C^1` there or,
equivalently, if it is `C^1` and its derivative is `C^{n-1}`.
Finally, it is `C^∞` if it is `C^n` for all n.

We formalize these notions by defining iteratively the `n+1`-th derivative of a function as the
derivative of the `n`-th derivative. It is called `iterated_fderiv 𝕜 n f x` where `𝕜` is the
field, `n` is the number of iterations, `f` is the function and `x` is the point, and it is given
as an `n`-multilinear map. We also define a version `iterated_fderiv_within` relative to a domain,
as well as predicates `cont_diff_within_at`, `cont_diff_at`, `cont_diff_on` and
`cont_diff` saying that the function is `C^n` within a set at a point, at a point, on a set
and on the whole space respectively.

To avoid the issue of choice when choosing a derivative in sets where the derivative is not
necessarily unique, `cont_diff_on` is not defined directly in terms of the
regularity of the specific choice `iterated_fderiv_within 𝕜 n f s` inside `s`, but in terms of the
existence of a nice sequence of derivatives, expressed with a predicate
`has_ftaylor_series_up_to_on`.

We prove basic properties of these notions.

## Main definitions and results
Let `f : E → F` be a map between normed vector spaces over a nontrivially normed field `𝕜`.

* `has_ftaylor_series_up_to n f p`: expresses that the formal multilinear series `p` is a sequence
  of iterated derivatives of `f`, up to the `n`-th term (where `n` is a natural number or `∞`).
* `has_ftaylor_series_up_to_on n f p s`: same thing, but inside a set `s`. The notion of derivative
  is now taken inside `s`. In particular, derivatives don't have to be unique.
* `cont_diff 𝕜 n f`: expresses that `f` is `C^n`, i.e., it admits a Taylor series up to
  rank `n`.
* `cont_diff_on 𝕜 n f s`: expresses that `f` is `C^n` in `s`.
* `cont_diff_at 𝕜 n f x`: expresses that `f` is `C^n` around `x`.
* `cont_diff_within_at 𝕜 n f s x`: expresses that `f` is `C^n` around `x` within the set `s`.
* `iterated_fderiv_within 𝕜 n f s x` is an `n`-th derivative of `f` over the field `𝕜` on the
  set `s` at the point `x`. It is a continuous multilinear map from `E^n` to `F`, defined as a
  derivative within `s` of `iterated_fderiv_within 𝕜 (n-1) f s` if one exists, and `0` otherwise.
* `iterated_fderiv 𝕜 n f x` is the `n`-th derivative of `f` over the field `𝕜` at the point `x`.
  It is a continuous multilinear map from `E^n` to `F`, defined as a derivative of
  `iterated_fderiv 𝕜 (n-1) f` if one exists, and `0` otherwise.

In sets of unique differentiability, `cont_diff_on 𝕜 n f s` can be expressed in terms of the
properties of `iterated_fderiv_within 𝕜 m f s` for `m ≤ n`. In the whole space,
`cont_diff 𝕜 n f` can be expressed in terms of the properties of `iterated_fderiv 𝕜 m f`
for `m ≤ n`.

## Implementation notes

The definitions in this file are designed to work on any field `𝕜`. They are sometimes slightly more
complicated than the naive definitions one would guess from the intuition over the real or complex
numbers, but they are designed to circumvent the lack of gluing properties and partitions of unity
in general. In the usual situations, they coincide with the usual definitions.

### Definition of `C^n` functions in domains

One could define `C^n` functions in a domain `s` by fixing an arbitrary choice of derivatives (this
is what we do with `iterated_fderiv_within`) and requiring that all these derivatives up to `n` are
continuous. If the derivative is not unique, this could lead to strange behavior like two `C^n`
functions `f` and `g` on `s` whose sum is not `C^n`. A better definition is thus to say that a
function is `C^n` inside `s` if it admits a sequence of derivatives up to `n` inside `s`.

This definition still has the problem that a function which is locally `C^n` would not need to
be `C^n`, as different choices of sequences of derivatives around different points might possibly
not be glued together to give a globally defined sequence of derivatives. (Note that this issue
can not happen over reals, thanks to partition of unity, but the behavior over a general field is
not so clear, and we want a definition for general fields). Also, there are locality
problems for the order parameter: one could image a function which, for each `n`, has a nice
sequence of derivatives up to order `n`, but they do not coincide for varying `n` and can therefore
not be glued to give rise to an infinite sequence of derivatives. This would give a function
which is `C^n` for all `n`, but not `C^∞`. We solve this issue by putting locality conditions
in space and order in our definition of `cont_diff_within_at` and `cont_diff_on`.
The resulting definition is slightly more complicated to work with (in fact not so much), but it
gives rise to completely satisfactory theorems.

For instance, with this definition, a real function which is `C^m` (but not better) on `(-1/m, 1/m)`
for each natural `m` is by definition `C^∞` at `0`.

There is another issue with the definition of `cont_diff_within_at 𝕜 n f s x`. We can
require the existence and good behavior of derivatives up to order `n` on a neighborhood of `x`
within `s`. However, this does not imply continuity or differentiability within `s` of the function
at `x` when `x` does not belong to `s`. Therefore, we require such existence and good behavior on
a neighborhood of `x` within `s ∪ {x}` (which appears as `insert x s` in this file).

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
`iterated_fderiv 𝕜 (n + 1) f x = iterated_fderiv 𝕜 n (fderiv 𝕜 f) x` by induction, we need to
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

One point where we depart from this explicit approach is in the proof of smoothness of a
composition: there is a formula for the `n`-th derivative of a composition (Faà di Bruno's formula),
but it is very complicated and barely usable, while the inductive proof is very simple. Thus, we
give the inductive proof. As explained above, it works by generalizing over the target space, hence
it only works well if all spaces belong to the same universe. To get the general version, we lift
things to a common universe using a trick.

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

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `⊤ : ℕ∞` with `∞`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/


noncomputable section

open Classical BigOperators NNReal Topology Filter

-- mathport name: «expr∞»
local notation "∞" => (⊤ : ℕ∞)

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule' AddCommGroup.toAddCommMonoid

open Set Fin Filter Function

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {X : Type _} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {s s₁ t u : Set E} {f f₁ : E → F} {g : F → G} {x x₀ : E} {c : F} {m n : ℕ∞}
  {p : E → FormalMultilinearSeries 𝕜 E F}

/-! ### Functions with a Taylor series on a domain -/


/-- `has_ftaylor_series_up_to_on n f p s` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`has_fderiv_within_at` but for higher order derivatives. -/
structure HasFtaylorSeriesUpToOn (n : ℕ∞) (f : E → F) (p : E → FormalMultilinearSeries 𝕜 E F)
  (s : Set E) : Prop where
  zero_eq : ∀ x ∈ s, (p x 0).uncurry0 = f x
  fderivWithin :
    ∀ (m : ℕ) (hm : (m : ℕ∞) < n),
      ∀ x ∈ s, HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft s x
  cont : ∀ (m : ℕ) (hm : (m : ℕ∞) ≤ n), ContinuousOn (fun x => p x m) s
#align has_ftaylor_series_up_to_on HasFtaylorSeriesUpToOn

theorem HasFtaylorSeriesUpToOn.zero_eq' (h : HasFtaylorSeriesUpToOn n f p s) {x : E} (hx : x ∈ s) :
    p x 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (f x) := by rw [← h.zero_eq x hx]; symm;
  exact ContinuousMultilinearMap.uncurry0_curry0 _
#align has_ftaylor_series_up_to_on.zero_eq' HasFtaylorSeriesUpToOn.zero_eq'

/-- If two functions coincide on a set `s`, then a Taylor series for the first one is as well a
Taylor series for the second one. -/
theorem HasFtaylorSeriesUpToOn.congr (h : HasFtaylorSeriesUpToOn n f p s)
    (h₁ : ∀ x ∈ s, f₁ x = f x) : HasFtaylorSeriesUpToOn n f₁ p s :=
  by
  refine' ⟨fun x hx => _, h.fderiv_within, h.cont⟩
  rw [h₁ x hx]
  exact h.zero_eq x hx
#align has_ftaylor_series_up_to_on.congr HasFtaylorSeriesUpToOn.congr

theorem HasFtaylorSeriesUpToOn.mono (h : HasFtaylorSeriesUpToOn n f p s) {t : Set E} (hst : t ⊆ s) :
    HasFtaylorSeriesUpToOn n f p t :=
  ⟨fun x hx => h.zero_eq x (hst hx), fun m hm x hx => (h.fderivWithin m hm x (hst hx)).mono hst,
    fun m hm => (h.cont m hm).mono hst⟩
#align has_ftaylor_series_up_to_on.mono HasFtaylorSeriesUpToOn.mono

theorem HasFtaylorSeriesUpToOn.ofLe (h : HasFtaylorSeriesUpToOn n f p s) (hmn : m ≤ n) :
    HasFtaylorSeriesUpToOn m f p s :=
  ⟨h.zero_eq, fun k hk x hx => h.fderivWithin k (lt_of_lt_of_le hk hmn) x hx, fun k hk =>
    h.cont k (le_trans hk hmn)⟩
#align has_ftaylor_series_up_to_on.of_le HasFtaylorSeriesUpToOn.ofLe

theorem HasFtaylorSeriesUpToOn.continuousOn (h : HasFtaylorSeriesUpToOn n f p s) :
    ContinuousOn f s :=
  by
  have := (h.cont 0 bot_le).congr fun x hx => (h.zero_eq' hx).symm
  rwa [LinearIsometryEquiv.comp_continuousOn_iff] at this
#align has_ftaylor_series_up_to_on.continuous_on HasFtaylorSeriesUpToOn.continuousOn

theorem hasFtaylorSeriesUpToOn_zero_iff :
    HasFtaylorSeriesUpToOn 0 f p s ↔ ContinuousOn f s ∧ ∀ x ∈ s, (p x 0).uncurry0 = f x :=
  by
  refine'
    ⟨fun H => ⟨H.ContinuousOn, H.zero_eq⟩, fun H =>
      ⟨H.2, fun m hm => False.elim (not_le.2 hm bot_le), _⟩⟩
  intro m hm
  obtain rfl : m = 0 := by exact_mod_cast hm.antisymm (zero_le _)
  have : ∀ x ∈ s, p x 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (f x) := by intro x hx;
    rw [← H.2 x hx]; symm; exact ContinuousMultilinearMap.uncurry0_curry0 _
  rw [continuousOn_congr this, LinearIsometryEquiv.comp_continuousOn_iff]
  exact H.1
#align has_ftaylor_series_up_to_on_zero_iff hasFtaylorSeriesUpToOn_zero_iff

theorem hasFtaylorSeriesUpToOn_top_iff :
    HasFtaylorSeriesUpToOn ∞ f p s ↔ ∀ n : ℕ, HasFtaylorSeriesUpToOn n f p s :=
  by
  constructor
  · intro H n; exact H.of_le le_top
  · intro H
    constructor
    · exact (H 0).zero_eq
    · intro m hm
      apply (H m.succ).fderivWithin m (WithTop.coe_lt_coe.2 (lt_add_one m))
    · intro m hm
      apply (H m).cont m le_rfl
#align has_ftaylor_series_up_to_on_top_iff hasFtaylorSeriesUpToOn_top_iff

/-- In the case that `n = ∞` we don't need the continuity assumption in
`has_ftaylor_series_up_to_on`. -/
theorem hasFtaylorSeriesUpToOn_top_iff' :
    HasFtaylorSeriesUpToOn ∞ f p s ↔
      (∀ x ∈ s, (p x 0).uncurry0 = f x) ∧
        ∀ m : ℕ, ∀ x ∈ s, HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft s x :=
  ⟨-- Everything except for the continuity is trivial:
  fun h => ⟨h.1, fun m => h.2 m (WithTop.coe_lt_top m)⟩, fun h =>
    ⟨h.1, fun m _ => h.2 m, fun m _ x hx =>
      (-- The continuity follows from the existence of a derivative:
            h.2
          m x hx).ContinuousWithinAt⟩⟩
#align has_ftaylor_series_up_to_on_top_iff' hasFtaylorSeriesUpToOn_top_iff'

/-- If a function has a Taylor series at order at least `1`, then the term of order `1` of this
series is a derivative of `f`. -/
theorem HasFtaylorSeriesUpToOn.hasFDerivWithinAt (h : HasFtaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
    (hx : x ∈ s) : HasFDerivWithinAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) s x :=
  by
  have A : ∀ y ∈ s, f y = (continuousMultilinearCurryFin0 𝕜 E F) (p y 0) := by intro y hy;
    rw [← h.zero_eq y hy]; rfl
  suffices H :
    HasFDerivWithinAt (fun y => continuousMultilinearCurryFin0 𝕜 E F (p y 0))
      (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) s x
  · exact H.congr A (A x hx)
  rw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff']
  have : ((0 : ℕ) : ℕ∞) < n := lt_of_lt_of_le (WithTop.coe_lt_coe.2 Nat.zero_lt_one) hn
  convert h.fderiv_within _ this x hx
  ext (y v)
  change (p x 1) (snoc 0 y) = (p x 1) (cons y v)
  unfold_coes
  congr with i
  rw [Unique.eq_default i]
  rfl
#align has_ftaylor_series_up_to_on.has_fderiv_within_at HasFtaylorSeriesUpToOn.hasFDerivWithinAt

theorem HasFtaylorSeriesUpToOn.differentiableOn (h : HasFtaylorSeriesUpToOn n f p s) (hn : 1 ≤ n) :
    DifferentiableOn 𝕜 f s := fun x hx => (h.HasFDerivWithinAt hn hx).DifferentiableWithinAt
#align has_ftaylor_series_up_to_on.differentiable_on HasFtaylorSeriesUpToOn.differentiableOn

/-- If a function has a Taylor series at order at least `1` on a neighborhood of `x`, then the term
of order `1` of this series is a derivative of `f` at `x`. -/
theorem HasFtaylorSeriesUpToOn.hasFDerivAt (h : HasFtaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
    (hx : s ∈ 𝓝 x) : HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) x :=
  (h.HasFDerivWithinAt hn (mem_of_mem_nhds hx)).HasFDerivAt hx
#align has_ftaylor_series_up_to_on.has_fderiv_at HasFtaylorSeriesUpToOn.hasFDerivAt

/-- If a function has a Taylor series at order at least `1` on a neighborhood of `x`, then
in a neighborhood of `x`, the term of order `1` of this series is a derivative of `f`. -/
theorem HasFtaylorSeriesUpToOn.eventually_hasFDerivAt (h : HasFtaylorSeriesUpToOn n f p s)
    (hn : 1 ≤ n) (hx : s ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p y 1)) y :=
  (eventually_eventually_nhds.2 hx).mono fun y hy => h.HasFDerivAt hn hy
#align has_ftaylor_series_up_to_on.eventually_has_fderiv_at HasFtaylorSeriesUpToOn.eventually_hasFDerivAt

/-- If a function has a Taylor series at order at least `1` on a neighborhood of `x`, then
it is differentiable at `x`. -/
theorem HasFtaylorSeriesUpToOn.differentiableAt (h : HasFtaylorSeriesUpToOn n f p s) (hn : 1 ≤ n)
    (hx : s ∈ 𝓝 x) : DifferentiableAt 𝕜 f x :=
  (h.HasFDerivAt hn hx).DifferentiableAt
#align has_ftaylor_series_up_to_on.differentiable_at HasFtaylorSeriesUpToOn.differentiableAt

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p` is a Taylor series up to `n`, and
`p (n + 1)` is a derivative of `p n`. -/
theorem hasFtaylorSeriesUpToOn_succ_iff_left {n : ℕ} :
    HasFtaylorSeriesUpToOn (n + 1) f p s ↔
      HasFtaylorSeriesUpToOn n f p s ∧
        (∀ x ∈ s, HasFDerivWithinAt (fun y => p y n) (p x n.succ).curryLeft s x) ∧
          ContinuousOn (fun x => p x (n + 1)) s :=
  by
  constructor
  · intro h
    exact
      ⟨h.of_le (WithTop.coe_le_coe.2 (Nat.le_succ n)),
        h.fderiv_within _ (WithTop.coe_lt_coe.2 (lt_add_one n)), h.cont (n + 1) le_rfl⟩
  · intro h
    constructor
    · exact h.1.zero_eq
    · intro m hm
      by_cases h' : m < n
      · exact h.1.fderivWithin m (WithTop.coe_lt_coe.2 h')
      · have : m = n := Nat.eq_of_lt_succ_of_not_lt (WithTop.coe_lt_coe.1 hm) h'
        rw [this]
        exact h.2.1
    · intro m hm
      by_cases h' : m ≤ n
      · apply h.1.cont m (WithTop.coe_le_coe.2 h')
      · have : m = n + 1 := le_antisymm (WithTop.coe_le_coe.1 hm) (not_le.1 h')
        rw [this]
        exact h.2.2
#align has_ftaylor_series_up_to_on_succ_iff_left hasFtaylorSeriesUpToOn_succ_iff_left

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. -/
theorem hasFtaylorSeriesUpToOn_succ_iff_right {n : ℕ} :
    HasFtaylorSeriesUpToOn (n + 1 : ℕ) f p s ↔
      (∀ x ∈ s, (p x 0).uncurry0 = f x) ∧
        (∀ x ∈ s, HasFDerivWithinAt (fun y => p y 0) (p x 1).curryLeft s x) ∧
          HasFtaylorSeriesUpToOn n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1))
            (fun x => (p x).shift) s :=
  by
  constructor
  · intro H
    refine' ⟨H.zero_eq, H.fderiv_within 0 (WithTop.coe_lt_coe.2 (Nat.succ_pos n)), _⟩
    constructor
    · intro x hx; rfl
    · intro m(hm : (m : ℕ∞) < n)x(hx : x ∈ s)
      have A : (m.succ : ℕ∞) < n.succ := by rw [WithTop.coe_lt_coe] at hm⊢;
        exact nat.lt_succ_iff.mpr hm
      change
        HasFDerivWithinAt
          ((continuousMultilinearCurryRightEquiv' 𝕜 m E F).symm ∘ fun y : E => p y m.succ)
          (p x m.succ.succ).curryRight.curryLeft s x
      rw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff']
      convert H.fderiv_within _ A x hx
      ext (y v)
      change
        (p x m.succ.succ) (snoc (cons y (init v)) (v (last _))) =
          (p x (Nat.succ (Nat.succ m))) (cons y v)
      rw [← cons_snoc_eq_snoc_cons, snoc_init_self]
    · intro m(hm : (m : ℕ∞) ≤ n)
      have A : (m.succ : ℕ∞) ≤ n.succ := by rw [WithTop.coe_le_coe] at hm⊢;
        exact nat.pred_le_iff.mp hm
      change
        ContinuousOn
          ((continuousMultilinearCurryRightEquiv' 𝕜 m E F).symm ∘ fun y : E => p y m.succ) s
      rw [LinearIsometryEquiv.comp_continuousOn_iff]
      exact H.cont _ A
  · rintro ⟨Hzero_eq, Hfderiv_zero, Htaylor⟩
    constructor
    · exact Hzero_eq
    · intro m(hm : (m : ℕ∞) < n.succ)x(hx : x ∈ s)
      cases m
      · exact Hfderiv_zero x hx
      · have A : (m : ℕ∞) < n := by rw [WithTop.coe_lt_coe] at hm⊢; exact Nat.lt_of_succ_lt_succ hm
        have :
          HasFDerivWithinAt
            ((continuousMultilinearCurryRightEquiv' 𝕜 m E F).symm ∘ fun y : E => p y m.succ)
            ((p x).shift m.succ).curryLeft s x :=
          Htaylor.fderiv_within _ A x hx
        rw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff'] at this
        convert this
        ext (y v)
        change
          (p x (Nat.succ (Nat.succ m))) (cons y v) =
            (p x m.succ.succ) (snoc (cons y (init v)) (v (last _)))
        rw [← cons_snoc_eq_snoc_cons, snoc_init_self]
    · intro m(hm : (m : ℕ∞) ≤ n.succ)
      cases m
      · have : DifferentiableOn 𝕜 (fun x => p x 0) s := fun x hx =>
          (Hfderiv_zero x hx).DifferentiableWithinAt
        exact this.continuous_on
      · have A : (m : ℕ∞) ≤ n := by rw [WithTop.coe_le_coe] at hm⊢; exact nat.lt_succ_iff.mp hm
        have :
          ContinuousOn
            ((continuousMultilinearCurryRightEquiv' 𝕜 m E F).symm ∘ fun y : E => p y m.succ) s :=
          Htaylor.cont _ A
        rwa [LinearIsometryEquiv.comp_continuousOn_iff] at this
#align has_ftaylor_series_up_to_on_succ_iff_right hasFtaylorSeriesUpToOn_succ_iff_right

/-! ### Smooth functions within a set around a point -/


variable (𝕜)

/-- A function is continuously differentiable up to order `n` within a set `s` at a point `x` if
it admits continuous derivatives up to order `n` in a neighborhood of `x` in `s ∪ {x}`.
For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).

For instance, a real function which is `C^m` on `(-1/m, 1/m)` for each natural `m`, but not
better, is `C^∞` at `0` within `univ`.
-/
def ContDiffWithinAt (n : ℕ∞) (f : E → F) (s : Set E) (x : E) : Prop :=
  ∀ m : ℕ,
    (m : ℕ∞) ≤ n →
      ∃ u ∈ 𝓝[insert x s] x, ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFtaylorSeriesUpToOn m f p u
#align cont_diff_within_at ContDiffWithinAt

variable {𝕜}

theorem contDiffWithinAt_nat {n : ℕ} :
    ContDiffWithinAt 𝕜 n f s x ↔
      ∃ u ∈ 𝓝[insert x s] x,
        ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFtaylorSeriesUpToOn n f p u :=
  ⟨fun H => H n le_rfl, fun ⟨u, hu, p, hp⟩ m hm => ⟨u, hu, p, hp.of_le hm⟩⟩
#align cont_diff_within_at_nat contDiffWithinAt_nat

theorem ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m ≤ n) :
    ContDiffWithinAt 𝕜 m f s x := fun k hk => h k (le_trans hk hmn)
#align cont_diff_within_at.of_le ContDiffWithinAt.of_le

theorem contDiffWithinAt_iff_forall_nat_le :
    ContDiffWithinAt 𝕜 n f s x ↔ ∀ m : ℕ, ↑m ≤ n → ContDiffWithinAt 𝕜 m f s x :=
  ⟨fun H m hm => H.of_le hm, fun H m hm => H m hm _ le_rfl⟩
#align cont_diff_within_at_iff_forall_nat_le contDiffWithinAt_iff_forall_nat_le

theorem contDiffWithinAt_top : ContDiffWithinAt 𝕜 ∞ f s x ↔ ∀ n : ℕ, ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_iff_forall_nat_le.trans <| by simp only [forall_prop_of_true, le_top]
#align cont_diff_within_at_top contDiffWithinAt_top

theorem ContDiffWithinAt.continuousWithinAt (h : ContDiffWithinAt 𝕜 n f s x) :
    ContinuousWithinAt f s x :=
  by
  rcases h 0 bot_le with ⟨u, hu, p, H⟩
  rw [mem_nhdsWithin_insert] at hu
  exact (H.continuous_on.continuous_within_at hu.1).mono_of_mem hu.2
#align cont_diff_within_at.continuous_within_at ContDiffWithinAt.continuousWithinAt

theorem ContDiffWithinAt.congr_of_eventuallyEq (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s x := fun m hm =>
  let ⟨u, hu, p, H⟩ := h m hm
  ⟨{ x ∈ u | f₁ x = f x }, Filter.inter_mem hu (mem_nhdsWithin_insert.2 ⟨hx, h₁⟩), p,
    (H.mono (sep_subset _ _)).congr fun _ => And.right⟩
#align cont_diff_within_at.congr_of_eventually_eq ContDiffWithinAt.congr_of_eventuallyEq

theorem ContDiffWithinAt.congr_of_eventuallyEq_insert (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventuallyEq (nhdsWithin_mono x (subset_insert x s) h₁)
    (mem_of_mem_nhdsWithin (mem_insert x s) h₁ : _)
#align cont_diff_within_at.congr_of_eventually_eq_insert ContDiffWithinAt.congr_of_eventuallyEq_insert

theorem ContDiffWithinAt.congr_of_eventually_eq' (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventuallyEq h₁ <| h₁.self_of_nhdsWithin hx
#align cont_diff_within_at.congr_of_eventually_eq' ContDiffWithinAt.congr_of_eventually_eq'

theorem Filter.EventuallyEq.contDiffWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H => ContDiffWithinAt.congr_of_eventuallyEq H h₁.symm hx.symm, fun H =>
    H.congr_of_eventuallyEq h₁ hx⟩
#align filter.eventually_eq.cont_diff_within_at_iff Filter.EventuallyEq.contDiffWithinAt_iff

theorem ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y)
    (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem self_mem_nhdsWithin h₁) hx
#align cont_diff_within_at.congr ContDiffWithinAt.congr

theorem ContDiffWithinAt.congr' (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y)
    (hx : x ∈ s) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr h₁ (h₁ _ hx)
#align cont_diff_within_at.congr' ContDiffWithinAt.congr'

theorem ContDiffWithinAt.mono_of_mem (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E}
    (hst : s ∈ 𝓝[t] x) : ContDiffWithinAt 𝕜 n f t x :=
  by
  intro m hm
  rcases h m hm with ⟨u, hu, p, H⟩
  exact ⟨u, nhdsWithin_le_of_mem (insert_mem_nhdsWithin_insert hst) hu, p, H⟩
#align cont_diff_within_at.mono_of_mem ContDiffWithinAt.mono_of_mem

theorem ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : t ⊆ s) :
    ContDiffWithinAt 𝕜 n f t x :=
  h.mono_of_mem <| Filter.mem_of_superset self_mem_nhdsWithin hst
#align cont_diff_within_at.mono ContDiffWithinAt.mono

theorem ContDiffWithinAt.congr_nhds (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E}
    (hst : 𝓝[s] x = 𝓝[t] x) : ContDiffWithinAt 𝕜 n f t x :=
  h.mono_of_mem <| hst ▸ self_mem_nhdsWithin
#align cont_diff_within_at.congr_nhds ContDiffWithinAt.congr_nhds

theorem contDiffWithinAt_congr_nhds {t : Set E} (hst : 𝓝[s] x = 𝓝[t] x) :
    ContDiffWithinAt 𝕜 n f s x ↔ ContDiffWithinAt 𝕜 n f t x :=
  ⟨fun h => h.congr_nhds hst, fun h => h.congr_nhds hst.symm⟩
#align cont_diff_within_at_congr_nhds contDiffWithinAt_congr_nhds

theorem contDiffWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    ContDiffWithinAt 𝕜 n f (s ∩ t) x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_congr_nhds <| Eq.symm <| nhdsWithin_restrict'' _ h
#align cont_diff_within_at_inter' contDiffWithinAt_inter'

theorem contDiffWithinAt_inter (h : t ∈ 𝓝 x) :
    ContDiffWithinAt 𝕜 n f (s ∩ t) x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_inter' (mem_nhdsWithin_of_mem_nhds h)
#align cont_diff_within_at_inter contDiffWithinAt_inter

theorem contDiffWithinAt_insert {y : E} :
    ContDiffWithinAt 𝕜 n f (insert y s) x ↔ ContDiffWithinAt 𝕜 n f s x :=
  by
  simp_rw [ContDiffWithinAt]
  rcases eq_or_ne x y with (rfl | h)
  · simp_rw [insert_eq_of_mem (mem_insert _ _)]
  simp_rw [insert_comm x y, nhdsWithin_insert_of_ne h]
#align cont_diff_within_at_insert contDiffWithinAt_insert

alias contDiffWithinAt_insert ↔ ContDiffWithinAt.of_insert ContDiffWithinAt.insert'
#align cont_diff_within_at.of_insert ContDiffWithinAt.of_insert
#align cont_diff_within_at.insert' ContDiffWithinAt.insert'

theorem ContDiffWithinAt.insert (h : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n f (insert x s) x :=
  h.insert'
#align cont_diff_within_at.insert ContDiffWithinAt.insert

/-- If a function is `C^n` within a set at a point, with `n ≥ 1`, then it is differentiable
within this set at this point. -/
theorem ContDiffWithinAt.differentiable_within_at' (h : ContDiffWithinAt 𝕜 n f s x) (hn : 1 ≤ n) :
    DifferentiableWithinAt 𝕜 f (insert x s) x :=
  by
  rcases h 1 hn with ⟨u, hu, p, H⟩
  rcases mem_nhdsWithin.1 hu with ⟨t, t_open, xt, tu⟩
  rw [inter_comm] at tu
  have := ((H.mono tu).DifferentiableOn le_rfl) x ⟨mem_insert x s, xt⟩
  exact (differentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1 this
#align cont_diff_within_at.differentiable_within_at' ContDiffWithinAt.differentiable_within_at'

theorem ContDiffWithinAt.differentiableWithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : 1 ≤ n) :
    DifferentiableWithinAt 𝕜 f s x :=
  (h.differentiable_within_at' hn).mono (subset_insert x s)
#align cont_diff_within_at.differentiable_within_at ContDiffWithinAt.differentiableWithinAt

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem contDiffWithinAt_succ_iff_hasFDerivWithinAt {n : ℕ} :
    ContDiffWithinAt 𝕜 (n + 1 : ℕ) f s x ↔
      ∃ u ∈ 𝓝[insert x s] x,
        ∃ f' : E → E →L[𝕜] F,
          (∀ x ∈ u, HasFDerivWithinAt f (f' x) u x) ∧ ContDiffWithinAt 𝕜 n f' u x :=
  by
  constructor
  · intro h
    rcases h n.succ le_rfl with ⟨u, hu, p, Hp⟩
    refine'
      ⟨u, hu, fun y => (continuousMultilinearCurryFin1 𝕜 E F) (p y 1), fun y hy =>
        Hp.has_fderiv_within_at (WithTop.coe_le_coe.2 (Nat.le_add_left 1 n)) hy, _⟩
    intro m hm
    refine' ⟨u, _, fun y : E => (p y).shift, _⟩
    · convert self_mem_nhdsWithin
      have : x ∈ insert x s := by simp
      exact insert_eq_of_mem (mem_of_mem_nhdsWithin this hu)
    · rw [hasFtaylorSeriesUpToOn_succ_iff_right] at Hp
      exact Hp.2.2.of_le hm
  · rintro ⟨u, hu, f', f'_eq_deriv, Hf'⟩
    rw [contDiffWithinAt_nat]
    rcases Hf' n le_rfl with ⟨v, hv, p', Hp'⟩
    refine' ⟨v ∩ u, _, fun x => (p' x).unshift (f x), _⟩
    · apply Filter.inter_mem _ hu
      apply nhdsWithin_le_of_mem hu
      exact nhdsWithin_mono _ (subset_insert x u) hv
    · rw [hasFtaylorSeriesUpToOn_succ_iff_right]
      refine' ⟨fun y hy => rfl, fun y hy => _, _⟩
      · change
          HasFDerivWithinAt (fun z => (continuousMultilinearCurryFin0 𝕜 E F).symm (f z))
            (FormalMultilinearSeries.unshift (p' y) (f y) 1).curryLeft (v ∩ u) y
        rw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff']
        convert(f'_eq_deriv y hy.2).mono (inter_subset_right v u)
        rw [← Hp'.zero_eq y hy.1]
        ext z
        change
          ((p' y 0) (init (@cons 0 (fun i => E) z 0))) (@cons 0 (fun i => E) z 0 (last 0)) =
            ((p' y 0) 0) z
        unfold_coes
        congr
        decide
      · convert(Hp'.mono (inter_subset_left v u)).congr fun x hx => Hp'.zero_eq x hx.1
        · ext (x y)
          change p' x 0 (init (@snoc 0 (fun i : Fin 1 => E) 0 y)) y = p' x 0 0 y
          rw [init_snoc]
        · ext (x k v y)
          change
            p' x k (init (@snoc k (fun i : Fin k.succ => E) v y))
                (@snoc k (fun i : Fin k.succ => E) v y (last k)) =
              p' x k v y
          rw [snoc_last, init_snoc]
#align cont_diff_within_at_succ_iff_has_fderiv_within_at contDiffWithinAt_succ_iff_hasFDerivWithinAt

/-- A version of `cont_diff_within_at_succ_iff_has_fderiv_within_at` where all derivatives
  are taken within the same set. -/
theorem contDiffWithinAt_succ_iff_has_fderiv_within_at' {n : ℕ} :
    ContDiffWithinAt 𝕜 (n + 1 : ℕ) f s x ↔
      ∃ u ∈ 𝓝[insert x s] x,
        u ⊆ insert x s ∧
          ∃ f' : E → E →L[𝕜] F,
            (∀ x ∈ u, HasFDerivWithinAt f (f' x) s x) ∧ ContDiffWithinAt 𝕜 n f' s x :=
  by
  refine' ⟨fun hf => _, _⟩
  · obtain ⟨u, hu, f', huf', hf'⟩ := cont_diff_within_at_succ_iff_has_fderiv_within_at.mp hf
    obtain ⟨w, hw, hxw, hwu⟩ := mem_nhds_within.mp hu
    rw [inter_comm] at hwu
    refine'
      ⟨insert x s ∩ w, inter_mem_nhdsWithin _ (hw.mem_nhds hxw), inter_subset_left _ _, f',
        fun y hy => _, _⟩
    · refine' ((huf' y <| hwu hy).mono hwu).mono_of_mem _
      refine' mem_of_superset _ (inter_subset_inter_left _ (subset_insert _ _))
      refine' inter_mem_nhdsWithin _ (hw.mem_nhds hy.2)
    · exact hf'.mono_of_mem (nhdsWithin_mono _ (subset_insert _ _) hu)
  · rw [← contDiffWithinAt_insert, contDiffWithinAt_succ_iff_hasFDerivWithinAt,
      insert_eq_of_mem (mem_insert _ _)]
    rintro ⟨u, hu, hus, f', huf', hf'⟩
    refine' ⟨u, hu, f', fun y hy => (huf' y hy).insert'.mono hus, hf'.insert.mono hus⟩
#align cont_diff_within_at_succ_iff_has_fderiv_within_at' contDiffWithinAt_succ_iff_has_fderiv_within_at'

/-! ### Smooth functions within a set -/


variable (𝕜)

/-- A function is continuously differentiable up to `n` on `s` if, for any point `x` in `s`, it
admits continuous derivatives up to order `n` on a neighborhood of `x` in `s`.

For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).
-/
def ContDiffOn (n : ℕ∞) (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, ContDiffWithinAt 𝕜 n f s x
#align cont_diff_on ContDiffOn

variable {𝕜}

theorem HasFtaylorSeriesUpToOn.contDiffOn {f' : E → FormalMultilinearSeries 𝕜 E F}
    (hf : HasFtaylorSeriesUpToOn n f f' s) : ContDiffOn 𝕜 n f s :=
  by
  intro x hx m hm
  use s
  simp only [Set.insert_eq_of_mem hx, self_mem_nhdsWithin, true_and_iff]
  exact ⟨f', hf.of_le hm⟩
#align has_ftaylor_series_up_to_on.cont_diff_on HasFtaylorSeriesUpToOn.contDiffOn

theorem ContDiffOn.contDiffWithinAt (h : ContDiffOn 𝕜 n f s) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 n f s x :=
  h x hx
#align cont_diff_on.cont_diff_within_at ContDiffOn.contDiffWithinAt

theorem ContDiffWithinAt.cont_diff_on' {m : ℕ} (hm : (m : ℕ∞) ≤ n)
    (h : ContDiffWithinAt 𝕜 n f s x) : ∃ u, IsOpen u ∧ x ∈ u ∧ ContDiffOn 𝕜 m f (insert x s ∩ u) :=
  by
  rcases h m hm with ⟨t, ht, p, hp⟩
  rcases mem_nhdsWithin.1 ht with ⟨u, huo, hxu, hut⟩
  rw [inter_comm] at hut
  exact ⟨u, huo, hxu, (hp.mono hut).ContDiffOn⟩
#align cont_diff_within_at.cont_diff_on' ContDiffWithinAt.cont_diff_on'

theorem ContDiffWithinAt.contDiffOn {m : ℕ} (hm : (m : ℕ∞) ≤ n) (h : ContDiffWithinAt 𝕜 n f s x) :
    ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ ContDiffOn 𝕜 m f u :=
  let ⟨u, uo, xu, h⟩ := h.cont_diff_on' hm
  ⟨_, inter_mem_nhdsWithin _ (uo.mem_nhds xu), inter_subset_left _ _, h⟩
#align cont_diff_within_at.cont_diff_on ContDiffWithinAt.contDiffOn

protected theorem ContDiffWithinAt.eventually {n : ℕ} (h : ContDiffWithinAt 𝕜 n f s x) :
    ∀ᶠ y in 𝓝[insert x s] x, ContDiffWithinAt 𝕜 n f s y :=
  by
  rcases h.cont_diff_on le_rfl with ⟨u, hu, hu_sub, hd⟩
  have : ∀ᶠ y : E in 𝓝[insert x s] x, u ∈ 𝓝[insert x s] y ∧ y ∈ u :=
    (eventually_nhdsWithin_nhdsWithin.2 hu).And hu
  refine' this.mono fun y hy => (hd y hy.2).mono_of_mem _
  exact nhdsWithin_mono y (subset_insert _ _) hy.1
#align cont_diff_within_at.eventually ContDiffWithinAt.eventually

theorem ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m ≤ n) : ContDiffOn 𝕜 m f s := fun x hx =>
  (h x hx).of_le hmn
#align cont_diff_on.of_le ContDiffOn.of_le

theorem ContDiffOn.of_succ {n : ℕ} (h : ContDiffOn 𝕜 (n + 1) f s) : ContDiffOn 𝕜 n f s :=
  h.of_le <| WithTop.coe_le_coe.mpr le_self_add
#align cont_diff_on.of_succ ContDiffOn.of_succ

theorem ContDiffOn.one_of_succ {n : ℕ} (h : ContDiffOn 𝕜 (n + 1) f s) : ContDiffOn 𝕜 1 f s :=
  h.of_le <| WithTop.coe_le_coe.mpr le_add_self
#align cont_diff_on.one_of_succ ContDiffOn.one_of_succ

theorem contDiffOn_iff_forall_nat_le : ContDiffOn 𝕜 n f s ↔ ∀ m : ℕ, ↑m ≤ n → ContDiffOn 𝕜 m f s :=
  ⟨fun H m hm => H.of_le hm, fun H x hx m hm => H m hm x hx m le_rfl⟩
#align cont_diff_on_iff_forall_nat_le contDiffOn_iff_forall_nat_le

theorem contDiffOn_top : ContDiffOn 𝕜 ∞ f s ↔ ∀ n : ℕ, ContDiffOn 𝕜 n f s :=
  contDiffOn_iff_forall_nat_le.trans <| by simp only [le_top, forall_prop_of_true]
#align cont_diff_on_top contDiffOn_top

theorem contDiffOn_all_iff_nat : (∀ n, ContDiffOn 𝕜 n f s) ↔ ∀ n : ℕ, ContDiffOn 𝕜 n f s :=
  by
  refine' ⟨fun H n => H n, _⟩
  rintro H (_ | n)
  exacts[contDiffOn_top.2 H, H n]
#align cont_diff_on_all_iff_nat contDiffOn_all_iff_nat

theorem ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s) : ContinuousOn f s := fun x hx =>
  (h x hx).ContinuousWithinAt
#align cont_diff_on.continuous_on ContDiffOn.continuousOn

theorem ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : ∀ x ∈ s, f₁ x = f x) :
    ContDiffOn 𝕜 n f₁ s := fun x hx => (h x hx).congr h₁ (h₁ x hx)
#align cont_diff_on.congr ContDiffOn.congr

theorem contDiffOn_congr (h₁ : ∀ x ∈ s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s ↔ ContDiffOn 𝕜 n f s :=
  ⟨fun H => H.congr fun x hx => (h₁ x hx).symm, fun H => H.congr h₁⟩
#align cont_diff_on_congr contDiffOn_congr

theorem ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (hst : t ⊆ s) : ContDiffOn 𝕜 n f t :=
  fun x hx => (h x (hst hx)).mono hst
#align cont_diff_on.mono ContDiffOn.mono

theorem ContDiffOn.congr_mono (hf : ContDiffOn 𝕜 n f s) (h₁ : ∀ x ∈ s₁, f₁ x = f x) (hs : s₁ ⊆ s) :
    ContDiffOn 𝕜 n f₁ s₁ :=
  (hf.mono hs).congr h₁
#align cont_diff_on.congr_mono ContDiffOn.congr_mono

/-- If a function is `C^n` on a set with `n ≥ 1`, then it is differentiable there. -/
theorem ContDiffOn.differentiableOn (h : ContDiffOn 𝕜 n f s) (hn : 1 ≤ n) :
    DifferentiableOn 𝕜 f s := fun x hx => (h x hx).DifferentiableWithinAt hn
#align cont_diff_on.differentiable_on ContDiffOn.differentiableOn

/-- If a function is `C^n` around each point in a set, then it is `C^n` on the set. -/
theorem contDiffOn_of_locally_contDiffOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ ContDiffOn 𝕜 n f (s ∩ u)) : ContDiffOn 𝕜 n f s :=
  by
  intro x xs
  rcases h x xs with ⟨u, u_open, xu, hu⟩
  apply (contDiffWithinAt_inter _).1 (hu x ⟨xs, xu⟩)
  exact IsOpen.mem_nhds u_open xu
#align cont_diff_on_of_locally_cont_diff_on contDiffOn_of_locally_contDiffOn

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem contDiffOn_succ_iff_hasFDerivWithinAt {n : ℕ} :
    ContDiffOn 𝕜 (n + 1 : ℕ) f s ↔
      ∀ x ∈ s,
        ∃ u ∈ 𝓝[insert x s] x,
          ∃ f' : E → E →L[𝕜] F, (∀ x ∈ u, HasFDerivWithinAt f (f' x) u x) ∧ ContDiffOn 𝕜 n f' u :=
  by
  constructor
  · intro h x hx
    rcases(h x hx) n.succ le_rfl with ⟨u, hu, p, Hp⟩
    refine'
      ⟨u, hu, fun y => (continuousMultilinearCurryFin1 𝕜 E F) (p y 1), fun y hy =>
        Hp.has_fderiv_within_at (WithTop.coe_le_coe.2 (Nat.le_add_left 1 n)) hy, _⟩
    rw [hasFtaylorSeriesUpToOn_succ_iff_right] at Hp
    intro z hz m hm
    refine' ⟨u, _, fun x : E => (p x).shift, Hp.2.2.of_le hm⟩
    convert self_mem_nhdsWithin
    exact insert_eq_of_mem hz
  · intro h x hx
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt]
    rcases h x hx with ⟨u, u_nhbd, f', hu, hf'⟩
    have : x ∈ u := mem_of_mem_nhdsWithin (mem_insert _ _) u_nhbd
    exact ⟨u, u_nhbd, f', hu, hf' x this⟩
#align cont_diff_on_succ_iff_has_fderiv_within_at contDiffOn_succ_iff_hasFDerivWithinAt

/-! ### Iterated derivative within a set -/


variable (𝕜)

/-- The `n`-th derivative of a function along a set, defined inductively by saying that the `n+1`-th
derivative of `f` is the derivative of the `n`-th derivative of `f` along this set, together with
an uncurrying step to see it as a multilinear map in `n+1` variables..
-/
noncomputable def iteratedFderivWithin (n : ℕ) (f : E → F) (s : Set E) : E → E[×n]→L[𝕜] F :=
  Nat.recOn n (fun x => ContinuousMultilinearMap.curry0 𝕜 E (f x)) fun n rec x =>
    ContinuousLinearMap.uncurryLeft (fderivWithin 𝕜 rec s x)
#align iterated_fderiv_within iteratedFderivWithin

/-- Formal Taylor series associated to a function within a set. -/
def ftaylorSeriesWithin (f : E → F) (s : Set E) (x : E) : FormalMultilinearSeries 𝕜 E F := fun n =>
  iteratedFderivWithin 𝕜 n f s x
#align ftaylor_series_within ftaylorSeriesWithin

variable {𝕜}

@[simp]
theorem iteratedFderivWithin_zero_apply (m : Fin 0 → E) :
    (iteratedFderivWithin 𝕜 0 f s x : (Fin 0 → E) → F) m = f x :=
  rfl
#align iterated_fderiv_within_zero_apply iteratedFderivWithin_zero_apply

theorem iteratedFderivWithin_zero_eq_comp :
    iteratedFderivWithin 𝕜 0 f s = (continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f :=
  rfl
#align iterated_fderiv_within_zero_eq_comp iteratedFderivWithin_zero_eq_comp

@[simp]
theorem norm_iteratedFderivWithin_zero : ‖iteratedFderivWithin 𝕜 0 f s x‖ = ‖f x‖ := by
  rw [iteratedFderivWithin_zero_eq_comp, LinearIsometryEquiv.norm_map]
#align norm_iterated_fderiv_within_zero norm_iteratedFderivWithin_zero

theorem iteratedFderivWithin_succ_apply_left {n : ℕ} (m : Fin (n + 1) → E) :
    (iteratedFderivWithin 𝕜 (n + 1) f s x : (Fin (n + 1) → E) → F) m =
      (fderivWithin 𝕜 (iteratedFderivWithin 𝕜 n f s) s x : E → E[×n]→L[𝕜] F) (m 0) (tail m) :=
  rfl
#align iterated_fderiv_within_succ_apply_left iteratedFderivWithin_succ_apply_left

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
theorem iteratedFderivWithin_succ_eq_comp_left {n : ℕ} :
    iteratedFderivWithin 𝕜 (n + 1) f s =
      continuousMultilinearCurryLeftEquiv 𝕜 (fun i : Fin (n + 1) => E) F ∘
        fderivWithin 𝕜 (iteratedFderivWithin 𝕜 n f s) s :=
  rfl
#align iterated_fderiv_within_succ_eq_comp_left iteratedFderivWithin_succ_eq_comp_left

theorem norm_fderivWithin_iteratedFderivWithin {n : ℕ} :
    ‖fderivWithin 𝕜 (iteratedFderivWithin 𝕜 n f s) s x‖ = ‖iteratedFderivWithin 𝕜 (n + 1) f s x‖ :=
  by rw [iteratedFderivWithin_succ_eq_comp_left, LinearIsometryEquiv.norm_map]
#align norm_fderiv_within_iterated_fderiv_within norm_fderivWithin_iteratedFderivWithin

theorem iteratedFderivWithin_succ_apply_right {n : ℕ} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s)
    (m : Fin (n + 1) → E) :
    (iteratedFderivWithin 𝕜 (n + 1) f s x : (Fin (n + 1) → E) → F) m =
      iteratedFderivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s x (init m) (m (last n)) :=
  by
  induction' n with n IH generalizing x
  · rw [iteratedFderivWithin_succ_eq_comp_left, iteratedFderivWithin_zero_eq_comp,
      iteratedFderivWithin_zero_apply, Function.comp_apply,
      LinearIsometryEquiv.comp_fderivWithin _ (hs x hx)]
    rfl
  · let I := continuousMultilinearCurryRightEquiv' 𝕜 n E F
    have A :
      ∀ y ∈ s,
        iteratedFderivWithin 𝕜 n.succ f s y =
          (I ∘ iteratedFderivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) y :=
      by intro y hy; ext m; rw [@IH m y hy]; rfl
    calc
      (iteratedFderivWithin 𝕜 (n + 2) f s x : (Fin (n + 2) → E) → F) m =
          (fderivWithin 𝕜 (iteratedFderivWithin 𝕜 n.succ f s) s x : E → E[×n + 1]→L[𝕜] F) (m 0)
            (tail m) :=
        rfl
      _ =
          (fderivWithin 𝕜 (I ∘ iteratedFderivWithin 𝕜 n (fderivWithin 𝕜 f s) s) s x :
              E → E[×n + 1]→L[𝕜] F)
            (m 0) (tail m) :=
        by rw [fderivWithin_congr A (A x hx)]
      _ =
          (I ∘ fderivWithin 𝕜 (iteratedFderivWithin 𝕜 n (fderivWithin 𝕜 f s) s) s x :
              E → E[×n + 1]→L[𝕜] F)
            (m 0) (tail m) :=
        by rw [LinearIsometryEquiv.comp_fderivWithin _ (hs x hx)]; rfl
      _ =
          (fderivWithin 𝕜 (iteratedFderivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) s x :
              E → E[×n]→L[𝕜] E →L[𝕜] F)
            (m 0) (init (tail m)) ((tail m) (last n)) :=
        rfl
      _ =
          iteratedFderivWithin 𝕜 (Nat.succ n) (fun y => fderivWithin 𝕜 f s y) s x (init m)
            (m (last (n + 1))) :=
        by rw [iteratedFderivWithin_succ_apply_left, tail_init_eq_init_tail]; rfl
      
#align iterated_fderiv_within_succ_apply_right iteratedFderivWithin_succ_apply_right

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the `n`-th derivative of the derivative. -/
theorem iteratedFderivWithin_succ_eq_comp_right {n : ℕ} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    iteratedFderivWithin 𝕜 (n + 1) f s x =
      (continuousMultilinearCurryRightEquiv' 𝕜 n E F ∘
          iteratedFderivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s)
        x :=
  by ext m; rw [iteratedFderivWithin_succ_apply_right hs hx]; rfl
#align iterated_fderiv_within_succ_eq_comp_right iteratedFderivWithin_succ_eq_comp_right

theorem norm_iteratedFderivWithin_fderivWithin {n : ℕ} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    ‖iteratedFderivWithin 𝕜 n (fderivWithin 𝕜 f s) s x‖ = ‖iteratedFderivWithin 𝕜 (n + 1) f s x‖ :=
  by rw [iteratedFderivWithin_succ_eq_comp_right hs hx, LinearIsometryEquiv.norm_map]
#align norm_iterated_fderiv_within_fderiv_within norm_iteratedFderivWithin_fderivWithin

@[simp]
theorem iteratedFderivWithin_one_apply (h : UniqueDiffWithinAt 𝕜 s x) (m : Fin 1 → E) :
    (iteratedFderivWithin 𝕜 1 f s x : (Fin 1 → E) → F) m = (fderivWithin 𝕜 f s x : E → F) (m 0) :=
  by
  simp only [iteratedFderivWithin_succ_apply_left, iteratedFderivWithin_zero_eq_comp,
    (continuousMultilinearCurryFin0 𝕜 E F).symm.comp_fderivWithin h]
  rfl
#align iterated_fderiv_within_one_apply iteratedFderivWithin_one_apply

theorem Filter.EventuallyEq.iterated_fderiv_within' (h : f₁ =ᶠ[𝓝[s] x] f) (ht : t ⊆ s) (n : ℕ) :
    iteratedFderivWithin 𝕜 n f₁ t =ᶠ[𝓝[s] x] iteratedFderivWithin 𝕜 n f t :=
  by
  induction' n with n ihn
  · exact h.mono fun y hy => FunLike.ext _ _ fun _ => hy
  · have : fderivWithin 𝕜 _ t =ᶠ[𝓝[s] x] fderivWithin 𝕜 _ t := ihn.fderiv_within' ht
    apply this.mono
    intro y hy
    simp only [iteratedFderivWithin_succ_eq_comp_left, hy, (· ∘ ·)]
#align filter.eventually_eq.iterated_fderiv_within' Filter.EventuallyEq.iterated_fderiv_within'

protected theorem Filter.EventuallyEq.iteratedFderivWithin (h : f₁ =ᶠ[𝓝[s] x] f) (n : ℕ) :
    iteratedFderivWithin 𝕜 n f₁ s =ᶠ[𝓝[s] x] iteratedFderivWithin 𝕜 n f s :=
  h.iterated_fderiv_within' Subset.rfl n
#align filter.eventually_eq.iterated_fderiv_within Filter.EventuallyEq.iteratedFderivWithin

/-- If two functions coincide in a neighborhood of `x` within a set `s` and at `x`, then their
iterated differentials within this set at `x` coincide. -/
theorem Filter.EventuallyEq.iteratedFderivWithin_eq (h : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
    (n : ℕ) : iteratedFderivWithin 𝕜 n f₁ s x = iteratedFderivWithin 𝕜 n f s x :=
  have : f₁ =ᶠ[𝓝[insert x s] x] f := by simpa [eventually_eq, hx]
  (this.iterated_fderiv_within' (subset_insert _ _) n).self_of_nhdsWithin (mem_insert _ _)
#align filter.eventually_eq.iterated_fderiv_within_eq Filter.EventuallyEq.iteratedFderivWithin_eq

/-- If two functions coincide on a set `s`, then their iterated differentials within this set
coincide. See also `filter.eventually_eq.iterated_fderiv_within_eq` and
`filter.eventually_eq.iterated_fderiv_within`. -/
theorem iteratedFderivWithin_congr (hs : EqOn f₁ f s) (hx : x ∈ s) (n : ℕ) :
    iteratedFderivWithin 𝕜 n f₁ s x = iteratedFderivWithin 𝕜 n f s x :=
  (hs.EventuallyEq.filter_mono inf_le_right).iteratedFderivWithin_eq (hs hx) _
#align iterated_fderiv_within_congr iteratedFderivWithin_congr

/-- If two functions coincide on a set `s`, then their iterated differentials within this set
coincide. See also `filter.eventually_eq.iterated_fderiv_within_eq` and
`filter.eventually_eq.iterated_fderiv_within`. -/
protected theorem Set.EqOn.iteratedFderivWithin (hs : EqOn f₁ f s) (n : ℕ) :
    EqOn (iteratedFderivWithin 𝕜 n f₁ s) (iteratedFderivWithin 𝕜 n f s) s := fun x hx =>
  iteratedFderivWithin_congr hs hx n
#align set.eq_on.iterated_fderiv_within Set.EqOn.iteratedFderivWithin

theorem iteratedFderivWithin_eventually_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) (n : ℕ) :
    iteratedFderivWithin 𝕜 n f s =ᶠ[𝓝 x] iteratedFderivWithin 𝕜 n f t :=
  by
  induction' n with n ihn generalizing x
  · rfl
  · refine' (eventually_nhds_nhdsWithin.2 h).mono fun y hy => _
    simp only [iteratedFderivWithin_succ_eq_comp_left, (· ∘ ·)]
    rw [(ihn hy).fderivWithin_eq_nhds, fderivWithin_congr_set' _ hy]
#align iterated_fderiv_within_eventually_congr_set' iteratedFderivWithin_eventually_congr_set'

theorem iteratedFderivWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) (n : ℕ) :
    iteratedFderivWithin 𝕜 n f s =ᶠ[𝓝 x] iteratedFderivWithin 𝕜 n f t :=
  iteratedFderivWithin_eventually_congr_set' x (h.filter_mono inf_le_left) n
#align iterated_fderiv_within_eventually_congr_set iteratedFderivWithin_eventually_congr_set

theorem iteratedFderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) (n : ℕ) :
    iteratedFderivWithin 𝕜 n f s x = iteratedFderivWithin 𝕜 n f t x :=
  (iteratedFderivWithin_eventually_congr_set h n).self_of_nhds
#align iterated_fderiv_within_congr_set iteratedFderivWithin_congr_set

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x` within `s`. -/
theorem iteratedFderivWithin_inter' {n : ℕ} (hu : u ∈ 𝓝[s] x) :
    iteratedFderivWithin 𝕜 n f (s ∩ u) x = iteratedFderivWithin 𝕜 n f s x :=
  iteratedFderivWithin_congr_set (nhdsWithin_eq_iff_eventuallyEq.1 <| nhdsWithin_inter_of_mem' hu) _
#align iterated_fderiv_within_inter' iteratedFderivWithin_inter'

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x`. -/
theorem iteratedFderivWithin_inter {n : ℕ} (hu : u ∈ 𝓝 x) :
    iteratedFderivWithin 𝕜 n f (s ∩ u) x = iteratedFderivWithin 𝕜 n f s x :=
  iteratedFderivWithin_inter' (mem_nhdsWithin_of_mem_nhds hu)
#align iterated_fderiv_within_inter iteratedFderivWithin_inter

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with an open set containing `x`. -/
theorem iteratedFderivWithin_inter_open {n : ℕ} (hu : IsOpen u) (hx : x ∈ u) :
    iteratedFderivWithin 𝕜 n f (s ∩ u) x = iteratedFderivWithin 𝕜 n f s x :=
  iteratedFderivWithin_inter (hu.mem_nhds hx)
#align iterated_fderiv_within_inter_open iteratedFderivWithin_inter_open

@[simp]
theorem contDiffOn_zero : ContDiffOn 𝕜 0 f s ↔ ContinuousOn f s :=
  by
  refine' ⟨fun H => H.ContinuousOn, fun H => _⟩
  intro x hx m hm
  have : (m : ℕ∞) = 0 := le_antisymm hm bot_le
  rw [this]
  refine' ⟨insert x s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, _⟩
  rw [hasFtaylorSeriesUpToOn_zero_iff]
  exact ⟨by rwa [insert_eq_of_mem hx], fun x hx => by simp [ftaylorSeriesWithin]⟩
#align cont_diff_on_zero contDiffOn_zero

theorem contDiffWithinAt_zero (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 0 f s x ↔ ∃ u ∈ 𝓝[s] x, ContinuousOn f (s ∩ u) :=
  by
  constructor
  · intro h
    obtain ⟨u, H, p, hp⟩ := h 0 (by norm_num)
    refine' ⟨u, _, _⟩
    · simpa [hx] using H
    · simp only [WithTop.coe_zero, hasFtaylorSeriesUpToOn_zero_iff] at hp
      exact hp.1.mono (inter_subset_right s u)
  · rintro ⟨u, H, hu⟩
    rw [← contDiffWithinAt_inter' H]
    have h' : x ∈ s ∩ u := ⟨hx, mem_of_mem_nhdsWithin hx H⟩
    exact (cont_diff_on_zero.mpr hu).ContDiffWithinAt h'
#align cont_diff_within_at_zero contDiffWithinAt_zero

/-- On a set with unique differentiability, any choice of iterated differential has to coincide
with the one we have chosen in `iterated_fderiv_within 𝕜 m f s`. -/
theorem HasFtaylorSeriesUpToOn.eq_ftaylor_series_of_uniqueDiffOn
    (h : HasFtaylorSeriesUpToOn n f p s) {m : ℕ} (hmn : (m : ℕ∞) ≤ n) (hs : UniqueDiffOn 𝕜 s)
    (hx : x ∈ s) : p x m = iteratedFderivWithin 𝕜 m f s x :=
  by
  induction' m with m IH generalizing x
  · rw [h.zero_eq' hx, iteratedFderivWithin_zero_eq_comp]
  · have A : (m : ℕ∞) < n := lt_of_lt_of_le (WithTop.coe_lt_coe.2 (lt_add_one m)) hmn
    have :
      HasFDerivWithinAt (fun y : E => iteratedFderivWithin 𝕜 m f s y)
        (ContinuousMultilinearMap.curryLeft (p x (Nat.succ m))) s x :=
      (h.fderiv_within m A x hx).congr (fun y hy => (IH (le_of_lt A) hy).symm)
        (IH (le_of_lt A) hx).symm
    rw [iteratedFderivWithin_succ_eq_comp_left, Function.comp_apply, this.fderiv_within (hs x hx)]
    exact (ContinuousMultilinearMap.uncurry_curryLeft _).symm
#align has_ftaylor_series_up_to_on.eq_ftaylor_series_of_unique_diff_on HasFtaylorSeriesUpToOn.eq_ftaylor_series_of_uniqueDiffOn

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylor_series_within 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem ContDiffOn.ftaylorSeriesWithin (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) :
    HasFtaylorSeriesUpToOn n f (ftaylorSeriesWithin 𝕜 f s) s :=
  by
  constructor
  · intro x hx
    simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.uncurry0_apply,
      iteratedFderivWithin_zero_apply]
  · intro m hm x hx
    rcases(h x hx) m.succ (ENat.add_one_le_of_lt hm) with ⟨u, hu, p, Hp⟩
    rw [insert_eq_of_mem hx] at hu
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [inter_comm] at ho
    have : p x m.succ = ftaylorSeriesWithin 𝕜 f s x m.succ :=
      by
      change p x m.succ = iteratedFderivWithin 𝕜 m.succ f s x
      rw [← iteratedFderivWithin_inter_open o_open xo]
      exact (Hp.mono ho).eq_ftaylor_series_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hx, xo⟩
    rw [← this, ← hasFDerivWithinAt_inter (IsOpen.mem_nhds o_open xo)]
    have A : ∀ y ∈ s ∩ o, p y m = ftaylorSeriesWithin 𝕜 f s y m :=
      by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFderivWithin 𝕜 m f s y
      rw [← iteratedFderivWithin_inter_open o_open yo]
      exact
        (Hp.mono ho).eq_ftaylor_series_of_uniqueDiffOn (WithTop.coe_le_coe.2 (Nat.le_succ m))
          (hs.inter o_open) ⟨hy, yo⟩
    exact
      ((Hp.mono ho).fderivWithin m (WithTop.coe_lt_coe.2 (lt_add_one m)) x ⟨hx, xo⟩).congr
        (fun y hy => (A y hy).symm) (A x ⟨hx, xo⟩).symm
  · intro m hm
    apply continuousOn_of_locally_continuousOn
    intro x hx
    rcases h x hx m hm with ⟨u, hu, p, Hp⟩
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [insert_eq_of_mem hx] at ho
    rw [inter_comm] at ho
    refine' ⟨o, o_open, xo, _⟩
    have A : ∀ y ∈ s ∩ o, p y m = ftaylorSeriesWithin 𝕜 f s y m :=
      by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFderivWithin 𝕜 m f s y
      rw [← iteratedFderivWithin_inter_open o_open yo]
      exact (Hp.mono ho).eq_ftaylor_series_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hy, yo⟩
    exact ((Hp.mono ho).cont m le_rfl).congr fun y hy => (A y hy).symm
#align cont_diff_on.ftaylor_series_within ContDiffOn.ftaylorSeriesWithin

theorem contDiffOn_of_continuousOn_differentiableOn
    (Hcont : ∀ m : ℕ, (m : ℕ∞) ≤ n → ContinuousOn (fun x => iteratedFderivWithin 𝕜 m f s x) s)
    (Hdiff :
      ∀ m : ℕ, (m : ℕ∞) < n → DifferentiableOn 𝕜 (fun x => iteratedFderivWithin 𝕜 m f s x) s) :
    ContDiffOn 𝕜 n f s := by
  intro x hx m hm
  rw [insert_eq_of_mem hx]
  refine' ⟨s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, _⟩
  constructor
  · intro y hy
    simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.uncurry0_apply,
      iteratedFderivWithin_zero_apply]
  · intro k hk y hy
    convert(Hdiff k (lt_of_lt_of_le hk hm) y hy).HasFDerivWithinAt
    simp only [ftaylorSeriesWithin, iteratedFderivWithin_succ_eq_comp_left,
      ContinuousLinearEquiv.coe_apply, Function.comp_apply, coeFn_coeBase]
    exact ContinuousLinearMap.curry_uncurryLeft _
  · intro k hk
    exact Hcont k (le_trans hk hm)
#align cont_diff_on_of_continuous_on_differentiable_on contDiffOn_of_continuousOn_differentiableOn

theorem contDiffOn_of_differentiableOn
    (h : ∀ m : ℕ, (m : ℕ∞) ≤ n → DifferentiableOn 𝕜 (iteratedFderivWithin 𝕜 m f s) s) :
    ContDiffOn 𝕜 n f s :=
  contDiffOn_of_continuousOn_differentiableOn (fun m hm => (h m hm).ContinuousOn) fun m hm =>
    h m (le_of_lt hm)
#align cont_diff_on_of_differentiable_on contDiffOn_of_differentiableOn

theorem ContDiffOn.continuousOn_iteratedFderivWithin {m : ℕ} (h : ContDiffOn 𝕜 n f s)
    (hmn : (m : ℕ∞) ≤ n) (hs : UniqueDiffOn 𝕜 s) : ContinuousOn (iteratedFderivWithin 𝕜 m f s) s :=
  (h.ftaylorSeriesWithin hs).cont m hmn
#align cont_diff_on.continuous_on_iterated_fderiv_within ContDiffOn.continuousOn_iteratedFderivWithin

theorem ContDiffOn.differentiableOn_iteratedFderivWithin {m : ℕ} (h : ContDiffOn 𝕜 n f s)
    (hmn : (m : ℕ∞) < n) (hs : UniqueDiffOn 𝕜 s) :
    DifferentiableOn 𝕜 (iteratedFderivWithin 𝕜 m f s) s := fun x hx =>
  ((h.ftaylorSeriesWithin hs).fderivWithin m hmn x hx).DifferentiableWithinAt
#align cont_diff_on.differentiable_on_iterated_fderiv_within ContDiffOn.differentiableOn_iteratedFderivWithin

theorem ContDiffWithinAt.differentiableWithinAt_iteratedFderivWithin {m : ℕ}
    (h : ContDiffWithinAt 𝕜 n f s x) (hmn : (m : ℕ∞) < n) (hs : UniqueDiffOn 𝕜 (insert x s)) :
    DifferentiableWithinAt 𝕜 (iteratedFderivWithin 𝕜 m f s) s x :=
  by
  rcases h.cont_diff_on' (ENat.add_one_le_of_lt hmn) with ⟨u, uo, xu, hu⟩
  set t := insert x s ∩ u
  have A : t =ᶠ[𝓝[≠] x] s :=
    by
    simp only [set_eventually_eq_iff_inf_principal, ← nhdsWithin_inter']
    rw [← inter_assoc, nhdsWithin_inter_of_mem', ← diff_eq_compl_inter, insert_diff_of_mem,
      diff_eq_compl_inter]
    exacts[rfl, mem_nhdsWithin_of_mem_nhds (uo.mem_nhds xu)]
  have B : iteratedFderivWithin 𝕜 m f s =ᶠ[𝓝 x] iteratedFderivWithin 𝕜 m f t :=
    iteratedFderivWithin_eventually_congr_set' _ A.symm _
  have C : DifferentiableWithinAt 𝕜 (iteratedFderivWithin 𝕜 m f t) t x :=
    hu.differentiable_on_iterated_fderiv_within (Nat.cast_lt.2 m.lt_succ_self) (hs.inter uo) x
      ⟨mem_insert _ _, xu⟩
  rw [differentiableWithinAt_congr_set' _ A] at C
  exact C.congr_of_eventually_eq (B.filter_mono inf_le_left) B.self_of_nhds
#align cont_diff_within_at.differentiable_within_at_iterated_fderiv_within ContDiffWithinAt.differentiableWithinAt_iteratedFderivWithin

theorem contDiffOn_iff_continuousOn_differentiableOn (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔
      (∀ m : ℕ, (m : ℕ∞) ≤ n → ContinuousOn (fun x => iteratedFderivWithin 𝕜 m f s x) s) ∧
        ∀ m : ℕ, (m : ℕ∞) < n → DifferentiableOn 𝕜 (fun x => iteratedFderivWithin 𝕜 m f s x) s :=
  ⟨fun h =>
    ⟨fun m hm => h.continuousOn_iteratedFderivWithin hm hs, fun m hm =>
      h.differentiableOn_iteratedFderivWithin hm hs⟩,
    fun h => contDiffOn_of_continuousOn_differentiableOn h.1 h.2⟩
#align cont_diff_on_iff_continuous_on_differentiable_on contDiffOn_iff_continuousOn_differentiableOn

theorem contDiffOn_succ_of_fderivWithin {n : ℕ} (hf : DifferentiableOn 𝕜 f s)
    (h : ContDiffOn 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) : ContDiffOn 𝕜 (n + 1 : ℕ) f s :=
  by
  intro x hx
  rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt, insert_eq_of_mem hx]
  exact
    ⟨s, self_mem_nhdsWithin, fderivWithin 𝕜 f s, fun y hy => (hf y hy).HasFDerivWithinAt, h x hx⟩
#align cont_diff_on_succ_of_fderiv_within contDiffOn_succ_of_fderivWithin

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (expressed with `fderiv_within`) is `C^n`. -/
theorem contDiffOn_succ_iff_fderivWithin {n : ℕ} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f s ↔
      DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 n (fun y => fderivWithin 𝕜 f s y) s :=
  by
  refine' ⟨fun H => _, fun h => contDiffOn_succ_of_fderivWithin h.1 h.2⟩
  refine' ⟨H.differentiable_on (WithTop.coe_le_coe.2 (Nat.le_add_left 1 n)), fun x hx => _⟩
  rcases contDiffWithinAt_succ_iff_hasFDerivWithinAt.1 (H x hx) with ⟨u, hu, f', hff', hf'⟩
  rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
  rw [inter_comm, insert_eq_of_mem hx] at ho
  have := hf'.mono ho
  rw [contDiffWithinAt_inter' (mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds o_open xo))] at this
  apply this.congr_of_eventually_eq' _ hx
  have : o ∩ s ∈ 𝓝[s] x := mem_nhdsWithin.2 ⟨o, o_open, xo, subset.refl _⟩
  rw [inter_comm] at this
  apply Filter.eventuallyEq_of_mem this fun y hy => _
  have A : fderivWithin 𝕜 f (s ∩ o) y = f' y :=
    ((hff' y (ho hy)).mono ho).fderivWithin (hs.inter o_open y hy)
  rwa [fderivWithin_inter (o_open.mem_nhds hy.2)] at A
#align cont_diff_on_succ_iff_fderiv_within contDiffOn_succ_iff_fderivWithin

theorem contDiffOn_succ_iff_has_fderiv_within {n : ℕ} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f s ↔
      ∃ f' : E → E →L[𝕜] F, ContDiffOn 𝕜 n f' s ∧ ∀ x, x ∈ s → HasFDerivWithinAt f (f' x) s x :=
  by
  rw [contDiffOn_succ_iff_fderivWithin hs]
  refine' ⟨fun h => ⟨fderivWithin 𝕜 f s, h.2, fun x hx => (h.1 x hx).HasFDerivWithinAt⟩, fun h => _⟩
  rcases h with ⟨f', h1, h2⟩
  refine' ⟨fun x hx => (h2 x hx).DifferentiableWithinAt, fun x hx => _⟩
  exact (h1 x hx).congr' (fun y hy => (h2 y hy).fderivWithin (hs y hy)) hx
#align cont_diff_on_succ_iff_has_fderiv_within contDiffOn_succ_iff_has_fderiv_within

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]] -/
/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (expressed with `fderiv`) is `C^n`. -/
theorem contDiffOn_succ_iff_fderiv_of_open {n : ℕ} (hs : IsOpen s) :
    ContDiffOn 𝕜 (n + 1 : ℕ) f s ↔
      DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 n (fun y => fderiv 𝕜 f y) s :=
  by
  rw [contDiffOn_succ_iff_fderivWithin hs.unique_diff_on]
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]]"
  apply contDiffOn_congr
  intro x hx
  exact fderivWithin_of_open hs hx
#align cont_diff_on_succ_iff_fderiv_of_open contDiffOn_succ_iff_fderiv_of_open

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative (expressed with `fderiv_within`) is `C^∞`. -/
theorem contDiffOn_top_iff_fderivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 ∞ f s ↔
      DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (fun y => fderivWithin 𝕜 f s y) s :=
  by
  constructor
  · intro h
    refine' ⟨h.differentiable_on le_top, _⟩
    apply contDiffOn_top.2 fun n => ((contDiffOn_succ_iff_fderivWithin hs).1 _).2
    exact h.of_le le_top
  · intro h
    refine' contDiffOn_top.2 fun n => _
    have A : (n : ℕ∞) ≤ ∞ := le_top
    apply ((contDiffOn_succ_iff_fderivWithin hs).2 ⟨h.1, h.2.of_le A⟩).of_le
    exact WithTop.coe_le_coe.2 (Nat.le_succ n)
#align cont_diff_on_top_iff_fderiv_within contDiffOn_top_iff_fderivWithin

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]] -/
/-- A function is `C^∞` on an open domain if and only if it is differentiable there, and its
derivative (expressed with `fderiv`) is `C^∞`. -/
theorem contDiffOn_top_iff_fderiv_of_open (hs : IsOpen s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (fun y => fderiv 𝕜 f y) s :=
  by
  rw [contDiffOn_top_iff_fderivWithin hs.unique_diff_on]
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr «expr ∧ »(_, _)]]"
  apply contDiffOn_congr
  intro x hx
  exact fderivWithin_of_open hs hx
#align cont_diff_on_top_iff_fderiv_of_open contDiffOn_top_iff_fderiv_of_open

theorem ContDiffOn.fderivWithin (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hmn : m + 1 ≤ n) : ContDiffOn 𝕜 m (fun y => fderivWithin 𝕜 f s y) s :=
  by
  cases m
  · change ∞ + 1 ≤ n at hmn
    have : n = ∞ := by simpa using hmn
    rw [this] at hf
    exact ((contDiffOn_top_iff_fderivWithin hs).1 hf).2
  · change (m.succ : ℕ∞) ≤ n at hmn
    exact ((contDiffOn_succ_iff_fderivWithin hs).1 (hf.of_le hmn)).2
#align cont_diff_on.fderiv_within ContDiffOn.fderivWithin

theorem ContDiffOn.fderiv_of_open (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (fun y => fderiv 𝕜 f y) s :=
  (hf.fderivWithin hs.UniqueDiffOn hmn).congr fun x hx => (fderivWithin_of_open hs hx).symm
#align cont_diff_on.fderiv_of_open ContDiffOn.fderiv_of_open

theorem ContDiffOn.continuousOn_fderivWithin (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hn : 1 ≤ n) : ContinuousOn (fun x => fderivWithin 𝕜 f s x) s :=
  ((contDiffOn_succ_iff_fderivWithin hs).1 (h.of_le hn)).2.ContinuousOn
#align cont_diff_on.continuous_on_fderiv_within ContDiffOn.continuousOn_fderivWithin

theorem ContDiffOn.continuousOn_fderiv_of_open (h : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hn : 1 ≤ n) : ContinuousOn (fun x => fderiv 𝕜 f x) s :=
  ((contDiffOn_succ_iff_fderiv_of_open hs).1 (h.of_le hn)).2.ContinuousOn
#align cont_diff_on.continuous_on_fderiv_of_open ContDiffOn.continuousOn_fderiv_of_open

/-! ### Functions with a Taylor series on the whole space -/


/-- `has_ftaylor_series_up_to n f p` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`has_fderiv_at` but for higher order derivatives. -/
structure HasFtaylorSeriesUpTo (n : ℕ∞) (f : E → F) (p : E → FormalMultilinearSeries 𝕜 E F) :
  Prop where
  zero_eq : ∀ x, (p x 0).uncurry0 = f x
  fderiv : ∀ (m : ℕ) (hm : (m : ℕ∞) < n), ∀ x, HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x
  cont : ∀ (m : ℕ) (hm : (m : ℕ∞) ≤ n), Continuous fun x => p x m
#align has_ftaylor_series_up_to HasFtaylorSeriesUpTo

theorem HasFtaylorSeriesUpTo.zero_eq' (h : HasFtaylorSeriesUpTo n f p) (x : E) :
    p x 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (f x) := by rw [← h.zero_eq x]; symm;
  exact ContinuousMultilinearMap.uncurry0_curry0 _
#align has_ftaylor_series_up_to.zero_eq' HasFtaylorSeriesUpTo.zero_eq'

theorem hasFtaylorSeriesUpToOn_univ_iff :
    HasFtaylorSeriesUpToOn n f p univ ↔ HasFtaylorSeriesUpTo n f p :=
  by
  constructor
  · intro H
    constructor
    · exact fun x => H.zero_eq x (mem_univ x)
    · intro m hm x
      rw [← hasFDerivWithinAt_univ]
      exact H.fderiv_within m hm x (mem_univ x)
    · intro m hm
      rw [continuous_iff_continuousOn_univ]
      exact H.cont m hm
  · intro H
    constructor
    · exact fun x hx => H.zero_eq x
    · intro m hm x hx
      rw [hasFDerivWithinAt_univ]
      exact H.fderiv m hm x
    · intro m hm
      rw [← continuous_iff_continuousOn_univ]
      exact H.cont m hm
#align has_ftaylor_series_up_to_on_univ_iff hasFtaylorSeriesUpToOn_univ_iff

theorem HasFtaylorSeriesUpTo.hasFtaylorSeriesUpToOn (h : HasFtaylorSeriesUpTo n f p) (s : Set E) :
    HasFtaylorSeriesUpToOn n f p s :=
  (hasFtaylorSeriesUpToOn_univ_iff.2 h).mono (subset_univ _)
#align has_ftaylor_series_up_to.has_ftaylor_series_up_to_on HasFtaylorSeriesUpTo.hasFtaylorSeriesUpToOn

theorem HasFtaylorSeriesUpTo.ofLe (h : HasFtaylorSeriesUpTo n f p) (hmn : m ≤ n) :
    HasFtaylorSeriesUpTo m f p := by rw [← hasFtaylorSeriesUpToOn_univ_iff] at h⊢; exact h.of_le hmn
#align has_ftaylor_series_up_to.of_le HasFtaylorSeriesUpTo.ofLe

theorem HasFtaylorSeriesUpTo.continuous (h : HasFtaylorSeriesUpTo n f p) : Continuous f :=
  by
  rw [← hasFtaylorSeriesUpToOn_univ_iff] at h
  rw [continuous_iff_continuousOn_univ]
  exact h.continuous_on
#align has_ftaylor_series_up_to.continuous HasFtaylorSeriesUpTo.continuous

theorem hasFtaylorSeriesUpTo_zero_iff :
    HasFtaylorSeriesUpTo 0 f p ↔ Continuous f ∧ ∀ x, (p x 0).uncurry0 = f x := by
  simp [has_ftaylor_series_up_to_on_univ_iff.symm, continuous_iff_continuousOn_univ,
    hasFtaylorSeriesUpToOn_zero_iff]
#align has_ftaylor_series_up_to_zero_iff hasFtaylorSeriesUpTo_zero_iff

theorem hasFtaylorSeriesUpTo_top_iff :
    HasFtaylorSeriesUpTo ∞ f p ↔ ∀ n : ℕ, HasFtaylorSeriesUpTo n f p := by
  simp only [← hasFtaylorSeriesUpToOn_univ_iff, hasFtaylorSeriesUpToOn_top_iff]
#align has_ftaylor_series_up_to_top_iff hasFtaylorSeriesUpTo_top_iff

/-- In the case that `n = ∞` we don't need the continuity assumption in
`has_ftaylor_series_up_to`. -/
theorem hasFtaylorSeriesUpTo_top_iff' :
    HasFtaylorSeriesUpTo ∞ f p ↔
      (∀ x, (p x 0).uncurry0 = f x) ∧
        ∀ (m : ℕ) (x), HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x :=
  by
  simp only [← hasFtaylorSeriesUpToOn_univ_iff, hasFtaylorSeriesUpToOn_top_iff', mem_univ,
    forall_true_left, hasFDerivWithinAt_univ]
#align has_ftaylor_series_up_to_top_iff' hasFtaylorSeriesUpTo_top_iff'

/-- If a function has a Taylor series at order at least `1`, then the term of order `1` of this
series is a derivative of `f`. -/
theorem HasFtaylorSeriesUpTo.hasFDerivAt (h : HasFtaylorSeriesUpTo n f p) (hn : 1 ≤ n) (x : E) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) x :=
  by
  rw [← hasFDerivWithinAt_univ]
  exact (hasFtaylorSeriesUpToOn_univ_iff.2 h).HasFDerivWithinAt hn (mem_univ _)
#align has_ftaylor_series_up_to.has_fderiv_at HasFtaylorSeriesUpTo.hasFDerivAt

theorem HasFtaylorSeriesUpTo.differentiable (h : HasFtaylorSeriesUpTo n f p) (hn : 1 ≤ n) :
    Differentiable 𝕜 f := fun x => (h.HasFDerivAt hn x).DifferentiableAt
#align has_ftaylor_series_up_to.differentiable HasFtaylorSeriesUpTo.differentiable

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. -/
theorem hasFtaylorSeriesUpTo_succ_iff_right {n : ℕ} :
    HasFtaylorSeriesUpTo (n + 1 : ℕ) f p ↔
      (∀ x, (p x 0).uncurry0 = f x) ∧
        (∀ x, HasFDerivAt (fun y => p y 0) (p x 1).curryLeft x) ∧
          HasFtaylorSeriesUpTo n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1)) fun x =>
            (p x).shift :=
  by
  simp only [hasFtaylorSeriesUpToOn_succ_iff_right, ← hasFtaylorSeriesUpToOn_univ_iff, mem_univ,
    forall_true_left, hasFDerivWithinAt_univ]
#align has_ftaylor_series_up_to_succ_iff_right hasFtaylorSeriesUpTo_succ_iff_right

/-! ### Smooth functions at a point -/


variable (𝕜)

/-- A function is continuously differentiable up to `n` at a point `x` if, for any integer `k ≤ n`,
there is a neighborhood of `x` where `f` admits derivatives up to order `n`, which are continuous.
-/
def ContDiffAt (n : ℕ∞) (f : E → F) (x : E) : Prop :=
  ContDiffWithinAt 𝕜 n f univ x
#align cont_diff_at ContDiffAt

variable {𝕜}

theorem contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f univ x ↔ ContDiffAt 𝕜 n f x :=
  Iff.rfl
#align cont_diff_within_at_univ contDiffWithinAt_univ

theorem contDiffAt_top : ContDiffAt 𝕜 ∞ f x ↔ ∀ n : ℕ, ContDiffAt 𝕜 n f x := by
  simp [← contDiffWithinAt_univ, contDiffWithinAt_top]
#align cont_diff_at_top contDiffAt_top

theorem ContDiffAt.contDiffWithinAt (h : ContDiffAt 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x :=
  h.mono (subset_univ _)
#align cont_diff_at.cont_diff_within_at ContDiffAt.contDiffWithinAt

theorem ContDiffWithinAt.contDiffAt (h : ContDiffWithinAt 𝕜 n f s x) (hx : s ∈ 𝓝 x) :
    ContDiffAt 𝕜 n f x := by rwa [ContDiffAt, ← contDiffWithinAt_inter hx, univ_inter]
#align cont_diff_within_at.cont_diff_at ContDiffWithinAt.contDiffAt

theorem ContDiffAt.congr_of_eventuallyEq (h : ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) :
    ContDiffAt 𝕜 n f₁ x :=
  h.congr_of_eventually_eq' (by rwa [nhdsWithin_univ]) (mem_univ x)
#align cont_diff_at.congr_of_eventually_eq ContDiffAt.congr_of_eventuallyEq

theorem ContDiffAt.of_le (h : ContDiffAt 𝕜 n f x) (hmn : m ≤ n) : ContDiffAt 𝕜 m f x :=
  h.of_le hmn
#align cont_diff_at.of_le ContDiffAt.of_le

theorem ContDiffAt.continuousAt (h : ContDiffAt 𝕜 n f x) : ContinuousAt f x := by
  simpa [continuousWithinAt_univ] using h.continuous_within_at
#align cont_diff_at.continuous_at ContDiffAt.continuousAt

/-- If a function is `C^n` with `n ≥ 1` at a point, then it is differentiable there. -/
theorem ContDiffAt.differentiableAt (h : ContDiffAt 𝕜 n f x) (hn : 1 ≤ n) :
    DifferentiableAt 𝕜 f x := by
  simpa [hn, differentiableWithinAt_univ] using h.differentiable_within_at
#align cont_diff_at.differentiable_at ContDiffAt.differentiableAt

/-- A function is `C^(n + 1)` at a point iff locally, it has a derivative which is `C^n`. -/
theorem contDiffAt_succ_iff_hasFDerivAt {n : ℕ} :
    ContDiffAt 𝕜 (n + 1 : ℕ) f x ↔
      ∃ f' : E → E →L[𝕜] F, (∃ u ∈ 𝓝 x, ∀ x ∈ u, HasFDerivAt f (f' x) x) ∧ ContDiffAt 𝕜 n f' x :=
  by
  rw [← contDiffWithinAt_univ, contDiffWithinAt_succ_iff_hasFDerivWithinAt]
  simp only [nhdsWithin_univ, exists_prop, mem_univ, insert_eq_of_mem]
  constructor
  · rintro ⟨u, H, f', h_fderiv, h_cont_diff⟩
    rcases mem_nhds_iff.mp H with ⟨t, htu, ht, hxt⟩
    refine' ⟨f', ⟨t, _⟩, h_cont_diff.cont_diff_at H⟩
    refine' ⟨mem_nhds_iff.mpr ⟨t, subset.rfl, ht, hxt⟩, _⟩
    intro y hyt
    refine' (h_fderiv y (htu hyt)).HasFDerivAt _
    exact mem_nhds_iff.mpr ⟨t, htu, ht, hyt⟩
  · rintro ⟨f', ⟨u, H, h_fderiv⟩, h_cont_diff⟩
    refine' ⟨u, H, f', _, h_cont_diff.cont_diff_within_at⟩
    intro x hxu
    exact (h_fderiv x hxu).HasFDerivWithinAt
#align cont_diff_at_succ_iff_has_fderiv_at contDiffAt_succ_iff_hasFDerivAt

protected theorem ContDiffAt.eventually {n : ℕ} (h : ContDiffAt 𝕜 n f x) :
    ∀ᶠ y in 𝓝 x, ContDiffAt 𝕜 n f y := by simpa [nhdsWithin_univ] using h.eventually
#align cont_diff_at.eventually ContDiffAt.eventually

/-! ### Smooth functions -/


variable (𝕜)

/-- A function is continuously differentiable up to `n` if it admits derivatives up to
order `n`, which are continuous. Contrary to the case of definitions in domains (where derivatives
might not be unique) we do not need to localize the definition in space or time.
-/
def ContDiff (n : ℕ∞) (f : E → F) : Prop :=
  ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFtaylorSeriesUpTo n f p
#align cont_diff ContDiff

variable {𝕜}

/-- If `f` has a Taylor series up to `n`, then it is `C^n`. -/
theorem HasFtaylorSeriesUpTo.contDiff {f' : E → FormalMultilinearSeries 𝕜 E F}
    (hf : HasFtaylorSeriesUpTo n f f') : ContDiff 𝕜 n f :=
  ⟨f', hf⟩
#align has_ftaylor_series_up_to.cont_diff HasFtaylorSeriesUpTo.contDiff

theorem contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n f :=
  by
  constructor
  · intro H
    use ftaylorSeriesWithin 𝕜 f univ
    rw [← hasFtaylorSeriesUpToOn_univ_iff]
    exact H.ftaylor_series_within uniqueDiffOn_univ
  · rintro ⟨p, hp⟩ x hx m hm
    exact ⟨univ, Filter.univ_sets _, p, (hp.has_ftaylor_series_up_to_on univ).of_le hm⟩
#align cont_diff_on_univ contDiffOn_univ

theorem contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ ∀ x, ContDiffAt 𝕜 n f x := by
  simp [← contDiffOn_univ, ContDiffOn, ContDiffAt]
#align cont_diff_iff_cont_diff_at contDiff_iff_contDiffAt

theorem ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiffAt 𝕜 n f x :=
  contDiff_iff_contDiffAt.1 h x
#align cont_diff.cont_diff_at ContDiff.contDiffAt

theorem ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f) : ContDiffWithinAt 𝕜 n f s x :=
  h.ContDiffAt.ContDiffWithinAt
#align cont_diff.cont_diff_within_at ContDiff.contDiffWithinAt

theorem contDiff_top : ContDiff 𝕜 ∞ f ↔ ∀ n : ℕ, ContDiff 𝕜 n f := by
  simp [cont_diff_on_univ.symm, contDiffOn_top]
#align cont_diff_top contDiff_top

theorem contDiff_all_iff_nat : (∀ n, ContDiff 𝕜 n f) ↔ ∀ n : ℕ, ContDiff 𝕜 n f := by
  simp only [← contDiffOn_univ, contDiffOn_all_iff_nat]
#align cont_diff_all_iff_nat contDiff_all_iff_nat

theorem ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiffOn 𝕜 n f s :=
  (contDiffOn_univ.2 h).mono (subset_univ _)
#align cont_diff.cont_diff_on ContDiff.contDiffOn

@[simp]
theorem contDiff_zero : ContDiff 𝕜 0 f ↔ Continuous f :=
  by
  rw [← contDiffOn_univ, continuous_iff_continuousOn_univ]
  exact contDiffOn_zero
#align cont_diff_zero contDiff_zero

theorem contDiffAt_zero : ContDiffAt 𝕜 0 f x ↔ ∃ u ∈ 𝓝 x, ContinuousOn f u := by
  rw [← contDiffWithinAt_univ]; simp [contDiffWithinAt_zero, nhdsWithin_univ]
#align cont_diff_at_zero contDiffAt_zero

theorem contDiffAt_one_iff :
    ContDiffAt 𝕜 1 f x ↔
      ∃ f' : E → E →L[𝕜] F, ∃ u ∈ 𝓝 x, ContinuousOn f' u ∧ ∀ x ∈ u, HasFDerivAt f (f' x) x :=
  by
  simp_rw [show (1 : ℕ∞) = (0 + 1 : ℕ) from (zero_add 1).symm, contDiffAt_succ_iff_hasFDerivAt,
    show ((0 : ℕ) : ℕ∞) = 0 from rfl, contDiffAt_zero,
    exists_mem_and_iff antitone_bforall antitone_continuousOn, and_comm']
#align cont_diff_at_one_iff contDiffAt_one_iff

theorem ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m ≤ n) : ContDiff 𝕜 m f :=
  contDiffOn_univ.1 <| (contDiffOn_univ.2 h).of_le hmn
#align cont_diff.of_le ContDiff.of_le

theorem ContDiff.of_succ {n : ℕ} (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 n f :=
  h.of_le <| WithTop.coe_le_coe.mpr le_self_add
#align cont_diff.of_succ ContDiff.of_succ

theorem ContDiff.one_of_succ {n : ℕ} (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 1 f :=
  h.of_le <| WithTop.coe_le_coe.mpr le_add_self
#align cont_diff.one_of_succ ContDiff.one_of_succ

theorem ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuous f :=
  contDiff_zero.1 (h.of_le bot_le)
#align cont_diff.continuous ContDiff.continuous

/-- If a function is `C^n` with `n ≥ 1`, then it is differentiable. -/
theorem ContDiff.differentiable (h : ContDiff 𝕜 n f) (hn : 1 ≤ n) : Differentiable 𝕜 f :=
  differentiableOn_univ.1 <| (contDiffOn_univ.2 h).DifferentiableOn hn
#align cont_diff.differentiable ContDiff.differentiable

theorem contDiff_iff_forall_nat_le : ContDiff 𝕜 n f ↔ ∀ m : ℕ, ↑m ≤ n → ContDiff 𝕜 m f := by
  simp_rw [← contDiffOn_univ]; exact contDiffOn_iff_forall_nat_le
#align cont_diff_iff_forall_nat_le contDiff_iff_forall_nat_le

/-- A function is `C^(n+1)` iff it has a `C^n` derivative. -/
theorem contDiff_succ_iff_has_fderiv {n : ℕ} :
    ContDiff 𝕜 (n + 1 : ℕ) f ↔
      ∃ f' : E → E →L[𝕜] F, ContDiff 𝕜 n f' ∧ ∀ x, HasFDerivAt f (f' x) x :=
  by
  simp only [← contDiffOn_univ, ← hasFDerivWithinAt_univ,
    contDiffOn_succ_iff_has_fderiv_within uniqueDiffOn_univ, Set.mem_univ, forall_true_left]
#align cont_diff_succ_iff_has_fderiv contDiff_succ_iff_has_fderiv

/-! ### Iterated derivative -/


variable (𝕜)

/-- The `n`-th derivative of a function, as a multilinear map, defined inductively. -/
noncomputable def iteratedFderiv (n : ℕ) (f : E → F) : E → E[×n]→L[𝕜] F :=
  Nat.recOn n (fun x => ContinuousMultilinearMap.curry0 𝕜 E (f x)) fun n rec x =>
    ContinuousLinearMap.uncurryLeft (fderiv 𝕜 rec x)
#align iterated_fderiv iteratedFderiv

/-- Formal Taylor series associated to a function within a set. -/
def ftaylorSeries (f : E → F) (x : E) : FormalMultilinearSeries 𝕜 E F := fun n =>
  iteratedFderiv 𝕜 n f x
#align ftaylor_series ftaylorSeries

variable {𝕜}

@[simp]
theorem iteratedFderiv_zero_apply (m : Fin 0 → E) :
    (iteratedFderiv 𝕜 0 f x : (Fin 0 → E) → F) m = f x :=
  rfl
#align iterated_fderiv_zero_apply iteratedFderiv_zero_apply

theorem iteratedFderiv_zero_eq_comp :
    iteratedFderiv 𝕜 0 f = (continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f :=
  rfl
#align iterated_fderiv_zero_eq_comp iteratedFderiv_zero_eq_comp

@[simp]
theorem norm_iteratedFderiv_zero : ‖iteratedFderiv 𝕜 0 f x‖ = ‖f x‖ := by
  rw [iteratedFderiv_zero_eq_comp, LinearIsometryEquiv.norm_map]
#align norm_iterated_fderiv_zero norm_iteratedFderiv_zero

theorem iteratedFderiv_with_zero_eq : iteratedFderivWithin 𝕜 0 f s = iteratedFderiv 𝕜 0 f := by ext;
  rfl
#align iterated_fderiv_with_zero_eq iteratedFderiv_with_zero_eq

theorem iteratedFderiv_succ_apply_left {n : ℕ} (m : Fin (n + 1) → E) :
    (iteratedFderiv 𝕜 (n + 1) f x : (Fin (n + 1) → E) → F) m =
      (fderiv 𝕜 (iteratedFderiv 𝕜 n f) x : E → E[×n]→L[𝕜] F) (m 0) (tail m) :=
  rfl
#align iterated_fderiv_succ_apply_left iteratedFderiv_succ_apply_left

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
theorem iteratedFderiv_succ_eq_comp_left {n : ℕ} :
    iteratedFderiv 𝕜 (n + 1) f =
      continuousMultilinearCurryLeftEquiv 𝕜 (fun i : Fin (n + 1) => E) F ∘
        fderiv 𝕜 (iteratedFderiv 𝕜 n f) :=
  rfl
#align iterated_fderiv_succ_eq_comp_left iteratedFderiv_succ_eq_comp_left

/-- Writing explicitly the derivative of the `n`-th derivative as the composition of a currying
linear equiv, and the `n + 1`-th derivative. -/
theorem fderiv_iteratedFderiv {n : ℕ} :
    fderiv 𝕜 (iteratedFderiv 𝕜 n f) =
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun i : Fin (n + 1) => E) F).symm ∘
        iteratedFderiv 𝕜 (n + 1) f :=
  by
  rw [iteratedFderiv_succ_eq_comp_left]
  ext1 x
  simp only [Function.comp_apply, LinearIsometryEquiv.symm_apply_apply]
#align fderiv_iterated_fderiv fderiv_iteratedFderiv

theorem HasCompactSupport.iteratedFderiv (hf : HasCompactSupport f) (n : ℕ) :
    HasCompactSupport (iteratedFderiv 𝕜 n f) :=
  by
  induction' n with n IH
  · rw [iteratedFderiv_zero_eq_comp]
    apply hf.comp_left
    exact LinearIsometryEquiv.map_zero _
  · rw [iteratedFderiv_succ_eq_comp_left]
    apply (IH.fderiv 𝕜).compLeft
    exact LinearIsometryEquiv.map_zero _
#align has_compact_support.iterated_fderiv HasCompactSupport.iteratedFderiv

theorem norm_fderiv_iteratedFderiv {n : ℕ} :
    ‖fderiv 𝕜 (iteratedFderiv 𝕜 n f) x‖ = ‖iteratedFderiv 𝕜 (n + 1) f x‖ := by
  rw [iteratedFderiv_succ_eq_comp_left, LinearIsometryEquiv.norm_map]
#align norm_fderiv_iterated_fderiv norm_fderiv_iteratedFderiv

theorem iteratedFderivWithin_univ {n : ℕ} :
    iteratedFderivWithin 𝕜 n f univ = iteratedFderiv 𝕜 n f :=
  by
  induction' n with n IH
  · ext x; simp
  · ext (x m)
    rw [iteratedFderiv_succ_apply_left, iteratedFderivWithin_succ_apply_left, IH, fderivWithin_univ]
#align iterated_fderiv_within_univ iteratedFderivWithin_univ

/-- In an open set, the iterated derivative within this set coincides with the global iterated
derivative. -/
theorem iteratedFderivWithin_of_isOpen (n : ℕ) (hs : IsOpen s) :
    EqOn (iteratedFderivWithin 𝕜 n f s) (iteratedFderiv 𝕜 n f) s :=
  by
  induction' n with n IH
  · intro x hx
    ext1 m
    simp only [iteratedFderivWithin_zero_apply, iteratedFderiv_zero_apply]
  · intro x hx
    rw [iteratedFderiv_succ_eq_comp_left, iteratedFderivWithin_succ_eq_comp_left]
    dsimp
    congr 1
    rw [fderivWithin_of_open hs hx]
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hs.mem_nhds hx]
    exact IH
#align iterated_fderiv_within_of_is_open iteratedFderivWithin_of_isOpen

theorem ftaylorSeriesWithin_univ : ftaylorSeriesWithin 𝕜 f univ = ftaylorSeries 𝕜 f :=
  by
  ext1 x; ext1 n
  change iteratedFderivWithin 𝕜 n f univ x = iteratedFderiv 𝕜 n f x
  rw [iteratedFderivWithin_univ]
#align ftaylor_series_within_univ ftaylorSeriesWithin_univ

theorem iteratedFderiv_succ_apply_right {n : ℕ} (m : Fin (n + 1) → E) :
    (iteratedFderiv 𝕜 (n + 1) f x : (Fin (n + 1) → E) → F) m =
      iteratedFderiv 𝕜 n (fun y => fderiv 𝕜 f y) x (init m) (m (last n)) :=
  by
  rw [← iteratedFderivWithin_univ, ← iteratedFderivWithin_univ, ← fderivWithin_univ]
  exact iteratedFderivWithin_succ_apply_right uniqueDiffOn_univ (mem_univ _) _
#align iterated_fderiv_succ_apply_right iteratedFderiv_succ_apply_right

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the `n`-th derivative of the derivative. -/
theorem iteratedFderiv_succ_eq_comp_right {n : ℕ} :
    iteratedFderiv 𝕜 (n + 1) f x =
      (continuousMultilinearCurryRightEquiv' 𝕜 n E F ∘ iteratedFderiv 𝕜 n fun y => fderiv 𝕜 f y)
        x :=
  by ext m; rw [iteratedFderiv_succ_apply_right]; rfl
#align iterated_fderiv_succ_eq_comp_right iteratedFderiv_succ_eq_comp_right

theorem norm_iteratedFderiv_fderiv {n : ℕ} :
    ‖iteratedFderiv 𝕜 n (fderiv 𝕜 f) x‖ = ‖iteratedFderiv 𝕜 (n + 1) f x‖ := by
  rw [iteratedFderiv_succ_eq_comp_right, LinearIsometryEquiv.norm_map]
#align norm_iterated_fderiv_fderiv norm_iteratedFderiv_fderiv

@[simp]
theorem iteratedFderiv_one_apply (m : Fin 1 → E) :
    (iteratedFderiv 𝕜 1 f x : (Fin 1 → E) → F) m = (fderiv 𝕜 f x : E → F) (m 0) := by
  rw [iteratedFderiv_succ_apply_right, iteratedFderiv_zero_apply]; rfl
#align iterated_fderiv_one_apply iteratedFderiv_one_apply

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylor_series_within 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem contDiff_iff_ftaylorSeries :
    ContDiff 𝕜 n f ↔ HasFtaylorSeriesUpTo n f (ftaylorSeries 𝕜 f) :=
  by
  constructor
  · rw [← contDiffOn_univ, ← hasFtaylorSeriesUpToOn_univ_iff, ← ftaylorSeriesWithin_univ]
    exact fun h => ContDiffOn.ftaylorSeriesWithin h uniqueDiffOn_univ
  · intro h; exact ⟨ftaylorSeries 𝕜 f, h⟩
#align cont_diff_iff_ftaylor_series contDiff_iff_ftaylorSeries

theorem contDiff_iff_continuous_differentiable :
    ContDiff 𝕜 n f ↔
      (∀ m : ℕ, (m : ℕ∞) ≤ n → Continuous fun x => iteratedFderiv 𝕜 m f x) ∧
        ∀ m : ℕ, (m : ℕ∞) < n → Differentiable 𝕜 fun x => iteratedFderiv 𝕜 m f x :=
  by
  simp [cont_diff_on_univ.symm, continuous_iff_continuousOn_univ, differentiable_on_univ.symm,
    iteratedFderivWithin_univ, contDiffOn_iff_continuousOn_differentiableOn uniqueDiffOn_univ]
#align cont_diff_iff_continuous_differentiable contDiff_iff_continuous_differentiable

/-- If `f` is `C^n` then its `m`-times iterated derivative is continuous for `m ≤ n`. -/
theorem ContDiff.continuous_iteratedFderiv {m : ℕ} (hm : (m : ℕ∞) ≤ n) (hf : ContDiff 𝕜 n f) :
    Continuous fun x => iteratedFderiv 𝕜 m f x :=
  (contDiff_iff_continuous_differentiable.mp hf).1 m hm
#align cont_diff.continuous_iterated_fderiv ContDiff.continuous_iteratedFderiv

/-- If `f` is `C^n` then its `m`-times iterated derivative is differentiable for `m < n`. -/
theorem ContDiff.differentiable_iteratedFderiv {m : ℕ} (hm : (m : ℕ∞) < n) (hf : ContDiff 𝕜 n f) :
    Differentiable 𝕜 fun x => iteratedFderiv 𝕜 m f x :=
  (contDiff_iff_continuous_differentiable.mp hf).2 m hm
#align cont_diff.differentiable_iterated_fderiv ContDiff.differentiable_iteratedFderiv

theorem contDiff_of_differentiable_iteratedFderiv
    (h : ∀ m : ℕ, (m : ℕ∞) ≤ n → Differentiable 𝕜 (iteratedFderiv 𝕜 m f)) : ContDiff 𝕜 n f :=
  contDiff_iff_continuous_differentiable.2
    ⟨fun m hm => (h m hm).Continuous, fun m hm => h m (le_of_lt hm)⟩
#align cont_diff_of_differentiable_iterated_fderiv contDiff_of_differentiable_iteratedFderiv

/-- A function is `C^(n + 1)` if and only if it is differentiable,
and its derivative (formulated in terms of `fderiv`) is `C^n`. -/
theorem contDiff_succ_iff_fderiv {n : ℕ} :
    ContDiff 𝕜 (n + 1 : ℕ) f ↔ Differentiable 𝕜 f ∧ ContDiff 𝕜 n fun y => fderiv 𝕜 f y := by
  simp only [← contDiffOn_univ, ← differentiableOn_univ, ← fderivWithin_univ,
    contDiffOn_succ_iff_fderivWithin uniqueDiffOn_univ]
#align cont_diff_succ_iff_fderiv contDiff_succ_iff_fderiv

theorem contDiff_one_iff_fderiv : ContDiff 𝕜 1 f ↔ Differentiable 𝕜 f ∧ Continuous (fderiv 𝕜 f) :=
  contDiff_succ_iff_fderiv.trans <| Iff.rfl.And contDiff_zero
#align cont_diff_one_iff_fderiv contDiff_one_iff_fderiv

/-- A function is `C^∞` if and only if it is differentiable,
and its derivative (formulated in terms of `fderiv`) is `C^∞`. -/
theorem contDiff_top_iff_fderiv :
    ContDiff 𝕜 ∞ f ↔ Differentiable 𝕜 f ∧ ContDiff 𝕜 ∞ fun y => fderiv 𝕜 f y :=
  by
  simp only [← contDiffOn_univ, ← differentiableOn_univ, ← fderivWithin_univ]
  rw [contDiffOn_top_iff_fderivWithin uniqueDiffOn_univ]
#align cont_diff_top_iff_fderiv contDiff_top_iff_fderiv

theorem ContDiff.continuous_fderiv (h : ContDiff 𝕜 n f) (hn : 1 ≤ n) :
    Continuous fun x => fderiv 𝕜 f x :=
  (contDiff_succ_iff_fderiv.1 (h.of_le hn)).2.Continuous
#align cont_diff.continuous_fderiv ContDiff.continuous_fderiv

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
theorem ContDiff.continuous_fderiv_apply (h : ContDiff 𝕜 n f) (hn : 1 ≤ n) :
    Continuous fun p : E × E => (fderiv 𝕜 f p.1 : E → F) p.2 :=
  have A : Continuous fun q : (E →L[𝕜] F) × E => q.1 q.2 := isBoundedBilinearMapApply.Continuous
  have B : Continuous fun p : E × E => (fderiv 𝕜 f p.1, p.2) :=
    ((h.continuous_fderiv hn).comp continuous_fst).prod_mk continuous_snd
  A.comp B
#align cont_diff.continuous_fderiv_apply ContDiff.continuous_fderiv_apply

