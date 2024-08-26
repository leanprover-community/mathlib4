/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FormalMultilinearSeries

/-!
# Functions with a Taylor series

-/

noncomputable section

open scoped Classical
open NNReal Topology Filter

local notation "∞" => (⊤ : ℕ∞)

/-
Porting note: These lines are not required in Mathlib4.
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule' AddCommGroup.toAddCommMonoid
-/

open Set Fin Filter Function

universe u uE uF uG uX

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {s s₁ t u : Set E} {f f₁ : E → F} {g : F → G} {x x₀ : E} {c : F}
  {p : E → FormalMultilinearSeries 𝕜 E F} {m n : ℕ∞}

/-! ### Functions with a Taylor series on a domain -/

/-- `HasFTaylorSeriesUpToOn n f p s` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`HasFDerivWithinAt` but for higher order derivatives.

Notice that `p` does not sum up to `f` on the diagonal (`FormalMultilinearSeries.sum`), even if
`f` is analytic and `n = ∞`: an additional `1/m!` factor on the `m`th term is necessary for that. -/
structure HasFTaylorSeriesUpToOn (n : ℕ∞) (f : E → F) (p : E → FormalMultilinearSeries 𝕜 E F)
  (s : Set E) : Prop where
  zero_eq : ∀ x ∈ s, (p x 0).uncurry0 = f x
  protected fderivWithin : ∀ m : ℕ, (m : ℕ∞) < n → ∀ x ∈ s,
    HasFDerivWithinAt (p · m) (p x m.succ).curryLeft s x
  cont : ∀ m : ℕ, (m : ℕ∞) ≤ n → ContinuousOn (p · m) s

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
    HasFTaylorSeriesUpToOn 0 f p s ↔ ContinuousOn f s ∧ ∀ x ∈ s, (p x 0).uncurry0 = f x := by
  refine ⟨fun H => ⟨H.continuousOn, H.zero_eq⟩, fun H =>
      ⟨H.2, fun m hm => False.elim (not_le.2 hm bot_le), fun m hm ↦ ?_⟩⟩
  obtain rfl : m = 0 := mod_cast hm.antisymm (zero_le _)
  have : EqOn (p · 0) ((continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f) s := fun x hx ↦
    (continuousMultilinearCurryFin0 𝕜 E F).eq_symm_apply.2 (H.2 x hx)
  rw [continuousOn_congr this, LinearIsometryEquiv.comp_continuousOn_iff]
  exact H.1

theorem hasFTaylorSeriesUpToOn_top_iff :
    HasFTaylorSeriesUpToOn ∞ f p s ↔ ∀ n : ℕ, HasFTaylorSeriesUpToOn n f p s := by
  constructor
  · intro H n; exact H.of_le le_top
  · intro H
    constructor
    · exact (H 0).zero_eq
    · intro m _
      apply (H m.succ).fderivWithin m (WithTop.coe_lt_coe.2 (lt_add_one m))
    · intro m _
      apply (H m).cont m le_rfl

/-- In the case that `n = ∞` we don't need the continuity assumption in
`HasFTaylorSeriesUpToOn`. -/
theorem hasFTaylorSeriesUpToOn_top_iff' :
    HasFTaylorSeriesUpToOn ∞ f p s ↔
      (∀ x ∈ s, (p x 0).uncurry0 = f x) ∧
        ∀ m : ℕ, ∀ x ∈ s, HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft s x :=
  -- Everything except for the continuity is trivial:
  ⟨fun h => ⟨h.1, fun m => h.2 m (WithTop.coe_lt_top m)⟩, fun h =>
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
  · exact fun h ↦ ⟨h.of_le (WithTop.coe_le_coe.2 (Nat.le_succ n)),
      h.fderivWithin _ (WithTop.coe_lt_coe.2 (lt_add_one n)), h.cont (n + 1) le_rfl⟩
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

#adaptation_note
/--
After https://github.com/leanprover/lean4/pull/4119,
without `set_option maxSynthPendingDepth 2` this proof needs substantial repair.
-/
set_option maxSynthPendingDepth 2 in
-- Porting note: this was split out from `hasFTaylorSeriesUpToOn_succ_iff_right` to avoid a timeout.
theorem HasFTaylorSeriesUpToOn.shift_of_succ
    {n : ℕ} (H : HasFTaylorSeriesUpToOn (n + 1 : ℕ) f p s) :
    (HasFTaylorSeriesUpToOn n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1))
      (fun x => (p x).shift)) s := by
  constructor
  · intro x _
    rfl
  · intro m (hm : (m : ℕ∞) < n) x (hx : x ∈ s)
    have A : (m.succ : ℕ∞) < n.succ := by
      rw [Nat.cast_lt] at hm ⊢
      exact Nat.succ_lt_succ hm
    change HasFDerivWithinAt ((continuousMultilinearCurryRightEquiv' 𝕜 m E F).symm ∘ (p · m.succ))
      (p x m.succ.succ).curryRight.curryLeft s x
    rw [((continuousMultilinearCurryRightEquiv' 𝕜 m E F).symm).comp_hasFDerivWithinAt_iff']
    convert H.fderivWithin _ A x hx
    ext y v
    change p x (m + 2) (snoc (cons y (init v)) (v (last _))) = p x (m + 2) (cons y v)
    rw [← cons_snoc_eq_snoc_cons, snoc_init_self]
  · intro m (hm : (m : ℕ∞) ≤ n)
    suffices A : ContinuousOn (p · (m + 1)) s from
      ((continuousMultilinearCurryRightEquiv' 𝕜 m E F).symm).continuous.comp_continuousOn A
    refine H.cont _ ?_
    rw [Nat.cast_le] at hm ⊢
    exact Nat.succ_le_succ hm

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. -/
theorem hasFTaylorSeriesUpToOn_succ_iff_right {n : ℕ} :
    HasFTaylorSeriesUpToOn (n + 1 : ℕ) f p s ↔
      (∀ x ∈ s, (p x 0).uncurry0 = f x) ∧
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
    · intro m (hm : (m : ℕ∞) < n.succ) x (hx : x ∈ s)
      cases' m with m
      · exact Hfderiv_zero x hx
      · have A : (m : ℕ∞) < n := by
          rw [Nat.cast_lt] at hm ⊢
          exact Nat.lt_of_succ_lt_succ hm
        have :
          HasFDerivWithinAt ((continuousMultilinearCurryRightEquiv' 𝕜 m E F).symm ∘ (p · m.succ))
            ((p x).shift m.succ).curryLeft s x := Htaylor.fderivWithin _ A x hx
        rw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff'] at this
        convert this
        ext y v
        change
          (p x (Nat.succ (Nat.succ m))) (cons y v) =
            (p x m.succ.succ) (snoc (cons y (init v)) (v (last _)))
        rw [← cons_snoc_eq_snoc_cons, snoc_init_self]
    · intro m (hm : (m : ℕ∞) ≤ n.succ)
      cases' m with m
      · have : DifferentiableOn 𝕜 (fun x => p x 0) s := fun x hx =>
          (Hfderiv_zero x hx).differentiableWithinAt
        exact this.continuousOn
      · refine (continuousMultilinearCurryRightEquiv' 𝕜 m E F).symm.comp_continuousOn_iff.mp ?_
        refine Htaylor.cont _ ?_
        rw [Nat.cast_le] at hm ⊢
        exact Nat.lt_succ_iff.mp hm


/-! ### Functions with a Taylor series on the whole space -/

/-- `HasFTaylorSeriesUpTo n f p` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`HasFDerivAt` but for higher order derivatives.

Notice that `p` does not sum up to `f` on the diagonal (`FormalMultilinearSeries.sum`), even if
`f` is analytic and `n = ∞`: an addition `1/m!` factor on the `m`th term is necessary for that. -/
structure HasFTaylorSeriesUpTo (n : ℕ∞) (f : E → F) (p : E → FormalMultilinearSeries 𝕜 E F) :
  Prop where
  zero_eq : ∀ x, (p x 0).uncurry0 = f x
  fderiv : ∀ m : ℕ, (m : ℕ∞) < n → ∀ x, HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x
  cont : ∀ m : ℕ, (m : ℕ∞) ≤ n → Continuous fun x => p x m

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
      rw [continuous_iff_continuousOn_univ]
      exact H.cont m hm
  · intro H
    constructor
    · exact fun x _ => H.zero_eq x
    · intro m hm x _
      rw [hasFDerivWithinAt_univ]
      exact H.fderiv m hm x
    · intro m hm
      rw [← continuous_iff_continuousOn_univ]
      exact H.cont m hm

theorem HasFTaylorSeriesUpTo.hasFTaylorSeriesUpToOn (h : HasFTaylorSeriesUpTo n f p) (s : Set E) :
    HasFTaylorSeriesUpToOn n f p s :=
  (hasFTaylorSeriesUpToOn_univ_iff.2 h).mono (subset_univ _)

theorem HasFTaylorSeriesUpTo.ofLe (h : HasFTaylorSeriesUpTo n f p) (hmn : m ≤ n) :
    HasFTaylorSeriesUpTo m f p := by
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h ⊢; exact h.of_le hmn

theorem HasFTaylorSeriesUpTo.continuous (h : HasFTaylorSeriesUpTo n f p) : Continuous f := by
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h
  rw [continuous_iff_continuousOn_univ]
  exact h.continuousOn

theorem hasFTaylorSeriesUpTo_zero_iff :
    HasFTaylorSeriesUpTo 0 f p ↔ Continuous f ∧ ∀ x, (p x 0).uncurry0 = f x := by
  simp [hasFTaylorSeriesUpToOn_univ_iff.symm, continuous_iff_continuousOn_univ,
    hasFTaylorSeriesUpToOn_zero_iff]

theorem hasFTaylorSeriesUpTo_top_iff :
    HasFTaylorSeriesUpTo ∞ f p ↔ ∀ n : ℕ, HasFTaylorSeriesUpTo n f p := by
  simp only [← hasFTaylorSeriesUpToOn_univ_iff, hasFTaylorSeriesUpToOn_top_iff]

/-- In the case that `n = ∞` we don't need the continuity assumption in
`HasFTaylorSeriesUpTo`. -/
theorem hasFTaylorSeriesUpTo_top_iff' :
    HasFTaylorSeriesUpTo ∞ f p ↔
      (∀ x, (p x 0).uncurry0 = f x) ∧
        ∀ (m : ℕ) (x), HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x := by
  simp only [← hasFTaylorSeriesUpToOn_univ_iff, hasFTaylorSeriesUpToOn_top_iff', mem_univ,
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
theorem hasFTaylorSeriesUpTo_succ_iff_right {n : ℕ} :
    HasFTaylorSeriesUpTo (n + 1 : ℕ) f p ↔
      (∀ x, (p x 0).uncurry0 = f x) ∧
        (∀ x, HasFDerivAt (fun y => p y 0) (p x 1).curryLeft x) ∧
          HasFTaylorSeriesUpTo n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1)) fun x =>
            (p x).shift := by
  simp only [hasFTaylorSeriesUpToOn_succ_iff_right, ← hasFTaylorSeriesUpToOn_univ_iff, mem_univ,
    forall_true_left, hasFDerivWithinAt_univ]
