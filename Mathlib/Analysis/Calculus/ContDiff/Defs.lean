/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Higher differentiability

A function is `C^1` on a domain if it is differentiable there, and its derivative is continuous.
By induction, it is `C^n` if it is `C^{n-1}` and its (n-1)-th derivative is `C^1` there or,
equivalently, if it is `C^1` and its derivative is `C^{n-1}`.
Finally, it is `C^∞` if it is `C^n` for all n.

We formalize these notions with predicates `ContDiffWithinAt`, `ContDiffAt`, `ContDiffOn` and
`ContDiff` saying that the function is `C^n` within a set at a point, at a point, on a set
and on the whole space respectively.

To avoid the issue of choice when choosing a derivative in sets where the derivative is not
necessarily unique, `ContDiffOn` is not defined directly in terms of the
regularity of the specific choice `iteratedFDerivWithin 𝕜 n f s` inside `s`, but in terms of the
existence of a nice sequence of derivatives, expressed with a predicate
`HasFTaylorSeriesUpToOn` defined in the file `FTaylorSeries`.

We prove basic properties of these notions.

## Main definitions and results
Let `f : E → F` be a map between normed vector spaces over a nontrivially normed field `𝕜`.

* `ContDiff 𝕜 n f`: expresses that `f` is `C^n`, i.e., it admits a Taylor series up to
  rank `n`.
* `ContDiffOn 𝕜 n f s`: expresses that `f` is `C^n` in `s`.
* `ContDiffAt 𝕜 n f x`: expresses that `f` is `C^n` around `x`.
* `ContDiffWithinAt 𝕜 n f s x`: expresses that `f` is `C^n` around `x` within the set `s`.

In sets of unique differentiability, `ContDiffOn 𝕜 n f s` can be expressed in terms of the
properties of `iteratedFDerivWithin 𝕜 m f s` for `m ≤ n`. In the whole space,
`ContDiff 𝕜 n f` can be expressed in terms of the properties of `iteratedFDeriv 𝕜 m f`
for `m ≤ n`.

## Implementation notes

The definitions in this file are designed to work on any field `𝕜`. They are sometimes slightly more
complicated than the naive definitions one would guess from the intuition over the real or complex
numbers, but they are designed to circumvent the lack of gluing properties and partitions of unity
in general. In the usual situations, they coincide with the usual definitions.

### Definition of `C^n` functions in domains

One could define `C^n` functions in a domain `s` by fixing an arbitrary choice of derivatives (this
is what we do with `iteratedFDerivWithin`) and requiring that all these derivatives up to `n` are
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
in space and order in our definition of `ContDiffWithinAt` and `ContDiffOn`.
The resulting definition is slightly more complicated to work with (in fact not so much), but it
gives rise to completely satisfactory theorems.

For instance, with this definition, a real function which is `C^m` (but not better) on `(-1/m, 1/m)`
for each natural `m` is by definition `C^∞` at `0`.

There is another issue with the definition of `ContDiffWithinAt 𝕜 n f s x`. We can
require the existence and good behavior of derivatives up to order `n` on a neighborhood of `x`
within `s`. However, this does not imply continuity or differentiability within `s` of the function
at `x` when `x` does not belong to `s`. Therefore, we require such existence and good behavior on
a neighborhood of `x` within `s ∪ {x}` (which appears as `insert x s` in this file).

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `⊤ : ℕ∞` with `∞`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

noncomputable section

open scoped Classical
open NNReal Topology Filter

/-- Smoothness exponent for analytic functions. Not implemented yet, `ω` smoothness is equivalent
to `∞` smoothness in current mathlib. -/
scoped [ContDiff] notation3 "ω" => (⊤ : WithTop ℕ∞)
/-- Smoothness exponent for infinitely differentiable functions. -/
scoped [ContDiff] notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

open ContDiff

open Set Fin Filter Function

universe u uE uF uG uX

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {s s₁ t u : Set E} {f f₁ : E → F} {g : F → G} {x x₀ : E} {c : F} {m n : WithTop ℕ∞}
  {p : E → FormalMultilinearSeries 𝕜 E F}

/-! ### Smooth functions within a set around a point -/

variable (𝕜)

/-- A function is continuously differentiable up to order `n` within a set `s` at a point `x` if
it admits continuous derivatives up to order `n` in a neighborhood of `x` in `s ∪ {x}`.
For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).

For instance, a real function which is `C^m` on `(-1/m, 1/m)` for each natural `m`, but not
better, is `C^∞` at `0` within `univ`.

We take the exponent `n` in `WithTop ℕ∞` to allow for an extension to analytic functions in the
future, but currently the notion is the same for `n = ∞` and `n = ω`.
-/
def ContDiffWithinAt (n : WithTop ℕ∞) (f : E → F) (s : Set E) (x : E) : Prop :=
  ∀ m : ℕ, m ≤ n → ∃ u ∈ 𝓝[insert x s] x,
    ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpToOn m f p u

variable {𝕜}

theorem contDiffWithinAt_nat {n : ℕ} :
    ContDiffWithinAt 𝕜 n f s x ↔ ∃ u ∈ 𝓝[insert x s] x,
      ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpToOn n f p u :=
  ⟨fun H => H n le_rfl, fun ⟨u, hu, p, hp⟩ _m hm => ⟨u, hu, p, hp.of_le (mod_cast hm)⟩⟩

theorem ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m ≤ n) :
    ContDiffWithinAt 𝕜 m f s x := fun k hk => h k (le_trans hk hmn)

theorem contDiffWithinAt_iff_forall_nat_le {n : ℕ∞} :
    ContDiffWithinAt 𝕜 n f s x ↔ ∀ m : ℕ, ↑m ≤ n → ContDiffWithinAt 𝕜 m f s x :=
  ⟨fun H _m hm => H.of_le (mod_cast hm), fun H m hm => H m (mod_cast hm) _ le_rfl⟩

theorem contDiffWithinAt_top : ContDiffWithinAt 𝕜 ∞ f s x ↔ ∀ n : ℕ, ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_iff_forall_nat_le.trans <| by simp only [forall_prop_of_true, le_top]

theorem ContDiffWithinAt.continuousWithinAt (h : ContDiffWithinAt 𝕜 n f s x) :
    ContinuousWithinAt f s x := by
  rcases h 0 bot_le with ⟨u, hu, p, H⟩
  rw [mem_nhdsWithin_insert] at hu
  exact (H.continuousOn.continuousWithinAt hu.1).mono_of_mem_nhdsWithin hu.2

theorem ContDiffWithinAt.congr_of_eventuallyEq (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s x := fun m hm =>
  let ⟨u, hu, p, H⟩ := h m hm
  ⟨{ x ∈ u | f₁ x = f x }, Filter.inter_mem hu (mem_nhdsWithin_insert.2 ⟨hx, h₁⟩), p,
    (H.mono (sep_subset _ _)).congr fun _ => And.right⟩

theorem Filter.EventuallyEq.congr_contDiffWithinAt (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H ↦ H.congr_of_eventuallyEq h₁.symm hx.symm, fun H ↦ H.congr_of_eventuallyEq h₁ hx⟩

@[deprecated (since := "2024-10-18")]
alias Filter.EventuallyEq.contDiffWithinAt_iff := Filter.EventuallyEq.congr_contDiffWithinAt

theorem ContDiffWithinAt.congr_of_eventuallyEq_insert (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventuallyEq (nhdsWithin_mono x (subset_insert x s) h₁)
    (mem_of_mem_nhdsWithin (mem_insert x s) h₁ : _)

theorem Filter.EventuallyEq.congr_contDiffWithinAt_of_insert (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H ↦ H.congr_of_eventuallyEq_insert h₁.symm, fun H ↦ H.congr_of_eventuallyEq_insert h₁⟩

theorem ContDiffWithinAt.congr_of_eventuallyEq_of_mem (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventuallyEq h₁ <| h₁.self_of_nhdsWithin hx

@[deprecated (since := "2024-10-18")]
alias ContDiffWithinAt.congr_of_eventually_eq' := ContDiffWithinAt.congr_of_eventuallyEq_of_mem

theorem Filter.EventuallyEq.congr_contDiffWithinAt_of_mem (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s):
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H ↦ H.congr_of_eventuallyEq_of_mem h₁.symm hx, fun H ↦ H.congr_of_eventuallyEq_of_mem h₁ hx⟩

theorem ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y)
    (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem self_mem_nhdsWithin h₁) hx

theorem contDiffWithinAt_congr (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : f₁ x = f x) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun h' ↦ h'.congr (fun x hx ↦ (h₁ x hx).symm) hx.symm, fun h' ↦  h'.congr h₁ hx⟩

theorem ContDiffWithinAt.congr_of_mem (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y)
    (hx : x ∈ s) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr h₁ (h₁ _ hx)

@[deprecated (since := "2024-10-18")]
alias ContDiffWithinAt.congr' := ContDiffWithinAt.congr_of_mem

theorem contDiffWithinAt_congr_of_mem (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_congr h₁ (h₁ x hx)

theorem ContDiffWithinAt.congr_of_insert (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : ∀ y ∈ insert x s, f₁ y = f y) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr (fun y hy ↦ h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

theorem contDiffWithinAt_congr_of_insert (h₁ : ∀ y ∈ insert x s, f₁ y = f y) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_congr (fun y hy ↦ h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

theorem ContDiffWithinAt.mono_of_mem_nhdsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E}
    (hst : s ∈ 𝓝[t] x) : ContDiffWithinAt 𝕜 n f t x := by
  intro m hm
  rcases h m hm with ⟨u, hu, p, H⟩
  exact ⟨u, nhdsWithin_le_of_mem (insert_mem_nhdsWithin_insert hst) hu, p, H⟩

@[deprecated (since := "2024-10-30")]
alias ContDiffWithinAt.mono_of_mem := ContDiffWithinAt.mono_of_mem_nhdsWithin

theorem ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : t ⊆ s) :
    ContDiffWithinAt 𝕜 n f t x :=
  h.mono_of_mem_nhdsWithin <| Filter.mem_of_superset self_mem_nhdsWithin hst

theorem ContDiffWithinAt.congr_mono
    (h : ContDiffWithinAt 𝕜 n f s x) (h' : EqOn f₁ f s₁) (h₁ : s₁ ⊆ s) (hx : f₁ x = f x) :
    ContDiffWithinAt 𝕜 n f₁ s₁ x :=
  (h.mono h₁).congr h' hx

theorem ContDiffWithinAt.congr_set (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E}
    (hst : s =ᶠ[𝓝 x] t) : ContDiffWithinAt 𝕜 n f t x := by
  rw [← nhdsWithin_eq_iff_eventuallyEq] at hst
  apply h.mono_of_mem_nhdsWithin <| hst ▸ self_mem_nhdsWithin

@[deprecated (since := "2024-10-23")]
alias ContDiffWithinAt.congr_nhds := ContDiffWithinAt.congr_set

theorem contDiffWithinAt_congr_set {t : Set E} (hst : s =ᶠ[𝓝 x] t) :
    ContDiffWithinAt 𝕜 n f s x ↔ ContDiffWithinAt 𝕜 n f t x :=
  ⟨fun h => h.congr_set hst, fun h => h.congr_set hst.symm⟩

@[deprecated (since := "2024-10-23")]
alias contDiffWithinAt_congr_nhds := contDiffWithinAt_congr_set

theorem contDiffWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    ContDiffWithinAt 𝕜 n f (s ∩ t) x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_congr_set (mem_nhdsWithin_iff_eventuallyEq.1 h).symm

theorem contDiffWithinAt_inter (h : t ∈ 𝓝 x) :
    ContDiffWithinAt 𝕜 n f (s ∩ t) x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_inter' (mem_nhdsWithin_of_mem_nhds h)

theorem contDiffWithinAt_insert_self :
    ContDiffWithinAt 𝕜 n f (insert x s) x ↔ ContDiffWithinAt 𝕜 n f s x := by
  simp_rw [ContDiffWithinAt, insert_idem]

theorem contDiffWithinAt_insert {y : E} :
    ContDiffWithinAt 𝕜 n f (insert y s) x ↔ ContDiffWithinAt 𝕜 n f s x := by
  rcases eq_or_ne x y with (rfl | h)
  · exact contDiffWithinAt_insert_self
  simp_rw [ContDiffWithinAt, insert_comm x y, nhdsWithin_insert_of_ne h]

alias ⟨ContDiffWithinAt.of_insert, ContDiffWithinAt.insert'⟩ := contDiffWithinAt_insert

protected theorem ContDiffWithinAt.insert (h : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n f (insert x s) x :=
  h.insert'

theorem contDiffWithinAt_diff_singleton {y : E} :
    ContDiffWithinAt 𝕜 n f (s \ {y}) x ↔ ContDiffWithinAt 𝕜 n f s x := by
  rw [← contDiffWithinAt_insert, insert_diff_singleton, contDiffWithinAt_insert]

/-- If a function is `C^n` within a set at a point, with `n ≥ 1`, then it is differentiable
within this set at this point. -/
theorem ContDiffWithinAt.differentiableWithinAt' (h : ContDiffWithinAt 𝕜 n f s x) (hn : 1 ≤ n) :
    DifferentiableWithinAt 𝕜 f (insert x s) x := by
  rcases h 1 hn with ⟨u, hu, p, H⟩
  rcases mem_nhdsWithin.1 hu with ⟨t, t_open, xt, tu⟩
  rw [inter_comm] at tu
  exact (differentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1 <|
    ((H.mono tu).differentiableOn le_rfl) x ⟨mem_insert x s, xt⟩

@[deprecated (since := "2024-10-10")]
alias ContDiffWithinAt.differentiable_within_at' := ContDiffWithinAt.differentiableWithinAt'

theorem ContDiffWithinAt.differentiableWithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : 1 ≤ n) :
    DifferentiableWithinAt 𝕜 f s x :=
  (h.differentiableWithinAt' hn).mono (subset_insert x s)

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem contDiffWithinAt_succ_iff_hasFDerivWithinAt {n : ℕ} :
    ContDiffWithinAt 𝕜 (n + 1) f s x ↔ ∃ u ∈ 𝓝[insert x s] x, ∃ f' : E → E →L[𝕜] F,
      (∀ x ∈ u, HasFDerivWithinAt f (f' x) u x) ∧ ContDiffWithinAt 𝕜 n f' u x := by
  constructor
  · intro h
    rcases h n.succ le_rfl with ⟨u, hu, p, Hp⟩
    refine
      ⟨u, hu, fun y => (continuousMultilinearCurryFin1 𝕜 E F) (p y 1), fun y hy =>
        Hp.hasFDerivWithinAt (mod_cast (Nat.le_add_left 1 n)) hy, ?_⟩
    intro m hm
    refine ⟨u, ?_, fun y : E => (p y).shift, ?_⟩
    · -- Porting note: without the explicit argument Lean is not sure of the type.
      convert @self_mem_nhdsWithin _ _ x u
      have : x ∈ insert x s := by simp
      exact insert_eq_of_mem (mem_of_mem_nhdsWithin this hu)
    · rw [show ((n.succ : ℕ) : WithTop ℕ∞) = n + 1 from rfl,
        hasFTaylorSeriesUpToOn_succ_iff_right] at Hp
      exact Hp.2.2.of_le (mod_cast hm)
  · rintro ⟨u, hu, f', f'_eq_deriv, Hf'⟩
    rw [show (n : WithTop ℕ∞) + 1 = (n + 1 : ℕ) from rfl, contDiffWithinAt_nat]
    rcases Hf' n le_rfl with ⟨v, hv, p', Hp'⟩
    refine ⟨v ∩ u, ?_, fun x => (p' x).unshift (f x), ?_⟩
    · apply Filter.inter_mem _ hu
      apply nhdsWithin_le_of_mem hu
      exact nhdsWithin_mono _ (subset_insert x u) hv
    · rw [show ((n.succ : ℕ) : WithTop ℕ∞) = n + 1 from rfl,
        hasFTaylorSeriesUpToOn_succ_iff_right]
      refine ⟨fun y _ => rfl, fun y hy => ?_, ?_⟩
      · change
          HasFDerivWithinAt (fun z => (continuousMultilinearCurryFin0 𝕜 E F).symm (f z))
            (FormalMultilinearSeries.unshift (p' y) (f y) 1).curryLeft (v ∩ u) y
        -- Porting note: needed `erw` here.
        -- https://github.com/leanprover-community/mathlib4/issues/5164
        erw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff']
        convert (f'_eq_deriv y hy.2).mono inter_subset_right
        rw [← Hp'.zero_eq y hy.1]
        ext z
        change ((p' y 0) (init (@cons 0 (fun _ => E) z 0))) (@cons 0 (fun _ => E) z 0 (last 0)) =
          ((p' y 0) 0) z
        congr
        norm_num [eq_iff_true_of_subsingleton]
      · convert (Hp'.mono inter_subset_left).congr fun x hx => Hp'.zero_eq x hx.1 using 1
        · ext x y
          change p' x 0 (init (@snoc 0 (fun _ : Fin 1 => E) 0 y)) y = p' x 0 0 y
          rw [init_snoc]
        · ext x k v y
          change p' x k (init (@snoc k (fun _ : Fin k.succ => E) v y))
            (@snoc k (fun _ : Fin k.succ => E) v y (last k)) = p' x k v y
          rw [snoc_last, init_snoc]

/-- A version of `contDiffWithinAt_succ_iff_hasFDerivWithinAt` where all derivatives
  are taken within the same set. -/
theorem contDiffWithinAt_succ_iff_hasFDerivWithinAt' {n : ℕ} :
    ContDiffWithinAt 𝕜 (n + 1) f s x ↔
      ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ ∃ f' : E → E →L[𝕜] F,
        (∀ x ∈ u, HasFDerivWithinAt f (f' x) s x) ∧ ContDiffWithinAt 𝕜 n f' s x := by
  refine ⟨fun hf => ?_, ?_⟩
  · obtain ⟨u, hu, f', huf', hf'⟩ := contDiffWithinAt_succ_iff_hasFDerivWithinAt.mp hf
    obtain ⟨w, hw, hxw, hwu⟩ := mem_nhdsWithin.mp hu
    rw [inter_comm] at hwu
    refine ⟨insert x s ∩ w, inter_mem_nhdsWithin _ (hw.mem_nhds hxw), inter_subset_left, f',
      fun y hy => ?_, ?_⟩
    · refine ((huf' y <| hwu hy).mono hwu).mono_of_mem_nhdsWithin ?_
      refine mem_of_superset ?_ (inter_subset_inter_left _ (subset_insert _ _))
      exact inter_mem_nhdsWithin _ (hw.mem_nhds hy.2)
    · exact hf'.mono_of_mem_nhdsWithin (nhdsWithin_mono _ (subset_insert _ _) hu)
  · rw [← contDiffWithinAt_insert, contDiffWithinAt_succ_iff_hasFDerivWithinAt,
      insert_eq_of_mem (mem_insert _ _)]
    rintro ⟨u, hu, hus, f', huf', hf'⟩
    exact ⟨u, hu, f', fun y hy => (huf' y hy).insert'.mono hus, hf'.insert.mono hus⟩

/-! ### Smooth functions within a set -/

variable (𝕜)

/-- A function is continuously differentiable up to `n` on `s` if, for any point `x` in `s`, it
admits continuous derivatives up to order `n` on a neighborhood of `x` in `s`.

For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).
-/
def ContDiffOn (n : WithTop ℕ∞) (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, ContDiffWithinAt 𝕜 n f s x

variable {𝕜}

theorem HasFTaylorSeriesUpToOn.contDiffOn {f' : E → FormalMultilinearSeries 𝕜 E F}
    (hf : HasFTaylorSeriesUpToOn n f f' s) : ContDiffOn 𝕜 n f s := by
  intro x hx m hm
  use s
  simp only [Set.insert_eq_of_mem hx, self_mem_nhdsWithin, true_and]
  exact ⟨f', hf.of_le (mod_cast hm)⟩

theorem ContDiffOn.contDiffWithinAt (h : ContDiffOn 𝕜 n f s) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 n f s x :=
  h x hx

theorem ContDiffWithinAt.contDiffOn' {m : ℕ} (hm : m ≤ n)
    (h : ContDiffWithinAt 𝕜 n f s x) :
    ∃ u, IsOpen u ∧ x ∈ u ∧ ContDiffOn 𝕜 m f (insert x s ∩ u) := by
  rcases h m hm with ⟨t, ht, p, hp⟩
  rcases mem_nhdsWithin.1 ht with ⟨u, huo, hxu, hut⟩
  rw [inter_comm] at hut
  exact ⟨u, huo, hxu, (hp.mono hut).contDiffOn⟩

theorem ContDiffWithinAt.contDiffOn {m : ℕ} (hm : m ≤ n) (h : ContDiffWithinAt 𝕜 n f s x) :
    ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ ContDiffOn 𝕜 m f u :=
  let ⟨_u, uo, xu, h⟩ := h.contDiffOn' hm
  ⟨_, inter_mem_nhdsWithin _ (uo.mem_nhds xu), inter_subset_left, h⟩

/-- A function is `C^n` within a set at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
theorem contDiffWithinAt_iff_contDiffOn_nhds {n : ℕ} :
    ContDiffWithinAt 𝕜 n f s x ↔ ∃ u ∈ 𝓝[insert x s] x, ContDiffOn 𝕜 n f u := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases h.contDiffOn le_rfl with ⟨u, hu, h'u⟩
    exact ⟨u, hu, h'u.2⟩
  · rcases h with ⟨u, u_mem, hu⟩
    have : x ∈ u := mem_of_mem_nhdsWithin (mem_insert x s) u_mem
    exact (hu x this).mono_of_mem_nhdsWithin (nhdsWithin_mono _ (subset_insert x s) u_mem)

protected theorem ContDiffWithinAt.eventually {n : ℕ} (h : ContDiffWithinAt 𝕜 n f s x) :
    ∀ᶠ y in 𝓝[insert x s] x, ContDiffWithinAt 𝕜 n f s y := by
  rcases h.contDiffOn le_rfl with ⟨u, hu, _, hd⟩
  have : ∀ᶠ y : E in 𝓝[insert x s] x, u ∈ 𝓝[insert x s] y ∧ y ∈ u :=
    (eventually_eventually_nhdsWithin.2 hu).and hu
  refine this.mono fun y hy => (hd y hy.2).mono_of_mem_nhdsWithin ?_
  exact nhdsWithin_mono y (subset_insert _ _) hy.1

theorem ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m ≤ n) : ContDiffOn 𝕜 m f s := fun x hx =>
  (h x hx).of_le hmn

theorem ContDiffOn.of_succ {n : ℕ} (h : ContDiffOn 𝕜 (n + 1) f s) : ContDiffOn 𝕜 n f s :=
  h.of_le <| WithTop.coe_le_coe.mpr le_self_add

theorem ContDiffOn.one_of_succ {n : ℕ} (h : ContDiffOn 𝕜 (n + 1) f s) : ContDiffOn 𝕜 1 f s :=
  h.of_le <| WithTop.coe_le_coe.mpr le_add_self

theorem contDiffOn_iff_forall_nat_le {n : ℕ∞} :
    ContDiffOn 𝕜 n f s ↔ ∀ m : ℕ, ↑m ≤ n → ContDiffOn 𝕜 m f s :=
  ⟨fun H _ hm => H.of_le (mod_cast hm), fun H x hx m hm => H m (mod_cast hm) x hx m le_rfl⟩

theorem contDiffOn_top : ContDiffOn 𝕜 ∞ f s ↔ ∀ n : ℕ, ContDiffOn 𝕜 n f s :=
  contDiffOn_iff_forall_nat_le.trans <| by simp only [le_top, forall_prop_of_true]

theorem contDiffOn_all_iff_nat :
    (∀ (n : ℕ∞), ContDiffOn 𝕜 n f s) ↔ ∀ n : ℕ, ContDiffOn 𝕜 n f s := by
  refine ⟨fun H n => H n, ?_⟩
  rintro H (_ | n)
  exacts [contDiffOn_top.2 H, H n]

theorem ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s) : ContinuousOn f s := fun x hx =>
  (h x hx).continuousWithinAt

theorem ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : ∀ x ∈ s, f₁ x = f x) :
    ContDiffOn 𝕜 n f₁ s := fun x hx => (h x hx).congr h₁ (h₁ x hx)

theorem contDiffOn_congr (h₁ : ∀ x ∈ s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s ↔ ContDiffOn 𝕜 n f s :=
  ⟨fun H => H.congr fun x hx => (h₁ x hx).symm, fun H => H.congr h₁⟩

theorem ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (hst : t ⊆ s) : ContDiffOn 𝕜 n f t :=
  fun x hx => (h x (hst hx)).mono hst

theorem ContDiffOn.congr_mono (hf : ContDiffOn 𝕜 n f s) (h₁ : ∀ x ∈ s₁, f₁ x = f x) (hs : s₁ ⊆ s) :
    ContDiffOn 𝕜 n f₁ s₁ :=
  (hf.mono hs).congr h₁

/-- If a function is `C^n` on a set with `n ≥ 1`, then it is differentiable there. -/
theorem ContDiffOn.differentiableOn (h : ContDiffOn 𝕜 n f s) (hn : 1 ≤ n) :
    DifferentiableOn 𝕜 f s := fun x hx => (h x hx).differentiableWithinAt hn

/-- If a function is `C^n` around each point in a set, then it is `C^n` on the set. -/
theorem contDiffOn_of_locally_contDiffOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ ContDiffOn 𝕜 n f (s ∩ u)) : ContDiffOn 𝕜 n f s := by
  intro x xs
  rcases h x xs with ⟨u, u_open, xu, hu⟩
  apply (contDiffWithinAt_inter _).1 (hu x ⟨xs, xu⟩)
  exact IsOpen.mem_nhds u_open xu

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem contDiffOn_succ_iff_hasFDerivWithinAt {n : ℕ} :
    ContDiffOn 𝕜 (n + 1) f s ↔
      ∀ x ∈ s, ∃ u ∈ 𝓝[insert x s] x, ∃ f' : E → E →L[𝕜] F,
        (∀ x ∈ u, HasFDerivWithinAt f (f' x) u x) ∧ ContDiffOn 𝕜 n f' u := by
  constructor
  · intro h x hx
    rcases (h x hx) n.succ le_rfl with ⟨u, hu, p, Hp⟩
    refine
      ⟨u, hu, fun y => (continuousMultilinearCurryFin1 𝕜 E F) (p y 1), fun y hy =>
        Hp.hasFDerivWithinAt (mod_cast (Nat.le_add_left 1 n)) hy, ?_⟩
    rw [show (n.succ : WithTop ℕ∞) = (n : ℕ) + 1 from rfl,
      hasFTaylorSeriesUpToOn_succ_iff_right] at Hp
    intro z hz m hm
    refine ⟨u, ?_, fun x : E => (p x).shift, Hp.2.2.of_le (mod_cast hm)⟩
    -- Porting note: without the explicit arguments `convert` can not determine the type.
    convert @self_mem_nhdsWithin _ _ z u
    exact insert_eq_of_mem hz
  · intro h x hx
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt]
    rcases h x hx with ⟨u, u_nhbd, f', hu, hf'⟩
    have : x ∈ u := mem_of_mem_nhdsWithin (mem_insert _ _) u_nhbd
    exact ⟨u, u_nhbd, f', hu, hf' x this⟩

@[simp]
theorem contDiffOn_zero : ContDiffOn 𝕜 0 f s ↔ ContinuousOn f s := by
  refine ⟨fun H => H.continuousOn, fun H => fun x hx m hm ↦ ?_⟩
  have : (m : WithTop ℕ∞) = 0 := le_antisymm (mod_cast hm) bot_le
  rw [this]
  refine ⟨insert x s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_⟩
  rw [hasFTaylorSeriesUpToOn_zero_iff]
  exact ⟨by rwa [insert_eq_of_mem hx], fun x _ => by simp [ftaylorSeriesWithin]⟩

theorem contDiffWithinAt_zero (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 0 f s x ↔ ∃ u ∈ 𝓝[s] x, ContinuousOn f (s ∩ u) := by
  constructor
  · intro h
    obtain ⟨u, H, p, hp⟩ := h 0 le_rfl
    refine ⟨u, ?_, ?_⟩
    · simpa [hx] using H
    · simp only [Nat.cast_zero, hasFTaylorSeriesUpToOn_zero_iff] at hp
      exact hp.1.mono inter_subset_right
  · rintro ⟨u, H, hu⟩
    rw [← contDiffWithinAt_inter' H]
    have h' : x ∈ s ∩ u := ⟨hx, mem_of_mem_nhdsWithin hx H⟩
    exact (contDiffOn_zero.mpr hu).contDiffWithinAt h'

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylorSeriesWithin 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
protected theorem ContDiffOn.ftaylorSeriesWithin (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) :
    HasFTaylorSeriesUpToOn n f (ftaylorSeriesWithin 𝕜 f s) s := by
  constructor
  · intro x _
    simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.curry0_apply,
      iteratedFDerivWithin_zero_apply]
  · intro m hm x hx
    have : (m + 1 : ℕ) ≤ n := ENat.add_one_natCast_le_withTop_of_lt hm
    rcases (h x hx).of_le this _ le_rfl with ⟨u, hu, p, Hp⟩
    rw [insert_eq_of_mem hx] at hu
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [inter_comm] at ho
    have : p x m.succ = ftaylorSeriesWithin 𝕜 f s x m.succ := by
      change p x m.succ = iteratedFDerivWithin 𝕜 m.succ f s x
      rw [← iteratedFDerivWithin_inter_open o_open xo]
      exact (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hx, xo⟩
    rw [← this, ← hasFDerivWithinAt_inter (IsOpen.mem_nhds o_open xo)]
    have A : ∀ y ∈ s ∩ o, p y m = ftaylorSeriesWithin 𝕜 f s y m := by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFDerivWithin 𝕜 m f s y
      rw [← iteratedFDerivWithin_inter_open o_open yo]
      exact
        (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn (mod_cast Nat.le_succ m)
          (hs.inter o_open) ⟨hy, yo⟩
    exact
      ((Hp.mono ho).fderivWithin m (mod_cast lt_add_one m) x ⟨hx, xo⟩).congr
        (fun y hy => (A y hy).symm) (A x ⟨hx, xo⟩).symm
  · intro m hm
    apply continuousOn_of_locally_continuousOn
    intro x hx
    rcases h x hx m (mod_cast hm) with ⟨u, hu, p, Hp⟩
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [insert_eq_of_mem hx] at ho
    rw [inter_comm] at ho
    refine ⟨o, o_open, xo, ?_⟩
    have A : ∀ y ∈ s ∩ o, p y m = ftaylorSeriesWithin 𝕜 f s y m := by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFDerivWithin 𝕜 m f s y
      rw [← iteratedFDerivWithin_inter_open o_open yo]
      exact (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hy, yo⟩
    exact ((Hp.mono ho).cont m le_rfl).congr fun y hy => (A y hy).symm

theorem contDiffOn_of_continuousOn_differentiableOn {n : ℕ∞}
    (Hcont : ∀ m : ℕ, m ≤ n → ContinuousOn (fun x => iteratedFDerivWithin 𝕜 m f s x) s)
    (Hdiff : ∀ m : ℕ, m < n →
      DifferentiableOn 𝕜 (fun x => iteratedFDerivWithin 𝕜 m f s x) s) :
    ContDiffOn 𝕜 n f s := by
  intro x hx m hm
  rw [insert_eq_of_mem hx]
  refine ⟨s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_⟩
  constructor
  · intro y _
    simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.curry0_apply,
      iteratedFDerivWithin_zero_apply]
  · intro k hk y hy
    convert (Hdiff k (lt_of_lt_of_le (mod_cast hk) (mod_cast hm)) y hy).hasFDerivWithinAt
  · intro k hk
    exact Hcont k (le_trans (mod_cast hk) (mod_cast hm))

theorem contDiffOn_of_differentiableOn {n : ℕ∞}
    (h : ∀ m : ℕ, m ≤ n → DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 m f s) s) :
    ContDiffOn 𝕜 n f s :=
  contDiffOn_of_continuousOn_differentiableOn (fun m hm => (h m hm).continuousOn) fun m hm =>
    h m (le_of_lt hm)

theorem ContDiffOn.continuousOn_iteratedFDerivWithin {m : ℕ} (h : ContDiffOn 𝕜 n f s)
    (hmn : m ≤ n) (hs : UniqueDiffOn 𝕜 s) : ContinuousOn (iteratedFDerivWithin 𝕜 m f s) s :=
  (h.ftaylorSeriesWithin hs).cont m (mod_cast hmn)

theorem ContDiffOn.differentiableOn_iteratedFDerivWithin {m : ℕ} (h : ContDiffOn 𝕜 n f s)
    (hmn : m < n) (hs : UniqueDiffOn 𝕜 s) :
    DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 m f s) s := fun x hx =>
  ((h.ftaylorSeriesWithin hs).fderivWithin m (mod_cast hmn) x hx).differentiableWithinAt

theorem ContDiffWithinAt.differentiableWithinAt_iteratedFDerivWithin {m : ℕ}
    (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m < n) (hs : UniqueDiffOn 𝕜 (insert x s)) :
    DifferentiableWithinAt 𝕜 (iteratedFDerivWithin 𝕜 m f s) s x := by
  rcases h.contDiffOn' (ENat.add_one_natCast_le_withTop_of_lt hmn) with ⟨u, uo, xu, hu⟩
  set t := insert x s ∩ u
  have A : t =ᶠ[𝓝[≠] x] s := by
    simp only [set_eventuallyEq_iff_inf_principal, ← nhdsWithin_inter']
    rw [← inter_assoc, nhdsWithin_inter_of_mem', ← diff_eq_compl_inter, insert_diff_of_mem,
      diff_eq_compl_inter]
    exacts [rfl, mem_nhdsWithin_of_mem_nhds (uo.mem_nhds xu)]
  have B : iteratedFDerivWithin 𝕜 m f s =ᶠ[𝓝 x] iteratedFDerivWithin 𝕜 m f t :=
    iteratedFDerivWithin_eventually_congr_set' _ A.symm _
  have C : DifferentiableWithinAt 𝕜 (iteratedFDerivWithin 𝕜 m f t) t x :=
    hu.differentiableOn_iteratedFDerivWithin (Nat.cast_lt.2 m.lt_succ_self) (hs.inter uo) x
      ⟨mem_insert _ _, xu⟩
  rw [differentiableWithinAt_congr_set' _ A] at C
  exact C.congr_of_eventuallyEq (B.filter_mono inf_le_left) B.self_of_nhds

theorem contDiffOn_iff_continuousOn_differentiableOn {n : ℕ∞} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔
      (∀ m : ℕ, m ≤ n → ContinuousOn (fun x => iteratedFDerivWithin 𝕜 m f s x) s) ∧
        ∀ m : ℕ, m < n → DifferentiableOn 𝕜 (fun x => iteratedFDerivWithin 𝕜 m f s x) s :=
  ⟨fun h => ⟨fun _m hm => h.continuousOn_iteratedFDerivWithin (mod_cast hm) hs, fun _m hm =>
      h.differentiableOn_iteratedFDerivWithin (mod_cast hm) hs⟩,
    fun h => contDiffOn_of_continuousOn_differentiableOn h.1 h.2⟩

theorem contDiffOn_succ_of_fderivWithin {n : ℕ} (hf : DifferentiableOn 𝕜 f s)
    (h : ContDiffOn 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) : ContDiffOn 𝕜 (n + 1) f s := by
  intro x hx
  rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt, insert_eq_of_mem hx]
  exact
    ⟨s, self_mem_nhdsWithin, fderivWithin 𝕜 f s, fun y hy => (hf y hy).hasFDerivWithinAt, h x hx⟩

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (expressed with `fderivWithin`) is `C^n`. -/
theorem contDiffOn_succ_iff_fderivWithin {n : ℕ} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 n (fun y => fderivWithin 𝕜 f s y) s := by
  refine ⟨fun H => ?_, fun h => contDiffOn_succ_of_fderivWithin h.1 h.2⟩
  refine ⟨H.differentiableOn le_add_self, fun x hx => ?_⟩
  rcases contDiffWithinAt_succ_iff_hasFDerivWithinAt.1 (H x hx) with ⟨u, hu, f', hff', hf'⟩
  rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
  rw [inter_comm, insert_eq_of_mem hx] at ho
  have := hf'.mono ho
  rw [contDiffWithinAt_inter' (mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds o_open xo))] at this
  apply this.congr_of_eventuallyEq_of_mem _ hx
  have : o ∩ s ∈ 𝓝[s] x := mem_nhdsWithin.2 ⟨o, o_open, xo, Subset.refl _⟩
  rw [inter_comm] at this
  refine Filter.eventuallyEq_of_mem this fun y hy => ?_
  have A : fderivWithin 𝕜 f (s ∩ o) y = f' y :=
    ((hff' y (ho hy)).mono ho).fderivWithin (hs.inter o_open y hy)
  rwa [fderivWithin_inter (o_open.mem_nhds hy.2)] at A

theorem contDiffOn_succ_iff_hasFDerivWithin {n : ℕ} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      ∃ f' : E → E →L[𝕜] F, ContDiffOn 𝕜 n f' s ∧ ∀ x, x ∈ s → HasFDerivWithinAt f (f' x) s x := by
  rw [contDiffOn_succ_iff_fderivWithin hs]
  refine ⟨fun h => ⟨fderivWithin 𝕜 f s, h.2, fun x hx => (h.1 x hx).hasFDerivWithinAt⟩, fun h => ?_⟩
  rcases h with ⟨f', h1, h2⟩
  refine ⟨fun x hx => (h2 x hx).differentiableWithinAt, fun x hx => ?_⟩
  exact (h1 x hx).congr_of_mem (fun y hy => (h2 y hy).fderivWithin (hs y hy)) hx

/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (expressed with `fderiv`) is `C^n`. -/
theorem contDiffOn_succ_iff_fderiv_of_isOpen {n : ℕ} (hs : IsOpen s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 n (fun y => fderiv 𝕜 f y) s := by
  rw [contDiffOn_succ_iff_fderivWithin hs.uniqueDiffOn]
  exact Iff.rfl.and (contDiffOn_congr fun x hx ↦ fderivWithin_of_isOpen hs hx)

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative (expressed with `fderivWithin`) is `C^∞`. -/
theorem contDiffOn_top_iff_fderivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 ∞ f s ↔
      DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (fun y => fderivWithin 𝕜 f s y) s := by
  constructor
  · intro h
    refine ⟨h.differentiableOn (mod_cast le_top), ?_⟩
    refine contDiffOn_top.2 fun n => ((contDiffOn_succ_iff_fderivWithin hs).1 ?_).2
    exact h.of_le (mod_cast le_top)
  · intro h
    refine contDiffOn_top.2 fun n => ?_
    have A : (n : ℕ∞) ≤ ∞ := mod_cast le_top
    apply ((contDiffOn_succ_iff_fderivWithin hs).2 ⟨h.1, h.2.of_le A⟩).of_le
    exact_mod_cast (Nat.le_succ n)

/-- A function is `C^∞` on an open domain if and only if it is differentiable there, and its
derivative (expressed with `fderiv`) is `C^∞`. -/
theorem contDiffOn_top_iff_fderiv_of_isOpen (hs : IsOpen s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (fun y => fderiv 𝕜 f y) s := by
  rw [contDiffOn_top_iff_fderivWithin hs.uniqueDiffOn]
  exact Iff.rfl.and <| contDiffOn_congr fun x hx ↦ fderivWithin_of_isOpen hs hx

protected theorem ContDiffOn.fderivWithin (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hmn : m + 1 ≤ n) : ContDiffOn 𝕜 m (fun y => fderivWithin 𝕜 f s y) s := by
  rcases le_or_lt ∞ n with hn | hn
  · have : ContDiffOn 𝕜 ∞ (fun y ↦ fderivWithin 𝕜 f s y) s :=
      ((contDiffOn_top_iff_fderivWithin hs).1 (hf.of_le hn)).2
    intro x hx k hk
    exact this x hx k (mod_cast le_top)
  · match m with
    | ω => simpa using hmn.trans_lt hn
    | ∞ => simpa using hmn.trans_lt hn
    | (m : ℕ) =>
      change (m.succ : ℕ∞) ≤ n at hmn
      exact ((contDiffOn_succ_iff_fderivWithin hs).1 (hf.of_le hmn)).2

theorem ContDiffOn.fderiv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (fun y => fderiv 𝕜 f y) s :=
  (hf.fderivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (fderivWithin_of_isOpen hs hx).symm

theorem ContDiffOn.continuousOn_fderivWithin (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hn : 1 ≤ n) : ContinuousOn (fun x => fderivWithin 𝕜 f s x) s :=
  ((contDiffOn_succ_iff_fderivWithin hs).1 (h.of_le hn)).2.continuousOn

theorem ContDiffOn.continuousOn_fderiv_of_isOpen (h : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hn : 1 ≤ n) : ContinuousOn (fun x => fderiv 𝕜 f x) s :=
  ((contDiffOn_succ_iff_fderiv_of_isOpen hs).1 (h.of_le hn)).2.continuousOn

/-- The following lemma will be removed when the definition of `C^ω` will be corrected. For now,
it is only there as a convenient shortcut. -/
theorem contDiffOn_infty_iff_contDiffOn_omega :
    ContDiffOn 𝕜 ∞ f s ↔ ContDiffOn 𝕜 ω f s := by
  have A (m : ℕ) : m ≤ ∞ := mod_cast le_top
  simp [ContDiffOn, ContDiffWithinAt, hasFTaylorSeriesUpTo_top_iff, A]

/-! ### Smooth functions at a point -/

variable (𝕜)

/-- A function is continuously differentiable up to `n` at a point `x` if, for any integer `k ≤ n`,
there is a neighborhood of `x` where `f` admits derivatives up to order `n`, which are continuous.
-/
def ContDiffAt (n : WithTop ℕ∞) (f : E → F) (x : E) : Prop :=
  ContDiffWithinAt 𝕜 n f univ x

variable {𝕜}

theorem contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f univ x ↔ ContDiffAt 𝕜 n f x :=
  Iff.rfl

theorem contDiffAt_top : ContDiffAt 𝕜 ∞ f x ↔ ∀ n : ℕ, ContDiffAt 𝕜 n f x := by
  simp [← contDiffWithinAt_univ, contDiffWithinAt_top]

theorem ContDiffAt.contDiffWithinAt (h : ContDiffAt 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x :=
  h.mono (subset_univ _)

theorem ContDiffWithinAt.contDiffAt (h : ContDiffWithinAt 𝕜 n f s x) (hx : s ∈ 𝓝 x) :
    ContDiffAt 𝕜 n f x := by rwa [ContDiffAt, ← contDiffWithinAt_inter hx, univ_inter]

theorem contDiffWithinAt_iff_contDiffAt (h : s ∈ 𝓝 x) :
    ContDiffWithinAt 𝕜 n f s x ↔ ContDiffAt 𝕜 n f x := by
  rw [← univ_inter s, contDiffWithinAt_inter h, contDiffWithinAt_univ]

theorem IsOpen.contDiffOn_iff (hs : IsOpen s) :
    ContDiffOn 𝕜 n f s ↔ ∀ ⦃a⦄, a ∈ s → ContDiffAt 𝕜 n f a :=
  forall₂_congr fun _ => contDiffWithinAt_iff_contDiffAt ∘ hs.mem_nhds

theorem ContDiffOn.contDiffAt (h : ContDiffOn 𝕜 n f s) (hx : s ∈ 𝓝 x) :
    ContDiffAt 𝕜 n f x :=
  (h _ (mem_of_mem_nhds hx)).contDiffAt hx

theorem ContDiffAt.congr_of_eventuallyEq (h : ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) :
    ContDiffAt 𝕜 n f₁ x :=
  h.congr_of_eventuallyEq_of_mem (by rwa [nhdsWithin_univ]) (mem_univ x)

theorem ContDiffAt.of_le (h : ContDiffAt 𝕜 n f x) (hmn : m ≤ n) : ContDiffAt 𝕜 m f x :=
  ContDiffWithinAt.of_le h hmn

theorem ContDiffAt.continuousAt (h : ContDiffAt 𝕜 n f x) : ContinuousAt f x := by
  simpa [continuousWithinAt_univ] using h.continuousWithinAt

@[simp]
theorem contDiffWithinAt_compl_self :
    ContDiffWithinAt 𝕜 n f {x}ᶜ x ↔ ContDiffAt 𝕜 n f x := by
  rw [compl_eq_univ_diff, contDiffWithinAt_diff_singleton, contDiffWithinAt_univ]

/-- If a function is `C^n` with `n ≥ 1` at a point, then it is differentiable there. -/
theorem ContDiffAt.differentiableAt (h : ContDiffAt 𝕜 n f x) (hn : 1 ≤ n) :
    DifferentiableAt 𝕜 f x := by
  simpa [hn, differentiableWithinAt_univ] using h.differentiableWithinAt

nonrec lemma ContDiffAt.contDiffOn {m : ℕ} (h : ContDiffAt 𝕜 n f x) (hm : m ≤ n) :
    ∃ u ∈ 𝓝 x, ContDiffOn 𝕜 m f u := by
  simpa [nhdsWithin_univ] using h.contDiffOn hm

/-- A function is `C^(n + 1)` at a point iff locally, it has a derivative which is `C^n`. -/
theorem contDiffAt_succ_iff_hasFDerivAt {n : ℕ} :
    ContDiffAt 𝕜 (n + 1) f x ↔
      ∃ f' : E → E →L[𝕜] F, (∃ u ∈ 𝓝 x, ∀ x ∈ u, HasFDerivAt f (f' x) x) ∧ ContDiffAt 𝕜 n f' x := by
  rw [← contDiffWithinAt_univ, contDiffWithinAt_succ_iff_hasFDerivWithinAt]
  simp only [nhdsWithin_univ, exists_prop, mem_univ, insert_eq_of_mem]
  constructor
  · rintro ⟨u, H, f', h_fderiv, h_cont_diff⟩
    rcases mem_nhds_iff.mp H with ⟨t, htu, ht, hxt⟩
    refine ⟨f', ⟨t, ?_⟩, h_cont_diff.contDiffAt H⟩
    refine ⟨mem_nhds_iff.mpr ⟨t, Subset.rfl, ht, hxt⟩, ?_⟩
    intro y hyt
    refine (h_fderiv y (htu hyt)).hasFDerivAt ?_
    exact mem_nhds_iff.mpr ⟨t, htu, ht, hyt⟩
  · rintro ⟨f', ⟨u, H, h_fderiv⟩, h_cont_diff⟩
    refine ⟨u, H, f', ?_, h_cont_diff.contDiffWithinAt⟩
    intro x hxu
    exact (h_fderiv x hxu).hasFDerivWithinAt

protected theorem ContDiffAt.eventually {n : ℕ} (h : ContDiffAt 𝕜 n f x) :
    ∀ᶠ y in 𝓝 x, ContDiffAt 𝕜 n f y := by
  simpa [nhdsWithin_univ] using ContDiffWithinAt.eventually h

/-! ### Smooth functions -/

variable (𝕜)

/-- A function is continuously differentiable up to `n` if it admits derivatives up to
order `n`, which are continuous. Contrary to the case of definitions in domains (where derivatives
might not be unique) we do not need to localize the definition in space or time.
-/
def ContDiff (n : WithTop ℕ∞) (f : E → F) : Prop :=
  ∃ p : E → FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpTo n f p

variable {𝕜}

/-- If `f` has a Taylor series up to `n`, then it is `C^n`. -/
theorem HasFTaylorSeriesUpTo.contDiff {f' : E → FormalMultilinearSeries 𝕜 E F}
    (hf : HasFTaylorSeriesUpTo n f f') : ContDiff 𝕜 n f :=
  ⟨f', hf⟩

theorem contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n f := by
  constructor
  · intro H
    use ftaylorSeriesWithin 𝕜 f univ
    rw [← hasFTaylorSeriesUpToOn_univ_iff]
    exact H.ftaylorSeriesWithin uniqueDiffOn_univ
  · rintro ⟨p, hp⟩ x _ m hm
    exact ⟨univ, Filter.univ_sets _, p, (hp.hasFTaylorSeriesUpToOn univ).of_le
      (mod_cast hm)⟩

theorem contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ ∀ x, ContDiffAt 𝕜 n f x := by
  simp [← contDiffOn_univ, ContDiffOn, ContDiffAt]

theorem ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiffAt 𝕜 n f x :=
  contDiff_iff_contDiffAt.1 h x

theorem ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f) : ContDiffWithinAt 𝕜 n f s x :=
  h.contDiffAt.contDiffWithinAt

/-- The following lemma will be removed when the definition of `C^ω` will be corrected. For now,
it is only there as a convenient shortcut. -/
theorem contDiff_infty_iff_contDiff_omega :
    ContDiff 𝕜 ∞ f ↔ ContDiff 𝕜 ω f := by
  simp [ContDiff, hasFTaylorSeriesUpTo_top_iff]

theorem contDiff_top : ContDiff 𝕜 ∞ f ↔ ∀ n : ℕ, ContDiff 𝕜 n f := by
  simp [contDiffOn_univ.symm, contDiffOn_top]

theorem contDiff_all_iff_nat : (∀ (n : ℕ∞), ContDiff 𝕜 n f) ↔ ∀ n : ℕ, ContDiff 𝕜 n f := by
  simp only [← contDiffOn_univ, contDiffOn_all_iff_nat]

theorem ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiffOn 𝕜 n f s :=
  (contDiffOn_univ.2 h).mono (subset_univ _)

@[simp]
theorem contDiff_zero : ContDiff 𝕜 0 f ↔ Continuous f := by
  rw [← contDiffOn_univ, continuous_iff_continuousOn_univ]
  exact contDiffOn_zero

theorem contDiffAt_zero : ContDiffAt 𝕜 0 f x ↔ ∃ u ∈ 𝓝 x, ContinuousOn f u := by
  rw [← contDiffWithinAt_univ]; simp [contDiffWithinAt_zero, nhdsWithin_univ]

theorem contDiffAt_one_iff :
    ContDiffAt 𝕜 1 f x ↔
      ∃ f' : E → E →L[𝕜] F, ∃ u ∈ 𝓝 x, ContinuousOn f' u ∧ ∀ x ∈ u, HasFDerivAt f (f' x) x := by
  rw [show (1 : WithTop ℕ∞) = (0 : ℕ) + 1 from rfl, contDiffAt_succ_iff_hasFDerivAt]
  simp_rw [show ((0 : ℕ) : WithTop ℕ∞) = 0 from rfl, contDiffAt_zero,
    exists_mem_and_iff antitone_bforall antitone_continuousOn, and_comm]

theorem ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m ≤ n) : ContDiff 𝕜 m f :=
  contDiffOn_univ.1 <| (contDiffOn_univ.2 h).of_le hmn

theorem ContDiff.of_succ {n : ℕ} (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 n f :=
  h.of_le <| WithTop.coe_le_coe.mpr le_self_add

theorem ContDiff.one_of_succ {n : ℕ} (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 1 f :=
  h.of_le <| WithTop.coe_le_coe.mpr le_add_self

theorem ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuous f :=
  contDiff_zero.1 (h.of_le bot_le)

/-- If a function is `C^n` with `n ≥ 1`, then it is differentiable. -/
theorem ContDiff.differentiable (h : ContDiff 𝕜 n f) (hn : 1 ≤ n) : Differentiable 𝕜 f :=
  differentiableOn_univ.1 <| (contDiffOn_univ.2 h).differentiableOn hn

theorem contDiff_iff_forall_nat_le {n : ℕ∞} :
    ContDiff 𝕜 n f ↔ ∀ m : ℕ, ↑m ≤ n → ContDiff 𝕜 m f := by
  simp_rw [← contDiffOn_univ]; exact contDiffOn_iff_forall_nat_le

/-- A function is `C^(n+1)` iff it has a `C^n` derivative. -/
theorem contDiff_succ_iff_hasFDerivAt {n : ℕ} :
    ContDiff 𝕜 (n + 1) f ↔
      ∃ f' : E → E →L[𝕜] F, ContDiff 𝕜 n f' ∧ ∀ x, HasFDerivAt f (f' x) x := by
  simp only [← contDiffOn_univ, ← hasFDerivWithinAt_univ,
    contDiffOn_succ_iff_hasFDerivWithin uniqueDiffOn_univ, Set.mem_univ, forall_true_left]

theorem contDiff_one_iff_hasFDerivAt : ContDiff 𝕜 1 f ↔
    ∃ f' : E → E →L[𝕜] F, Continuous f' ∧ ∀ x, HasFDerivAt f (f' x) x := by
  convert contDiff_succ_iff_hasFDerivAt using 4; simp

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylorSeriesWithin 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem contDiff_iff_ftaylorSeries :
    ContDiff 𝕜 n f ↔ HasFTaylorSeriesUpTo n f (ftaylorSeries 𝕜 f) := by
  constructor
  · rw [← contDiffOn_univ, ← hasFTaylorSeriesUpToOn_univ_iff, ← ftaylorSeriesWithin_univ]
    exact fun h => ContDiffOn.ftaylorSeriesWithin h uniqueDiffOn_univ
  · intro h; exact ⟨ftaylorSeries 𝕜 f, h⟩

theorem contDiff_iff_continuous_differentiable {n : ℕ∞} :
    ContDiff 𝕜 n f ↔
      (∀ m : ℕ, m ≤ n → Continuous fun x => iteratedFDeriv 𝕜 m f x) ∧
        ∀ m : ℕ, m < n → Differentiable 𝕜 fun x => iteratedFDeriv 𝕜 m f x := by
  simp [contDiffOn_univ.symm, continuous_iff_continuousOn_univ, differentiableOn_univ.symm,
    iteratedFDerivWithin_univ, contDiffOn_iff_continuousOn_differentiableOn uniqueDiffOn_univ]

/-- If `f` is `C^n` then its `m`-times iterated derivative is continuous for `m ≤ n`. -/
theorem ContDiff.continuous_iteratedFDeriv {m : ℕ} (hm : m ≤ n) (hf : ContDiff 𝕜 n f) :
    Continuous fun x => iteratedFDeriv 𝕜 m f x :=
  (contDiff_iff_continuous_differentiable.mp (hf.of_le hm)).1 m le_rfl

/-- If `f` is `C^n` then its `m`-times iterated derivative is differentiable for `m < n`. -/
theorem ContDiff.differentiable_iteratedFDeriv {m : ℕ} (hm : m < n) (hf : ContDiff 𝕜 n f) :
    Differentiable 𝕜 fun x => iteratedFDeriv 𝕜 m f x :=
  (contDiff_iff_continuous_differentiable.mp
    (hf.of_le (ENat.add_one_natCast_le_withTop_of_lt hm))).2 m (mod_cast lt_add_one m)

theorem contDiff_of_differentiable_iteratedFDeriv {n : ℕ∞}
    (h : ∀ m : ℕ, m ≤ n → Differentiable 𝕜 (iteratedFDeriv 𝕜 m f)) : ContDiff 𝕜 n f :=
  contDiff_iff_continuous_differentiable.2
    ⟨fun m hm => (h m hm).continuous, fun m hm => h m (le_of_lt hm)⟩

/-- A function is `C^(n + 1)` if and only if it is differentiable,
and its derivative (formulated in terms of `fderiv`) is `C^n`. -/
theorem contDiff_succ_iff_fderiv {n : ℕ} :
    ContDiff 𝕜 (n + 1) f ↔ Differentiable 𝕜 f ∧ ContDiff 𝕜 n fun y => fderiv 𝕜 f y := by
  simp only [← contDiffOn_univ, ← differentiableOn_univ, ← fderivWithin_univ,
    contDiffOn_succ_iff_fderivWithin uniqueDiffOn_univ]

theorem contDiff_one_iff_fderiv : ContDiff 𝕜 1 f ↔ Differentiable 𝕜 f ∧ Continuous (fderiv 𝕜 f) :=
  contDiff_succ_iff_fderiv.trans <| Iff.rfl.and contDiff_zero

/-- A function is `C^∞` if and only if it is differentiable,
and its derivative (formulated in terms of `fderiv`) is `C^∞`. -/
theorem contDiff_top_iff_fderiv :
    ContDiff 𝕜 ∞ f ↔ Differentiable 𝕜 f ∧ ContDiff 𝕜 ∞ fun y => fderiv 𝕜 f y := by
  simp only [← contDiffOn_univ, ← differentiableOn_univ, ← fderivWithin_univ]
  rw [contDiffOn_top_iff_fderivWithin uniqueDiffOn_univ]

theorem ContDiff.continuous_fderiv (h : ContDiff 𝕜 n f) (hn : 1 ≤ n) :
    Continuous fun x => fderiv 𝕜 f x :=
  (contDiff_succ_iff_fderiv.1 (h.of_le hn)).2.continuous

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
theorem ContDiff.continuous_fderiv_apply (h : ContDiff 𝕜 n f) (hn : 1 ≤ n) :
    Continuous fun p : E × E => (fderiv 𝕜 f p.1 : E → F) p.2 :=
  have A : Continuous fun q : (E →L[𝕜] F) × E => q.1 q.2 := isBoundedBilinearMap_apply.continuous
  have B : Continuous fun p : E × E => (fderiv 𝕜 f p.1, p.2) :=
    ((h.continuous_fderiv hn).comp continuous_fst).prod_mk continuous_snd
  A.comp B
