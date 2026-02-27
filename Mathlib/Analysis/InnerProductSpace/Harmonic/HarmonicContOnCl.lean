/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, based on code by Yury Kudryashov
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Functions Harmonic on a Domain and Continuous on Its Closure

Many theorems in harmonic analysis assume that a function is harmonic on a domain and is continuous
on its closure. In this file we define a predicate `HarmonicContOnCl` that expresses this property
and prove basic facts about this predicate.
-/

@[expose] public section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f f₁ f₂ : E → F}
  {x : E} {s : Set E} {c : ℝ}

open Laplacian Metric Topology

namespace InnerProductSpace

/--
A predicate saying that a function is harmonic on a set and is continuous on its closure. This is a
common assumption in harmonic analysis.
-/
structure HarmonicContOnCl (f : E → F) (s : Set E) : Prop where
  protected harmonicOnNhd : HarmonicOnNhd f s
  protected continuousOn : ContinuousOn f (closure s)

theorem HarmonicOnNhd.harmonicContOnCl (h : HarmonicOnNhd f (closure s)) :
    HarmonicContOnCl f s :=
  ⟨h.mono subset_closure, h.continuousOn⟩

theorem IsClosed.harmonicContOnCl_iff (hs : IsClosed s) :
    HarmonicContOnCl f s ↔ HarmonicOnNhd f s where
  mp := (·.1 · ·)
  mpr h := by
    rw [← hs.closure_eq] at h
    exact h.harmonicContOnCl

theorem harmonicContOnCl_const {c : F} : HarmonicContOnCl (fun _ : E ↦ c) s :=
  ⟨harmonicOnNhd_const c, continuousOn_const⟩

namespace HarmonicContOnCl

theorem continuousOn_ball [NormedSpace ℝ E] {x : E} {r : ℝ} (h : HarmonicContOnCl f (ball x r)) :
    ContinuousOn f (closedBall x r) := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · rw [closedBall_zero]
    exact continuousOn_singleton f x
  · rw [← closure_ball x hr]
    exact h.continuousOn

theorem mk_ball {x : E} {r : ℝ} (hd : HarmonicOnNhd f (ball x r))
    (hc : ContinuousOn f (closedBall x r)) :
    HarmonicContOnCl f (ball x r) :=
  ⟨hd, hc.mono <| closure_ball_subset_closedBall⟩

theorem contDiffAt (h : HarmonicContOnCl f s) (hx : x ∈ s) :
    ContDiffAt ℝ 2 f x := (h.1 x hx).1

theorem differentiableAt (h : HarmonicContOnCl f s) (hx : x ∈ s) :
    DifferentiableAt ℝ f x := (h.contDiffAt hx).differentiableAt two_ne_zero

theorem mono {t : Set E} (h : HarmonicContOnCl f s) (ht : t ⊆ s) :
    HarmonicContOnCl f t := ⟨h.harmonicOnNhd.mono ht, h.continuousOn.mono (closure_mono ht)⟩

@[to_fun] theorem add (hf₁ : HarmonicContOnCl f₁ s) (hf₂ : HarmonicContOnCl f₂ s) :
    HarmonicContOnCl (f₁ + f₂) s := ⟨hf₁.1.add hf₂.1, hf₁.2.add hf₂.2⟩

@[to_fun] theorem add_const (hf : HarmonicContOnCl f s) (c : F) :
    HarmonicContOnCl (f + fun _ ↦ c) s := hf.add harmonicContOnCl_const

@[to_fun] theorem const_add (hf : HarmonicContOnCl f s) (c : F) :
  HarmonicContOnCl ((fun _ ↦ c) + f) s := harmonicContOnCl_const.add hf

@[to_fun] theorem neg (hf : HarmonicContOnCl f s) :
    HarmonicContOnCl  (-f) s := ⟨hf.1.neg, hf.2.neg⟩

@[to_fun] theorem sub (hf₁ : HarmonicContOnCl f₁ s) (hf₂ : HarmonicContOnCl f₂ s) :
    HarmonicContOnCl (f₁ - f₂) s := ⟨hf₁.1.sub hf₂.1, hf₁.2.sub hf₂.2⟩

@[to_fun] theorem sub_const (hf : HarmonicContOnCl f s) (c : F) :
    HarmonicContOnCl (f - fun _ ↦ c) s := hf.sub harmonicContOnCl_const

@[to_fun] theorem const_sub (hf : HarmonicContOnCl f s) (c : F) :
    HarmonicContOnCl ((fun _ ↦ c) - f) s := harmonicContOnCl_const.sub hf

@[to_fun] theorem const_smul (hf : HarmonicContOnCl f s) (c : ℝ) :
    HarmonicContOnCl (c • f) s := ⟨hf.1.const_smul, hf.2.const_smul c⟩

end HarmonicContOnCl

end InnerProductSpace
