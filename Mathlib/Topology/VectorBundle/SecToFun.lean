/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Topology.FiberBundle.SecToFun
public import Mathlib.Topology.VectorBundle.Basic

import Mathlib.Geometry.Manifold.Notation

/-!
# Lemmas about `SecToFun` and `FunToSec` in topological vector bundles

Additional lemmas about `SecToFun` and `FunToSec` in topological vector bundles.
-/

public section

open Topology
open scoped Manifold ContDiff

namespace Bundle.Trivialization

section

variable {R B F : Type*} {E : B → Type*} [Semiring R]
  [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [AddCommMonoid F] [Module R F] [(x : B) → AddCommMonoid (E x)] [(x : B) → Module R (E x)]
  (e : Trivialization F (π F E))

@[simp]
lemma linearMapAt_funToSec [e.IsLinear R] {x : B} (hx : x ∈ e.baseSet) (s : B → F) :
    (Trivialization.linearMapAt R e x) (e.funToSec s x) = s x := by
  simp [funToSec, hx]

lemma secToFun_map_smul [e.IsLinear R] {σ : (b : B) → E b}
    {b : B} (hb : b ∈ e.baseSet) (a : R) :
    e.secToFun (a • σ) b = a • e.secToFun σ b := by
  simp [secToFun, e.map_smul hb]

variable (R)

lemma secToFun_map_add [e.IsLinear R] (σ σ' : (b : B) → E b)
    {b : B} (hb : b ∈ e.baseSet) :
    e.secToFun (σ + σ') b = e.secToFun σ b + e.secToFun σ' b := by
  simp [secToFun, e.map_add R hb]

lemma secToFun_map_zero [e.IsLinear R] {b : B} (hb : b ∈ e.baseSet) :
    e.secToFun 0 b = 0 := by
  simp [secToFun, e.map_zero R hb]

end

section

variable (R : Type*) {B F : Type*} {E : B → Type*} [NontriviallyNormedField R]
  [(x : B) → AddCommMonoid (E x)] [(x : B) → Module R (E x)]
  [NormedAddCommGroup F] [NormedSpace R F] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [(x : B) → TopologicalSpace (E x)] [FiberBundle F E]
  (e : Trivialization F (π F E))

lemma funToSec_map_add [e.IsLinear R] {s s' : B → F}
    {x : B} (hx : x ∈ e.baseSet) :
    e.funToSec (s + s') x = e.funToSec s x + e.funToSec s' x := by
  simp [funToSec, e.symm_map_add R, hx]

lemma funToSec_map_add_eventuallyEq [e.IsLinear R] (s s' : B → F)
    {x : B} (hx : x ∈ e.baseSet) :
    ∀ᶠ x' in 𝓝 x, e.funToSec (s + s') x' = e.funToSec s x' + e.funToSec s' x' :=
  e.eventually hx fun _ ↦ e.funToSec_map_add R

@[simp]
lemma funToSec_map_zero [e.IsLinear R] {x : B} (hx : x ∈ e.baseSet) :
    e.funToSec (0 : B → F) x = 0 :=
  e.symm_map_zero R hx

lemma funToSec_map_zero_eventuallyEq [e.IsLinear R] {x : B} (hx : x ∈ e.baseSet) :
    ∀ᶠ x' in 𝓝 x, e.funToSec (0 : B → F) x' = 0 :=
  e.eventually hx fun _ ↦ e.funToSec_map_zero R

variable {R}

lemma funToSec_map_smul_const [e.IsLinear R] {x : B} (hx : x ∈ e.baseSet)
    (a : R) (s : B → F) :
    e.funToSec (a • s) x = a • e.funToSec s x :=
  e.symm_map_smul hx ..

lemma funToSec_map_smul [e.IsLinear R] {x : B} (hx : x ∈ e.baseSet)
    (a : B → R) (s : B → F) : e.funToSec (a • s) x = a x • e.funToSec s x :=
  e.symm_map_smul hx ..

end

end Bundle.Trivialization
