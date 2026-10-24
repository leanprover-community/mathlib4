/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.Notation

/-!
# Converting a function into a section of the trivial bundle

TODO: make a proper doc-string for all of this, and describe what's happening here.

TODO: clean up this file, and make sure all lemmas that belong here actually are

-/

@[expose] public section

open Topology

open scoped Manifold ContDiff

namespace Bundle.Trivialization

section trivilization_topology

variable {B F Z : Type*} [TopologicalSpace B] [TopologicalSpace F]

section fiber_bundle

variable {E : B → Type*} [TopologicalSpace (TotalSpace F E)] (e : Trivialization F (π F E))

/-- Turn sections of a fiber bundle into function into the model fiber using a trivialization. -/
def secToFun (σ : (b : B) → E b) : B → F :=
  fun b ↦ e (σ b) |>.2

@[simp]
lemma secToFun_apply_of_eq {σ : (b : B) → E b} {v : TotalSpace F E} (h : σ v.proj = v) :
    e.secToFun σ v.proj = (e v).2 := by
  simp [secToFun, h]

lemma secToFun_congr {σ σ' : (b : B) → E b} {b : B} (h : σ b = σ' b) :
    e.secToFun σ b = e.secToFun σ' b := by
  simp [secToFun, h]

lemma apply_total_eventuallyEq
    {x : B} (hx : x ∈ e.baseSet) (σ : Π x, E x) :
    e ∘ T%σ =ᶠ[𝓝 x] fun x ↦ (x, e.secToFun σ x) := by
  filter_upwards [e.baseSet_mem_nhds hx] with y hy
  ext
  · exact e.coe_coe_fst hy
  · simp [secToFun]

-- @[congr]
-- lemma secToFun_congr {σ σ' : (b : B) → E b} {b : B} (h : ∀ x, x = b → σ x = σ' x) :
--     e.secToFun σ b = e.secToFun σ' b := by
--   simp [secToFun, h]
--
-- example  {σ σ' : (b : B) → E b} {b : B} (h : ∀ x, x = b → σ x = σ' x) :
--     e.secToFun σ b = e.secToFun σ' b := by
--   simp? +contextual [h]
section
variable [(x : B) → Nonempty (E x)]

/-- Turn functions into the model fiber of a fiber bundle into sections using a trivialization. -/
noncomputable def funToSec (s : B → F) : (b : B) → E b :=
  fun b ↦ e.symm b (s b)

lemma totalSpace_mk_funToSec {x : B} (hx : x ∈ e.baseSet) (s : B → F) :
    T% (e.funToSec s) =ᶠ[𝓝 x] e.invFun ∘ fun x ↦ (x, s x) := by
  filter_upwards [e.baseSet_mem_nhds hx] with y hy
  exact mk_symm e hy (s y)

@[simp]
lemma apply_funToSec {x : B} (hx : x ∈ e.baseSet) (s : B → F) :
    e ⟨x, e.funToSec s x⟩ = (x, s x) := by
  simp [funToSec, e.apply_mk_symm hx]

lemma snd_apply_funToSec {x : B} (hx : x ∈ e.baseSet) (s : B → F) :
    (e ⟨x, e.funToSec s x⟩).2 = s x := by
  simp [funToSec, e.apply_mk_symm hx]

@[simp]
lemma funToSec_proj_eq {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) {s : B → F}
    (hsv : s v.proj = (e v).2) :
    e.funToSec s v.proj = v.2 := by
  simp [funToSec, hsv, e.symm_proj_apply v hv]

@[simp]
lemma mk_funToSec_of_eq {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) {s : B → F}
    (h : s v.proj = (e v).2) : (⟨v.proj, e.funToSec s v.proj⟩ : TotalSpace F E) = v := by
  simp [funToSec, h, hv]

lemma funToSec_congr {s s' : B → F} {b : B} (h : s b = s' b) :
    e.funToSec s b = e.funToSec s' b := by
  simp [funToSec, h]

@[simp]
lemma secToFun_funToSec_eventuallyEq {x : B} (hx : x ∈ e.baseSet) (s : B → F) :
    e.secToFun (e.funToSec s) =ᶠ[𝓝 x] s := by
  filter_upwards [e.baseSet_mem_nhds hx] with y hy
  simp [secToFun, funToSec, hy]

@[simp]
lemma secToFun_funToSec {x : B} (hx : x ∈ e.baseSet) (s : B → F) :
    e.secToFun (e.funToSec s) x = s x :=
  (e.secToFun_funToSec_eventuallyEq hx s).eq_of_nhds
  -- TODO: understand why the following fails
  -- by
  --   have := e.secToFun_funToSec_eventuallyEq hx s
  --   apply?

@[simp]
lemma funToSec_secToFun_eventually_eq {x : B} (hx : x ∈ e.baseSet) (σ : (b : B) → E b) :
    ∀ᶠ x' in 𝓝 x, e.funToSec (e.secToFun σ) x' = σ x' := by
  filter_upwards [e.baseSet_mem_nhds hx] with y hy
  simp [secToFun, funToSec, hy]

@[simp]
lemma funToSec_secToFun {x : B} (hx : x ∈ e.baseSet) (σ : (b : B) → E b) :
    e.funToSec (e.secToFun σ) x = σ x :=
  (e.funToSec_secToFun_eventually_eq hx σ).self_of_nhds

section
variable (σ : (b : B) → E b)

@[simp]
lemma total_funToSec_secToFun_eventuallyEq {x : B} (hx : x ∈ e.baseSet) (σ : (b : B) → E b) :
    T% (e.funToSec <| e.secToFun σ) =ᶠ[𝓝 x] T% σ := by
  filter_upwards [e.baseSet_mem_nhds hx] with y hy
  simp [secToFun, funToSec, hy]

@[simp]
lemma total_funToSec_secToFun_eq {x : B} (hx : x ∈ e.baseSet) (σ : (b : B) → E b) :
    T% (e.funToSec <| e.secToFun σ) x = T% σ x :=
  e.total_funToSec_secToFun_eventuallyEq hx σ |>.self_of_nhds

end

@[simp]
lemma total_secToFun_funToSeq_eventually_eq {x : B} (hx : x ∈ e.baseSet) (s : B → F) :
    ∀ᶠ x' in 𝓝 x, T% (e.secToFun <| e.funToSec s) x' = T% s x' := by
  filter_upwards [e.baseSet_mem_nhds hx] with y hy
  simp [secToFun, funToSec, hy]

@[simp]
lemma total_secToFun_funToSeq {x : B} (hx : x ∈ e.baseSet) (s : B → F) :
    T% (e.secToFun <| e.funToSec s) x = T% s x :=
  e.total_secToFun_funToSeq_eventually_eq hx s |>.self_of_nhds

end

end fiber_bundle

end trivilization_topology

end Bundle.Trivialization
