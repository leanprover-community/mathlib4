/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.Topology.Germ

/-! # Germs of continuous maps

In this file we define the type `ContinuousGerm x Y` of germs of continuous maps `X → Y` at `x`.
-/

public section

open scoped Topology

open Filter

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A germ `f` at `x` is called continuous at `x` if it is represented by functions that are
continuous at `x`.

Note that this is weaker than being represented by a function that is continuous on an open
neighbourhood around `x`: the functions representing `x` may still have discontinuities arbitrarily
close to `x`. -/
protected def Filter.Germ.ContinuousAt {x : X} (f : Germ (𝓝 x) Y) : Prop :=
  Germ.liftOn f (fun f ↦ ContinuousAt f x) fun _ _ h ↦ (continuousAt_congr h).eq

lemma ContinuousAt.germ {x : X} {f : X → Y} (hf : ContinuousAt f x) :
    (f : Germ (𝓝 x) Y).ContinuousAt :=
  hf

@[simp]
lemma Filter.Germ.continuousAt_coe_iff {x : X} (f : X → Y) :
    (f : Germ (𝓝 x) Y).ContinuousAt ↔ ContinuousAt f x :=
  Iff.rfl

lemma Filter.Germ.continuousAt_iff_tendsto {x : X} {f : Germ (𝓝 x) Y} :
    f.ContinuousAt ↔ f.Tendsto (𝓝 f.value) := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep f
  rfl

/-- A germ `f` at `x` is called continuous if it is represented by functions that are continuous
near (i.e. on some open neighbourhood of) `x`.

Note that this is weaker than being represented by a globally continuous function, even for germs
between nice spaces like compact subsets of ℝ². -/
protected def Filter.Germ.Continuous {x : X} (f : Germ (𝓝 x) Y) : Prop :=
  RestrictGermPredicate (fun _ f ↦ f.ContinuousAt) {x} x f

lemma Continuous.germ {f : X → Y} (hf : Continuous f) (x : X) : (f : Germ (𝓝 x) Y).Continuous :=
  forall_restrictGermPredicate_of_forall (fun _ ↦ hf.continuousAt.germ) x

/-- A germ at `x` is continuous iff all functions representing it are continuous at all points
close enough to `x`. -/
lemma Filter.Germ.continuous_iff_forall {x : X} {f : Germ (𝓝 x) Y} :
    f.Continuous ↔ ∀ f' : X → Y, f = f' → ∀ᶠ x' in 𝓝 x, ContinuousAt f' x' := by
  simp [Germ.Continuous, restrictGermPredicate_iff_forall]

/-- A germ at `x` is continuous iff at least one function representing it is continuous at all
points close enough to `x`. -/
lemma Filter.Germ.continuous_iff_exists {x : X} {f : Germ (𝓝 x) Y} :
    f.Continuous ↔ ∃ f' : X → Y, f = f' ∧ ∀ᶠ x' in 𝓝 x, ContinuousAt f' x' := by
  simp [Germ.Continuous, restrictGermPredicate_iff_exists]

/-- The germ of a function `f` at `x` is continuous iff `f` is continuous at all points
close enough to `x`. -/
@[simp]
lemma Filter.Germ.continuous_coe_iff {x : X} {f : X → Y} :
    (f : Germ (𝓝 x) Y).Continuous ↔ ∀ᶠ x' in 𝓝 x, ContinuousAt f x' := by
  simp [Germ.Continuous]

/-- The germ of a function `f` at `x` is continuous iff `f` is continuous on a neighbourhood of
`x`. -/
lemma Filter.Germ.continuous_coe_iff' {x : X} {f : X → Y} :
    (f : Germ (𝓝 x) Y).Continuous ↔ ∃ u ∈ 𝓝 x, ContinuousOn f u := by
  simp [eventually_continuousAt_iff]

/-- Every continuous germ at `x` is in particular continuous at `x`. -/
lemma Filter.Germ.continuousAt {x : X} {f : Germ (𝓝 x) Y} (hf : f.Continuous) :
    f.ContinuousAt := by
  revert hf; refine f.inductionOn fun f hf ↦ ?_
  exact (Filter.Eventually.self_of_nhds (Filter.Germ.continuous_coe_iff.1 hf):)

/-- `ContinuousGerm x Y` is the type of all continuous germs of functions `f : X → Y` at `x : X`. -/
structure ContinuousGerm (x : X) (Y : Type*) [TopologicalSpace Y] where
  /-- The underlying germ. -/
  toGerm : Germ (𝓝 x) Y
  continuous : toGerm.Continuous

/-- `PointedContinuousGerm x y` is the type of all continuous germs at `x` taking `x` to `y`. -/
structure PointedContinuousGerm (x : X) (y : Y) extends ContinuousGerm x Y where
  value_eq : toGerm.value = y
