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

lemma Filter.Germ.ContinuousAt.tendsto {x : X} {f : Germ (𝓝 x) Y} (hf : f.ContinuousAt) :
    f.Tendsto (𝓝 f.value) :=
  continuousAt_iff_tendsto.1 hf

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
lemma Filter.Germ.Continuous.continuousAt {x : X} {f : Germ (𝓝 x) Y} (hf : f.Continuous) :
    f.ContinuousAt := by
  revert hf
  exact f.inductionOn fun f hf ↦ (continuous_coe_iff.1 hf).self_of_nhds

/-- If a germ `f` at `x` is continuous and `g : Y → Z` is continuous near `f.value`,
`f.map g` is continuous. -/
lemma Filter.Germ.Continuous.map {x : X} {f : Germ (𝓝 x) Y} (hf : f.Continuous) {g : Y → Z}
    (hg : ∀ᶠ y in 𝓝 f.value, ContinuousAt g y) : (f.map g).Continuous := by
  revert hf hg; refine f.inductionOn fun f hf hg ↦ ?_
  simp only [continuous_coe_iff, value_coe, map_coe] at hf hg ⊢
  exact (hf.and (hf.self_of_nhds.eventually hg)).mp <| .of_forall fun x h ↦ h.2.comp h.1

/-- `ContinuousGerm x Y` is the type of all continuous germs of functions `f : X → Y` at `x : X`. -/
structure ContinuousGerm (x : X) (Y : Type*) [TopologicalSpace Y] where
  /-- The underlying germ. -/
  toGerm : Germ (𝓝 x) Y
  continuous : toGerm.Continuous

@[elab_as_elim]
lemma ContinuousGerm.inductionOn {x : X} (f : ContinuousGerm x Y) {p : ContinuousGerm x Y → Prop}
    (h : ∀ (f : X → Y) (hf : (f : Germ (𝓝 x) Y).Continuous), p ⟨f, hf⟩) : p f := by
  obtain ⟨f, hf⟩ := f
  revert hf
  exact f.inductionOn fun f hf ↦ h f hf

/-- The composition of continuous germs `f` at `y` and `g` at `x`, provided that `g` sends `x` to
`y`. -/
def ContinuousGerm.comp {x : X} {y : Y} (f : ContinuousGerm y Z) (g : ContinuousGerm x Y)
    (h : g.toGerm.value = y) : ContinuousGerm x Z where
  toGerm := f.toGerm.compTendsto' g.toGerm (h ▸ g.continuous.continuousAt.tendsto)
  continuous := f.inductionOn fun f hf ↦ g.continuous.map <| by simpa [h] using hf

@[simp]
lemma ContinuousGerm.comp_value {x : X} {y : Y} (f : ContinuousGerm y Z) (g : ContinuousGerm x Y)
    (h : g.toGerm.value = y) : (f.comp g h).toGerm.value = f.toGerm.value :=
  f.inductionOn fun f hf ↦ by simp [comp, h]

/-- `PointedContinuousGerm x y` is the type of all continuous germs at `x` taking `x` to `y`. -/
structure PointedContinuousGerm (x : X) (y : Y) extends ContinuousGerm x Y where
  value_eq : toGerm.value = y

/-- The composition of continuous germs taking `x` to `y` and `y` to `z`. -/
def PointedContinuousGerm.comp {x : X} {y : Y} {z : Z} (f : PointedContinuousGerm y z)
    (g : PointedContinuousGerm x y) : PointedContinuousGerm x z where
  toContinuousGerm := f.toContinuousGerm.comp g.toContinuousGerm g.value_eq
  value_eq := by simp  [f.value_eq]
