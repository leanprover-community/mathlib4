/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!

# Indistinguishability of processes

In Mathlib, `E`-valued stochastic processes over a probability space `Ω` and indexed by a type `ι`
are represented as a family of `E`-valued random variables `X : ι → Ω → E` rather than as an
`ι → E`-valued random variable, following the convention on paper.

Two stochastic processes are said to be *indistinguishable* if they are almost everywhere equal
as `ι → E`-valued random variable, i.e. `(fun ω t ↦ X t ω) =ᵐ[P] (fun ω t ↦ Y t ω)`. This spelling
creates a lot of friction when manipulating indistinguishable processes, making it harder to use
for instance the `gcongr` tactic.

In this file we introduce a predicate `Indistinguishable P X Y`, denoted `X ≡ᵐ[P] Y`, which states
that `∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω`. The symbol `≡` can be typed with `\==`.

-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y Z : ι → Ω → E}

/-- Two processes are indistinguishable if almost surely they agree everywhere. -/
@[expose]
def Indistinguishable (P : Measure Ω) (X Y : ι → Ω → E) : Prop :=
  ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω

/-- Two processes are indistinguishable if almost surely they agree everywhere. -/
notation3:50 X " ≡ᵐ[" P:50 "] " Y:50 => Indistinguishable P X Y

namespace Indistinguishable

@[refl, simp]
protected lemma refl (P : Measure Ω) (X : ι → Ω → E) : X ≡ᵐ[P] X :=
  .of_forall fun _ _ ↦ rfl

protected lemma rfl : X ≡ᵐ[P] X := by rfl

@[symm]
protected lemma symm (h : X ≡ᵐ[P] Y) : Y ≡ᵐ[P] X := by
  filter_upwards [h] with ω h t using (h t).symm

@[trans]
protected lemma trans (h1 : X ≡ᵐ[P] Y) (h2 : Y ≡ᵐ[P] Z) : X ≡ᵐ[P] Z := by
  filter_upwards [h1, h2] with ω h t
  grind

instance : IsTrans (ι → Ω → E) (· ≡ᵐ[P] ·) := ⟨fun _ _ _ ↦ .trans⟩

protected lemma fun_comp {F : Type*} (h : X ≡ᵐ[P] Y) (f : E → F) :
    (fun t ω ↦ f (X t ω)) ≡ᵐ[P] (fun t ω ↦ f (Y t ω)) := by
  filter_upwards [h] with ω h t
  rw [h]

protected lemma fun_comp₂ {F G : Type*} {Z T : ι → Ω → F} (h1 : X ≡ᵐ[P] Y)
    (h2 : Z ≡ᵐ[P] T) (f : E → F → G) :
    (fun t ω ↦ f (X t ω) (Z t ω)) ≡ᵐ[P] (fun t ω ↦ f (Y t ω) (T t ω)) := by
  filter_upwards [h1, h2] with ω h1 h2 t
  rw [h1, h2]

@[to_additive (attr := to_fun, gcongr)]
protected lemma inv [Inv E] (h : X ≡ᵐ[P] Y) :
    X⁻¹ ≡ᵐ[P] Y⁻¹ := h.fun_comp _

@[to_additive (attr := to_fun, gcongr)]
protected lemma mul [Mul E] {Z T : ι → Ω → E} (h1 : X ≡ᵐ[P] Y) (h2 : Z ≡ᵐ[P] T) :
    X * Z ≡ᵐ[P] Y * T := h1.fun_comp₂ h2 _

@[to_additive (attr := to_fun, gcongr)]
protected lemma div [Div E] {Z T : ι → Ω → E} (h1 : X ≡ᵐ[P] Y) (h2 : Z ≡ᵐ[P] T) :
    X / Z ≡ᵐ[P] Y / T := h1.fun_comp₂ h2 _

@[to_additive (attr := to_fun, gcongr)]
protected lemma smul {F : Type*} {Z T : ι → Ω → F} [SMul F E] (h1 : X ≡ᵐ[P] Y)
    (h2 : Z ≡ᵐ[P] T) :
    Z • X ≡ᵐ[P] T • Y := h2.fun_comp₂ h1 _

@[to_additive (attr := to_fun, gcongr)]
protected lemma const_smul {F : Type*} [SMul F E] {c : F} (h : X ≡ᵐ[P] Y) :
    c • X ≡ᵐ[P] c • Y := h.fun_comp _

protected lemma prodMk {F : Type*} {Z T : ι → Ω → F} (h1 : X ≡ᵐ[P] Y) (h2 : Z ≡ᵐ[P] T) :
    (fun t ω ↦ (X t ω, Z t ω)) ≡ᵐ[P] (fun t ω ↦ (Y t ω, T t ω)) :=
  h1.fun_comp₂ h2 _

protected lemma ae_eq (h : X ≡ᵐ[P] Y) : (fun ω t ↦ X t ω) =ᵐ[P] (fun ω t ↦ Y t ω) := by
  filter_upwards [h] with ω h
  ext
  rw [h]

lemma ae_eq_eval (h : X ≡ᵐ[P] Y) (t : ι) : X t =ᵐ[P] Y t := by
  filter_upwards [h] with ω h
  rw [h]

lemma _root_.Filter.EventuallyEq.indist (h : (fun ω t ↦ X t ω) =ᵐ[P] (fun ω t ↦ Y t ω)) :
    X ≡ᵐ[P] Y := by
  filter_upwards [h] with ω h
  rwa [funext_iff] at h

end Indistinguishable

end ProbabilityTheory
