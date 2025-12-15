/-
Copyright (c) 2023 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek
-/
module

public import Mathlib.Analysis.RCLike.Basic

@[expose] public section

noncomputable section

universe u

namespace Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]



variable (𝕜 X) in
/-- A Schauder basis is a sequence (e n) such that every element x of the space can be uniquely
represented as a convergent series x = ∑' n, a n • e n for some coefficients a n in the field 𝕜. -/
def SchauderBasis (e : ℕ → X) : Prop :=
    (∀ x : X, ∃! a : ℕ → 𝕜, x = ∑' n, a n • e n)

namespace SchauderBasis

def coeff (e : ℕ → X) (h : SchauderBasis 𝕜 X e) (x : X) : ℕ → 𝕜 :=
    (Classical.choose (h x))

def repr (e : ℕ → X) (h : SchauderBasis 𝕜 X e) (x : X) : X :=
    ∑' n, (SchauderBasis.coeff e h x n) • e n


omit [IsRCLikeNormedField 𝕜]
@[simp]
theorem repr_self (e : ℕ → X) (h : SchauderBasis 𝕜 X e) (x : X) :
    x = SchauderBasis.repr e h x := (Classical.choose_spec (h x)).1

omit [IsRCLikeNormedField 𝕜]
@[simp]
theorem coeff_unique (e : ℕ → X) (h : SchauderBasis 𝕜 X e) (x : X) (a : ℕ → 𝕜)
    (hx : x = ∑' n, a n • e n) : a = SchauderBasis.coeff e h x :=
    (Classical.choose_spec (h x)).2 a hx


/-- A canonical projection associated to a Schauder basis. -/
def CanonicalProjection (e : ℕ → X) (h : SchauderBasis 𝕜 X e) (n : ℕ) (P : X →L[𝕜] X) : Prop  :=
    (∀ x: X,
    P x = ∑ i ∈ Finset.range n, (SchauderBasis.coeff e h x i) • e i)


end SchauderBasis

end Module
