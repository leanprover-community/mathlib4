/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Principal

/-!
# Properties of algebraic cycles

Here we define some basic properties of algebraic cycles which come up in practice, like being a
Weil divisor or having smooth support.
-/

@[expose] public section

open AlgebraicGeometry Order
universe u

variable {X : Scheme.{u}} {R : Type*} [Zero R] (D : AlgebraicCycle X R)

@[mk_iff]
class IsWeilDivisor (D : AlgebraicCycle X R) where
  is_divisor : D.support ⊆ {x | coheight x = 1}

lemma AlgebraicCycle.divisor_support {D : AlgebraicCycle X R} [h : IsWeilDivisor D] :
  D.support ⊆ {x | coheight x = 1} := h.is_divisor

/--
A smooth divisor is a Weil divisor with smooth support.

TODO: Change this definition to two typeclasses (IsWeilDivisor and IsSmooth or something). This
relies on knowing that a regular local ring is a domain.
-/
@[mk_iff]
class IsSmoothDivisor (D : AlgebraicCycle X R) where
  is_smooth : D.support ⊆ {x | ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing <|
    (X.presheaf.stalk x)}

instance : IsSmoothDivisor (0 : AlgebraicCycle X R) := by
  simp only [isSmoothDivisor_iff, Function.support_subset_iff, ne_eq, Set.mem_setOf_eq]
  intro x hx
  contradiction

lemma AlgebraicCycle.smooth_divisor_support (D : AlgebraicCycle X R) [h : IsSmoothDivisor D] :
    D.support ⊆ {x | ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing <|
    (X.presheaf.stalk x)} := h.is_smooth

lemma AlgebraicCycle.smooth_divisor_support_of_integral [IsIntegral X] {D : AlgebraicCycle X R}
    [IsSmoothDivisor D] : D.support ⊆ {x | IsDiscreteValuationRing <| X.presheaf.stalk x} := by
  convert D.smooth_divisor_support
  tauto

instance [IsIntegral X] {D : AlgebraicCycle X R}
    [IsSmoothDivisor D] {x : D.support} : IsDiscreteValuationRing <| X.presheaf.stalk x :=
  D.smooth_divisor_support_of_integral x.2

instance {D : AlgebraicCycle X R} [IsSmoothDivisor D] : IsWeilDivisor D := by
  rw [isWeilDivisor_iff]
  intro x hx
  obtain ⟨_, _⟩ : ∃ (x_1 : IsDomain ↑(X.presheaf.stalk x)),
    IsDiscreteValuationRing ↑(X.presheaf.stalk x) :=
    Exists.imp (fun a a_1 ↦ a_1) (D.smooth_divisor_support hx)
  have : ringKrullDim (X.presheaf.stalk x) = 1 :=
    IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk x)
  simp_all [ringKrullDim_stalk_eq_coheight]
