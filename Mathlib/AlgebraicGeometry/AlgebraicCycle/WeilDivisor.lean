module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

/-!
# Weil Divisors

In this file we define and develop some API for Weil divisors.

Notes: I think this is a better approach than just having everything in terms of algebraic
cycles. That said, I think potentially IsWeilDivisor should be with respect to some general
grading and should be in
-/

@[expose] public section

open Order

namespace AlgebraicGeometry

universe u
variable {X : Scheme.{u}}

def IsWeilDivisor {R : Type*} [Zero R] (α : AlgebraicCycle X R) :
    Prop := ∀ x : X, x ∈ α.support → coheight x = 1


/-
The following is probably a better design for this library (and similar for the bundled version)
-/
def IsHomogeneous {R N : Type*} [Zero R] (α : AlgebraicCycle X R) (w : X → N) (n : N) : Prop :=
    ∀ x : X, x ∈ α.support → w x = n

abbrev IsWeilDivisor' {R : Type*} [Zero R] (α : AlgebraicCycle X R) := IsHomogeneous α coheight 1



namespace IsWeilDivisor

lemma not_mem_support_of_coheight_ne_one {R : Type*} [Zero R] {α : AlgebraicCycle X R}
    (hα : IsWeilDivisor α) {x : X} (hx : coheight x ≠ 1) :
    x ∉ α.support := fun h ↦ hx <| hα x h

end IsWeilDivisor

variable (X) in
structure WeilDivisor (R : Type*) [Zero R] where
  cycle : AlgebraicCycle X R
  is_weilDivior : IsWeilDivisor cycle

instance {R : Type*} [Zero R] : FunLike (WeilDivisor X R) X R where
  coe D := D.cycle
  coe_injective' := fun ⟨_, _⟩ ⟨_, _⟩ ↦ by simp

namespace WeilDivisor

abbrev support {R : Type*} [Zero R] (D : WeilDivisor X R) := Function.support D

lemma not_mem_support_of_coheight_ne_one {R : Type*} [Zero R]
    (D : WeilDivisor X R) {x : X} (hx : coheight x ≠ 1) :
    x ∉ D.support := fun h ↦ hx <| D.2 x h

@[ext]
lemma ext {R : Type*} [Zero R] {D₁ D₂ : WeilDivisor X R}
    (h : ∀ a, coheight a = 1 → D₁ a = D₂ a) : D₁ = D₂ :=
  have h' : ∀ a, D₁ a = D₂ a := by
    intro a
    by_cases o : coheight a = 1
    · exact h a o
    · have h1 := D₁.not_mem_support_of_coheight_ne_one o
      have h2 := D₂.not_mem_support_of_coheight_ne_one o
      simp_all
  DFunLike.ext _ _ h'

end WeilDivisor

end AlgebraicGeometry
