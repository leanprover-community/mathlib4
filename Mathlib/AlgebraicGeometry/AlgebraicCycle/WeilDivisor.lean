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

open Order AlgebraicGeometry

universe u
variable {X : Scheme.{u}}
#check Function.locallyFinsuppWithin

/-
I think this homogeneous cycles nonsense can be avoided by simply defining algebriac cycles in terms
of Function.locallyFinsuppWithin. Then, we will get the relevant ext lemma for free
-/
def AlgebraicCycle.IsHomogeneous
    {R N : Type*} [Zero R] (α : AlgebraicCycle X R) (w : X → N) (n : N) : Prop :=
    ∀ x : X, x ∈ α.support → w x = n

def AlgebraicCycle.SupportedWithin {R : Type*} [Zero R] (α : AlgebraicCycle X R) (s : Set X) :=
    α.support ⊆ s

variable (X) in
structure HomogeneousCycle (R : Type*) {N : Type*} [Zero R] (w : X → N) (n : N) where
    cycle : AlgebraicCycle X R
    homogeneous : cycle.IsHomogeneous w n

abbrev IsWeilDivisor {R : Type*} [Zero R] (α : AlgebraicCycle X R) := α.IsHomogeneous coheight 1

variable (X) in
abbrev WeilDivisor (R : Type*) [Zero R] := HomogeneousCycle X R coheight 1

namespace IsWeilDivisor

lemma not_mem_support_of_coheight_ne_one {R : Type*} [Zero R] {α : AlgebraicCycle X R}
    {N : Type*}
    (w : X → N) (n : N)
    (hα : α.IsHomogeneous w n) {x : X} (hx : w x ≠ n) :
    x ∉ α.support := fun h ↦ hx <| hα x h

end IsWeilDivisor

/-variable (X) in
structure WeilDivisor (R : Type*) [Zero R] where
  cycle : AlgebraicCycle X R
  isWeilDivior : IsWeilDivisor cycle-/

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
