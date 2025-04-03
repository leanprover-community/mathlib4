/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Topology.ContinuousFunction.Algebra

/-!
# Continuous maps sending zero to zero

This is the type of continuous maps from `X` to `R` such that `(0 : X) ↦ (0 : R)` for which we
provide the scoped notation `C(X, R)₀`.  We provide this as a dedicated type solely for the
non-unital continuous functional calculus, as using various terms of type `Ideal C(X, R)` were
overly burdensome on type class synthesis.

Of course, one could generalize to maps between pointed topological spaces, but that goes beyond
the purpose of this type.
-/

/-- The type of continuous maps which map zero to zero. -/
structure ContinuousMapZero (X R : Type*) [Zero X] [Zero R] [TopologicalSpace X]
    [TopologicalSpace R] extends C(X, R) where
  map_zero' : toContinuousMap 0 = 0

namespace ContinuousMapZero

@[inherit_doc]
scoped notation "C(" X ", " R ")₀" => ContinuousMapZero X R

section Basic

variable {X Y R : Type*} [Zero X] [Zero Y] [Zero R]
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace R]

instance instFunLike : FunLike C(X, R)₀ X R where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance instContinuousMapClass : ContinuousMapClass C(X, R)₀ X R where
  map_continuous f := f.continuous

instance instZeroHomClass : ZeroHomClass C(X, R)₀ X R where
  map_zero f := f.map_zero'

@[ext]
lemma ext {f g : C(X, R)₀} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

@[simp]
lemma coe_mk {f : C(X, R)} {h0 : f 0 = 0} : ⇑(mk f h0) = f := rfl

/-- Composition of continuous maps which map zero to zero. -/
def comp (g : C(Y, R)₀) (f : C(X, Y)₀) : C(X, R)₀ where
  toContinuousMap := g.toContinuousMap.comp f.toContinuousMap
  map_zero' := show g (f 0) = 0 from map_zero f ▸ map_zero g

@[simp]
lemma comp_apply (g : C(Y, R)₀) (f : C(X, Y)₀) (x : X) : g.comp f x = g (f x) := rfl

end Basic

section Semiring

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]

instance instZero : Zero C(X, R)₀ where
  zero := ⟨0, rfl⟩

instance instAdd : Add C(X, R)₀ where
  add f g := ⟨f + g, by simp⟩

instance instMul : Mul C(X, R)₀ where
  mul f g := ⟨f * g, by simp⟩

instance instSMul {M : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R] :
    SMul M C(X, R)₀ where
  smul m f := ⟨m • f, by simp⟩

lemma toContinuousMap_injective :
    Function.Injective (toContinuousMap (X := X) (R := R)) :=
  fun f g h ↦ by refine congr(.mk $(h) ?_); exacts [f.map_zero', g.map_zero']

instance instNonUnitalCommSemiring : NonUnitalCommSemiring C(X, R)₀ :=
  (toContinuousMap_injective (X := X) (R := R)).nonUnitalCommSemiring
    _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance instModule {M : Type*} [Semiring M] [Module M R] [ContinuousConstSMul M R] :
    Module M C(X, R)₀ :=
  (toContinuousMap_injective (X := X) (R := R)).module M
    { toFun := _, map_add' := fun _ _ ↦ rfl, map_zero' := rfl } (fun _ _ ↦ rfl)

instance instSMulCommClass {M N : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
    [SMulZeroClass N R] [ContinuousConstSMul N R] [SMulCommClass M N R] :
    SMulCommClass M N C(X, R)₀ where
  smul_comm _ _ _ := ext fun _ ↦ smul_comm ..

instance instIsScalarTower {M N : Type*} [SMulZeroClass M R] [ContinuousConstSMul M R]
    [SMulZeroClass N R] [ContinuousConstSMul N R] [SMul M N] [IsScalarTower M N R] :
    IsScalarTower M N C(X, R)₀ where
  smul_assoc _ _ _ := ext fun _ ↦ smul_assoc ..

instance instStarRing [StarRing R] [ContinuousStar R] : StarRing C(X, R)₀ where
  star f := ⟨star f, by simp⟩
  star_involutive _ := ext fun _ ↦ star_star _
  star_mul _ _ := ext fun _ ↦ star_mul ..
  star_add _ _ := ext fun _ ↦ star_add ..

instance instTopologicalSpace : TopologicalSpace C(X, R)₀ :=
  TopologicalSpace.induced toContinuousMap inferInstance

end Semiring

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [CommRing R] [TopologicalSpace R] [TopologicalRing R]
section Ring

instance instSub : Sub C(X, R)₀ where
  sub f g := ⟨f - g, by simp⟩

instance instNeg : Neg C(X, R)₀ where
  neg f := ⟨-f, by simp⟩

instance instNonUnitalCommRing : NonUnitalCommRing C(X, R)₀ :=
  (toContinuousMap_injective (X := X) (R := R)).nonUnitalCommRing _ rfl
  (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end Ring

end ContinuousMapZero
