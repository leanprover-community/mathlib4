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

open Set Function

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
  coe_injective' _ _ h := congr(⟨⟨$(h), _⟩, _⟩)

instance instContinuousMapClass : ContinuousMapClass C(X, R)₀ X R where
  map_continuous f := f.continuous

instance instZeroHomClass : ZeroHomClass C(X, R)₀ X R where
  map_zero f := f.map_zero'

@[ext]
lemma ext {f g : C(X, R)₀} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

@[simp]
lemma coe_mk {f : C(X, R)} {h0 : f 0 = 0} : ⇑(mk f h0) = f := rfl

lemma toContinuousMap_injective [Zero R] : Injective (toContinuousMap (X := X) (R := R)) :=
  fun _ _ h ↦ congr(.mk $(h) _)

lemma range_toContinuousMap : range (toContinuousMap (X := X) (R := R)) =
    {f : C(X, R) | f 0 = 0} :=
  Set.ext fun f ↦ ⟨fun ⟨f', hf'⟩ ↦ hf' ▸ map_zero f', fun hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩

/-- Composition of continuous maps which map zero to zero. -/
def comp (g : C(Y, R)₀) (f : C(X, Y)₀) : C(X, R)₀ where
  toContinuousMap := g.toContinuousMap.comp f.toContinuousMap
  map_zero' := show g (f 0) = 0 from map_zero f ▸ map_zero g

@[simp]
lemma comp_apply (g : C(Y, R)₀) (f : C(X, Y)₀) (x : X) : g.comp f x = g (f x) := rfl

instance instPartialOrder [PartialOrder R] : PartialOrder C(X, R)₀ :=
  .lift _ DFunLike.coe_injective'

lemma le_def [PartialOrder R] (f g : C(X, R)₀) : f ≤ g ↔ ∀ x, f x ≤ g x := Iff.rfl

protected instance instTopologicalSpace : TopologicalSpace C(X, R)₀ :=
  TopologicalSpace.induced toContinuousMap inferInstance

lemma embedding_toContinuousMap : Embedding (toContinuousMap (X := X) (R := R)) where
  induced := rfl
  inj _ _ h := ext fun x ↦ congr($(h) x)

instance [T0Space R] : T0Space C(X, R)₀ := embedding_toContinuousMap.t0Space
instance [T1Space R] : T1Space C(X, R)₀ := embedding_toContinuousMap.t1Space
instance [T2Space R] : T2Space C(X, R)₀ := embedding_toContinuousMap.t2Space

lemma closedEmbedding_toContinuousMap [T1Space R] :
    ClosedEmbedding (toContinuousMap (X := X) (R := R)) where
  toEmbedding := embedding_toContinuousMap
  isClosed_range := by
    rw [range_toContinuousMap]
    exact isClosed_singleton.preimage <| ContinuousMap.continuous_eval_const 0

end Basic

section Algebra

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [TopologicalSpace R]

instance instZero [Zero R] : Zero C(X, R)₀ where
  zero := ⟨0, rfl⟩

@[simp] lemma coe_zero [Zero R] : ⇑(0 : C(X, R)₀) = 0 := rfl

instance instAdd [AddZeroClass R] [ContinuousAdd R] : Add C(X, R)₀ where
  add f g := ⟨f + g, by simp⟩

@[simp] lemma coe_add [AddZeroClass R] [ContinuousAdd R] (f g : C(X, R)₀) : ⇑(f + g) = f + g := rfl

instance instMul [MulZeroClass R] [ContinuousMul R] : Mul C(X, R)₀ where
  mul f g := ⟨f * g, by simp⟩

@[simp] lemma coe_mul [MulZeroClass R] [ContinuousMul R] (f g : C(X, R)₀) : ⇑(f * g) = f * g := rfl

instance instSMul {M : Type*} [Zero R] [SMulZeroClass M R] [ContinuousConstSMul M R] :
    SMul M C(X, R)₀ where
  smul m f := ⟨m • f, by simp⟩

@[simp] lemma coe_smul {M : Type*} [Zero R] [SMulZeroClass M R] [ContinuousConstSMul M R]
    (m : M) (f : C(X, R)₀) : ⇑(m • f) = m • f := rfl

section Semiring

variable [CommSemiring R] [TopologicalSemiring R]

instance instNonUnitalCommSemiring : NonUnitalCommSemiring C(X, R)₀ :=
  toContinuousMap_injective.nonUnitalCommSemiring
    _ rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

instance instModule {M : Type*} [Semiring M] [Module M R] [ContinuousConstSMul M R] :
    Module M C(X, R)₀ :=
  toContinuousMap_injective.module M
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

@[simp] lemma coe_star [StarRing R] [ContinuousStar R] (f : C(X, R)₀) : ⇑(star f) = star ⇑f := rfl

instance instCanLift : CanLift C(X, R) C(X, R)₀ (↑) (fun f ↦ f 0 = 0) where
  prf f hf := ⟨⟨f, hf⟩, rfl⟩

end Semiring

section Ring

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [CommRing R] [TopologicalSpace R] [TopologicalRing R]

instance instSub : Sub C(X, R)₀ where
  sub f g := ⟨f - g, by simp⟩

instance instNeg : Neg C(X, R)₀ where
  neg f := ⟨-f, by simp⟩

instance instNonUnitalCommRing : NonUnitalCommRing C(X, R)₀ :=
  toContinuousMap_injective.nonUnitalCommRing _ rfl
  (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

end Ring

end Algebra

section UniformSpace

variable {X R : Type*} [Zero X] [TopologicalSpace X]
variable [Zero R] [UniformSpace R]

protected instance instUniformSpace : UniformSpace C(X, R)₀ := .comap toContinuousMap inferInstance

lemma uniformEmbedding_toContinuousMap :
    UniformEmbedding (toContinuousMap (X := X) (R := R)) where
  comap_uniformity := rfl
  inj _ _ h := ext fun x ↦ congr($(h) x)

instance [T1Space R] [CompleteSpace C(X, R)] : CompleteSpace C(X, R)₀ :=
  completeSpace_iff_isComplete_range uniformEmbedding_toContinuousMap.toUniformInducing
    |>.mpr closedEmbedding_toContinuousMap.isClosed_range.isComplete

end UniformSpace

end ContinuousMapZero
