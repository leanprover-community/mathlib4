/-
Copyright (c) 2025 Hanliu Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang , Hanliu Jiang
-/
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.ContinuousMap.CocompactMap

/-!
# Continuous functions vanishing atBot

The type of continuous functions vanishing atBot.

## TODO

* Create more instances of algebraic structures (e.g., `NonUnitalSemiring`) once the necessary
  type classes (e.g., `IsTopologicalRing`) are sufficiently generalized.
* Relate the unitization of `C_₀(α, β)` to the Alexandroff compactification.
-/


universe u v w

variable {F : Type*} {α : Type u} {β : Type v} {γ : Type w}
[Preorder α] [TopologicalSpace α]

open BoundedContinuousFunction Topology Bornology

open Filter Metric

/-- `C_₀(α, β)` is the type of continuous functions `α → β` which vanish at infinity from a
topological space to a metric space with a zero element.

When possible, instead of parametrizing results over `(f : C_₀(α, β))`,
you should parametrize over `(F : Type*) [ZeroAtBotContinuousMapClass F α β] (f : F)`.

When you extend this structure, make sure to extend `ZeroAtBotContinuousMapClass`. -/
structure ZeroAtBotContinuousMap (α : Type u) (β : Type v) [Preorder α]
[TopologicalSpace α][Zero β][TopologicalSpace β] : Type max u v extends ContinuousMap α β where
  /-- The function tends to zero along the `cocompact` filter. -/
  zero_atBot' : Tendsto toFun (atBot) (𝓝 0)

@[inherit_doc]
scoped[zero_atBot] notation (priority := 2000) "C_₀(" α ", " β ")" =>
ZeroAtBotContinuousMap α β

@[inherit_doc]
scoped[zero_atBot] notation α " →C_₀ " β => ZeroAtBotContinuousMap α β

open zero_atBot

section

/-- `ZeroAtInftyContinuousMapClass F α β` states that `F` is a type of continuous maps which
vanish at infinity.

You should also extend this typeclass when you extend `ZeroAtInftyContinuousMap`. -/
class ZeroAtBotContinuousMapClass (F : Type*) (α β : outParam Type*) [Preorder α]
[TopologicalSpace α]
    [Zero β] [TopologicalSpace β] [FunLike F α β] : Prop extends ContinuousMapClass F α β where
  /-- Each member of the class tends to zero along the `cocompact` filter. -/
  zero_atBot (f : F) : Tendsto f (atBot) (𝓝 0)

end

export ZeroAtBotContinuousMapClass (zero_atBot)

namespace ZeroAtBotContinuousMap

section Basics

variable [TopologicalSpace β] [Zero β] [FunLike F α β] [ZeroAtBotContinuousMapClass F α β]

instance instFunLike : FunLike C_₀(α, β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

instance instZeroAtBotContinuousMapClass : ZeroAtBotContinuousMapClass C_₀(α, β) α β where
  map_continuous f := f.continuous_toFun
  zero_atBot f := f.zero_atBot'

instance instCoeTC : CoeTC F C_₀(α, β) :=
  ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      zero_atBot' := zero_atBot f }⟩

@[simp]
theorem coe_toContinuousMap (f : C_₀(α, β)) : (f.toContinuousMap : α → β) = f :=
  rfl

@[ext]
theorem ext {f g : C_₀(α, β)} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
lemma coe_mk {f : α → β} (hf : Continuous f) (hf' : Tendsto f (atBot) (𝓝 0)) :
    { toFun := f,
      continuous_toFun := hf,
      zero_atBot' := hf' : ZeroAtBotContinuousMap α β} = f :=
  rfl

/-- Copy of a `ZeroAtInftyContinuousMap` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : C_₀(α, β)) (f' : α → β) (h : f' = f) : C_₀(α, β) where
  toFun := f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  zero_atBot' := by
    simp_rw [h]
    exact f.zero_atBot'

@[simp]
theorem coe_copy (f : C_₀(α, β)) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : C_₀(α, β)) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

theorem eq_of_empty [IsEmpty α] (f g : C_₀(α, β)) : f = g :=
  ext <| IsEmpty.elim ‹_›

end Basics

/-! ### Algebraic structure

Whenever `β` has suitable algebraic structure and a compatible topological structure, then
`C_₀(α, β)` inherits a corresponding algebraic structure. The primary exception to this is that
`C_₀(α, β)` will not have a multiplicative identity.
-/


section AlgebraicStructure

variable [TopologicalSpace β] (x : α)

instance instZero [Zero β] : Zero C_₀(α, β) :=
  ⟨⟨0, tendsto_const_nhds⟩⟩

instance instInhabited [Zero β] : Inhabited C_₀(α, β) :=
  ⟨0⟩

@[simp]
theorem coe_zero [Zero β] : ⇑(0 : C_₀(α, β)) = 0 :=
  rfl

theorem zero_apply [Zero β] : (0 : C_₀(α, β)) x = 0 :=
  rfl

instance instMul [MulZeroClass β] [ContinuousMul β] : Mul C_₀(α, β) :=
  ⟨fun f g =>
    ⟨f * g, by simpa only [mul_zero] using (zero_atBot f).mul (zero_atBot g)⟩⟩

@[simp]
theorem coe_mul [MulZeroClass β] [ContinuousMul β] (f g : C_₀(α, β)) : ⇑(f * g) = f * g :=
  rfl

theorem mul_apply [MulZeroClass β] [ContinuousMul β] (f g : C_₀(α, β)) :
 (f * g) x = f x * g x :=
  rfl

instance instMulZeroClass [MulZeroClass β] [ContinuousMul β] : MulZeroClass C_₀(α, β) :=
  DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

instance instSemigroupWithZero [SemigroupWithZero β] [ContinuousMul β] :
    SemigroupWithZero C_₀(α, β) :=
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

instance instAdd [AddZeroClass β] [ContinuousAdd β] : Add C_₀(α, β) :=
  ⟨fun f g => ⟨f + g, by simpa only [add_zero] using (zero_atBot f).add (zero_atBot g)⟩⟩

@[simp]
theorem coe_add [AddZeroClass β] [ContinuousAdd β] (f g : C_₀(α, β)) : ⇑(f + g) = f + g :=
  rfl

theorem add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C_₀(α, β)) :
(f + g) x = f x + g x :=
  rfl

instance instAddZeroClass [AddZeroClass β] [ContinuousAdd β] : AddZeroClass C_₀(α, β) :=
  DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

instance instSMul [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β] :
    SMul R C_₀(α, β) :=
  -- Porting note: Original version didn't have `Continuous.const_smul f.continuous r`
  ⟨fun r f => ⟨⟨r • ⇑f, Continuous.const_smul f.continuous r⟩,
    by simpa [smul_zero] using (zero_atBot f).const_smul r⟩⟩

@[simp, norm_cast]
theorem coe_smul [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β] (r : R)
    (f : C_₀(α, β)) : ⇑(r • f) = r • ⇑f :=
  rfl

theorem smul_apply [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [ContinuousConstSMul R β]
    (r : R) (f : C_₀(α, β)) (x : α) : (r • f) x = r • f x :=
  rfl

section AddMonoid

variable [AddMonoid β] [ContinuousAdd β] (f g : C_₀(α, β))

instance instAddMonoid : AddMonoid C_₀(α, β) :=
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

end AddMonoid

instance instAddCommMonoid [AddCommMonoid β] [ContinuousAdd β] : AddCommMonoid C_₀(α, β) :=
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

section AddGroup

variable [AddGroup β] [IsTopologicalAddGroup β] (f g : C_₀(α, β))

instance instNeg : Neg C_₀(α, β) :=
  ⟨fun f => ⟨-f, by simpa only [neg_zero] using (zero_atBot f).neg⟩⟩

@[simp]
theorem coe_neg : ⇑(-f) = -f :=
  rfl

theorem neg_apply : (-f) x = -f x :=
  rfl

instance instSub : Sub C_₀(α, β) :=
  ⟨fun f g => ⟨f - g, by simpa only [sub_zero] using (zero_atBot f).sub (zero_atBot g)⟩⟩

@[simp]
theorem coe_sub : ⇑(f - g) = f - g :=
  rfl

theorem sub_apply : (f - g) x = f x - g x :=
  rfl

instance instAddGroup : AddGroup C_₀(α, β) :=
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end AddGroup

instance instAddCommGroup [AddCommGroup β] [IsTopologicalAddGroup β] : AddCommGroup C_₀(α, β) :=
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ =>
    rfl

instance instIsCentralScalar [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [SMulWithZero Rᵐᵒᵖ β]
    [ContinuousConstSMul R β] [IsCentralScalar R β] : IsCentralScalar R C_₀(α, β) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

instance instSMulWithZero [Zero β] {R : Type*} [Zero R] [SMulWithZero R β]
    [ContinuousConstSMul R β] : SMulWithZero R C_₀(α, β) :=
  Function.Injective.smulWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

instance instMulActionWithZero [Zero β] {R : Type*} [MonoidWithZero R] [MulActionWithZero R β]
    [ContinuousConstSMul R β] : MulActionWithZero R C_₀(α, β) :=
  Function.Injective.mulActionWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

instance instModule [AddCommMonoid β] [ContinuousAdd β] {R : Type*} [Semiring R] [Module R β]
    [ContinuousConstSMul R β] : Module R C_₀(α, β) :=
  Function.Injective.module R ⟨⟨_, coe_zero⟩, coe_add⟩ DFunLike.coe_injective coe_smul

instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] [IsTopologicalSemiring β] :
    NonUnitalNonAssocSemiring C_₀(α, β) :=
  DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance instNonUnitalSemiring [NonUnitalSemiring β] [IsTopologicalSemiring β] :
    NonUnitalSemiring C_₀(α, β) :=
  DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance instNonUnitalCommSemiring [NonUnitalCommSemiring β] [IsTopologicalSemiring β] :
    NonUnitalCommSemiring C_₀(α, β) :=
  DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing β] [IsTopologicalRing β] :
    NonUnitalNonAssocRing C_₀(α, β) :=
  DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

instance instNonUnitalRing [NonUnitalRing β] [IsTopologicalRing β] : NonUnitalRing C_₀(α, β) :=
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

instance instNonUnitalCommRing [NonUnitalCommRing β] [IsTopologicalRing β] :
    NonUnitalCommRing C_₀(α, β) :=
  DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

instance instIsScalarTower {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
    [IsTopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [IsScalarTower R β β] :
    IsScalarTower R C_₀(α, β) C_₀(α, β) where
  smul_assoc r f g := by
    ext
    simp only [smul_eq_mul, coe_mul, coe_smul, Pi.mul_apply, Pi.smul_apply]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_assoc]

instance instSMulCommClass {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
    [IsTopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [SMulCommClass R β β] :
    SMulCommClass R C_₀(α, β) C_₀(α, β) where
  smul_comm r f g := by
    ext
    simp only [smul_eq_mul, coe_smul, coe_mul, Pi.smul_apply, Pi.mul_apply]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_comm]

end AlgebraicStructure
end ZeroAtBotContinuousMap
