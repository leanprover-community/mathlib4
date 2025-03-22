/-
Copyright (c) 2024 Luigi Massacci. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luigi Massacci
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Katetov Maps

In this file we define Katetov maps.

## Notation

 - `E(X)` is the type of Katetov maps on `X`.

## References

* [melleray_urysohn_2008]
-/


variable {α : Type _} [MetricSpace α]

/-- A real valued function from a metric space is Katetov if
   it is 1-Lipschitz, and for all `x` and `y` we have `dist x y ≤ f x + f y`. -/
@[mk_iff]
structure IsKatetov (f : α → ℝ) : Prop where
  /-- Proposition that `f` is 1-Lipschitz -/
  abs_sub_le_dist : ∀ x y, |f x - f y| ≤ dist x y
  /-- "triangle inequality" for Katetov maps  -/
  dist_le_add : ∀ x y, dist x y ≤ f x + f y

/-- The type of Katetov maps from `α` -/
structure KatetovMap (α : Type*) [MetricSpace α] where
  /-- The function `α → ℝ` -/
  protected toFun : α → ℝ
  /-- Proposition that `toFun` is a Katetov map -/
  protected isKatetov : IsKatetov toFun

/-- The type of Katetov maps from `α`. -/
scoped[KatetovMap] notation "E(" α ")" => KatetovMap α

section

/-- `KatetovMapClass F α` states that `F` is a type of Katetov maps. -/
class KatetovMapClass (F : Type*) (α : Type*) [MetricSpace α] [FunLike F α  ℝ] : Prop where
  map_katetov (f : F) : IsKatetov f

end

export KatetovMapClass (map_katetov)

section KatetovMapClass

variable {F α : Type*} [MetricSpace α] [FunLike F α  ℝ]
variable [KatetovMapClass F α]

/-- Coerce a bundled morphism with a `KatetovMapClass` instance to a `KatetovMap`. -/
@[coe] def toKatetovMap (f : F) : (KatetovMap α) := ⟨f, map_katetov f⟩

instance : CoeTC F (KatetovMap α) := ⟨toKatetovMap⟩

end KatetovMapClass

namespace KatetovMap

variable {α : Type*} [MetricSpace α]

instance funLike : FunLike E(α) α ℝ where
  coe := KatetovMap.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance toKatetovMapClass : KatetovMapClass E(α) α where
  map_katetov := KatetovMap.isKatetov

@[simp]
theorem toFun_eq_coe {f : E(α)} : f.toFun = (f : α → ℝ) := rfl

instance : CanLift (α → ℝ) E(α) DFunLike.coe IsKatetov := ⟨fun f hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩

/-- See Topology/ContinuousFunction.Basic -/
def Simps.apply (f : E(α)) : α → ℝ := f

initialize_simps_projections KatetovMap (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F α ℝ] [KatetovMapClass F α] (f : F) :
    ⇑(f : E(α)) = f := rfl

@[ext]
theorem ext {f g : E(α)} (h : ∀ a, f a = g a) : f = g := DFunLike.ext _ _ h

/-- Copy of a `KatetovMap` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. See Topology/ContinuousFunction.Basic -/
protected def copy (f : E(α)) (f' : α → ℝ) (h : f' = f) : E(α) where
  toFun := f'
  isKatetov := h.symm ▸ f.isKatetov

@[simp]
theorem coe_copy (f : E(α)) (f' : α → ℝ) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : E(α)) (f' : α → ℝ) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable {f g : E(α)}


theorem coe_injective : @Function.Injective E(α) (α → ℝ) (↑) :=
  fun f g h ↦ by cases f; cases g; congr

@[simp]
theorem coe_mk (f : α → ℝ) (h : IsKatetov f) : ⇑(⟨f, h⟩ : E(α)) = f :=
  rfl

end KatetovMap
