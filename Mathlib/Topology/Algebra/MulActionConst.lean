/-
Copyright (c) 2025 Lara Toledano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lara Toledano
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Monoid actions continuous in the first variable

In this file we define the class `ContinuousSMulConst`. We say `ContinuousSMulConst Γ T` if
`Γ` acts on `T` and for each `x`, the map `γ ↦ γ • x` is continuous. (This is analogous to
`ContinuousConstSMul` and differs from `ContinuousSMul`, which requires simultaneous continuity in
both variables.)

-/

@[expose] public section

section ball
variable {G X : Type*}

open scoped Pointwise

namespace MulAction

/--
The set `{g • x | g ∈ U}`. Intended to be used for `U ∈ 𝓝 1`. Named in analogy to
`UniformSpace.ball`.
-/
abbrev ball [SMul G X] (x : X) (U : Set G) : Set X := U • {x}

lemma ball_eq_image [SMul G X] (x : X) (U : Set G) : U • {x} = (· • x)'' U := by simp

lemma mem_ball_iff [SMul G X] {x : X} {U : Set G} {y : X} :
    y ∈ U • ({x} : Set X) ↔ ∃ g ∈ U, g • x = y := by simp

lemma ball_iUnion [SMul G X] (x : X) {ι : Type*} (U : ι → Set G) :
    (⋃ i, U i) • {x} = ⋃ i, (U i) • {x} := by
  simp [Set.image_iUnion]

lemma ball_iUnion₂ [SMul G X] (x : X) {ι : Type*} {κ : ι → Sort*} (U : (i : ι) → κ i → Set G) :
    (⋃ i, ⋃ j, U i j) • {x} = ⋃ i, ⋃ j, (U i j) • {x} := by simp [Set.image_iUnion₂]

lemma ball_mul [Monoid G] [MulAction G X] (x : X) (U V : Set G) :
    ((U * V) • {x} : Set X) = U • (V • {x}) := by
  ext y
  simp [Set.mem_smul, mul_smul]

lemma ball_smul [Monoid G] [MulAction G X] (x : X) (g : G) (U : Set G) :
    (g • U) • ({x} : Set X) = g • (U • {x}) := by
  calc (g • U) • {x}
    _ = ({g} • U) • {x} := by rw [Set.singleton_smul]
    _ = ({g} * U) • {x} := by rw [smul_eq_mul]
    _ = {g} • (U • {x}) := by rw [ball_mul]
    _ = g • (U • {x}) := by simp

lemma ball_inter [SMul G X] (x : X) (U V : Set G) :
    (U ∩ V) • ({x} : Set X) ⊆ U • {x} ∩ V • {x} := by
  simp_rw [MulAction.ball_eq_image]
  apply Set.image_inter_subset

open scoped RightActions
lemma ball_op_smul [Monoid G] [MulAction G X] (x : X) (g : G) (U : Set G) :
    (U <• g) • ({x} : Set X) = U • {g • x} := by
  calc (U <• g) • ({x} : Set X)
    _ = (U * {g}) • {x} := by rw [Set.mul_singleton]; rfl
    _ = U • ({g} • {x}) := ball_mul ..
    _ = U • {g • x} := by simp
end MulAction

end ball

section ContinuousSMulConst
/-! The `ContinuousSMulConst` class. -/

/-- Class `ContinuousSMulConst Γ T` says that the scalar multiplication `(•) : Γ → T → T`
is continuous in the first argument. We use the same class for all kinds of multiplicative
actions, including (semi)modules and algebras. -/
@[mk_iff] class ContinuousSMulConst (Γ : Type*) (T : Type*)
    [TopologicalSpace Γ] [TopologicalSpace T] [SMul Γ T] : Prop where
  /-- The scalar multiplication `(•) : Γ → T → T` is continuous in the first argument. -/
  continuous_smul_const : ∀ x : T, Continuous fun γ : Γ => γ • x

instance (priority := 100) ContinuousMul.toContinuousSMulConst (M : Type*) [TopologicalSpace M]
    [Mul M] [ContinuousMul M] : ContinuousSMulConst M M where
  continuous_smul_const := continuous_mul_right

lemma continuous_smul_const (Γ : Type*) {T : Type*} [TopologicalSpace Γ] [TopologicalSpace T]
    [SMul Γ T] [ContinuousSMulConst Γ T] (x : T) : Continuous fun γ : Γ => γ • x :=
  ContinuousSMulConst.continuous_smul_const x

end ContinuousSMulConst
