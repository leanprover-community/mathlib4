/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module topology.algebra.uniform_mul_action
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Topology.UniformSpace.Completion

/-!
# Multiplicative action on the completion of a uniform space

In this file we define typeclasses `has_uniform_continuous_const_vadd` and
`has_uniform_continuous_const_smul` and prove that a multiplicative action on `X` with uniformly
continuous `(•) c` can be extended to a multiplicative action on `uniform_space.completion X`.

In later files once the additive group structure is set up, we provide
* `uniform_space.completion.distrib_mul_action`
* `uniform_space.completion.mul_action_with_zero`
* `uniform_space.completion.module`

TODO: Generalise the results here from the concrete `completion` to any `abstract_completion`.
-/


universe u v w x y z

noncomputable section

variable (R : Type u) (M : Type v) (N : Type w) (X : Type x) (Y : Type y) [UniformSpace X]
  [UniformSpace Y]

/-- An additive action such that for all `c`, the map `λ x, c +ᵥ x` is uniformly continuous. -/
class HasUniformContinuousConstVadd [VAdd M X] : Prop where
  uniformContinuous_const_vadd : ∀ c : M, UniformContinuous ((· +ᵥ ·) c : X → X)
#align has_uniform_continuous_const_vadd HasUniformContinuousConstVadd

/-- A multiplicative action such that for all `c`, the map `λ x, c • x` is uniformly continuous. -/
@[to_additive]
class HasUniformContinuousConstSmul [SMul M X] : Prop where
  uniformContinuous_const_smul : ∀ c : M, UniformContinuous ((· • ·) c : X → X)
#align has_uniform_continuous_const_smul HasUniformContinuousConstSmul
#align has_uniform_continuous_const_vadd HasUniformContinuousConstVadd

export HasUniformContinuousConstVadd (uniformContinuous_const_vadd)

export HasUniformContinuousConstSmul (uniformContinuous_const_smul)

instance AddMonoid.hasUniformContinuousConstSmul_nat [AddGroup X] [UniformAddGroup X] :
    HasUniformContinuousConstSmul ℕ X :=
  ⟨uniformContinuous_const_nsmul⟩
#align add_monoid.has_uniform_continuous_const_smul_nat AddMonoid.hasUniformContinuousConstSmul_nat

instance AddGroup.hasUniformContinuousConstSmul_int [AddGroup X] [UniformAddGroup X] :
    HasUniformContinuousConstSmul ℤ X :=
  ⟨uniformContinuous_const_zsmul⟩
#align add_group.has_uniform_continuous_const_smul_int AddGroup.hasUniformContinuousConstSmul_int

/-- A `distrib_mul_action` that is continuous on a uniform group is uniformly continuous.
This can't be an instance due to it forming a loop with
`has_uniform_continuous_const_smul.to_has_continuous_const_smul` -/
theorem hasUniformContinuousConstSmul_of_continuous_const_smul [Monoid R] [AddCommGroup M]
    [DistribMulAction R M] [UniformSpace M] [UniformAddGroup M] [ContinuousConstSMul R M] :
    HasUniformContinuousConstSmul R M :=
  ⟨fun r =>
    uniform_continuous_of_continuous_at_zero (DistribMulAction.toAddMonoidHom M r)
      (Continuous.continuousAt (continuous_const_smul r))⟩
#align has_uniform_continuous_const_smul_of_continuous_const_smul hasUniformContinuousConstSmul_of_continuous_const_smul

/-- The action of `semiring.to_module` is uniformly continuous. -/
instance Ring.hasUniformContinuousConstSmul [Ring R] [UniformSpace R] [UniformAddGroup R]
    [ContinuousMul R] : HasUniformContinuousConstSmul R R :=
  hasUniformContinuousConstSmul_of_continuous_const_smul _ _
#align ring.has_uniform_continuous_const_smul Ring.hasUniformContinuousConstSmul

/-- The action of `semiring.to_opposite_module` is uniformly continuous. -/
instance Ring.has_uniform_continuous_const_op_smul [Ring R] [UniformSpace R] [UniformAddGroup R]
    [ContinuousMul R] : HasUniformContinuousConstSmul Rᵐᵒᵖ R :=
  hasUniformContinuousConstSmul_of_continuous_const_smul _ _
#align ring.has_uniform_continuous_const_op_smul Ring.has_uniform_continuous_const_op_smul

section SMul

variable [SMul M X]

@[to_additive]
instance (priority := 100) HasUniformContinuousConstSmul.to_continuousConstSMul
    [HasUniformContinuousConstSmul M X] : ContinuousConstSMul M X :=
  ⟨fun c => (uniformContinuous_const_smul c).Continuous⟩
#align has_uniform_continuous_const_smul.to_has_continuous_const_smul HasUniformContinuousConstSmul.to_continuousConstSMul
#align has_uniform_continuous_const_vadd.to_has_continuous_const_vadd HasUniformContinuousConstVadd.to_has_continuous_const_vadd

variable {M X Y}

@[to_additive]
theorem UniformContinuous.const_smul [HasUniformContinuousConstSmul M X] {f : Y → X}
    (hf : UniformContinuous f) (c : M) : UniformContinuous (c • f) :=
  (uniformContinuous_const_smul c).comp hf
#align uniform_continuous.const_smul UniformContinuous.const_smul
#align uniform_continuous.const_vadd UniformContinuous.const_vadd

/-- If a scalar action is central, then its right action is uniform continuous when its left action
is. -/
@[to_additive
      "If an additive action is central, then its right action is uniform\ncontinuous when its left action,is."]
instance (priority := 100) HasUniformContinuousConstSmul.op [SMul Mᵐᵒᵖ X] [IsCentralScalar M X]
    [HasUniformContinuousConstSmul M X] : HasUniformContinuousConstSmul Mᵐᵒᵖ X :=
  ⟨MulOpposite.rec' fun c =>
      by
      change UniformContinuous fun m => MulOpposite.op c • m
      simp_rw [op_smul_eq_smul]
      exact uniform_continuous_const_smul c⟩
#align has_uniform_continuous_const_smul.op HasUniformContinuousConstSmul.op
#align has_uniform_continuous_const_vadd.op HasUniformContinuousConstVadd.op

@[to_additive]
instance MulOpposite.hasUniformContinuousConstSmul [HasUniformContinuousConstSmul M X] :
    HasUniformContinuousConstSmul M Xᵐᵒᵖ :=
  ⟨fun c =>
    MulOpposite.uniformContinuous_op.comp <| MulOpposite.uniformContinuous_unop.const_smul c⟩
#align mul_opposite.has_uniform_continuous_const_smul MulOpposite.hasUniformContinuousConstSmul
#align add_opposite.has_uniform_continuous_const_vadd AddOpposite.has_uniform_continuous_const_vadd

end SMul

@[to_additive]
instance UniformGroup.to_hasUniformContinuousConstSmul {G : Type u} [Group G] [UniformSpace G]
    [UniformGroup G] : HasUniformContinuousConstSmul G G :=
  ⟨fun c => uniformContinuous_const.mul uniformContinuous_id⟩
#align uniform_group.to_has_uniform_continuous_const_smul UniformGroup.to_hasUniformContinuousConstSmul
#align uniform_add_group.to_has_uniform_continuous_const_vadd UniformAddGroup.to_has_uniform_continuous_const_vadd

namespace UniformSpace

namespace Completion

section SMul

variable [SMul M X]

@[to_additive]
instance : SMul M (Completion X) :=
  ⟨fun c => Completion.map ((· • ·) c)⟩

@[to_additive]
theorem smul_def (c : M) (x : Completion X) : c • x = Completion.map ((· • ·) c) x :=
  rfl
#align uniform_space.completion.smul_def UniformSpace.Completion.smul_def
#align uniform_space.completion.vadd_def UniformSpace.Completion.vadd_def

@[to_additive]
instance : HasUniformContinuousConstSmul M (Completion X) :=
  ⟨fun c => uniformContinuous_map⟩

@[to_additive]
instance [SMul N X] [SMul M N] [HasUniformContinuousConstSmul M X]
    [HasUniformContinuousConstSmul N X] [IsScalarTower M N X] : IsScalarTower M N (Completion X) :=
  ⟨fun m n x =>
    by
    have : _ = (_ : completion X → completion X) :=
      map_comp (uniform_continuous_const_smul m) (uniform_continuous_const_smul n)
    refine' Eq.trans _ (congr_fun this.symm x)
    exact congr_arg (fun f => completion.map f x) (funext (smul_assoc _ _))⟩

@[to_additive]
instance [SMul N X] [SMulCommClass M N X] [HasUniformContinuousConstSmul M X]
    [HasUniformContinuousConstSmul N X] : SMulCommClass M N (Completion X) :=
  ⟨fun m n x =>
    by
    have hmn : m • n • x = (completion.map (SMul.smul m) ∘ completion.map (SMul.smul n)) x := rfl
    have hnm : n • m • x = (completion.map (SMul.smul n) ∘ completion.map (SMul.smul m)) x := rfl
    rw [hmn, hnm, map_comp, map_comp]
    exact congr_arg (fun f => completion.map f x) (funext (smul_comm _ _))
    repeat' exact uniform_continuous_const_smul _⟩

@[to_additive]
instance [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] : IsCentralScalar M (Completion X) :=
  ⟨fun c a => (congr_arg fun f => Completion.map f a) <| funext (op_smul_eq_smul c)⟩

variable {M X} [HasUniformContinuousConstSmul M X]

@[simp, norm_cast, to_additive]
theorem coe_smul (c : M) (x : X) : ↑(c • x) = (c • x : Completion X) :=
  (map_coe (uniformContinuous_const_smul c) x).symm
#align uniform_space.completion.coe_smul UniformSpace.Completion.coe_smul
#align uniform_space.completion.coe_vadd UniformSpace.Completion.coe_vadd

end SMul

@[to_additive]
instance [Monoid M] [MulAction M X] [HasUniformContinuousConstSmul M X] : MulAction M (Completion X)
    where
  smul := (· • ·)
  one_smul := ext' (continuous_const_smul _) continuous_id fun a => by rw [← coe_smul, one_smul]
  mul_smul x y :=
    ext' (continuous_const_smul _) ((continuous_const_smul _).const_smul _) fun a => by
      simp only [← coe_smul, mul_smul]

end Completion

end UniformSpace

