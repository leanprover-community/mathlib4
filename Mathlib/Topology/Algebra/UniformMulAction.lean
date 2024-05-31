/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Topology.Algebra.UniformGroup
import Mathlib.Topology.UniformSpace.Completion

#align_import topology.algebra.uniform_mul_action from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Multiplicative action on the completion of a uniform space

In this file we define typeclasses `UniformContinuousConstVAdd` and
`UniformContinuousConstSMul` and prove that a multiplicative action on `X` with uniformly
continuous `(•) c` can be extended to a multiplicative action on `UniformSpace.Completion X`.

In later files once the additive group structure is set up, we provide
* `UniformSpace.Completion.DistribMulAction`
* `UniformSpace.Completion.MulActionWithZero`
* `UniformSpace.Completion.Module`

TODO: Generalise the results here from the concrete `Completion` to any `AbstractCompletion`.
-/


universe u v w x y

noncomputable section

variable (R : Type u) (M : Type v) (N : Type w) (X : Type x) (Y : Type y) [UniformSpace X]
  [UniformSpace Y]

/-- An additive action such that for all `c`, the map `fun x ↦ c +ᵥ x` is uniformly continuous. -/
class UniformContinuousConstVAdd [VAdd M X] : Prop where
  uniformContinuous_const_vadd : ∀ c : M, UniformContinuous (c +ᵥ · : X → X)
#align has_uniform_continuous_const_vadd UniformContinuousConstVAdd

/-- A multiplicative action such that for all `c`,
the map `fun x ↦c • x` is uniformly continuous. -/
@[to_additive]
class UniformContinuousConstSMul [SMul M X] : Prop where
  uniformContinuous_const_smul : ∀ c : M, UniformContinuous (c • · : X → X)
#align has_uniform_continuous_const_smul UniformContinuousConstSMul

export UniformContinuousConstVAdd (uniformContinuous_const_vadd)

export UniformContinuousConstSMul (uniformContinuous_const_smul)

instance AddMonoid.uniformContinuousConstSMul_nat [AddGroup X] [UniformAddGroup X] :
    UniformContinuousConstSMul ℕ X :=
  ⟨uniformContinuous_const_nsmul⟩
#align add_monoid.has_uniform_continuous_const_smul_nat AddMonoid.uniformContinuousConstSMul_nat

instance AddGroup.uniformContinuousConstSMul_int [AddGroup X] [UniformAddGroup X] :
    UniformContinuousConstSMul ℤ X :=
  ⟨uniformContinuous_const_zsmul⟩
#align add_group.has_uniform_continuous_const_smul_int AddGroup.uniformContinuousConstSMul_int

/-- A `DistribMulAction` that is continuous on a uniform group is uniformly continuous.
This can't be an instance due to it forming a loop with
`UniformContinuousConstSMul.to_continuousConstSMul` -/
theorem uniformContinuousConstSMul_of_continuousConstSMul [Monoid R] [AddCommGroup M]
    [DistribMulAction R M] [UniformSpace M] [UniformAddGroup M] [ContinuousConstSMul R M] :
    UniformContinuousConstSMul R M :=
  ⟨fun r =>
    uniformContinuous_of_continuousAt_zero (DistribMulAction.toAddMonoidHom M r)
      (Continuous.continuousAt (continuous_const_smul r))⟩
#align has_uniform_continuous_const_smul_of_continuous_const_smul uniformContinuousConstSMul_of_continuousConstSMul

/-- The action of `Semiring.toModule` is uniformly continuous. -/
instance Ring.uniformContinuousConstSMul [Ring R] [UniformSpace R] [UniformAddGroup R]
    [ContinuousMul R] : UniformContinuousConstSMul R R :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _
#align ring.has_uniform_continuous_const_smul Ring.uniformContinuousConstSMul

/-- The action of `Semiring.toOppositeModule` is uniformly continuous. -/
instance Ring.uniformContinuousConstSMul_op [Ring R] [UniformSpace R] [UniformAddGroup R]
    [ContinuousMul R] : UniformContinuousConstSMul Rᵐᵒᵖ R :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _
#align ring.has_uniform_continuous_const_op_smul Ring.uniformContinuousConstSMul_op

section SMul

variable [SMul M X]

@[to_additive]
instance (priority := 100) UniformContinuousConstSMul.to_continuousConstSMul
    [UniformContinuousConstSMul M X] : ContinuousConstSMul M X :=
  ⟨fun c => (uniformContinuous_const_smul c).continuous⟩
#align has_uniform_continuous_const_smul.to_has_continuous_const_smul UniformContinuousConstSMul.to_continuousConstSMul
#align has_uniform_continuous_const_vadd.to_has_continuous_const_vadd UniformContinuousConstVAdd.to_continuousConstVAdd

variable {M X Y}

@[to_additive]
theorem UniformContinuous.const_smul [UniformContinuousConstSMul M X] {f : Y → X}
    (hf : UniformContinuous f) (c : M) : UniformContinuous (c • f) :=
  (uniformContinuous_const_smul c).comp hf
#align uniform_continuous.const_smul UniformContinuous.const_smul
#align uniform_continuous.const_vadd UniformContinuous.const_vadd

@[to_additive]
lemma UniformInducing.uniformContinuousConstSMul [SMul M Y] [UniformContinuousConstSMul M Y]
    {f : X → Y} (hf : UniformInducing f) (hsmul : ∀ (c : M) x, f (c • x) = c • f x) :
    UniformContinuousConstSMul M X where
  uniformContinuous_const_smul c := by
    simpa only [hf.uniformContinuous_iff, Function.comp_def, hsmul]
      using hf.uniformContinuous.const_smul c

/-- If a scalar action is central, then its right action is uniform continuous when its left action
is. -/
@[to_additive "If an additive action is central, then its right action is uniform
continuous when its left action is."]
instance (priority := 100) UniformContinuousConstSMul.op [SMul Mᵐᵒᵖ X] [IsCentralScalar M X]
    [UniformContinuousConstSMul M X] : UniformContinuousConstSMul Mᵐᵒᵖ X :=
  ⟨MulOpposite.rec' fun c ↦ by simpa only [op_smul_eq_smul] using uniformContinuous_const_smul c⟩
#align has_uniform_continuous_const_smul.op UniformContinuousConstSMul.op
#align has_uniform_continuous_const_vadd.op UniformContinuousConstVAdd.op

@[to_additive]
instance MulOpposite.uniformContinuousConstSMul [UniformContinuousConstSMul M X] :
    UniformContinuousConstSMul M Xᵐᵒᵖ :=
  ⟨fun c =>
    MulOpposite.uniformContinuous_op.comp <| MulOpposite.uniformContinuous_unop.const_smul c⟩
#align mul_opposite.has_uniform_continuous_const_smul MulOpposite.uniformContinuousConstSMul
#align add_opposite.has_uniform_continuous_const_vadd AddOpposite.uniformContinuousConstVAdd

end SMul

@[to_additive]
instance UniformGroup.to_uniformContinuousConstSMul {G : Type u} [Group G] [UniformSpace G]
    [UniformGroup G] : UniformContinuousConstSMul G G :=
  ⟨fun _ => uniformContinuous_const.mul uniformContinuous_id⟩
#align uniform_group.to_has_uniform_continuous_const_smul UniformGroup.to_uniformContinuousConstSMul
#align uniform_add_group.to_has_uniform_continuous_const_vadd UniformAddGroup.to_uniformContinuousConstVAdd

namespace UniformSpace

namespace Completion

section SMul

variable [SMul M X]

@[to_additive]
noncomputable instance : SMul M (Completion X) :=
  ⟨fun c => Completion.map (c • ·)⟩

@[to_additive]
theorem smul_def (c : M) (x : Completion X) : c • x = Completion.map (c • ·) x :=
  rfl
#align uniform_space.completion.smul_def UniformSpace.Completion.smul_def
#align uniform_space.completion.vadd_def UniformSpace.Completion.vadd_def

@[to_additive]
instance : UniformContinuousConstSMul M (Completion X) :=
  ⟨fun _ => uniformContinuous_map⟩

@[to_additive instVAddAssocClass]
instance instIsScalarTower [SMul N X] [SMul M N] [UniformContinuousConstSMul M X]
    [UniformContinuousConstSMul N X] [IsScalarTower M N X] : IsScalarTower M N (Completion X) :=
  ⟨fun m n x => by
    have : _ = (_ : Completion X → Completion X) :=
      map_comp (uniformContinuous_const_smul m) (uniformContinuous_const_smul n)
    refine Eq.trans ?_ (congr_fun this.symm x)
    exact congr_arg (fun f => Completion.map f x) (funext (smul_assoc _ _))⟩
#align uniform_space.completion.is_scalar_tower UniformSpace.Completion.instIsScalarTower
#align uniform_space.completion.vadd_assoc_class UniformSpace.Completion.instVAddAssocClass

@[to_additive]
instance [SMul N X] [SMulCommClass M N X] [UniformContinuousConstSMul M X]
    [UniformContinuousConstSMul N X] : SMulCommClass M N (Completion X) :=
  ⟨fun m n x => by
    have hmn : m • n • x = (Completion.map (SMul.smul m) ∘ Completion.map (SMul.smul n)) x := rfl
    have hnm : n • m • x = (Completion.map (SMul.smul n) ∘ Completion.map (SMul.smul m)) x := rfl
    rw [hmn, hnm, map_comp, map_comp]
    · exact congr_arg (fun f => Completion.map f x) (funext (smul_comm _ _))
    repeat' exact uniformContinuous_const_smul _⟩

@[to_additive]
instance [SMul Mᵐᵒᵖ X] [IsCentralScalar M X] : IsCentralScalar M (Completion X) :=
  ⟨fun c a => (congr_arg fun f => Completion.map f a) <| funext (op_smul_eq_smul c)⟩

variable {M X}
variable [UniformContinuousConstSMul M X]

@[to_additive (attr := simp, norm_cast)]
theorem coe_smul (c : M) (x : X) : (↑(c • x) : Completion X) = c • (x : Completion X) :=
  (map_coe (uniformContinuous_const_smul c) x).symm
#align uniform_space.completion.coe_smul UniformSpace.Completion.coe_smul
#align uniform_space.completion.coe_vadd UniformSpace.Completion.coe_vadd

end SMul

@[to_additive]
noncomputable instance [Monoid M] [MulAction M X] [UniformContinuousConstSMul M X] :
    MulAction M (Completion X) where
  smul := (· • ·)
  one_smul := ext' (continuous_const_smul _) continuous_id fun a => by rw [← coe_smul, one_smul]
  mul_smul x y :=
    ext' (continuous_const_smul _) ((continuous_const_smul _).const_smul _) fun a => by
      simp only [← coe_smul, mul_smul]

end Completion

end UniformSpace
