/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Module.Opposite
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.IsUniformGroup.Defs

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

/-- A multiplicative action such that for all `c`,
the map `fun x ↦ c • x` is uniformly continuous. -/
@[to_additive]
class UniformContinuousConstSMul [SMul M X] : Prop where
  uniformContinuous_const_smul : ∀ c : M, UniformContinuous (c • · : X → X)

export UniformContinuousConstVAdd (uniformContinuous_const_vadd)

export UniformContinuousConstSMul (uniformContinuous_const_smul)

instance AddMonoid.uniformContinuousConstSMul_nat [AddGroup X] [IsUniformAddGroup X] :
    UniformContinuousConstSMul ℕ X :=
  ⟨uniformContinuous_const_nsmul⟩

instance AddGroup.uniformContinuousConstSMul_int [AddGroup X] [IsUniformAddGroup X] :
    UniformContinuousConstSMul ℤ X :=
  ⟨uniformContinuous_const_zsmul⟩

/-- A `DistribMulAction` that is continuous on a uniform group is uniformly continuous.
This can't be an instance due to it forming a loop with
`UniformContinuousConstSMul.to_continuousConstSMul` -/
theorem uniformContinuousConstSMul_of_continuousConstSMul [Monoid R] [AddGroup M]
    [DistribMulAction R M] [UniformSpace M] [IsUniformAddGroup M] [ContinuousConstSMul R M] :
    UniformContinuousConstSMul R M :=
  ⟨fun r =>
    uniformContinuous_of_continuousAt_zero (DistribMulAction.toAddMonoidHom M r)
      (Continuous.continuousAt (continuous_const_smul r))⟩

/-- The action of `Semiring.toModule` is uniformly continuous. -/
instance Ring.uniformContinuousConstSMul [Ring R] [UniformSpace R] [IsUniformAddGroup R]
    [ContinuousMul R] : UniformContinuousConstSMul R R :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _

/-- The action of `Semiring.toOppositeModule` is uniformly continuous. -/
instance Ring.uniformContinuousConstSMul_op [Ring R] [UniformSpace R] [IsUniformAddGroup R]
    [ContinuousMul R] : UniformContinuousConstSMul Rᵐᵒᵖ R :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _

section SMul

variable [SMul M X]

@[to_additive]
instance (priority := 100) UniformContinuousConstSMul.to_continuousConstSMul
    [UniformContinuousConstSMul M X] : ContinuousConstSMul M X :=
  ⟨fun c => (uniformContinuous_const_smul c).continuous⟩

variable {M X Y}

@[to_additive]
theorem UniformContinuous.const_smul [UniformContinuousConstSMul M X] {f : Y → X}
    (hf : UniformContinuous f) (c : M) : UniformContinuous (c • f) :=
  (uniformContinuous_const_smul c).comp hf

@[to_additive]
lemma IsUniformInducing.uniformContinuousConstSMul [SMul M Y] [UniformContinuousConstSMul M Y]
    {f : X → Y} (hf : IsUniformInducing f) (hsmul : ∀ (c : M) x, f (c • x) = c • f x) :
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

@[to_additive]
instance MulOpposite.uniformContinuousConstSMul [UniformContinuousConstSMul M X] :
    UniformContinuousConstSMul M Xᵐᵒᵖ :=
  ⟨fun c =>
    MulOpposite.uniformContinuous_op.comp <| MulOpposite.uniformContinuous_unop.const_smul c⟩

end SMul

@[to_additive]
instance IsUniformGroup.to_uniformContinuousConstSMul {G : Type u} [Group G] [UniformSpace G]
    [IsUniformGroup G] : UniformContinuousConstSMul G G :=
  ⟨fun _ => uniformContinuous_const.mul uniformContinuous_id⟩

section Ring

variable {R β : Type*} [Ring R] [UniformSpace R] [UniformSpace β]

theorem UniformContinuous.const_mul' [UniformContinuousConstSMul R R] {f : β → R}
    (hf : UniformContinuous f) (a : R) : UniformContinuous fun x ↦ a * f x :=
  hf.const_smul a

theorem UniformContinuous.mul_const' [UniformContinuousConstSMul Rᵐᵒᵖ R] {f : β → R}
    (hf : UniformContinuous f) (a : R) : UniformContinuous fun x ↦ f x * a :=
  hf.const_smul (MulOpposite.op a)

theorem uniformContinuous_mul_left' [UniformContinuousConstSMul R R] (a : R) :
    UniformContinuous fun b : R => a * b :=
  uniformContinuous_id.const_mul' _

theorem uniformContinuous_mul_right' [UniformContinuousConstSMul Rᵐᵒᵖ R] (a : R) :
    UniformContinuous fun b : R => b * a :=
  uniformContinuous_id.mul_const' _

theorem UniformContinuous.div_const' {R β : Type*} [DivisionRing R] [UniformSpace R]
    [UniformContinuousConstSMul Rᵐᵒᵖ R] [UniformSpace β] {f : β → R}
    (hf : UniformContinuous f) (a : R) :
    UniformContinuous fun x ↦ f x / a := by
  simpa [div_eq_mul_inv] using hf.mul_const' a⁻¹

theorem uniformContinuous_div_const' {R : Type*} [DivisionRing R] [UniformSpace R]
    [UniformContinuousConstSMul Rᵐᵒᵖ R] (a : R) :
    UniformContinuous fun b : R => b / a :=
  uniformContinuous_id.div_const' _

end Ring

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

@[to_additive]
instance : UniformContinuousConstSMul M (Completion X) :=
  ⟨fun _ => uniformContinuous_map⟩

@[to_additive]
instance instIsScalarTower [SMul N X] [SMul M N] [UniformContinuousConstSMul M X]
    [UniformContinuousConstSMul N X] [IsScalarTower M N X] : IsScalarTower M N (Completion X) :=
  ⟨fun m n x => by
    have : _ = (_ : Completion X → Completion X) :=
      map_comp (uniformContinuous_const_smul m) (uniformContinuous_const_smul n)
    refine Eq.trans ?_ (congr_fun this.symm x)
    exact congr_arg (fun f => Completion.map f x) (funext (smul_assoc _ _))⟩

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
