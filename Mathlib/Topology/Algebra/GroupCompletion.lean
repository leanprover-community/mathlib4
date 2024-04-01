/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Mitchell Lee
-/
import Mathlib.Topology.Algebra.UniformGroup
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.UniformSpace.Completion

#align_import topology.algebra.group_completion from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Completion of topological groups:

This files endows the completion of a topological abelian group with a group structure.
More precisely the instance `UniformSpace.Completion.addGroup` builds an abelian group structure
on the completion of an abelian group endowed with a compatible uniform structure.
Then the instance `UniformSpace.Completion.uniformAddGroup` proves this group structure is
compatible with the completed uniform structure. The compatibility condition is `UniformAddGroup`.

## Main declarations:

Beyond the instances explained above (that don't have to be explicitly invoked),
the main constructions deal with continuous group morphisms.

* `MonoidHom.extension`: extends a continuous group morphism from `G`
  to a complete separated group `H` to `Completion G`.
* `MonoidHom.completion`: promotes a continuous group morphism
  from `G` to `H` into a continuous group morphism
  from `Completion G` to `Completion H`.
-/


noncomputable section

variable {M R α β : Type*}

section Group

open UniformSpace CauchyFilter Filter Set

variable [UniformSpace α]

@[to_additive]
instance [One α] : One (Completion α) :=
  ⟨(1 : α)⟩

@[to_additive]
noncomputable instance [Inv α] : Inv (Completion α) :=
  ⟨Completion.map (fun a ↦ a⁻¹ : α → α)⟩

@[to_additive]
noncomputable instance [Mul α] : Mul (Completion α) :=
  ⟨Completion.map₂ (· * ·)⟩

@[to_additive]
noncomputable instance [Div α] : Div (Completion α) :=
  ⟨Completion.map₂ Div.div⟩

@[to_additive (attr := norm_cast) coe_zero]
theorem UniformSpace.Completion.coe_one' [One α] : ((1 : α) : Completion α) = 1 :=
  rfl
#align uniform_space.completion.coe_zero UniformSpace.Completion.coe_zero

end Group

namespace UniformSpace.Completion

open UniformSpace

section Zero

instance [UniformSpace α] [MonoidWithZero M] [Zero α] [MulActionWithZero M α]
    [UniformContinuousConstSMul M α] : MulActionWithZero M (Completion α) :=
  { (inferInstance : MulAction M <| Completion α) with
    smul_zero := fun r ↦ by rw [← coe_zero, ← coe_smul, MulActionWithZero.smul_zero r]
    zero_smul :=
      ext' (continuous_const_smul _) continuous_const fun a ↦ by
        rw [← coe_smul, zero_smul, coe_zero] }

end Zero

section UniformGroup

variable [UniformSpace α] [Group α] [UniformGroup α]

@[to_additive (attr := norm_cast)]
theorem coe_inv (a : α) : ((a⁻¹ : α) : Completion α) = (a : Completion α)⁻¹ :=
  (map_coe uniformContinuous_inv a).symm
#align uniform_space.completion.coe_neg UniformSpace.Completion.coe_neg

@[to_additive (attr := norm_cast)]
theorem coe_div (a b : α) : ((a / b : α) : Completion α) = a / b :=
  (map₂_coe_coe a b Div.div uniformContinuous_div).symm
#align uniform_space.completion.coe_sub UniformSpace.Completion.coe_sub

@[to_additive (attr := norm_cast) coe_add]
theorem coe_mul' (a b : α) : ((a * b : α) : Completion α) = a * b :=
  (map₂_coe_coe a b (· * ·) uniformContinuous_mul).symm
#align uniform_space.completion.coe_add UniformSpace.Completion.coe_add

@[to_additive]
noncomputable instance : Monoid (Completion α) :=
  { (inferInstance : One <| Completion α),
    (inferInstance : Mul <| Completion α) with
    one_mul := fun a ↦
      Completion.induction_on a
        (isClosed_eq (continuous_map₂ continuous_const continuous_id) continuous_id) fun a ↦
        show 1 * (a : Completion α) = a by rw [← coe_one', ← coe_mul', one_mul]
    mul_one := fun a ↦
      Completion.induction_on a
        (isClosed_eq (continuous_map₂ continuous_id continuous_const) continuous_id) fun a ↦
        show (a : Completion α) * 1 = a by rw [← coe_one', ← coe_mul', mul_one]
    mul_assoc := fun a b c ↦
      Completion.induction_on₃ a b c
        (isClosed_eq
          (continuous_map₂ (continuous_map₂ continuous_fst (continuous_fst.comp continuous_snd))
            (continuous_snd.comp continuous_snd))
          (continuous_map₂ continuous_fst
            (continuous_map₂ (continuous_fst.comp continuous_snd)
              (continuous_snd.comp continuous_snd))))
        fun a b c ↦
        show (a : Completion α) * b * c = a * (b * c) by repeat' rw_mod_cast [mul_assoc]
    npow := fun n ↦ Completion.map (fun a ↦ a ^ n : α → α)
    npow_zero := fun a ↦
      Completion.induction_on a (isClosed_eq continuous_map continuous_const) fun a ↦
        show Completion.map (fun a ↦ a ^ 0 : α → α) a = 1 by
          simp_rw [map_coe (uniformContinuous_pow_const _), pow_zero, coe_one']
    npow_succ := fun n a ↦
      Completion.induction_on a
        (isClosed_eq continuous_map <| continuous_map₂ continuous_map continuous_id) fun a ↦
        show Completion.map (fun a ↦ a ^ (n + 1) : α → α) a =
            Completion.map (fun a ↦ a ^ n : α → α) a * a by
          simp_rw [map_coe (uniformContinuous_pow_const _), pow_succ, coe_mul'] }

@[to_additive]
noncomputable instance : DivInvMonoid (Completion α) :=
  { (inferInstance : Monoid <| Completion α),
    (inferInstance : Inv <| Completion α),
    (inferInstance : Div <| Completion α) with
    div_eq_mul_inv := fun a b ↦
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_map₂ continuous_fst continuous_snd)
          (continuous_map₂ continuous_fst (Completion.continuous_map.comp continuous_snd)))
        fun a b ↦ mod_cast congr_arg ((↑) : α → Completion α) (div_eq_mul_inv a b)
    zpow := fun n ↦ Completion.map (fun a ↦ a ^ n : α → α)
    zpow_zero' := fun a ↦
      Completion.induction_on a (isClosed_eq continuous_map continuous_const) fun a ↦
        show Completion.map (fun a ↦ a ^ (0 : ℤ) : α → α) a = 1 by
          rw [map_coe (uniformContinuous_zpow_const _), zpow_zero, coe_one']
    zpow_succ' := fun n a ↦
      Completion.induction_on a
        (isClosed_eq continuous_map <| continuous_map₂ continuous_map continuous_id) fun a ↦
          show Completion.map (fun a ↦ a ^ (n + 1 : ℤ) : α → α) a =
              Completion.map (fun a ↦ a ^ (n : ℤ) : α → α) a * a by
            simp_rw [map_coe (uniformContinuous_zpow_const _), zpow_add, zpow_one, coe_mul']
    zpow_neg' := fun n a ↦
      Completion.induction_on a
        (isClosed_eq continuous_map <| Completion.continuous_map.comp continuous_map) fun a ↦
          show Completion.map (fun a ↦ a ^ (Int.negSucc n) : α → α) a =
              (Completion.map (fun a ↦ a ^ (n + 1 : ℤ) : α → α) a)⁻¹ by
            simp_rw [map_coe (uniformContinuous_zpow_const _), zpow_negSucc]
            norm_cast }

@[to_additive]
noncomputable instance group : Group (Completion α) :=
  { (inferInstance : DivInvMonoid <| Completion α) with
    mul_left_inv := fun a ↦
      Completion.induction_on a
        (isClosed_eq (continuous_map₂ Completion.continuous_map continuous_id) continuous_const)
        fun a ↦
        show (a : Completion α)⁻¹ * a = 1 by
          rw_mod_cast [mul_left_inv]
          rfl }

@[to_additive]
noncomputable instance uniformGroup : UniformGroup (Completion α) :=
  ⟨uniformContinuous_map₂ Div.div⟩

/-- The map from a group to its completion as a group hom. -/
@[to_additive (attr := simps) toCompl]
def toCompl_mul : α →* Completion α where
  toFun := (↑)
  map_mul' := coe_mul'
  map_one' := coe_one'
#align uniform_space.completion.to_compl UniformSpace.Completion.toCompl

@[to_additive]
theorem continuous_toCompl_mul : Continuous (toCompl_mul : α →* Completion α) :=
  continuous_coe α
#align uniform_space.completion.continuous_to_compl UniformSpace.Completion.continuous_toCompl_add

variable (α)

@[to_additive]
theorem denseInducing_toCompl_mul : DenseInducing (toCompl_mul : α →* Completion α) :=
  denseInducing_coe
#align uniform_space.completion.dense_inducing_to_compl UniformSpace.Completion.denseInducing_toCompl_add

variable {α}

end UniformGroup

section UniformAddGroup

variable [UniformSpace α] [AddGroup α] [UniformAddGroup α]

instance {M} [Monoid M] [DistribMulAction M α] [UniformContinuousConstSMul M α] :
    DistribMulAction M (Completion α) :=
  { (inferInstance : MulAction M <| Completion α) with
    smul_add := fun r x y ↦
      induction_on₂ x y
        (isClosed_eq ((continuous_fst.add continuous_snd).const_smul _)
          ((continuous_fst.const_smul _).add (continuous_snd.const_smul _)))
        fun a b ↦ by simp only [← coe_add, ← coe_smul, smul_add]
    smul_zero := fun r ↦ by rw [← coe_zero, ← coe_smul, smul_zero r] }

end UniformAddGroup

section UniformCommGroup

variable [UniformSpace α] [CommGroup α] [UniformGroup α]

@[to_additive]
noncomputable instance : CommGroup (Completion α) :=
  { (inferInstance : Group <| Completion α) with
    mul_comm := fun a b ↦
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_map₂ continuous_fst continuous_snd)
          (continuous_map₂ continuous_snd continuous_fst))
        fun x y ↦ by
        change (x : Completion α) * ↑y = ↑y * ↑x
        rw [← coe_mul', ← coe_mul', mul_comm] }

end UniformCommGroup

section UniformAddCommGroup

variable [UniformSpace α] [AddCommGroup α] [UniformAddGroup α]

instance instModule [Semiring R] [Module R α] [UniformContinuousConstSMul R α] :
    Module R (Completion α) :=
  { (inferInstance : DistribMulAction R <| Completion α),
    (inferInstance : MulActionWithZero R <| Completion α) with
    add_smul := fun a b ↦
      ext' (continuous_const_smul _) ((continuous_const_smul _).add (continuous_const_smul _))
        fun x ↦ by
          rw [← coe_smul, add_smul, coe_add, coe_smul, coe_smul] }
#align uniform_space.completion.module UniformSpace.Completion.instModule

end UniformAddCommGroup

end UniformSpace.Completion

section MonoidHom

variable [UniformSpace α] [Group α] [UniformGroup α] [UniformSpace β] [Group β]
  [UniformGroup β]

open UniformSpace UniformSpace.Completion

/-- Extension to the completion of a continuous multiplicative group hom. -/
@[to_additive "Extension to the completion of a continuous additive group hom."]
noncomputable def MonoidHom.extension [CompleteSpace β] [T0Space β] (f : α →* β)
    (hf : Continuous f) : Completion α →* β :=
  have hf : UniformContinuous f := uniformContinuous_monoidHom_of_continuous hf
  { toFun := Completion.extension f
    map_one' := by rw [← coe_one', extension_coe hf, f.map_one]
    map_mul' := fun a b ↦
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_extension.comp continuous_mul)
          ((continuous_extension.comp continuous_fst).mul
            (continuous_extension.comp continuous_snd)))
        fun a b ↦
        show Completion.extension f _ = Completion.extension f _ * Completion.extension f _ by
        rw_mod_cast [extension_coe hf, extension_coe hf, extension_coe hf, f.map_mul] }
#align add_monoid_hom.extension AddMonoidHom.extension

@[to_additive]
theorem MonoidHom.extension_coe [CompleteSpace β] [T0Space β] (f : α →* β)
    (hf : Continuous f) (a : α) : f.extension hf a = f a :=
  UniformSpace.Completion.extension_coe (uniformContinuous_monoidHom_of_continuous hf) a
#align add_monoid_hom.extension_coe AddMonoidHom.extension_coe

@[to_additive (attr := continuity)]
theorem MonoidHom.continuous_extension [CompleteSpace β] [T0Space β] (f : α →* β)
    (hf : Continuous f) : Continuous (f.extension hf) :=
  UniformSpace.Completion.continuous_extension
#align add_monoid_hom.continuous_extension AddMonoidHom.continuous_extension

/-- Completion of a continuous multiplicative group hom, as a group hom. -/
@[to_additive "Completion of a continuous additive group hom, as a group hom."]
noncomputable def MonoidHom.completion (f : α →* β) (hf : Continuous f) :
    Completion α →* Completion β :=
  (toCompl_mul.comp f).extension (continuous_toCompl_mul.comp hf)
#align add_monoid_hom.completion AddMonoidHom.completion

@[to_additive (attr := continuity)]
theorem MonoidHom.continuous_completion (f : α →* β) (hf : Continuous f) :
    Continuous (MonoidHom.completion f hf : Completion α → Completion β) :=
  continuous_map
#align add_monoid_hom.continuous_completion AddMonoidHom.continuous_completion

@[to_additive]
theorem MonoidHom.completion_coe (f : α →* β) (hf : Continuous f) (a : α) :
    MonoidHom.completion f hf a = f a :=
  map_coe (uniformContinuous_monoidHom_of_continuous hf) a
#align add_monoid_hom.completion_coe AddMonoidHom.completion_coe

@[to_additive]
theorem MonoidHom.completion_one :
    MonoidHom.completion (1 : α →* β) continuous_const = 1 := by
  ext x
  refine Completion.induction_on x ?_ ?_
  · apply isClosed_eq (MonoidHom.continuous_completion (1 : α →* β) continuous_const)
    simp [continuous_const]
  · intro a
    simp [(1 : α →* β).completion_coe continuous_const, coe_one']
#align add_monoid_hom.completion_zero AddMonoidHom.completion_zero

@[to_additive]
theorem MonoidHom.completion_mul {γ : Type*} [CommGroup γ] [UniformSpace γ]
    [UniformGroup γ] (f g : α →* γ) (hf : Continuous f) (hg : Continuous g) :
    MonoidHom.completion (f * g) (hf.mul hg) =
    MonoidHom.completion f hf * MonoidHom.completion g hg := by
  have hfg := hf.mul hg
  ext x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq ((f * g).continuous_completion hfg)
      ((f.continuous_completion hf).mul (g.continuous_completion hg))
  · intro a
    simp [(f * g).completion_coe hfg, coe_mul', f.completion_coe hf, g.completion_coe hg]
#align add_monoid_hom.completion_add AddMonoidHom.completion_add

end MonoidHom
