/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

! This file was ported from Lean 3 source module topology.algebra.group_completion
! leanprover-community/mathlib commit a148d797a1094ab554ad4183a4ad6f130358ef64
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Topology.Algebra.UniformMulAction
import Mathbin.Topology.UniformSpace.Completion

/-!
# Completion of topological groups:

This files endows the completion of a topological abelian group with a group structure.
More precisely the instance `uniform_space.completion.add_group` builds an abelian group structure
on the completion of an abelian group endowed with a compatible uniform structure.
Then the instance `uniform_space.completion.uniform_add_group` proves this group structure is
compatible with the completed uniform structure. The compatibility condition is `uniform_add_group`.

## Main declarations:

Beyond the instances explained above (that don't have to be explicitly invoked),
the main constructions deal with continuous group morphisms.

* `add_monoid_hom.extension`: extends a continuous group morphism from `G`
  to a complete separated group `H` to `completion G`.
* `add_monoid_hom.completion`: promotes a continuous group morphism
  from `G` to `H` into a continuous group morphism
  from `completion G` to `completion H`.
-/


noncomputable section

variable {M R α β : Type _}

section Group

open UniformSpace CauchyFilter Filter Set

variable [UniformSpace α]

instance [Zero α] : Zero (Completion α) :=
  ⟨(0 : α)⟩

instance [Neg α] : Neg (Completion α) :=
  ⟨Completion.map (fun a => -a : α → α)⟩

instance [Add α] : Add (Completion α) :=
  ⟨Completion.map₂ (· + ·)⟩

instance [Sub α] : Sub (Completion α) :=
  ⟨Completion.map₂ Sub.sub⟩

@[norm_cast]
theorem UniformSpace.Completion.coe_zero [Zero α] : ((0 : α) : Completion α) = 0 :=
  rfl
#align uniform_space.completion.coe_zero UniformSpace.Completion.coe_zero

end Group

namespace UniformSpace.Completion

open UniformSpace

section Zero

instance [UniformSpace α] [MonoidWithZero M] [Zero α] [MulActionWithZero M α]
    [UniformContinuousConstSMul M α] : MulActionWithZero M (Completion α) :=
  { Completion.mulAction M α with
    smul := (· • ·)
    smul_zero := fun r => by rw [← coe_zero, ← coe_smul, MulActionWithZero.smul_zero r]
    zero_smul :=
      ext' (continuous_const_smul _) continuous_const fun a => by
        rw [← coe_smul, zero_smul, coe_zero] }

end Zero

section UniformAddGroup

variable [UniformSpace α] [AddGroup α] [UniformAddGroup α]

@[norm_cast]
theorem coe_neg (a : α) : ((-a : α) : Completion α) = -a :=
  (map_coe uniformContinuous_neg a).symm
#align uniform_space.completion.coe_neg UniformSpace.Completion.coe_neg

@[norm_cast]
theorem coe_sub (a b : α) : ((a - b : α) : Completion α) = a - b :=
  (map₂_coe_coe a b Sub.sub uniformContinuous_sub).symm
#align uniform_space.completion.coe_sub UniformSpace.Completion.coe_sub

@[norm_cast]
theorem coe_add (a b : α) : ((a + b : α) : Completion α) = a + b :=
  (map₂_coe_coe a b (· + ·) uniformContinuous_add).symm
#align uniform_space.completion.coe_add UniformSpace.Completion.coe_add

instance : AddMonoid (Completion α) :=
  { Completion.hasZero,
    Completion.hasAdd with
    zero_add := fun a =>
      Completion.induction_on a
        (isClosed_eq (continuous_map₂ continuous_const continuous_id) continuous_id) fun a =>
        show 0 + (a : Completion α) = a by rw_mod_cast [zero_add]
    add_zero := fun a =>
      Completion.induction_on a
        (isClosed_eq (continuous_map₂ continuous_id continuous_const) continuous_id) fun a =>
        show (a : Completion α) + 0 = a by rw_mod_cast [add_zero]
    add_assoc := fun a b c =>
      Completion.induction_on₃ a b c
        (isClosed_eq
          (continuous_map₂ (continuous_map₂ continuous_fst (continuous_fst.comp continuous_snd))
            (continuous_snd.comp continuous_snd))
          (continuous_map₂ continuous_fst
            (continuous_map₂ (continuous_fst.comp continuous_snd)
              (continuous_snd.comp continuous_snd))))
        fun a b c =>
        show (a : Completion α) + b + c = a + (b + c) by repeat' rw_mod_cast [add_assoc]
    nsmul := (· • ·)
    nsmul_zero := fun a =>
      Completion.induction_on a (isClosed_eq continuous_map continuous_const) fun a => by
        rw [← coe_smul, ← coe_zero, zero_smul]
    nsmul_succ := fun n a =>
      Completion.induction_on a
        (isClosed_eq continuous_map <| continuous_map₂ continuous_id continuous_map) fun a => by
        rw_mod_cast [succ_nsmul] }

instance : SubNegMonoid (Completion α) :=
  { Completion.addMonoid, Completion.hasNeg,
    Completion.hasSub with
    sub_eq_add_neg := fun a b =>
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_map₂ continuous_fst continuous_snd)
          (continuous_map₂ continuous_fst (Completion.continuous_map.comp continuous_snd)))
        fun a b => by exact_mod_cast congr_arg coe (sub_eq_add_neg a b)
    zsmul := (· • ·)
    zsmul_zero' := fun a =>
      Completion.induction_on a (isClosed_eq continuous_map continuous_const) fun a =>
        by
        rw_mod_cast [zero_smul]
        rfl
    zsmul_succ' := fun n a =>
      Completion.induction_on a
        (isClosed_eq continuous_map <| continuous_map₂ continuous_id continuous_map) fun a => by
        rw_mod_cast [show Int.ofNat n.succ • a = a + Int.ofNat n • a from
            SubNegMonoid.zsmul_succ' n a]
    zsmul_neg' := fun n a =>
      Completion.induction_on a
        (isClosed_eq continuous_map <| Completion.continuous_map.comp continuous_map) fun a => by
        rw [← coe_smul, ← coe_smul, ← coe_neg,
          show -[n+1] • a = -((n.succ : ℤ) • a) from SubNegMonoid.zsmul_neg' n a] }

instance : AddGroup (Completion α) :=
  { Completion.subNegMonoid with
    add_left_neg := fun a =>
      Completion.induction_on a
        (isClosed_eq (continuous_map₂ Completion.continuous_map continuous_id) continuous_const)
        fun a =>
        show -(a : Completion α) + a = 0
          by
          rw_mod_cast [add_left_neg]
          rfl }

instance : UniformAddGroup (Completion α) :=
  ⟨uniformContinuous_map₂ Sub.sub⟩

instance {M} [Monoid M] [DistribMulAction M α] [UniformContinuousConstSMul M α] :
    DistribMulAction M (Completion α) :=
  { Completion.mulAction M α with
    smul := (· • ·)
    smul_add := fun r x y =>
      induction_on₂ x y
        (isClosed_eq ((continuous_fst.add continuous_snd).const_smul _)
          ((continuous_fst.const_smul _).add (continuous_snd.const_smul _)))
        fun a b => by simp only [← coe_add, ← coe_smul, smul_add]
    smul_zero := fun r => by rw [← coe_zero, ← coe_smul, smul_zero r] }

/-- The map from a group to its completion as a group hom. -/
@[simps]
def toCompl : α →+ Completion α where
  toFun := coe
  map_add' := coe_add
  map_zero' := coe_zero
#align uniform_space.completion.to_compl UniformSpace.Completion.toCompl

theorem continuous_toCompl : Continuous (toCompl : α → Completion α) :=
  continuous_coe α
#align uniform_space.completion.continuous_to_compl UniformSpace.Completion.continuous_toCompl

variable (α)

theorem denseInducing_toCompl : DenseInducing (toCompl : α → Completion α) :=
  denseInducing_coe
#align uniform_space.completion.dense_inducing_to_compl UniformSpace.Completion.denseInducing_toCompl

variable {α}

end UniformAddGroup

section UniformAddCommGroup

variable [UniformSpace α] [AddCommGroup α] [UniformAddGroup α]

instance : AddCommGroup (Completion α) :=
  { Completion.addGroup with
    add_comm := fun a b =>
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_map₂ continuous_fst continuous_snd)
          (continuous_map₂ continuous_snd continuous_fst))
        fun x y => by
        change ↑x + ↑y = ↑y + ↑x
        rw [← coe_add, ← coe_add, add_comm] }

instance [Semiring R] [Module R α] [UniformContinuousConstSMul R α] : Module R (Completion α) :=
  { Completion.distribMulAction,
    Completion.mulActionWithZero with
    smul := (· • ·)
    add_smul := fun a b =>
      ext' (continuous_const_smul _) ((continuous_const_smul _).add (continuous_const_smul _))
        fun x => by
        norm_cast
        rw [add_smul] }

end UniformAddCommGroup

end UniformSpace.Completion

section AddMonoidHom

variable [UniformSpace α] [AddGroup α] [UniformAddGroup α] [UniformSpace β] [AddGroup β]
  [UniformAddGroup β]

open UniformSpace UniformSpace.Completion

/-- Extension to the completion of a continuous group hom. -/
def AddMonoidHom.extension [CompleteSpace β] [SeparatedSpace β] (f : α →+ β) (hf : Continuous f) :
    Completion α →+ β :=
  have hf : UniformContinuous f := uniformContinuous_addMonoidHom_of_continuous hf
  { toFun := Completion.extension f
    map_zero' := by rw [← coe_zero, extension_coe hf, f.map_zero]
    map_add' := fun a b =>
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_extension.comp continuous_add)
          ((continuous_extension.comp continuous_fst).add
            (continuous_extension.comp continuous_snd)))
        fun a b => by
        rw_mod_cast [extension_coe hf, extension_coe hf, extension_coe hf, f.map_add] }
#align add_monoid_hom.extension AddMonoidHom.extension

theorem AddMonoidHom.extension_coe [CompleteSpace β] [SeparatedSpace β] (f : α →+ β)
    (hf : Continuous f) (a : α) : f.extension hf a = f a :=
  extension_coe (uniformContinuous_addMonoidHom_of_continuous hf) a
#align add_monoid_hom.extension_coe AddMonoidHom.extension_coe

@[continuity]
theorem AddMonoidHom.continuous_extension [CompleteSpace β] [SeparatedSpace β] (f : α →+ β)
    (hf : Continuous f) : Continuous (f.extension hf) :=
  continuous_extension
#align add_monoid_hom.continuous_extension AddMonoidHom.continuous_extension

/-- Completion of a continuous group hom, as a group hom. -/
def AddMonoidHom.completion (f : α →+ β) (hf : Continuous f) : Completion α →+ Completion β :=
  (toCompl.comp f).extension (continuous_toCompl.comp hf)
#align add_monoid_hom.completion AddMonoidHom.completion

@[continuity]
theorem AddMonoidHom.continuous_completion (f : α →+ β) (hf : Continuous f) :
    Continuous (f.Completion hf : Completion α → Completion β) :=
  ContinuousMap
#align add_monoid_hom.continuous_completion AddMonoidHom.continuous_completion

theorem AddMonoidHom.completion_coe (f : α →+ β) (hf : Continuous f) (a : α) :
    f.Completion hf a = f a :=
  map_coe (uniformContinuous_addMonoidHom_of_continuous hf) a
#align add_monoid_hom.completion_coe AddMonoidHom.completion_coe

theorem AddMonoidHom.completion_zero : (0 : α →+ β).Completion continuous_const = 0 :=
  by
  ext x
  apply completion.induction_on x
  · apply isClosed_eq ((0 : α →+ β).continuous_completion continuous_const)
    simp [continuous_const]
  · intro a
    simp [(0 : α →+ β).completion_coe continuous_const, coe_zero]
#align add_monoid_hom.completion_zero AddMonoidHom.completion_zero

theorem AddMonoidHom.completion_add {γ : Type _} [AddCommGroup γ] [UniformSpace γ]
    [UniformAddGroup γ] (f g : α →+ γ) (hf : Continuous f) (hg : Continuous g) :
    (f + g).Completion (hf.add hg) = f.Completion hf + g.Completion hg :=
  by
  have hfg := hf.add hg
  ext x
  apply completion.induction_on x
  ·
    exact
      isClosed_eq ((f + g).continuous_completion hfg)
        ((f.continuous_completion hf).add (g.continuous_completion hg))
  · intro a
    simp [(f + g).completion_coe hfg, coe_add, f.completion_coe hf, g.completion_coe hg]
#align add_monoid_hom.completion_add AddMonoidHom.completion_add

end AddMonoidHom

