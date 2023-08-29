/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
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

* `AddMonoidHom.extension`: extends a continuous group morphism from `G`
  to a complete separated group `H` to `Completion G`.
* `AddMonoidHom.completion`: promotes a continuous group morphism
  from `G` to `H` into a continuous group morphism
  from `Completion G` to `Completion H`.
-/


noncomputable section

variable {M R α β : Type*}

section Group

open UniformSpace CauchyFilter Filter Set

variable [UniformSpace α]

instance [Zero α] : Zero (Completion α) :=
  ⟨(0 : α)⟩

instance [Neg α] : Neg (Completion α) :=
  ⟨Completion.map (fun a ↦ -a : α → α)⟩

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
  { (inferInstance : MulAction M $ Completion α) with
    smul := (· • ·)
    smul_zero := fun r ↦ by rw [← coe_zero, ← coe_smul, MulActionWithZero.smul_zero r]
                            -- 🎉 no goals
    zero_smul :=
      ext' (continuous_const_smul _) continuous_const fun a ↦ by
        rw [← coe_smul, zero_smul, coe_zero] }
        -- 🎉 no goals

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
  { (inferInstance : Zero $ Completion α),
    (inferInstance : Add $ Completion α) with
    zero_add := fun a ↦
      Completion.induction_on a
        (isClosed_eq (continuous_map₂ continuous_const continuous_id) continuous_id) fun a ↦
        show 0 + (a : Completion α) = a by rw [← coe_zero, ← coe_add, zero_add]
                                           -- 🎉 no goals
    add_zero := fun a ↦
      Completion.induction_on a
        (isClosed_eq (continuous_map₂ continuous_id continuous_const) continuous_id) fun a ↦
        show (a : Completion α) + 0 = a by rw [← coe_zero, ← coe_add, add_zero]
                                           -- 🎉 no goals
    add_assoc := fun a b c ↦
      Completion.induction_on₃ a b c
        (isClosed_eq
          (continuous_map₂ (continuous_map₂ continuous_fst (continuous_fst.comp continuous_snd))
            (continuous_snd.comp continuous_snd))
          (continuous_map₂ continuous_fst
            (continuous_map₂ (continuous_fst.comp continuous_snd)
              (continuous_snd.comp continuous_snd))))
                                                         -- 🎉 no goals
        fun a b c ↦
        show (a : Completion α) + b + c = a + (b + c) by repeat' rw_mod_cast [add_assoc]
    nsmul := (· • ·)
    nsmul_zero := fun a ↦
      Completion.induction_on a (isClosed_eq continuous_map continuous_const) fun a ↦
        show 0 • (a : Completion α) = 0 by rw [← coe_smul, ← coe_zero, zero_smul]
                                           -- 🎉 no goals
    nsmul_succ := fun n a ↦
      Completion.induction_on a
        (isClosed_eq continuous_map <| continuous_map₂ continuous_id continuous_map) fun a ↦
        show (n + 1) • (a : Completion α) = (a : Completion α) + n • (a : Completion α) by
          rw [← coe_smul, succ_nsmul, coe_add, coe_smul] }
          -- 🎉 no goals

instance : SubNegMonoid (Completion α) :=
  { (inferInstance : AddMonoid $ Completion α),
    (inferInstance : Neg $ Completion α),
    (inferInstance : Sub $ Completion α) with
    sub_eq_add_neg := fun a b ↦
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_map₂ continuous_fst continuous_snd)
          (continuous_map₂ continuous_fst (Completion.continuous_map.comp continuous_snd)))
        fun a b ↦ by exact_mod_cast congr_arg ((↑) : α → Completion α) (sub_eq_add_neg a b)
                     -- 🎉 no goals
    zsmul := (· • ·)
    zsmul_zero' := fun a ↦
      Completion.induction_on a (isClosed_eq continuous_map continuous_const) fun a ↦
        show (0 : ℤ) • (a : Completion α) = 0 by rw [← coe_smul, ← coe_zero, zero_smul]
                                                 -- 🎉 no goals
    zsmul_succ' := fun n a ↦
      Completion.induction_on a
        (isClosed_eq continuous_map <| continuous_map₂ continuous_id continuous_map) fun a ↦
          show Int.ofNat n.succ • (a : Completion α) = _ by
            rw [← coe_smul, show Int.ofNat n.succ • a = a + Int.ofNat n • a from
              SubNegMonoid.zsmul_succ' n a, coe_add, coe_smul]
    zsmul_neg' := fun n a ↦
      Completion.induction_on a
        (isClosed_eq continuous_map <| Completion.continuous_map.comp continuous_map) fun a ↦
          show (Int.negSucc n) • (a : Completion α) = _ by
            rw [← coe_smul, show (Int.negSucc n) • a = -((n.succ : ℤ) • a) from
              SubNegMonoid.zsmul_neg' n a, coe_neg, coe_smul] }

instance addGroup : AddGroup (Completion α) :=
  { (inferInstance : SubNegMonoid $ Completion α) with
    add_left_neg := fun a ↦
      Completion.induction_on a
        (isClosed_eq (continuous_map₂ Completion.continuous_map continuous_id) continuous_const)
        fun a ↦
        show -(a : Completion α) + a = 0 by
          rw_mod_cast [add_left_neg]
          -- ⊢ ↑α 0 = 0
          rfl }
          -- 🎉 no goals

instance uniformAddGroup : UniformAddGroup (Completion α) :=
  ⟨uniformContinuous_map₂ Sub.sub⟩

instance {M} [Monoid M] [DistribMulAction M α] [UniformContinuousConstSMul M α] :
    DistribMulAction M (Completion α) :=
  { (inferInstance : MulAction M $ Completion α) with
    smul := (· • ·)
    smul_add := fun r x y ↦
      induction_on₂ x y
        (isClosed_eq ((continuous_fst.add continuous_snd).const_smul _)
          ((continuous_fst.const_smul _).add (continuous_snd.const_smul _)))
        fun a b ↦ by simp only [← coe_add, ← coe_smul, smul_add]
                     -- 🎉 no goals
                            -- 🎉 no goals
    smul_zero := fun r ↦ by rw [← coe_zero, ← coe_smul, smul_zero r] }

/-- The map from a group to its completion as a group hom. -/
@[simps]
def toCompl : α →+ Completion α where
  toFun := (↑)
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
  { (inferInstance : AddGroup $ Completion α) with
    add_comm := fun a b ↦
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_map₂ continuous_fst continuous_snd)
          (continuous_map₂ continuous_snd continuous_fst))
        fun x y ↦ by
        change (x : Completion α) + ↑y = ↑y + ↑x
        -- ⊢ ↑α x + ↑α y = ↑α y + ↑α x
        rw [← coe_add, ← coe_add, add_comm] }
        -- 🎉 no goals

instance instModule [Semiring R] [Module R α] [UniformContinuousConstSMul R α] :
    Module R (Completion α) :=
  { (inferInstance : DistribMulAction R $ Completion α),
    (inferInstance : MulActionWithZero R $ Completion α) with
    smul := (· • ·)
    add_smul := fun a b ↦
      ext' (continuous_const_smul _) ((continuous_const_smul _).add (continuous_const_smul _))
        fun x ↦ by
          rw [← coe_smul, add_smul, coe_add, coe_smul, coe_smul] }
          -- 🎉 no goals
#align uniform_space.completion.module UniformSpace.Completion.instModule

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
                    -- 🎉 no goals
    map_add' := fun a b ↦
      Completion.induction_on₂ a b
        (isClosed_eq (continuous_extension.comp continuous_add)
          ((continuous_extension.comp continuous_fst).add
            (continuous_extension.comp continuous_snd)))
        fun a b ↦
        show Completion.extension f _ = Completion.extension f _ + Completion.extension f _ by
        rw_mod_cast [extension_coe hf, extension_coe hf, extension_coe hf, f.map_add] }
        -- 🎉 no goals
#align add_monoid_hom.extension AddMonoidHom.extension

theorem AddMonoidHom.extension_coe [CompleteSpace β] [SeparatedSpace β] (f : α →+ β)
    (hf : Continuous f) (a : α) : f.extension hf a = f a :=
  UniformSpace.Completion.extension_coe (uniformContinuous_addMonoidHom_of_continuous hf) a
#align add_monoid_hom.extension_coe AddMonoidHom.extension_coe

@[continuity]
theorem AddMonoidHom.continuous_extension [CompleteSpace β] [SeparatedSpace β] (f : α →+ β)
    (hf : Continuous f) : Continuous (f.extension hf) :=
  UniformSpace.Completion.continuous_extension
#align add_monoid_hom.continuous_extension AddMonoidHom.continuous_extension

/-- Completion of a continuous group hom, as a group hom. -/
def AddMonoidHom.completion (f : α →+ β) (hf : Continuous f) : Completion α →+ Completion β :=
  (toCompl.comp f).extension (continuous_toCompl.comp hf)
#align add_monoid_hom.completion AddMonoidHom.completion

@[continuity]
theorem AddMonoidHom.continuous_completion (f : α →+ β) (hf : Continuous f) :
    Continuous (AddMonoidHom.completion f hf : Completion α → Completion β) :=
  continuous_map
#align add_monoid_hom.continuous_completion AddMonoidHom.continuous_completion

theorem AddMonoidHom.completion_coe (f : α →+ β) (hf : Continuous f) (a : α) :
    AddMonoidHom.completion f hf a = f a :=
  map_coe (uniformContinuous_addMonoidHom_of_continuous hf) a
#align add_monoid_hom.completion_coe AddMonoidHom.completion_coe

theorem AddMonoidHom.completion_zero :
    AddMonoidHom.completion (0 : α →+ β) continuous_const = 0 := by
  ext x
  -- ⊢ ↑(completion 0 (_ : Continuous fun x => AddZeroClass.toZero.1)) x = ↑0 x
  refine Completion.induction_on x ?_ ?_
  -- ⊢ IsClosed {a | ↑(completion 0 (_ : Continuous fun x => AddZeroClass.toZero.1) …
  · apply isClosed_eq (AddMonoidHom.continuous_completion (0 : α →+ β) continuous_const)
    -- ⊢ Continuous fun x => ↑0 x
    simp [continuous_const]
    -- 🎉 no goals
  · intro a
    -- ⊢ ↑(completion 0 (_ : Continuous fun x => AddZeroClass.toZero.1)) (↑α a) = ↑0  …
    simp [(0 : α →+ β).completion_coe continuous_const, coe_zero]
    -- 🎉 no goals
#align add_monoid_hom.completion_zero AddMonoidHom.completion_zero

theorem AddMonoidHom.completion_add {γ : Type*} [AddCommGroup γ] [UniformSpace γ]
    [UniformAddGroup γ] (f g : α →+ γ) (hf : Continuous f) (hg : Continuous g) :
    AddMonoidHom.completion (f + g) (hf.add hg) =
    AddMonoidHom.completion f hf + AddMonoidHom.completion g hg := by
  have hfg := hf.add hg
  -- ⊢ completion (f + g) (_ : Continuous fun x => ↑f x + ↑g x) = completion f hf + …
  ext x
  -- ⊢ ↑(completion (f + g) (_ : Continuous fun x => ↑f x + ↑g x)) x = ↑(completion …
  refine Completion.induction_on x ?_ ?_
  -- ⊢ IsClosed {a | ↑(completion (f + g) (_ : Continuous fun x => ↑f x + ↑g x)) a  …
  · exact isClosed_eq ((f + g).continuous_completion hfg)
      ((f.continuous_completion hf).add (g.continuous_completion hg))
  · intro a
    -- ⊢ ↑(completion (f + g) (_ : Continuous fun x => ↑f x + ↑g x)) (↑α a) = ↑(compl …
    simp [(f + g).completion_coe hfg, coe_add, f.completion_coe hf, g.completion_coe hg]
    -- 🎉 no goals
#align add_monoid_hom.completion_add AddMonoidHom.completion_add

end AddMonoidHom
