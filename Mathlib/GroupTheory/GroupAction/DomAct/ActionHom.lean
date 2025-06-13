/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.GroupTheory.GroupAction.DomAct.Basic
import Mathlib.GroupTheory.GroupAction.Hom
/-!
# Action of `Mᵈᵃ` on `α →[N] β` and `A →+[N] B`

In this file we define action of `DomAct M = Mᵈᵃ` on `α →[N] β` and on `A →+[N] B`. At the
time of writing, these homomorphisms are not widely used in the library, so we put these instances
into a separate file, not with the definition of `DomAct`.

## TODO

Add left actions of, e.g., `M` on `α →[N] β` to `Mathlib/Algebra/Hom/GroupAction.lean` and
`SMulCommClass` instances saying that left and right actions commute.
-/

namespace DomAct

section MulActionSemiHom

section SMul

variable {M α N β : Type*}
variable [SMul M α] [SMul N α] [SMulCommClass M N α] [SMul N β]

instance : SMul Mᵈᵃ (α →[N] β) where
  smul c f := f.comp (SMulCommClass.toMulActionHom _ _ (mk.symm c))

instance {M' : Type*} [SMul M' α] [SMulCommClass M' N α] [SMulCommClass M M' α] :
    SMulCommClass Mᵈᵃ M'ᵈᵃ (α →[N] β) :=
  DFunLike.coe_injective.smulCommClass (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

theorem smul_mulActionHom_apply (c : Mᵈᵃ) (f : α →[N] β) (a : α) :
    (c • f) a = f (mk.symm c • a) :=
  rfl

@[simp]
theorem mk_smul_mulActionHom_apply (c : M) (f : α →[N] β) (a : α) : (mk c • f) a = f (c • a) := rfl

end SMul

instance {M α N β : Type*} [Monoid M] [MulAction M α] [SMul N α] [SMulCommClass M N α] [SMul N β] :
    MulAction Mᵈᵃ (α →[N] β) :=
  DFunLike.coe_injective.mulAction _ fun _ _ ↦ rfl

end MulActionSemiHom

section DistribMulActionHom

section SMul

variable {M N A B : Type*} [AddMonoid A] [DistribSMul M A] [Monoid N] [AddMonoid B]
  [DistribMulAction N A] [SMulCommClass M N A] [DistribMulAction N B]

instance : SMul Mᵈᵃ (A →+[N] B) where
  smul c f := f.comp (SMulCommClass.toDistribMulActionHom _ _ (mk.symm c))

instance {M' : Type*} [DistribSMul M' A] [SMulCommClass M' N A] [SMulCommClass M M' A] :
    SMulCommClass Mᵈᵃ M'ᵈᵃ (A →+[N] B) :=
  DFunLike.coe_injective.smulCommClass (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

theorem smul_mulDistribActionHom_apply (c : Mᵈᵃ) (f : A →+[N] B) (a : A) :
    (c • f) a = f (mk.symm c • a) :=
  rfl

@[simp]
theorem mk_smul_mulDistribActionHom_apply (c : M) (f : A →+[N] B) (a : A) :
    (mk c • f) a = f (c • a) := rfl

end SMul

instance {M N A B : Type*} [Monoid M] [AddMonoid A] [DistribMulAction M A] [Monoid N] [AddMonoid B]
    [DistribMulAction N A] [SMulCommClass M N A] [DistribMulAction N B] :
    MulAction Mᵈᵃ (A →+[N] B) :=
  DFunLike.coe_injective.mulAction _ fun _ _ ↦ rfl

end DistribMulActionHom

end DomAct
