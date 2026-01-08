/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Module.Pi

/-! # Module structure for `FunLike` -/

@[expose] public section

variable {M M' F α β : Type*} [FunLike F α β]

namespace FunLike

section SMulInstances

variable [SMul M β] [SMul M' β] [SMul M F] [SMul M' F] [FunLikeSMul M F α β] [FunLikeSMul M' F α β]

instance instIsScalarTower [SMul M M'] [IsScalarTower M M' β] : IsScalarTower M M' F :=
  ⟨fun a b f => DFunLike.ext _ _ fun _ ↦ by simp⟩

instance instSMulCommClass [SMulCommClass M M' β] : SMulCommClass M M' F :=
  ⟨fun a b f => DFunLike.ext _ _ fun _ => by simp [smul_comm]⟩

end SMulInstances

section ModuleInstance

variable [Semiring M] [AddCommMonoid β] [Module M β]
  [Zero F] [Add F] [SMul ℕ F] [SMul M F]
  [FunLikeZero F α β] [FunLikeAdd F α β] [FunLikeSMul ℕ F α β] [FunLikeSMul M F α β]

instance instModule : Module M F :=
  coeAddHom_injective.module M (coeAddHom F α β) coe_smul

end ModuleInstance

end FunLike
