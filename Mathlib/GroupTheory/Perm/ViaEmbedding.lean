/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Set

#align_import group_theory.perm.via_embedding from "leanprover-community/mathlib"@"9116dd6709f303dcf781632e15fdef382b0fc579"

/-!
# `Equiv.Perm.viaEmbedding`, a noncomputable analogue of `Equiv.Perm.viaFintypeEmbedding`.
-/


variable {α β : Type*}

namespace Equiv

namespace Perm

variable (e : Perm α) (ι : α ↪ β)

open scoped Classical

/-- Noncomputable version of `Equiv.Perm.viaFintypeEmbedding` that does not assume `Fintype` -/
noncomputable def viaEmbedding : Perm β :=
  extendDomain e (ofInjective ι.1 ι.2)
#align equiv.perm.via_embedding Equiv.Perm.viaEmbedding

theorem viaEmbedding_apply (x : α) : e.viaEmbedding ι (ι x) = ι (e x) :=
  extendDomain_apply_image e (ofInjective ι.1 ι.2) x
#align equiv.perm.via_embedding_apply Equiv.Perm.viaEmbedding_apply

theorem viaEmbedding_apply_of_not_mem (x : β) (hx : x ∉ Set.range ι) : e.viaEmbedding ι x = x :=
  extendDomain_apply_not_subtype e (ofInjective ι.1 ι.2) hx
#align equiv.perm.via_embedding_apply_of_not_mem Equiv.Perm.viaEmbedding_apply_of_not_mem

/-- `viaEmbedding` as a group homomorphism -/
noncomputable def viaEmbeddingHom : Perm α →* Perm β :=
  extendDomainHom (ofInjective ι.1 ι.2)
#align equiv.perm.via_embedding_hom Equiv.Perm.viaEmbeddingHom

theorem viaEmbeddingHom_apply : viaEmbeddingHom ι e = viaEmbedding e ι :=
  rfl
#align equiv.perm.via_embedding_hom_apply Equiv.Perm.viaEmbeddingHom_apply

theorem viaEmbeddingHom_injective : Function.Injective (viaEmbeddingHom ι) :=
  extendDomainHom_injective (ofInjective ι.1 ι.2)
#align equiv.perm.via_embedding_hom_injective Equiv.Perm.viaEmbeddingHom_injective

end Perm

end Equiv
