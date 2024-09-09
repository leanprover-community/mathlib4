/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Equiv.Set

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

theorem viaEmbedding_apply (x : α) : e.viaEmbedding ι (ι x) = ι (e x) :=
  extendDomain_apply_image e (ofInjective ι.1 ι.2) x

theorem viaEmbedding_apply_of_not_mem (x : β) (hx : x ∉ Set.range ι) : e.viaEmbedding ι x = x :=
  extendDomain_apply_not_subtype e (ofInjective ι.1 ι.2) hx

/-- `viaEmbedding` as a group homomorphism -/
noncomputable def viaEmbeddingHom : Perm α →* Perm β :=
  extendDomainHom (ofInjective ι.1 ι.2)

theorem viaEmbeddingHom_apply : viaEmbeddingHom ι e = viaEmbedding e ι :=
  rfl

theorem viaEmbeddingHom_injective : Function.Injective (viaEmbeddingHom ι) :=
  extendDomainHom_injective (ofInjective ι.1 ι.2)

end Perm

end Equiv
