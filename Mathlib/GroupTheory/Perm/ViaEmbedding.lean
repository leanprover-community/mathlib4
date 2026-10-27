/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Equiv.Set

/-!
# `Equiv.Perm.viaEmbedding`, a noncomputable analogue of `Equiv.Perm.viaFintypeEmbedding`.
-/

@[expose] public section


variable {α β : Type*}

namespace Equiv

namespace Perm

variable (e : Perm α) (ι : α ↪ β)

open scoped Classical in
/-- Noncomputable version of `Equiv.Perm.viaFintypeEmbedding` that does not assume `Fintype` -/
noncomputable def viaEmbedding : Perm β :=
  extendDomain e (ofInjective ι.toFun ι.inj')

theorem viaEmbedding_apply (x : α) : e.viaEmbedding ι (ι x) = ι (e x) := by
  classical
  exact extendDomain_apply_image e (ofInjective ι.toFun ι.inj') x

theorem viaEmbedding_apply_of_notMem (x : β) (hx : x ∉ Set.range ι) : e.viaEmbedding ι x = x := by
  classical
  exact extendDomain_apply_not_subtype e (ofInjective ι.toFun ι.inj') hx

open scoped Classical in
/-- `viaEmbedding` as a group homomorphism -/
noncomputable def viaEmbeddingHom : Perm α →* Perm β :=
  extendDomainHom (ofInjective ι.toFun ι.inj')

theorem viaEmbeddingHom_apply : viaEmbeddingHom ι e = viaEmbedding e ι :=
  rfl

theorem viaEmbeddingHom_injective : Function.Injective (viaEmbeddingHom ι) := by
  classical
  exact extendDomainHom_injective (ofInjective ι.toFun ι.inj')

end Perm

end Equiv
