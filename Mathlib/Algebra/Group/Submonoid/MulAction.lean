/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Action.Defs

/-!
# Actions by `Submonoid`s

These instances transfer the action by an element `m : M` of a monoid `M` written as `m • a` onto
the action by an element `s : S` of a submonoid `S : Submonoid M` such that `s • a = (s : M) • a`.

These instances work particularly well in conjunction with `Monoid.toMulAction`, enabling
`s • m` as an alias for `↑s * m`.
-/

assert_not_exists RelIso

namespace Submonoid

variable {M' : Type*} {α β : Type*}

section SetLike

variable {S' : Type*} [SetLike S' M'] (s : S')

@[to_additive]
instance (priority := low) [SMul M' α] : SMul s α where
  smul m a := (m : M') • a

section MulOneClass

variable [MulOneClass M']

@[to_additive]
instance (priority := low) [SMul M' β] [SMul α β] [SMulCommClass M' α β] : SMulCommClass s α β :=
  ⟨fun a _ _ => smul_comm (a : M') _ _⟩

@[to_additive]
instance (priority := low) [SMul α β] [SMul M' β] [SMulCommClass α M' β] : SMulCommClass α s β :=
  ⟨fun a s => smul_comm a (s : M')⟩

@[to_additive]
instance (priority := low) [SMul α β] [SMul M' α] [SMul M' β] [IsScalarTower M' α β] :
    IsScalarTower s α β :=
  ⟨fun a => smul_assoc (a : M')⟩

end MulOneClass

variable [Monoid M'] [SubmonoidClass S' M']

@[to_additive]
instance (priority := low) [MulAction M' α] : MulAction s α where
  one_smul := one_smul M'
  mul_smul m₁ m₂ := mul_smul (m₁ : M') m₂

end SetLike

section MulOneClass

variable [MulOneClass M']

@[to_additive]
instance smul [SMul M' α] (S : Submonoid M') : SMul S α :=
  inferInstance

@[to_additive]
instance smulCommClass_left [SMul M' β] [SMul α β] [SMulCommClass M' α β]
    (S : Submonoid M') : SMulCommClass S α β :=
  inferInstance

@[to_additive]
instance smulCommClass_right [SMul α β] [SMul M' β] [SMulCommClass α M' β]
    (S : Submonoid M') : SMulCommClass α S β :=
  inferInstance

/-- Note that this provides `IsScalarTower S M' M'` which is needed by `SMulMulAssoc`. -/
@[to_additive]
instance isScalarTower [SMul α β] [SMul M' α] [SMul M' β] [IsScalarTower M' α β]
      (S : Submonoid M') :
    IsScalarTower S α β :=
  inferInstance

section SMul
variable [SMul M' α] {S : Submonoid M'}

@[to_additive] lemma smul_def (g : S) (a : α) : g • a = (g : M') • a := rfl

@[to_additive (attr := simp)]
lemma mk_smul (g : M') (hg : g ∈ S) (a : α) : (⟨g, hg⟩ : S) • a = g • a := rfl

end SMul
end MulOneClass

variable [Monoid M']

/-- The action by a submonoid is the action by the underlying monoid. -/
@[to_additive
      /-- The additive action by an `AddSubmonoid` is the action by the underlying `AddMonoid`. -/]
instance mulAction [MulAction M' α] (S : Submonoid M') : MulAction S α :=
  inferInstance

example {S : Submonoid M'} : IsScalarTower S M' M' := by infer_instance

end Submonoid
