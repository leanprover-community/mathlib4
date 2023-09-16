/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

import Mathlib.Algebra.Module.Equiv
import Mathlib.Algebra.Module.Submodule.Basic

#align_import algebra.module.submodule.basic from "leanprover-community/mathlib"@"8130e5155d637db35907c272de9aec9dc851c03a"

/-!

# Linear maps involving submodules of a module

In this file we define a number of linear maps involving submodules of a module.

## Tags

submodule, subspace, linear map
-/

open BigOperators Function

universe u'' u' u v w

section

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

namespace SMulMemClass

variable [Semiring R] [AddCommMonoid M] [Module R M] {A : Type*} [SetLike A M]
  [AddSubmonoidClass A M] [SMulMemClass A R M] (S' : A)

/-- The natural `R`-linear map from a submodule of an `R`-module `M` to `M`. -/
protected def subtype : S' →ₗ[R] M where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
#align submodule_class.subtype SMulMemClass.subtype

@[simp]
protected theorem coeSubtype : (SMulMemClass.subtype S' : S' → M) = Subtype.val :=
  rfl
#align submodule_class.coe_subtype SMulMemClass.coeSubtype

end SMulMemClass

namespace Submodule

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M]

-- We can infer the module structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variable {module_M : Module R M}

variable {p q : Submodule R M}

variable {r : R} {x y : M}

variable (p)

/-- Embedding of a submodule `p` to the ambient space `M`. -/
protected def subtype : p →ₗ[R] M := by refine' { toFun := Subtype.val.. } <;> simp [coe_smul]
#align submodule.subtype Submodule.subtype

theorem subtype_apply (x : p) : p.subtype x = x :=
  rfl
#align submodule.subtype_apply Submodule.subtype_apply

@[simp]
theorem coeSubtype : (Submodule.subtype p : p → M) = Subtype.val :=
  rfl
#align submodule.coe_subtype Submodule.coeSubtype

theorem injective_subtype : Injective p.subtype :=
  Subtype.coe_injective
#align submodule.injective_subtype Submodule.injective_subtype

/-- Note the `AddSubmonoid` version of this lemma is called `AddSubmonoid.coe_finset_sum`. -/
-- porting note: removing the `@[simp]` attribute since it's literally `AddSubmonoid.coe_finset_sum`
theorem coe_sum (x : ι → p) (s : Finset ι) : ↑(∑ i in s, x i) = ∑ i in s, (x i : M) :=
  map_sum p.subtype _ _
#align submodule.coe_sum Submodule.coe_sum

section AddAction

variable {α β : Type*}

/-- The action by a submodule is the action by the underlying module. -/
instance [AddAction M α] : AddAction p α :=
  AddAction.compHom _ p.subtype.toAddMonoidHom

end AddAction

section RestrictScalars

variable (S) [Semiring S] [Module S M] [Module R M] [SMul S R] [IsScalarTower S R M]
variable (R M)

/-- Turning `p : Submodule R M` into an `S`-submodule gives the same module structure
as turning it into a type and adding a module structure. -/
@[simps (config := { simpRhs := true })]
def restrictScalarsEquiv (p : Submodule R M) : p.restrictScalars S ≃ₗ[R] p :=
  { AddEquiv.refl p with
    map_smul' := fun _ _ => rfl }
#align submodule.restrict_scalars_equiv Submodule.restrictScalarsEquiv
#align submodule.restrict_scalars_equiv_symm_apply Submodule.restrictScalarsEquiv_symm_apply

end RestrictScalars

end AddCommMonoid

end Submodule

end
