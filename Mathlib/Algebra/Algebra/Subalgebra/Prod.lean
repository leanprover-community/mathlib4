/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Basic

#align_import algebra.algebra.subalgebra.basic from "leanprover-community/mathlib"@"b915e9392ecb2a861e1e766f0e1df6ac481188ca"

/-!
# Products of subalgebras

In this file we define the product of two subalgebras as a subalgebra of the product algebra.

## Main definitions

 * `Subalgebra.prod`: the product of two subalgebras.
-/


namespace Subalgebra

open Algebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable (S : Subalgebra R A) (S₁ : Subalgebra R B)

/-- The product of two subalgebras is a subalgebra. -/
def prod : Subalgebra R (A × B) :=
  { S.toSubsemiring.prod S₁.toSubsemiring with
    carrier := S ×ˢ S₁
    algebraMap_mem' := fun _ => ⟨algebraMap_mem _ _, algebraMap_mem _ _⟩ }
#align subalgebra.prod Subalgebra.prod

@[simp]
theorem coe_prod : (prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ (S₁ : Set B) :=
  rfl
#align subalgebra.coe_prod Subalgebra.coe_prod

open Subalgebra in
theorem prod_toSubmodule : toSubmodule (S.prod S₁) = (toSubmodule S).prod (toSubmodule S₁) := rfl
#align subalgebra.prod_to_submodule Subalgebra.prod_toSubmodule

@[simp]
theorem mem_prod {S : Subalgebra R A} {S₁ : Subalgebra R B} {x : A × B} :
    x ∈ prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ := Set.mem_prod
#align subalgebra.mem_prod Subalgebra.mem_prod

@[simp]
theorem prod_top : (prod ⊤ ⊤ : Subalgebra R (A × B)) = ⊤ := by ext; simp
#align subalgebra.prod_top Subalgebra.prod_top

theorem prod_mono {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} :
    S ≤ T → S₁ ≤ T₁ → prod S S₁ ≤ prod T T₁ :=
  Set.prod_mono
#align subalgebra.prod_mono Subalgebra.prod_mono

@[simp]
theorem prod_inf_prod {S T : Subalgebra R A} {S₁ T₁ : Subalgebra R B} :
    S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) :=
  SetLike.coe_injective Set.prod_inter_prod
#align subalgebra.prod_inf_prod Subalgebra.prod_inf_prod
