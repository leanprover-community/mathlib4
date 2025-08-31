/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Bimodules

One frequently encounters situations in which several sets of scalars act on a single space, subject
to compatibility condition(s). A distinguished instance of this is the theory of bimodules: one has
two rings `R`, `S` acting on an additive group `M`, with `R` acting covariantly ("on the left")
and `S` acting contravariantly ("on the right"). The compatibility condition is just:
`(r • m) • s = r • (m • s)` for all `r : R`, `s : S`, `m : M`.

This situation can be set up in Mathlib as:
```lean
variable (R S M : Type*) [Ring R] [Ring S]
variable [AddCommGroup M] [Module R M] [Module Sᵐᵒᵖ M] [SMulCommClass R Sᵐᵒᵖ M]
```
The key fact is:
```lean
example : Module (R ⊗[ℕ] Sᵐᵒᵖ) M := TensorProduct.Algebra.module
```
Note that the corresponding result holds for the canonically isomorphic ring `R ⊗[ℤ] Sᵐᵒᵖ` but it is
preferable to use the `R ⊗[ℕ] Sᵐᵒᵖ` instance since it works without additive inverses.

Bimodules are thus just a special case of `Module`s and most of their properties follow from the
theory of `Module`s. In particular a two-sided Submodule of a bimodule is simply a term of type
`Submodule (R ⊗[ℕ] Sᵐᵒᵖ) M`.

This file is a place to collect results which are specific to bimodules.

## Main definitions

* `Subbimodule.mk`
* `Subbimodule.smul_mem`
* `Subbimodule.smul_mem'`
* `Subbimodule.toSubmodule`
* `Subbimodule.toSubmodule'`

## Implementation details

For many definitions and lemmas it is preferable to set things up without opposites, i.e., as:
`[Module S M] [SMulCommClass R S M]` rather than `[Module Sᵐᵒᵖ M] [SMulCommClass R Sᵐᵒᵖ M]`.
The corresponding results for opposites then follow automatically and do not require taking
advantage of the fact that `(Sᵐᵒᵖ)ᵐᵒᵖ` is defeq to `S`.

## TODO

Develop the theory of two-sided ideals, which have type `Submodule (R ⊗[ℕ] Rᵐᵒᵖ) R`.

-/


open TensorProduct

attribute [local instance] TensorProduct.Algebra.module

namespace Subbimodule

section Algebra

variable {R A B M : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [Semiring A] [Semiring B] [Module A M] [Module B M]
variable [Algebra R A] [Algebra R B]
variable [IsScalarTower R A M] [IsScalarTower R B M]
variable [SMulCommClass A B M]

/-- A constructor for a subbimodule which demands closure under the two sets of scalars
individually, rather than jointly via their tensor product.

Note that `R` plays no role but it is convenient to make this generalisation to support the cases
`R = ℕ` and `R = ℤ` which both show up naturally. See also `Subbimodule.baseChange`. -/
@[simps]
noncomputable def mk (p : AddSubmonoid M) (hA : ∀ (a : A) {m : M}, m ∈ p → a • m ∈ p)
    (hB : ∀ (b : B) {m : M}, m ∈ p → b • m ∈ p) : Submodule (A ⊗[R] B) M :=
  { p with
    carrier := p
    smul_mem' := fun ab m =>
      TensorProduct.induction_on ab (fun _ => by simpa only [zero_smul] using p.zero_mem)
        (fun a b hm => by simpa only [TensorProduct.Algebra.smul_def] using hA a (hB b hm))
        fun z w hz hw hm => by simpa only [add_smul] using p.add_mem (hz hm) (hw hm) }

theorem smul_mem (p : Submodule (A ⊗[R] B) M) (a : A) {m : M} (hm : m ∈ p) : a • m ∈ p := by
  suffices a • m = a ⊗ₜ[R] (1 : B) • m by exact this.symm ▸ p.smul_mem _ hm
  simp [TensorProduct.Algebra.smul_def]

theorem smul_mem' (p : Submodule (A ⊗[R] B) M) (b : B) {m : M} (hm : m ∈ p) : b • m ∈ p := by
  suffices b • m = (1 : A) ⊗ₜ[R] b • m by exact this.symm ▸ p.smul_mem _ hm
  simp [TensorProduct.Algebra.smul_def]

/-- If `A` and `B` are also `Algebra`s over yet another set of scalars `S` then we may "base change"
from `R` to `S`. -/
@[simps!]
noncomputable def baseChange (S : Type*) [CommSemiring S] [Module S M] [Algebra S A] [Algebra S B]
    [IsScalarTower S A M] [IsScalarTower S B M] (p : Submodule (A ⊗[R] B) M) :
    Submodule (A ⊗[S] B) M :=
  mk p.toAddSubmonoid (smul_mem p) (smul_mem' p)

/-- Forgetting the `B` action, a `Submodule` over `A ⊗[R] B` is just a `Submodule` over `A`. -/
@[simps]
def toSubmodule (p : Submodule (A ⊗[R] B) M) : Submodule A M :=
  { p with
    carrier := p
    smul_mem' := smul_mem p }

/-- Forgetting the `A` action, a `Submodule` over `A ⊗[R] B` is just a `Submodule` over `B`. -/
@[simps]
def toSubmodule' (p : Submodule (A ⊗[R] B) M) : Submodule B M :=
  { p with
    carrier := p
    smul_mem' := smul_mem' p }

end Algebra

section Ring

variable (R S M : Type*) [Ring R] [Ring S]
variable [AddCommGroup M] [Module R M] [Module S M] [SMulCommClass R S M]

/-- A `Submodule` over `R ⊗[ℕ] S` is naturally also a `Submodule` over the canonically-isomorphic
ring `R ⊗[ℤ] S`. -/
@[simps!]
noncomputable def toSubbimoduleInt (p : Submodule (R ⊗[ℕ] S) M) : Submodule (R ⊗[ℤ] S) M :=
  baseChange ℤ p

/-- A `Submodule` over `R ⊗[ℤ] S` is naturally also a `Submodule` over the canonically-isomorphic
ring `R ⊗[ℕ] S`. -/
@[simps!]
noncomputable def toSubbimoduleNat (p : Submodule (R ⊗[ℤ] S) M) : Submodule (R ⊗[ℕ] S) M :=
  baseChange ℕ p

end Ring

end Subbimodule
