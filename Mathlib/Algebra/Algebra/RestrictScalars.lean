/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Tower

/-!

# The `RestrictScalars` type alias

See the documentation attached to the `RestrictScalars` definition for advice on how and when to
use this type alias. As described there, it is often a better choice to use the `IsScalarTower`
typeclass instead.

## Main definitions

* `RestrictScalars R S M`: the `S`-module `M` viewed as an `R` module when `S` is an `R`-algebra.
  Note that by default we do *not* have a `Module S (RestrictScalars R S M)` instance
  for the original action.
  This is available as a def `RestrictScalars.moduleOrig` if really needed.
* `RestrictScalars.addEquiv : RestrictScalars R S M ≃+ M`: the additive equivalence
  between the restricted and original space (in fact, they are definitionally equal,
  but sometimes it is helpful to avoid using this fact, to keep instances from leaking).
* `RestrictScalars.ringEquiv : RestrictScalars R S A ≃+* A`: the ring equivalence
  between the restricted and original space when the module is an algebra.

## See also

There are many similarly-named definitions elsewhere which do not refer to this type alias. These
refer to restricting the scalar type in a bundled type, such as from `A →ₗ[R] B` to `A →ₗ[S] B`:

* `LinearMap.restrictScalars`
* `LinearEquiv.restrictScalars`
* `AlgHom.restrictScalars`
* `AlgEquiv.restrictScalars`
* `Submodule.restrictScalars`
* `Subalgebra.restrictScalars`
-/


variable (R S M A : Type*)

/-- If we put an `R`-algebra structure on a semiring `S`, we get a natural equivalence from the
category of `S`-modules to the category of representations of the algebra `S` (over `R`). The type
synonym `RestrictScalars` is essentially this equivalence.

Warning: use this type synonym judiciously! Consider an example where we want to construct an
`R`-linear map from `M` to `S`, given:
```lean
variable (R S M : Type*)
variable [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module S M]
```
With the assumptions above we can't directly state our map as we have no `Module R M` structure, but
`RestrictScalars` permits it to be written as:
```lean
-- an `R`-module structure on `M` is provided by `RestrictScalars` which is compatible
example : RestrictScalars R S M →ₗ[R] S := sorry
```
However, it is usually better just to add this extra structure as an argument:
```lean
-- an `R`-module structure on `M` and proof of its compatibility is provided by the user
example [Module R M] [IsScalarTower R S M] : M →ₗ[R] S := sorry
```
The advantage of the second approach is that it defers the duty of providing the missing typeclasses
`[Module R M] [IsScalarTower R S M]`. If some concrete `M` naturally carries these (as is often
the case) then we have avoided `RestrictScalars` entirely. If not, we can pass
`RestrictScalars R S M` later on instead of `M`.

Note that this means we almost always want to state definitions and lemmas in the language of
`IsScalarTower` rather than `RestrictScalars`.

An example of when one might want to use `RestrictScalars` would be if one has a vector space
over a field of characteristic zero and wishes to make use of the `ℚ`-algebra structure. -/
@[nolint unusedArguments]
def RestrictScalars (_R _S M : Type*) : Type _ := M

instance [I : Inhabited M] : Inhabited (RestrictScalars R S M) := I

instance [I : AddCommMonoid M] : AddCommMonoid (RestrictScalars R S M) := I

instance [I : AddCommGroup M] : AddCommGroup (RestrictScalars R S M) := I

section Module

section

variable [Semiring S] [AddCommMonoid M]

/-- We temporarily install an action of the original ring on `RestrictScalars R S M`. -/
def RestrictScalars.moduleOrig [I : Module S M] : Module S (RestrictScalars R S M) := I

variable [CommSemiring R] [Algebra R S]

section

attribute [local instance] RestrictScalars.moduleOrig

/-- When `M` is a module over a ring `S`, and `S` is an algebra over `R`, then `M` inherits a
module structure over `R`.

The preferred way of setting this up is `[Module R M] [Module S M] [IsScalarTower R S M]`.
-/
instance RestrictScalars.module [Module S M] : Module R (RestrictScalars R S M) :=
  Module.compHom M (algebraMap R S)

/-- This instance is only relevant when `RestrictScalars.moduleOrig` is available as an instance.
-/
instance RestrictScalars.isScalarTower [Module S M] : IsScalarTower R S (RestrictScalars R S M) :=
  ⟨fun r S M ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩

end

/-- When `M` is a right-module over a ring `S`, and `S` is an algebra over `R`, then `M` inherits a
right-module structure over `R`.
The preferred way of setting this up is
`[Module Rᵐᵒᵖ M] [Module Sᵐᵒᵖ M] [IsScalarTower Rᵐᵒᵖ Sᵐᵒᵖ M]`.
-/
instance RestrictScalars.opModule [Module Sᵐᵒᵖ M] : Module Rᵐᵒᵖ (RestrictScalars R S M) :=
  letI : Module Sᵐᵒᵖ (RestrictScalars R S M) := ‹Module Sᵐᵒᵖ M›
  Module.compHom M (RingHom.op <| algebraMap R S)

instance RestrictScalars.isCentralScalar [Module S M] [Module Sᵐᵒᵖ M] [IsCentralScalar S M] :
    IsCentralScalar R (RestrictScalars R S M) where
  op_smul_eq_smul r _x := (op_smul_eq_smul (algebraMap R S r) (_ : M) :)

/-- The `R`-algebra homomorphism from the original coefficient algebra `S` to endomorphisms
of `RestrictScalars R S M`.
-/
def RestrictScalars.lsmul [Module S M] : S →ₐ[R] Module.End R (RestrictScalars R S M) :=
  -- We use `RestrictScalars.moduleOrig` in the implementation,
  -- but not in the type.
  letI : Module S (RestrictScalars R S M) := RestrictScalars.moduleOrig R S M
  Algebra.lsmul R R (RestrictScalars R S M)

end

variable [AddCommMonoid M]

/-- `RestrictScalars.addEquiv` is the additive equivalence with the original module. -/
def RestrictScalars.addEquiv : RestrictScalars R S M ≃+ M :=
  AddEquiv.refl M

variable [CommSemiring R] [Semiring S] [Algebra R S] [Module S M]

theorem RestrictScalars.smul_def (c : R) (x : RestrictScalars R S M) :
    c • x = (RestrictScalars.addEquiv R S M).symm
      (algebraMap R S c • RestrictScalars.addEquiv R S M x) :=
  rfl

@[simp]
theorem RestrictScalars.addEquiv_map_smul (c : R) (x : RestrictScalars R S M) :
    RestrictScalars.addEquiv R S M (c • x) = algebraMap R S c • RestrictScalars.addEquiv R S M x :=
  rfl

theorem RestrictScalars.addEquiv_symm_map_algebraMap_smul (r : R) (x : M) :
    (RestrictScalars.addEquiv R S M).symm (algebraMap R S r • x) =
      r • (RestrictScalars.addEquiv R S M).symm x :=
  rfl

theorem RestrictScalars.addEquiv_symm_map_smul_smul (r : R) (s : S) (x : M) :
    (RestrictScalars.addEquiv R S M).symm ((r • s) • x) =
      r • (RestrictScalars.addEquiv R S M).symm (s • x) := by
  rw [Algebra.smul_def, mul_smul]
  rfl

theorem RestrictScalars.lsmul_apply_apply (s : S) (x : RestrictScalars R S M) :
    RestrictScalars.lsmul R S M s x =
      (RestrictScalars.addEquiv R S M).symm (s • RestrictScalars.addEquiv R S M x) :=
  rfl

end Module

section Algebra

instance [I : Semiring A] : Semiring (RestrictScalars R S A) := I

instance [I : Ring A] : Ring (RestrictScalars R S A) := I

instance [I : CommSemiring A] : CommSemiring (RestrictScalars R S A) := I

instance [I : CommRing A] : CommRing (RestrictScalars R S A) := I

variable [Semiring A]

/-- Tautological ring isomorphism `RestrictScalars R S A ≃+* A`. -/
def RestrictScalars.ringEquiv : RestrictScalars R S A ≃+* A :=
  RingEquiv.refl _

variable [CommSemiring S] [Algebra S A] [CommSemiring R] [Algebra R S]

@[simp]
theorem RestrictScalars.ringEquiv_map_smul (r : R) (x : RestrictScalars R S A) :
    RestrictScalars.ringEquiv R S A (r • x) =
      algebraMap R S r • RestrictScalars.ringEquiv R S A x :=
  rfl

/-- `R ⟶ S` induces `S-Alg ⥤ R-Alg` -/
instance RestrictScalars.algebra : Algebra R (RestrictScalars R S A) where
  algebraMap := (algebraMap S A).comp (algebraMap R S)
  commutes' := fun _ _ ↦ Algebra.commutes' (A := A) _ _
  smul_def' := fun _ _ ↦ Algebra.smul_def' (A := A) _ _

@[simp]
theorem RestrictScalars.ringEquiv_algebraMap (r : R) :
    RestrictScalars.ringEquiv R S A (algebraMap R (RestrictScalars R S A) r) =
      algebraMap S A (algebraMap R S r) :=
  rfl

end Algebra
