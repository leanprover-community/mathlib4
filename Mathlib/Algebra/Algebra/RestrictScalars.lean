/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Tower

/-!

# Restriction of scalars type aliases

See the documentation attached to the `RestrictScalarsRingHom` definition for advice on how and
when to use these type aliases. As described there, it is often a better choice to use the
`IsScalarTower` typeclass instead.

## Main definitions

* `RestrictScalarsRingHom f M`: the `S`-module `M` viewed as an `R`-module via a ring homomorphism
  `f : R →+* S`. The `R`-action is `r • m := f r • m`. Note that by default we do *not* have a
  `Module S (RestrictScalarsRingHom f M)` instance for the original action; this is available as
  `RestrictScalarsRingHom.moduleOrig` if really needed.
* `RestrictScalars R S M`: abbreviation for `RestrictScalarsRingHom (algebraMap R S) M` when
  `[CommSemiring R] [Algebra R S]`. This is the classical restriction of scalars along an algebra
  map.
* `RestrictScalarsRingHom.addEquiv f M : RestrictScalarsRingHom f M ≃+ M`: the additive
  equivalence between the restricted and original space (in fact, they are definitionally equal,
  but sometimes it is helpful to avoid using this fact, to keep instances from leaking).
* `RestrictScalarsRingHom.ringEquiv f A : RestrictScalarsRingHom f A ≃+* A`: the ring equivalence
  between the restricted and original space when the module is a ring.
* `Module.restrictScalars R S M`, `Algebra.restrictScalars R S A`: non-instance definitions for
  `Module R M` and `Algebra R A`.

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

@[expose] public section

set_option linter.unusedVariables false in
/-- Given a ring homomorphism `f : R →+* S`, `RestrictScalarsRingHom f M` is a type synonym for the
`S`-module `M`, viewed as an `R`-module via `f`. The `R`-action is defined by `r • m := f r • m`.

Warning: use this type synonym judiciously! Consider an example where we want to construct an
`R`-linear map from `M` to `N`, given:
```lean
variable (R S M N : Type*)
variable [Ring R] [Ring S] (f : R →+* S) [AddCommGroup M] [Module S M] [AddCommGroup N] [Module R N]
```
With the assumptions above we can't directly state our map as we have no `Module R M` structure, but
`RestrictScalarsRingHom` permits it to be written as:
```lean
-- an `R`-module structure on `M` is provided by `RestrictScalarsRingHom` which is compatible
example : RestrictScalarsRingHom f M →ₗ[R] N := sorry
```
However, when `R` is commutative it is usually better just to add this extra structure as an
argument:
```lean
-- an `R`-module structure on `M` and proof of its compatibility is provided by the user
example [Module R M] [IsScalarTower R S M] : M →ₗ[R] N := sorry
```
The advantage of the second approach is that it defers the duty of providing the missing typeclasses
`[Module R M] [IsScalarTower R S M]`. If some concrete `M` naturally carries these (as is often
the case) then we have avoided `RestrictScalarsRingHom` entirely. If not, we can pass
`RestrictScalarsRingHom f M` later on instead of `M`.

Note that this means we almost always want to state definitions and lemmas in the language of
`IsScalarTower` rather than `RestrictScalarsRingHom`.

When `R` is a commutative semiring and `[Algebra R S]`, `RestrictScalars R S M` is an abbreviation
for `RestrictScalarsRingHom (algebraMap R S) M`. -/
@[nolint unusedArguments]
def RestrictScalarsRingHom {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (f : R →+* S) (M : Type*) : Type _ := M

section Instances

variable {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S)

variable (M A : Type*)

instance [I : Inhabited M] : Inhabited (RestrictScalarsRingHom f M) := I

instance [I : AddCommMonoid M] : AddCommMonoid (RestrictScalarsRingHom f M) := I

instance [I : AddCommGroup M] : AddCommGroup (RestrictScalarsRingHom f M) := I

instance [I : Semiring A] : Semiring (RestrictScalarsRingHom f A) := I

instance [I : Ring A] : Ring (RestrictScalarsRingHom f A) := I

instance [I : CommSemiring A] : CommSemiring (RestrictScalarsRingHom f A) := I

instance [I : CommRing A] : CommRing (RestrictScalarsRingHom f A) := I

end Instances

namespace RestrictScalarsRingHom

section NonAssocSemiring

variable {R S : Type*} [NonAssocSemiring R] [Semiring S] (f : R →+* S)

variable (M : Type*) [AddCommMonoid M]
variable (A : Type*) [Semiring A]

/-- We temporarily install the action of the original ring `S` on `RestrictScalarsRingHom f M`. -/
@[instance_reducible]
def moduleOrig [I : Module S M] : Module S (RestrictScalarsRingHom f M) := I

/-- The additive equivalence between `RestrictScalarsRingHom f M` and the original module `M`.
In fact they are definitionally equal, but sometimes it is helpful to avoid using this fact,
to keep instances from leaking. -/
def addEquiv : RestrictScalarsRingHom f M ≃+ M :=
  AddEquiv.refl M

/-- Tautological ring isomorphism `RestrictScalarsRingHom f A ≃+* A`. -/
def ringEquiv : RestrictScalarsRingHom f A ≃+* A :=
  RingEquiv.refl _

end NonAssocSemiring

section Semiring

variable {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)

variable (M : Type*) [AddCommMonoid M]

/-- When `M` is a module over a semiring `S` and `f : R →+* S` is a ring homomorphism, then `M`
inherits an `R`-module structure via `r • m := f r • m`.

In the commutative case, the preferred way of setting this up is
`[Module R M] [Module S M] [IsScalarTower R S M]`.
-/
instance module [Module S M] : Module R (RestrictScalarsRingHom f M) :=
  Module.compHom M f

/-- When `M` is a right-module over a semiring `S` and `f : R →+* S` is a ring homomorphism,
then `M` inherits a right `R`-module structure. In the commutative case, the preferred way of
setting this up is `[Module Rᵐᵒᵖ M] [Module Sᵐᵒᵖ M] [IsScalarTower Rᵐᵒᵖ Sᵐᵒᵖ M]`. -/
instance opModule [Module Sᵐᵒᵖ M] :
    Module Rᵐᵒᵖ (RestrictScalarsRingHom f M) :=
  letI : Module Sᵐᵒᵖ (RestrictScalarsRingHom f M) := ‹Module Sᵐᵒᵖ M›
  Module.compHom M f.op

variable [Module S M]

instance isCentralScalar [Module Sᵐᵒᵖ M] [IsCentralScalar S M] :
    IsCentralScalar R (RestrictScalarsRingHom f M) where
  op_smul_eq_smul r _x := op_smul_eq_smul (f r) (_ : M)

theorem smul_def (c : R) (x : RestrictScalarsRingHom f M) :
    c • x = (RestrictScalarsRingHom.addEquiv f M).symm
      (f c • RestrictScalarsRingHom.addEquiv f M x) :=
  rfl

@[deprecated (since := "2026-04-30")] alias _root_.RestrictScalars.smul_def := smul_def

@[simp]
theorem addEquiv_map_smul (c : R) (x : RestrictScalarsRingHom f M) :
    RestrictScalarsRingHom.addEquiv f M (c • x) = f c • RestrictScalarsRingHom.addEquiv f M x :=
  rfl

@[deprecated (since := "2026-04-30")]
alias _root_.RestrictScalars.addEquiv_map_smul := addEquiv_map_smul

theorem addEquiv_symm_map_smul (r : R) (x : M) :
    (RestrictScalarsRingHom.addEquiv f M).symm (f r • x) =
      r • (RestrictScalarsRingHom.addEquiv f M).symm x :=
  rfl

@[deprecated (since := "2026-04-30")]
alias _root_.RestrictScalars.addEquiv_symm_map_algebraMap_smul := addEquiv_symm_map_smul

theorem addEquiv_symm_map_smul_smul (r : R) (s : S) (x : M) :
    (RestrictScalarsRingHom.addEquiv f M).symm ((f r * s) • x) =
      r • (RestrictScalarsRingHom.addEquiv f M).symm (s • x) := by
  rw [mul_smul]
  rfl

end Semiring

end RestrictScalarsRingHom

section CommSemiring

variable (R S : Type*) [CommSemiring R]

/-- When `S` is an `R`-algebra, `RestrictScalars R S M` is the `S`-module `M` viewed as an
`R`-module. This is an abbreviation for `RestrictScalarsRingHom (algebraMap R S) M`.

See `RestrictScalarsRingHom` for the more general version that works for any ring homomorphism
`f : R →+* S` without requiring `R` to be commutative. -/
abbrev RestrictScalars [Semiring S] [Algebra R S] (M : Type*) : Type _ :=
  RestrictScalarsRingHom (algebraMap R S) M

variable (M A : Type*)

namespace RestrictScalars

/-- We temporarily install the action of the original ring `S` on `RestrictScalars R S M`.
Abbreviation for `RestrictScalarsRingHom.moduleOrig (algebraMap R S) M`. -/
abbrev moduleOrig [Semiring S] [Algebra R S] [AddCommMonoid M] [Module S M] :
    Module S (RestrictScalars R S M) :=
  RestrictScalarsRingHom.moduleOrig (algebraMap R S) M

/-- The additive equivalence between `RestrictScalars R S M` and the original module `M`.
Abbreviation for `RestrictScalarsRingHom.addEquiv (algebraMap R S) M`. -/
abbrev addEquiv [Semiring S] [Algebra R S] [AddCommMonoid M] :
    RestrictScalars R S M ≃+ M :=
  RestrictScalarsRingHom.addEquiv (algebraMap R S) M

/-- Tautological ring isomorphism `RestrictScalars R S A ≃+* A`.
Abbreviation for `RestrictScalarsRingHom.ringEquiv (algebraMap R S) A`. -/
abbrev ringEquiv [Semiring S] [Algebra R S] [Semiring A] :
    RestrictScalars R S A ≃+* A :=
  RestrictScalarsRingHom.ringEquiv (algebraMap R S) A

end RestrictScalars

section Module

variable [Semiring S] [Algebra R S]

variable [AddCommMonoid M] [Module S M]

/-- When `M` is a module over a ring `S`, and `S` is an algebra over `R`, then `M` inherits a
module structure over `R`. Not an instance because `S` cannot be inferred.

The preferred way of setting this up is `[Module R M] [Module S M] [IsScalarTower R S M]`.
-/
abbrev Module.restrictScalars : Module R M :=
  Module.compHom M (algebraMap R S)

/-- `Module.restrictScalars` forms a scalar tower. -/
theorem IsScalarTower.restrictScalars :
    letI := Module.compHom M (algebraMap R S)
    IsScalarTower R S M :=
  IsScalarTower.of_compHom R S M

namespace RestrictScalars

theorem addEquiv_symm_map_smul_smul (r : R) (s : S) (x : M) :
    (RestrictScalars.addEquiv R S M).symm ((r • s) • x) =
      r • (RestrictScalars.addEquiv R S M).symm (s • x) := by
  rw [Algebra.smul_def, mul_smul]
  rfl

attribute [local instance] RestrictScalars.moduleOrig in
/-- This instance is only relevant when `RestrictScalars.moduleOrig` is available as
an instance. -/
instance isScalarTower :
    IsScalarTower R S (RestrictScalars R S M) :=
  IsScalarTower.restrictScalars R S M

/-- The `R`-algebra homomorphism from the original coefficient algebra `S` to endomorphisms
of `RestrictScalars R S M`. -/
def lsmul : S →ₐ[R] Module.End R (RestrictScalars R S M) :=
  -- We use `RestrictScalars.moduleOrig` in the implementation,
  -- but not in the type.
  letI : Module S (RestrictScalars R S M) := RestrictScalars.moduleOrig R S M
  Algebra.lsmul R R (RestrictScalars R S M)

theorem lsmul_apply_apply (s : S) (x : RestrictScalars R S M) :
    RestrictScalars.lsmul R S M s x =
      (RestrictScalars.addEquiv R S M).symm (s • RestrictScalars.addEquiv R S M x) :=
  rfl

end RestrictScalars

end Module

section Algebra

variable [CommSemiring S] [Algebra R S]

variable [Semiring A]

variable [Algebra S A]

/-- `R ⟶ S` induces `S-Alg ⥤ R-Alg`. Not an instance because `S` cannot be inferred. -/
abbrev Algebra.restrictScalars : Algebra R A :=
  Algebra.compHom A (algebraMap R S)

namespace RestrictScalars

@[simp]
theorem ringEquiv_map_smul (r : R) (x : RestrictScalars R S A) :
    RestrictScalars.ringEquiv R S A (r • x) =
      algebraMap R S r • RestrictScalars.ringEquiv R S A x :=
  rfl

/-- `R ⟶ S` induces `S-Alg ⥤ R-Alg` -/
instance algebra : Algebra R (RestrictScalars R S A) :=
  Algebra.restrictScalars R S A

@[simp]
theorem ringEquiv_algebraMap (r : R) :
    RestrictScalars.ringEquiv R S A (algebraMap R (RestrictScalars R S A) r) =
      algebraMap S A (algebraMap R S r) :=
  rfl

end RestrictScalars

end Algebra

end CommSemiring
