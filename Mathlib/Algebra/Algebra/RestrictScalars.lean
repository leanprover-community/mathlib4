/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov, Edison Xie
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Algebra.Ring.TransferInstance

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

section Module

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
@[ext]
structure RestrictScalars {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (M : Type*) where
  of (f) ::
  toM (f) : M

variable {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (M : Type*)

namespace RestrictScalars

@[simp]
lemma toM_ofM (m : M) : (of f m).toM = m := rfl

@[simp]
lemma ofM_toM (m : RestrictScalars f M) : of f (toM f m) = m := rfl

@[simps]
def toMEquiv : RestrictScalars f M ≃ M where
  toFun := RestrictScalars.toM f
  invFun := RestrictScalars.of f

instance [Inhabited M] : Inhabited (RestrictScalars f M) :=
  fast_instance% (RestrictScalars.toMEquiv f M).inhabited

instance [AddCommMonoid M] : AddCommMonoid (RestrictScalars f M) :=
  fast_instance% (RestrictScalars.toMEquiv f M).addCommMonoid

instance [AddCommGroup M] : AddCommGroup (RestrictScalars f M) :=
  fast_instance% (RestrictScalars.toMEquiv f M).addCommGroup

@[simp]
lemma add_toM [AddCommMonoid M] (x y : RestrictScalars f M) :
    (x + y).toM = x.toM + y.toM := rfl

@[simp]
lemma ofM_add [AddCommMonoid M] (x y : M) : of f (x + y) = of f x + of f y := rfl

@[simps!]
def toMAddEquiv [AddCommMonoid M] : RestrictScalars f M ≃+ M where
  __ := RestrictScalars.toMEquiv f M
  map_add' x y := by simp

/-- We temporarily install an action of the original ring on `RestrictScalars R S M`. -/
@[instance_reducible]
def moduleOrig [AddCommMonoid M] [Module S M] : Module S (RestrictScalars f M) :=
  fast_instance% (RestrictScalars.toMAddEquiv f M).module S

/-- When `M` is a module over a ring `S`, and `S` is an algebra over `R`, then `M` inherits a
module structure over `R`. Not an instance because `S` cannot be inferred.

The preferred way of setting this up is `[Module R M] [Module S M] [IsScalarTower R S M]`.
-/
instance [AddCommMonoid M] [Module S M] : Module R (RestrictScalars f M) :=
  letI := Module.compHom M f
  fast_instance% (RestrictScalars.toMAddEquiv f M).module R

theorem smul_def [AddCommMonoid M] [Module S M] (c : R) (x : RestrictScalars f M) :
    c • x = (RestrictScalars.toMAddEquiv f M).symm (f c • RestrictScalars.toMAddEquiv f M x) :=
  rfl

lemma smul_toM [AddCommMonoid M] [Module S M] (r : R)
    (x : RestrictScalars f M) :
    (r • x).toM = f r • x.toM := rfl

theorem addEquiv_map_smul [AddCommMonoid M] [Module S M] (c : R) (x : RestrictScalars f M) :
    RestrictScalars.toMAddEquiv f M (c • x) = f c • RestrictScalars.toMAddEquiv f M x :=
  rfl

@[simps]
def toMSemilinearMap [AddCommMonoid M] [Module S M] :
    RestrictScalars f M →ₛₗ[f] M where
  toFun := toM f
  map_add' := by simp
  map_smul' := by simp [smul_toM]

@[simps]
def ofAddHom [AddCommMonoid M] [Module S M] :
    M →+ RestrictScalars f M where
  toFun := RestrictScalars.of f
  map_add' := by simp
  map_zero' := rfl

instance {R : Type*} [Semiring R] : Semiring (RestrictScalars f R) :=
  fast_instance% (RestrictScalars.toMEquiv f R).semiring

instance {R : Type*} [Ring R] : Ring (RestrictScalars f R) :=
  fast_instance% (RestrictScalars.toMEquiv f R).ring

instance {R : Type*} [CommSemiring R] : CommSemiring (RestrictScalars f R) :=
  fast_instance% (RestrictScalars.toMEquiv f R).commSemiring

instance {R : Type*} [CommRing R] : CommRing (RestrictScalars f R) :=
  fast_instance% (RestrictScalars.toMEquiv f R).commRing

/-- Tautological ring isomorphism `RestrictScalars R S A ≃+* A`. -/
def ringEquiv {A : Type*} [Semiring A] : RestrictScalars f A ≃+* A where
  __ := toMAddEquiv f A
  map_mul' := by intros; rfl

@[simp]
theorem ringEquiv_map_smul {A : Type*} [Semiring A] [Module S A] (r : R)
    (x : RestrictScalars f A) : RestrictScalars.ringEquiv f (r • x) =
      f r • RestrictScalars.ringEquiv f x :=
  rfl

/-- When `M` is a right-module over a ring `S`, and `S` is an algebra over `R`, then `M` inherits a
right-module structure over `R`.
The preferred way of setting this up is
`[Module Rᵐᵒᵖ M] [Module Sᵐᵒᵖ M] [IsScalarTower Rᵐᵒᵖ Sᵐᵒᵖ M]`.
-/
instance opModule [AddCommMonoid M] [Module Sᵐᵒᵖ M] : Module Rᵐᵒᵖ (RestrictScalars f M) :=
  letI : Module Sᵐᵒᵖ (RestrictScalars f M) := (toMAddEquiv f M).module Sᵐᵒᵖ
  Module.compHom _ f.op

lemma op_smul_def [AddCommMonoid M] [Module Sᵐᵒᵖ M] (c : Rᵐᵒᵖ) (x : RestrictScalars f M) :
    letI : Module Sᵐᵒᵖ (RestrictScalars f M) := (toMAddEquiv f M).module Sᵐᵒᵖ
    c • x = f.op c • x := rfl

end RestrictScalars

end Module

section Algebra

variable (R S M : Type*) [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M]

abbrev RestrictScalars' := RestrictScalars (algebraMap R S) M

/-- `Module.restrictScalars` forms a scalar tower. -/
instance IsScalarTower.restrictScalars [Module S M] :
    letI := RestrictScalars.moduleOrig (algebraMap R S) M
    IsScalarTower R S (RestrictScalars' R S M) :=
  letI := RestrictScalars.moduleOrig (algebraMap R S) M
  IsScalarTower.of_compHom ..

instance RestrictScalars.isCentralScalar [Module S M] [Module Sᵐᵒᵖ M] [IsCentralScalar S M] :
    IsCentralScalar R (RestrictScalars' R S M) where
  op_smul_eq_smul r x := by
    rw [op_smul_def, smul_def]
    change (RestrictScalars.toMAddEquiv (algebraMap R S) M).symm
      ((algebraMap R S).op (MulOpposite.op r) • RestrictScalars.toMAddEquiv (algebraMap R S) M x) =
      _
    simp

/-- The `R`-algebra homomorphism from the original coefficient algebra `S` to endomorphisms
of `RestrictScalars R S M`.
-/
def RestrictScalars.lsmul [Module S M] : S →ₐ[R] Module.End R (RestrictScalars' R S M) :=
  -- We use `RestrictScalars.moduleOrig` in the implementation,
  -- but not in the type.
  letI : Module S (RestrictScalars' R S M) := RestrictScalars.moduleOrig (algebraMap R S) M
  Algebra.lsmul R R (RestrictScalars' R S M)

variable [Module S M]

theorem addEquiv_symm_map_algebraMap_smul (r : R) (x : M) :
    (RestrictScalars.toMAddEquiv (algebraMap R S) M).symm (algebraMap R S r • x) =
      r • (RestrictScalars.toMAddEquiv (algebraMap R S) M).symm x :=
  rfl

theorem RestrictScalars.addEquiv_symm_map_smul_smul (r : R) (s : S) (x : M) :
    (RestrictScalars.toMAddEquiv (algebraMap R S) M).symm ((r • s) • x) =
      r • (RestrictScalars.toMAddEquiv (algebraMap R S) M).symm (s • x) := by
  rw [Algebra.smul_def, mul_smul]
  rfl

theorem RestrictScalars.lsmul_apply_apply (s : S) (x : RestrictScalars' R S M) :
    RestrictScalars.lsmul R S M s x =
      (RestrictScalars.toMAddEquiv (algebraMap R S) M).symm
      (s • RestrictScalars.toMAddEquiv (algebraMap R S) M x) :=
  rfl

section Algebra

@[instance_reducible]
def RestrictScalars.algebraOrig (R S A : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
    [Semiring A] [Algebra S A] : Algebra S (RestrictScalars' R S A) :=
  (RestrictScalars.toMEquiv (algebraMap R S) A).algebra S

/-- `R ⟶ S` induces `S-Alg ⥤ R-Alg`. Not an instance because `S` cannot be inferred. -/
instance Algebra.restrictScalars {R S A : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [Semiring A] [Algebra S A] : Algebra R (RestrictScalars' R S A) :=
  let := RestrictScalars.algebraOrig R S A
  Algebra.compHom _ (algebraMap R S)

@[simp]
theorem RestrictScalars.ringEquiv_algebraMap {R S A : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [Semiring A] [Algebra S A] (r : R) :
    RestrictScalars.ringEquiv (algebraMap R S) (algebraMap R (RestrictScalars' R S A) r) =
      algebraMap S A (algebraMap R S r) :=
  rfl

end Algebra
