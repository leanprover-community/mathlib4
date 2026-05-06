/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Tower

/-!

# Restriction of scalars type aliases

See the documentation attached to the `RestrictScalarsMap` definition for advice on how and
when to use these type aliases. As described there, it is often a better choice to use the
`IsScalarTower` typeclass instead.

## Main definitions

* `RestrictScalarsMap f M`: for a function `f : R → S`, a type synonym for the type `M`.
  When `f : R →+* S` is a ring homomorphism and `M` is an `S`-module, this carries an `R`-module
  structure via `r • m := f r • m`. Note that by default we do *not* have a
  `Module S (RestrictScalarsMap f M)` instance for the original action; this is available as
  `RestrictScalarsMap.moduleOrig` if really needed.
* `RestrictScalars R S M`: abbreviation for `RestrictScalarsMap (algebraMap R S) M` when
  `[CommSemiring R] [Algebra R S]`. This is the classical restriction of scalars along an algebra
  map.
* `RestrictScalarsMap.addEquiv f M : RestrictScalarsMap f M ≃+ M`: the additive
  equivalence between the restricted and original space (in fact, they are definitionally equal,
  but sometimes it is helpful to avoid using this fact, to keep instances from leaking).
* `RestrictScalarsMap.ringEquiv f A : RestrictScalarsMap f A ≃+* A`: the ring equivalence
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
/-- Given a function `f : R → S`, `RestrictScalarsMap f M` is a type synonym for `M`.
It is used to equip `M` with `R`-structures derived from `S`-structures via `f`. The main
instance `RestrictScalarsMap.module` requires `f : R →+* S` to be a ring homomorphism and
provides the `R`-module structure `r • m := f r • m` when `M` is an `S`-module.

Warning: use this type synonym judiciously! Consider an example where we want to construct an
`R`-linear map from `M` to `N`, given:
```lean
variable (R S M N : Type*)
variable [Ring R] [Ring S] (f : R →+* S) [AddCommGroup M] [Module S M] [AddCommGroup N] [Module R N]
```
With the assumptions above we can't directly state our map as we have no `Module R M` structure, but
`RestrictScalarsMap` permits it to be written as:
```lean
-- an `R`-module structure on `M` is provided by `RestrictScalarsMap` which is compatible
example : RestrictScalarsMap f M →ₗ[R] N := sorry
```
However, when `R` is commutative it is usually better just to add this extra structure as an
argument:
```lean
-- an `R`-module structure on `M` and proof of its compatibility is provided by the user
example [Module R M] [IsScalarTower R S M] : M →ₗ[R] N := sorry
```
The advantage of the second approach is that it defers the duty of providing the missing typeclasses
`[Module R M] [IsScalarTower R S M]`. If some concrete `M` naturally carries these (as is often
the case) then we have avoided `RestrictScalarsMap` entirely. If not, we can pass
`RestrictScalarsMap f M` later on instead of `M`.

Note that this means we almost always want to state definitions and lemmas in the language of
`IsScalarTower` rather than `RestrictScalarsMap`.

When `R` is a commutative semiring and `[Algebra R S]`, `RestrictScalars R S M` is an abbreviation
for `RestrictScalarsMap (algebraMap R S) M`. -/
@[nolint unusedArguments]
structure RestrictScalarsMap {R S : Type*} (f : R → S) (M : Type*) where res' ::
  unres' : M

variable {R S M A : Type*} (f : R → S)

namespace RestrictScalarsMap

def res : M → RestrictScalarsMap f M := res'

variable {f} in
def unres : RestrictScalarsMap f M → M := unres'

@[simp] lemma res_unres (m : RestrictScalarsMap f M) : res f (unres m) = m := rfl

@[simp] lemma unres_res (m : M) : unres (res f m) = m := rfl

def equiv : RestrictScalarsMap f M ≃ M :=
  ⟨unres, res f, res_unres f, unres_res f⟩

instance [Inhabited M] : Inhabited (RestrictScalarsMap f M) := ⟨res f default⟩

@[to_additive]
instance [One M] : One (RestrictScalarsMap f M) where
  one := res f 1

@[to_additive (attr := simp)]
lemma res_one [One M] : res f (1 : M) = 1 := rfl

@[to_additive (attr := simp)]
lemma unres_one [One M] : unres (1 : RestrictScalarsMap f M) = 1 := rfl

@[to_additive]
instance [Mul M] : Mul (RestrictScalarsMap f M) where
  mul x y := res f (x.unres * y.unres)

@[to_additive (attr := simp)]
lemma res_mul [Mul M] (x y : M) :
    res f (x * y) = res f x * res f y := rfl

@[to_additive (attr := simp)]
lemma unres_mul [Mul M] (x y : RestrictScalarsMap f M) :
    unres (x * y) = unres x * unres y := rfl

/-- The additive equivalence between `RestrictScalarsMap f M` and the original module `M`. -/
@[to_additive]
def mulEquiv [Mul M] : RestrictScalarsMap f M ≃* M where
  map_mul' := unres_mul f
  __ := equiv f

@[to_additive]
instance [Semigroup M] : Semigroup (RestrictScalarsMap f M) where
  mul_assoc _ _ _ := congr(res f $(mul_assoc _ _ _))

@[to_additive]
instance [MulOneClass M] : MulOneClass (RestrictScalarsMap f M) where
  one_mul _ := congr(res f $(one_mul _))
  mul_one _ := congr(res f $(mul_one _))

@[to_additive]
instance [Monoid M] : Monoid (RestrictScalarsMap f M) where

@[to_additive]
instance [CommMonoid M] : CommMonoid (RestrictScalarsMap f M) where
  mul_comm _ _ := congr(res f $(mul_comm _ _))

instance [Sub M] : Sub (RestrictScalarsMap f M) where
  sub x y := res f (x.unres - y.unres)

@[simp] lemma res_sub [Sub M] (x y : M) :
    res f (x - y) = res f x - res f y := rfl

@[simp] lemma unres_sub [Sub M] (x y : RestrictScalarsMap f M) :
    unres (x - y) = unres x - unres y := rfl

instance [Neg M] : Neg (RestrictScalarsMap f M) where
  neg x := res f (-x.unres)

@[simp] lemma res_neg [Neg M] (x : M) :
    res f (-x) = -(res f x) := rfl

@[simp] lemma unres_neg [Neg M] (x : RestrictScalarsMap f M) :
    (-x).unres = -x.unres := rfl

instance [SubNegMonoid M] : SubNegMonoid (RestrictScalarsMap f M) where
  sub_eq_add_neg _ _ := congr(res f $(sub_eq_add_neg _ _))

instance [AddGroup M] : AddGroup (RestrictScalarsMap f M) where
  neg_add_cancel _ := congr(res f $(neg_add_cancel _))
  sub_eq_add_neg _ _ := congr(res f $(sub_eq_add_neg _ _))
  zsmul := zsmulRec

instance [AddCommGroup M] : AddCommGroup (RestrictScalarsMap f M) where

instance [I : Semiring A] : Semiring (RestrictScalarsMap f A) := sorry

instance [I : Ring A] : Ring (RestrictScalarsMap f A) := sorry

instance [I : CommSemiring A] : CommSemiring (RestrictScalarsMap f A) := sorry

instance [I : CommRing A] : CommRing (RestrictScalarsMap f A) := sorry

section Action

instance smul [SMul S M] : SMul R (RestrictScalarsMap f M) where
  smul r m := res f (f r • m.unres)

theorem smul_def [SMul S M] (r : R) (m : RestrictScalarsMap f M) :
    r • m = res f (f r • m.unres) := rfl

theorem smul_def' [SMul S M] (r : R) (m : M) :
    (r • res f m).unres = f r • m := rfl

instance semigroupAction [Semigroup R] [Semigroup S] (f : R →ₙ* S) [SemigroupAction S M] :
    SemigroupAction R (RestrictScalarsMap f M) where
  mul_smul a b m := by simp [smul_def, mul_smul]

instance mulAction [Monoid R] [Monoid S] (f : R →* S) [MulAction S M] :
    MulAction R (RestrictScalarsMap f M) where
  one_smul m := by simp [smul_def]
  __ := semigroupAction f.toMulHom

instance distribMulAction [Monoid R] [Monoid S] (f : R →* S) [AddMonoid M] [DistribMulAction S M] :
    DistribMulAction R (RestrictScalarsMap f M) where
  smul_zero _ := by simp [smul_def]
  smul_add _ _ _ := by simp [smul_def]

instance module [Semiring R] [Semiring S] (f : R →+* S) [AddCommMonoid M] [Module S M] :
    Module R (RestrictScalarsMap f M) where
  add_smul a b m := by simp [smul_def, add_smul]
  zero_smul m := by simp [smul_def]
  __ := distribMulAction f.toMonoidHom

-- todo
/-- We temporarily install the action of the original ring `S` on `RestrictScalarsMap f M`. -/
@[implicit_reducible]
def moduleOrig [Semiring S] [AddCommMonoid M] [Module S M] :
    Module S (RestrictScalarsMap f M) where
  smul s m := res f (s • m.unres)
  mul_smul := sorry
  one_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry


end Action

section Map


variable {R S : Type*} (f : R → S)

variable (M : Type*) [AddCommMonoid M]
variable (A : Type*) [Semiring A]

/-- We temporarily install the action of the original ring `S` on `RestrictScalarsMap f M`. -/
/- @[instance_reducible] -/
/- def moduleOrig [Semiring S] [I : Module S M] : Module S (RestrictScalarsMap f M) := I -/

/-- Tautological ring isomorphism `RestrictScalarsMap f A ≃+* A`. -/
def ringEquiv : RestrictScalarsMap f A ≃+* A :=
  RingEquiv.refl _

end Map

section RingHom

variable {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)

variable (M : Type*) [AddCommMonoid M]

/-- When `M` is a module over a semiring `S` and `f : R →+* S` is a ring homomorphism, then `M`
inherits an `R`-module structure via `r • m := f r • m`.

In the commutative case, the preferred way of setting this up is
`[Module R M] [Module S M] [IsScalarTower R S M]`.
-/
instance module [Module S M] : Module R (RestrictScalarsMap f M) :=
  Module.compHom M f

/-- When `M` is a right-module over a semiring `S` and `f : R →+* S` is a ring homomorphism,
then `M` inherits a right `R`-module structure. In the commutative case, the preferred way of
setting this up is `[Module Rᵐᵒᵖ M] [Module Sᵐᵒᵖ M] [IsScalarTower Rᵐᵒᵖ Sᵐᵒᵖ M]`. -/
instance opModule [Module Sᵐᵒᵖ M] :
    Module Rᵐᵒᵖ (RestrictScalarsMap f M) :=
  letI : Module Sᵐᵒᵖ (RestrictScalarsMap f M) := ‹Module Sᵐᵒᵖ M›
  Module.compHom M f.op

variable [Module S M]

instance isCentralScalar [Module Sᵐᵒᵖ M] [IsCentralScalar S M] :
    IsCentralScalar R (RestrictScalarsMap f M) where
  op_smul_eq_smul r _x := op_smul_eq_smul (f r) (_ : M)

theorem smul_def (c : R) (x : RestrictScalarsMap f M) :
    c • x = (RestrictScalarsMap.addEquiv f M).symm
      (f c • RestrictScalarsMap.addEquiv f M x) :=
  rfl

@[deprecated (since := "2026-04-30")] alias _root_.RestrictScalars.smul_def := smul_def

@[simp]
theorem addEquiv_map_smul (c : R) (x : RestrictScalarsMap f M) :
    RestrictScalarsMap.addEquiv f M (c • x) = f c • RestrictScalarsMap.addEquiv f M x :=
  rfl

@[deprecated (since := "2026-04-30")]
alias _root_.RestrictScalars.addEquiv_map_smul := addEquiv_map_smul

theorem addEquiv_symm_map_smul (r : R) (x : M) :
    (RestrictScalarsMap.addEquiv f M).symm (f r • x) =
      r • (RestrictScalarsMap.addEquiv f M).symm x :=
  rfl

@[deprecated (since := "2026-04-30")]
alias _root_.RestrictScalars.addEquiv_symm_map_algebraMap_smul := addEquiv_symm_map_smul

theorem addEquiv_symm_map_smul_smul (r : R) (s : S) (x : M) :
    (RestrictScalarsMap.addEquiv f M).symm ((f r * s) • x) =
      r • (RestrictScalarsMap.addEquiv f M).symm (s • x) := by
  rw [mul_smul]
  rfl

end RingHom

end RestrictScalarsMap

section AlgebraMap

variable (R S : Type*) [CommSemiring R]

/-- When `S` is an `R`-algebra, `RestrictScalars R S M` is the `S`-module `M` viewed as an
`R`-module. This is an abbreviation for `RestrictScalarsMap (algebraMap R S) M`.

See `RestrictScalarsMap` for the more general version that works for any ring homomorphism
`f : R →+* S` without requiring `R` to be commutative. -/
abbrev RestrictScalars [Semiring S] [Algebra R S] (M : Type*) : Type _ :=
  RestrictScalarsMap (algebraMap R S) M

variable (M A : Type*)

namespace RestrictScalars

/-- We temporarily install the action of the original ring `S` on `RestrictScalars R S M`.
Abbreviation for `RestrictScalarsMap.moduleOrig (algebraMap R S) M`. -/
abbrev moduleOrig [Semiring S] [Algebra R S] [AddCommMonoid M] [Module S M] :
    Module S (RestrictScalars R S M) :=
  RestrictScalarsMap.moduleOrig (algebraMap R S) M

/-- The additive equivalence between `RestrictScalars R S M` and the original module `M`.
Abbreviation for `RestrictScalarsMap.addEquiv (algebraMap R S) M`. -/
abbrev addEquiv [Semiring S] [Algebra R S] [AddCommMonoid M] :
    RestrictScalars R S M ≃+ M :=
  RestrictScalarsMap.addEquiv (algebraMap R S) M

/-- Tautological ring isomorphism `RestrictScalars R S A ≃+* A`.
Abbreviation for `RestrictScalarsMap.ringEquiv (algebraMap R S) A`. -/
abbrev ringEquiv [Semiring S] [Algebra R S] [Semiring A] :
    RestrictScalars R S A ≃+* A :=
  RestrictScalarsMap.ringEquiv (algebraMap R S) A

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

end AlgebraMap
