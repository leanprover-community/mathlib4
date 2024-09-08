/-
Copyright (c) XXX. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XXX
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# XXX
-/

universe u v w u₁ v₁

namespace Algebra

variable {R : Type u} {S : Type v} {A : Type w} {B : Type*}

section Semiring

variable [CommSemiring R] [CommSemiring S]
variable [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- Algebra over a subsemiring. This builds upon `Subsemiring.module`. -/
instance ofSubsemiring (S : Subsemiring R) : Algebra S A where
  toRingHom := (algebraMap R A).comp S.subtype
  smul := (· • ·)
  commutes' r x := Algebra.commutes (r : R) x
  smul_def' r x := Algebra.smul_def (r : R) x

theorem algebraMap_ofSubsemiring (S : Subsemiring R) :
    (algebraMap S R : S →+* R) = Subsemiring.subtype S :=
  rfl

theorem coe_algebraMap_ofSubsemiring (S : Subsemiring R) : (algebraMap S R : S → R) = Subtype.val :=
  rfl

theorem algebraMap_ofSubsemiring_apply (S : Subsemiring R) (x : S) : algebraMap S R x = x :=
  rfl

/-- Algebra over a subring. This builds upon `Subring.module`. -/
instance ofSubring {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (S : Subring R) :
    Algebra S A where -- Porting note: don't use `toSubsemiring` because of a timeout
  toRingHom := (algebraMap R A).comp S.subtype
  smul := (· • ·)
  commutes' r x := Algebra.commutes (r : R) x
  smul_def' r x := Algebra.smul_def (r : R) x

theorem algebraMap_ofSubring {R : Type*} [CommRing R] (S : Subring R) :
    (algebraMap S R : S →+* R) = Subring.subtype S :=
  rfl

theorem coe_algebraMap_ofSubring {R : Type*} [CommRing R] (S : Subring R) :
    (algebraMap S R : S → R) = Subtype.val :=
  rfl

theorem algebraMap_ofSubring_apply {R : Type*} [CommRing R] (S : Subring R) (x : S) :
    algebraMap S R x = x :=
  rfl

/-- Explicit characterization of the submonoid map in the case of an algebra.
`S` is made explicit to help with type inference -/
def algebraMapSubmonoid (S : Type*) [Semiring S] [Algebra R S] (M : Submonoid R) : Submonoid S :=
  M.map (algebraMap R S)

theorem mem_algebraMapSubmonoid_of_mem {S : Type*} [Semiring S] [Algebra R S] {M : Submonoid R}
    (x : M) : algebraMap R S x ∈ algebraMapSubmonoid S M :=
  Set.mem_image_of_mem (algebraMap R S) x.2

end Semiring

end Algebra
