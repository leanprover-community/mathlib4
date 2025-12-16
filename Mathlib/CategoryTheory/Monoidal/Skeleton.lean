/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Skeletal

/-!
# The monoid on the skeleton of a monoidal category

The skeleton of a monoidal category is a monoid.

## Main results

* `Skeleton.instMonoid`, for monoidal categories.
* `Skeleton.instCommMonoid`, for braided monoidal categories.

-/

@[expose] public section


namespace CategoryTheory

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- If `C` is monoidal and skeletal, it is a monoid.
See note [reducible non-instances]. -/
abbrev monoidOfSkeletalMonoidal (hC : Skeletal C) : Monoid C where
  mul X Y := X ⊗ Y
  one := 𝟙_ C
  one_mul X := hC ⟨λ_ X⟩
  mul_one X := hC ⟨ρ_ X⟩
  mul_assoc X Y Z := hC ⟨α_ X Y Z⟩

/-- If `C` is braided and skeletal, it is a commutative monoid. -/
abbrev commMonoidOfSkeletalBraided [BraidedCategory C] (hC : Skeletal C) : CommMonoid C :=
  { monoidOfSkeletalMonoidal hC with mul_comm := fun X Y => hC ⟨β_ X Y⟩ }

namespace Skeleton

/-- The skeleton of a monoidal category has a monoidal structure itself, induced by the equivalence.
-/
noncomputable instance instMonoidalCategory : MonoidalCategory (Skeleton C) :=
  Monoidal.transport (skeletonEquivalence C).symm

/--
The skeleton of a monoidal category can be viewed as a monoid, where the multiplication is given by
the tensor product, and satisfies the monoid axioms since it is a skeleton.
-/
noncomputable instance instMonoid : Monoid (Skeleton C) :=
  monoidOfSkeletalMonoidal (skeleton_isSkeleton _).skel

theorem mul_eq (X Y : Skeleton C) : X * Y = toSkeleton (X.out ⊗ Y.out) := rfl
theorem one_eq : (1 : Skeleton C) = toSkeleton (𝟙_ C) := rfl

theorem toSkeleton_tensorObj (X Y : C) : toSkeleton (X ⊗ Y) = toSkeleton X * toSkeleton Y :=
  let φ := (skeletonEquivalence C).symm.unitIso.app; Quotient.sound ⟨φ X ⊗ᵢ φ Y⟩

/-- The skeleton of a braided monoidal category has a braided monoidal structure itself, induced by
the equivalence. -/
noncomputable instance instBraidedCategory [BraidedCategory C] : BraidedCategory (Skeleton C) :=
  (BraidedCategory.ofFullyFaithful
    (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).inverse:)

/--
The skeleton of a braided monoidal category can be viewed as a commutative monoid, where the
multiplication is given by the tensor product, and satisfies the monoid axioms since it is a
skeleton.
-/
noncomputable instance instCommMonoid [BraidedCategory C] : CommMonoid (Skeleton C) :=
  commMonoidOfSkeletalBraided (skeleton_isSkeleton _).skel

end Skeleton

open Functor

noncomputable instance : (skeletonEquivalence C).functor.Monoidal :=
  inferInstanceAs (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).inverse.Monoidal

noncomputable instance : (skeletonEquivalence C).inverse.Monoidal :=
  inferInstanceAs (Monoidal.equivalenceTransported (skeletonEquivalence C).symm).functor.Monoidal

variable {D : Type*} [Category* D] [MonoidalCategory D] (F : C ⥤ D) (e : C ≌ D)

noncomputable instance [F.LaxMonoidal] : F.mapSkeleton.LaxMonoidal := .comp ..
noncomputable instance [F.OplaxMonoidal] : F.mapSkeleton.OplaxMonoidal := .comp ..
noncomputable instance [F.Monoidal] : F.mapSkeleton.Monoidal := .instComp ..

/-- A monoidal functor between skeletal monoidal categories induces a monoid homomorphism. -/
def Skeletal.monoidHom [F.Monoidal] (hC : Skeletal C) (hD : Skeletal D) :
    let _ := monoidOfSkeletalMonoidal hC
    let _ := monoidOfSkeletalMonoidal hD
    C →* D := by
  intros; exact
  { toFun := F.obj
    map_one' := hD ⟨(Monoidal.εIso F).symm⟩
    map_mul' X Y := hD ⟨(Monoidal.μIso F X Y).symm⟩ }

/-- A monoidal functor between monoidal categories induces a monoid homomorphism between
the skeleta. -/
noncomputable def Skeleton.monoidHom [F.Monoidal] : Skeleton C →* Skeleton D :=
  (skeleton_skeletal C).monoidHom F.mapSkeleton (skeleton_skeletal D)

/-- A monoidal equivalence between skeletal monoidal categories induces a monoid isomorphism. -/
def Skeletal.mulEquiv [e.functor.Monoidal] (hC : Skeletal C) (hD : Skeletal D) :
    let _ := monoidOfSkeletalMonoidal hC
    let _ := monoidOfSkeletalMonoidal hD
    C ≃* D := by
  intros; exact
  { toFun := e.functor.obj
    invFun := e.inverse.obj
    left_inv X := hC ⟨(e.unitIso.app X).symm⟩
    right_inv X := hD ⟨e.counitIso.app X⟩
    map_mul' X Y := hD ⟨(Monoidal.μIso e.functor X Y).symm⟩ }

/-- A monoidal equivalence between monoidal categories induces a monoid isomorphism between
the skeleta. -/
noncomputable def Skeleton.mulEquiv [e.functor.Monoidal] : Skeleton C ≃* Skeleton D :=
  (skeleton_skeletal C).mulEquiv
    (((skeletonEquivalence C).trans e).trans (skeletonEquivalence D).symm) (skeleton_skeletal D)

end CategoryTheory
