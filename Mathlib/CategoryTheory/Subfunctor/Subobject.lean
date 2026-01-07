/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Comparison between `Subfunctor`, `MonoOver` and `Subobject`

Given a type-valued functor `F : C ⥤ Type w`, we define an equivalence
of categories `Subfunctor.equivalenceMonoOver F : Subfunctor F ≌ MonoOver F`
and an order isomorphism `Subfunctor.orderIsoSubject F : Subfunctor F ≃o Subobject F`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

namespace Subfunctor

/-- The equivalence of categories `Subfunctor F ≌ MonoOver F`. -/
@[simps]
noncomputable def equivalenceMonoOver : Subfunctor F ≌ MonoOver F where
  functor :=
    { obj A := MonoOver.mk A.ι
      map {A B} f := MonoOver.homMk (Subfunctor.homOfLe (leOfHom f)) }
  inverse :=
    { obj X := Subfunctor.range X.arrow
      map {X Y} f := homOfLE (by
        rw [← MonoOver.w f]
        apply range_comp_le ) }
  unitIso := NatIso.ofComponents (fun A ↦ eqToIso (by simp))
  counitIso := NatIso.ofComponents
    (fun X ↦ MonoOver.isoMk ((asIso (toRange X.arrow)).symm))

variable {F} in
@[simp]
lemma range_subobjectMk_ι (A : Subfunctor F) :
    range (Subobject.mk A.ι).arrow = A :=
  (((equivalenceMonoOver F).trans
    (ThinSkeleton.equivalence _).symm).unitIso.app A).to_eq.symm

variable {F} in
@[simp]
lemma subobjectMk_range_arrow (X : Subobject F) :
    Subobject.mk (range X.arrow).ι = X :=
  (((equivalenceMonoOver F).trans
    (ThinSkeleton.equivalence _).symm).counitIso.app X).to_eq

/-- The order isomorphism `Subfunctor F ≃o MonoOver F`. -/
@[simps]
noncomputable def orderIsoSubobject : Subfunctor F ≃o Subobject F where
  toFun A := Subobject.mk A.ι
  invFun X := Subfunctor.range X.arrow
  left_inv A := by simp
  right_inv X := by simp
  map_rel_iff' {A B} := by
    constructor
    · intro h
      have : range (Subobject.mk A.ι).arrow ≤ range (Subobject.mk B.ι).arrow :=
        leOfHom (((equivalenceMonoOver F).trans
          (ThinSkeleton.equivalence _).symm).inverse.map (homOfLE h))
      simpa using this
    · intro h
      exact leOfHom (((equivalenceMonoOver F).trans
        (ThinSkeleton.equivalence _).symm).functor.map (homOfLE h))

@[deprecated (since := "2025-12-11")] alias Subpresheaf.equivalenceMonoOver := equivalenceMonoOver
@[deprecated (since := "2025-12-11")] alias Subpresheaf.range_subobjectMk_ι := range_subobjectMk_ι
@[deprecated (since := "2025-12-11")] alias Subpresheaf.subobjectMk_range_arrow :=
  subobjectMk_range_arrow
@[deprecated (since := "2025-12-11")] alias Subpresheaf.orderIsoSubobject := orderIsoSubobject

end Subfunctor

end CategoryTheory
