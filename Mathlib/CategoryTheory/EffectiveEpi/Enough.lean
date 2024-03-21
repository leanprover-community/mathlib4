import Mathlib.CategoryTheory.EffectiveEpi.Basic

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

namespace Functor

structure EffectivePresentation (X : D) where
  p : C
  f : F.obj p ⟶ X
  effectiveEpi : EffectiveEpi f

class EffectivelyEnough : Prop where
  presentation : ∀ (X : D), Nonempty (F.EffectivePresentation X)

variable [F.EffectivelyEnough]

/--
`F.over X` provides an arbitrarily chosen object in the image of `F` equipped with an effective
epimorphism `F.π : F.over X ⟶ X`.
-/
noncomputable def over (X : D) : D :=
  F.obj (EffectivelyEnough.presentation (F := F) X).some.p

/--
The epimorphism `F.π : F.over X ⟶ X` from the arbitrarily chosen object in the image of `F`
over `X`.
-/
noncomputable def π (X : D) : over F X ⟶ X :=
  (EffectivelyEnough.presentation (F := F) X).some.f

instance (X : D) : EffectiveEpi (F.π X) :=
  (EffectivelyEnough.presentation X).some.effectiveEpi

end Functor
