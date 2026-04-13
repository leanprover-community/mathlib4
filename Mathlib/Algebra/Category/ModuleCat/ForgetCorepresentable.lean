/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Yoneda

/-!
# The forgetful functor on `ModuleCat` is corepresentable

For a commutative ring `R`, the forgetful functor `ModuleCat R ⥤ Type u` is
corepresentable by the free rank-1 module `R`. The natural isomorphism
`coyoneda.obj (op R) ≅ forget (ModuleCat R)` sends a linear map `f : R →ₗ[R] M`
to `f(1)`.

## Main results

- `ModuleCat.coyonedaObjIsoForget`: `Hom(R, -)` is naturally isomorphic to the
  forgetful functor.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- The functor `Hom(R, -)` is naturally isomorphic to the forgetful functor
`ModuleCat R ⥤ Type u`. The equivalence at each component sends a linear map
`f : R →ₗ[R] M` to `f(1)`. -/
@[simps! inv_app]
noncomputable def coyonedaObjIsoForget :
    coyoneda.obj (op (ModuleCat.of R R)) ≅ forget (ModuleCat.{u} R) :=
  NatIso.ofComponents
    (fun M ↦ (ModuleCat.homEquiv.trans
      (LinearMap.ringLmapEquivSelf R R M).toEquiv).toIso)
    (fun {X Y} f => by ext g; exact ConcreteCategory.comp_apply g f 1)

@[simp]
lemma coyonedaObjIsoForget_hom_app (R : Type u) [CommRing R] (X : ModuleCat R)
    (a : (coyoneda.obj (op (of R R))).obj X) :
    (coyonedaObjIsoForget R).hom.app X a = a.hom 1 :=
  rfl

end ModuleCat
