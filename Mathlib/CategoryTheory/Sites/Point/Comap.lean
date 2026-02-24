/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Inverse image of a point by a continuous functor

Let `F : C ⥤ D` be a representably flat continuous functor between sites `(C, J)`
and `(D, K)`. Let `Φ` be a point of `(D, K)`. Assume `hF : CoverPreserving J K F`.
In this file, we define a point `Φ.comap F hF` of the site `(C, J)` and
construct an isomorphism
`(Φ.comap F hF).sheafFiber ≅ F.sheafPullback A J K ⋙ Φ.sheafFiber`.

-/

@[expose] public section

universe w v

namespace CategoryTheory.GrothendieckTopology.Point

open Limits

variable {C D : Type*} [Category* C] [Category* D]
  {K : GrothendieckTopology D}
  (Φ : Point.{w} K) (F : C ⥤ D) [RepresentablyFlat F] {J : GrothendieckTopology C}
  (hF : CoverPreserving J K F)
  [InitiallySmall (F ⋙ Φ.fiber).Elements]

/-- If `F : C ⥤ D` is a representably flat and cover preserving functor between sites, then
any point on `D` induces a point on `C` by precomposing the fiber functor with `F`. -/
@[simps]
def comap : Point.{w} J where
  fiber := F ⋙ Φ.fiber
  isCofiltered := by
    infer_instance
  jointly_surjective {X} {R} hR x := by
    obtain ⟨Y, f, ⟨W, g, h, hg, rfl⟩, y, rfl⟩ :=
      Φ.jointly_surjective (Sieve.functorPushforward F R) (hF.cover_preserve hR) x
    use W, g, hg, Φ.fiber.map h y
    simp

variable (A : Type*) [Category.{v} A] [HasProducts.{w} A]
  [Functor.IsContinuous.{v} F J K]

/-- Given a continuous functor `F : C ⥤ D` between sites `(C, J)` and `(D, K)`,
and a point `Φ` of `(D, K)`, this is the isomorphism between
`Φ.skyscraperSheafFunctor ⋙ F.sheafPushforwardContinuous A J K` and
`(Φ.comap F hF).skyscraperSheafFunctor`. -/
noncomputable def skyscraperSheafFunctorCompSheafPushforwardContinuous :
    Φ.skyscraperSheafFunctor ⋙ F.sheafPushforwardContinuous A J K ≅
      (Φ.comap F hF).skyscraperSheafFunctor :=
  Iso.refl _

variable [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasColimitsOfSize.{w, w} A]

/-- Given a continuous functor `F : C ⥤ D` between sites `(C, J)` and `(D, K)`,
and a point `Φ` of `(D, K)`, the fiber functor on sheaves of the
point `Φ.comap F hF` on `(C, J)` identifies to the composition
`F.sheafPullback A J K ⋙ Φ.sheafFiber`. -/
noncomputable def sheafFiberComapIso :
    (Φ.comap F hF).sheafFiber ≅ F.sheafPullback A J K ⋙ Φ.sheafFiber :=
  (conjugateIsoEquiv ((F.sheafAdjunctionContinuous A J K).comp Φ.skyscraperSheafAdjunction)
    (Φ.comap F hF).skyscraperSheafAdjunction).symm
      (Φ.skyscraperSheafFunctorCompSheafPushforwardContinuous F hF A)

end CategoryTheory.GrothendieckTopology.Point
