/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer

/-!
# Preservation of multicoequalizers

Let `J : MultispanShape` and `d : MultispanIndex J C`.
If `F : C ⥤ D`, we define `d.map F : MultispanIndex J D` and
an isomorphism of functors `(d.map F).multispan ≅ d.multispan ⋙ F`
(see `MultispanIndex.multispanMapIso`).
If `c : Multicofork d`, we define `c.map F : Multicofork (d.map F)` and
obtain a bijection `IsColimit (F.mapCocone c) ≃ IsColimit (c.map F)`
(see `Multicofork.isColimitMapEquiv`). As a result, if `F` preserves
the colimit of `d.multispan`, we deduce that if `c` is a colimit,
then `c.map F` also is (see `Multicofork.isColimitMapOfPreserves`).

-/

universe w w' v u

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

namespace Limits

variable {J : MultispanShape.{w, w'}} (d : MultispanIndex J C)
  (c : Multicofork d) (F : C ⥤ D)

/-- The multispan index obtained by applying a functor. -/
@[simps]
def MultispanIndex.map : MultispanIndex J D where
  left i := F.obj (d.left i)
  right i := F.obj (d.right i)
  fst i := F.map (d.fst i)
  snd i := F.map (d.snd i)

/-- If `d : MultispanIndex J C` and `F : C ⥤ D`, this is the obvious isomorphism
`(d.map F).multispan ≅ d.multispan ⋙ F`. -/
@[simps!]
def MultispanIndex.multispanMapIso : (d.map F).multispan ≅ d.multispan ⋙ F :=
  NatIso.ofComponents
    (fun i ↦ match i with
      | .left _ => Iso.refl _
      | .right _ => Iso.refl _)
    (by rintro _ _ (_ | _) <;> simp)

variable {d}

/-- If `d : MultispanIndex J C`, `c : Multicofork d` and `F : C ⥤ D`,
this is the induced multicofork of `d.map F`. -/
@[simps!]
def Multicofork.map : Multicofork (d.map F) :=
  Multicofork.ofπ _ (F.obj c.pt) (fun i ↦ F.map (c.π i)) (fun j ↦ by
    dsimp
    rw [← F.map_comp, ← F.map_comp, condition])

/-- If `d : MultispanIndex J C`, `c : Multicofork d` and `F : C ⥤ D`,
the cocone `F.mapCocone c` is colimit iff the multicofork `c.map F` is. -/
def Multicofork.isColimitMapEquiv :
    IsColimit (F.mapCocone c) ≃ IsColimit (c.map F) :=
  (IsColimit.precomposeInvEquiv (d.multispanMapIso F).symm (F.mapCocone c)).symm.trans
    (IsColimit.equivIsoColimit
      (Multicofork.ext (Iso.refl _) (fun i ↦ by dsimp only [Multicofork.π]; simp)))

/-- If `d : MultispanIndex J C`, `c : Multicofork d` is a colimit multicofork,
and `F : C ⥤ D` is a functor which preserves the colimit of `d.multispan`,
then the multicofork `c.map F` is colimit. -/
noncomputable def Multicofork.isColimitMapOfPreserves
    [PreservesColimit d.multispan F] (hc : IsColimit c) : IsColimit (c.map F) :=
  (isColimitMapEquiv c F) (isColimitOfPreserves F hc)

end Limits

end CategoryTheory
