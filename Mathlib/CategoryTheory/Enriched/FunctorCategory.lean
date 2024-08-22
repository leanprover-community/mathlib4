import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Enriched.Basic
import Mathlib.CategoryTheory.Closed.Monoidal
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

universe v v' v'' u u' u''

namespace CategoryTheory

open Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [MonoidalCategory D] [MonoidalClosed D]

namespace Functor

section

variable (F G : C ⥤ D)

@[simps]
def enrichedHom.multicospanIndex : MulticospanIndex D where
  L := ULift C
  R := Arrow C
  fstTo f := ULift.up f.left
  sndTo f := ULift.up f.right
  left := fun ⟨X⟩ ↦ (ihom (F.obj X)).obj (G.obj X)
  right f := (ihom (F.obj f.left)).obj (G.obj f.right)
  fst f := (ihom _).map (G.map f.hom)
  snd f := (MonoidalClosed.pre (F.map f.hom)).app (G.obj f.right)

abbrev HasEnrichedHom := HasMultiequalizer (enrichedHom.multicospanIndex F G)

noncomputable def enrichedHom [HasEnrichedHom F G] : D :=
  multiequalizer (enrichedHom.multicospanIndex F G)

end

namespace enrichedHom

section

variable (F G : C ⥤ D) [HasEnrichedHom F G] (X : C)

noncomputable abbrev app : enrichedHom F G ⟶ (ihom (F.obj X)).obj (G.obj X) :=
  Multiequalizer.ι (enrichedHom.multicospanIndex F G) (ULift.up X)

end

noncomputable def id (F : C ⥤ D) [HasEnrichedHom F F] : 𝟙_ D ⟶ enrichedHom F F :=
    Multiequalizer.lift _ _ (fun ⟨X⟩ ↦
      -- this should be part of the `ihom` API
      MonoidalClosed.curry (ρ_ _).hom) (by
  sorry)

noncomputable def comp (F G H : C ⥤ D)
    [HasEnrichedHom F G] [HasEnrichedHom G H] [HasEnrichedHom F H] :
    F.enrichedHom G ⊗ G.enrichedHom H ⟶ F.enrichedHom H :=
  Multiequalizer.lift _ _
    (fun ⟨X⟩ ↦ (app F G X ⊗ app G H X) ≫
      -- this should be part of the `ihom` API
      MonoidalClosed.curry ((α_ _ _ _).inv ≫ (ihom.ev _).app _ ▷ _ ≫ (ihom.ev _).app _))
    sorry

end enrichedHom

variable [∀ (F G : C ⥤ D), HasEnrichedHom F G]

noncomputable instance : EnrichedCategory D (C ⥤ D) where
  Hom F G := enrichedHom F G
  id F := enrichedHom.id F
  comp F G H := enrichedHom.comp F G H
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end Functor

end CategoryTheory
