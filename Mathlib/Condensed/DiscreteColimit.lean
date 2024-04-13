import Mathlib.Condensed.LocallyConstant

universe u

open CategoryTheory Functor Limits Condensed FintypeCat StructuredArrow

namespace Condensed

variable {I : Type*} [Category I] [IsCofiltered I] (F : I ⥤ FintypeCat.{u})
    (c : Cone <| F ⋙ toProfinite) (hc : IsLimit c)

namespace ToStructuredArrow

@[simps]
def functor : I ⥤ StructuredArrow c.pt toProfinite where
  obj i := StructuredArrow.mk (c.π.app i)
  map f := StructuredArrow.homMk (F.map f) (c.w f)
  map_id _ := by
    simp only [CategoryTheory.Functor.map_id, hom_eq_iff, mk_right, homMk_right, id_right]
  map_comp _ _ := by simp only [Functor.map_comp, hom_eq_iff, mk_right, homMk_right, comp_right]

def functorIso : functor F c ⋙ StructuredArrow.proj c.pt toProfinite ≅ F := Iso.refl _

end Condensed.ToStructuredArrow
