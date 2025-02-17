/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Exactness of colimits in abelian categories

Assuming `HasExactColimitsOfShape J C`, we rephrase the exactness of
`colim : (J ⥤ C) ⥤ C` by saying that if `S : ShortComplex (J ⥤ C)`
is exact, and we have colimit cocones `c₁`, `c₂`, `c₃`
for `S.X₁`, `S.X₂` and `S.X₃`, then the induced short complex
`c₁.pt ⟶ c₂.pt ⟶ c₃.pt` is exact.

-/

universe v v' u u'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]
  {J : Type u'} [Category.{v'} J]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
  (S : ShortComplex (J ⥤ C)) (hS : S.Exact)
  {c₁ : Cocone S.X₁} (hc₁ : IsColimit c₁) (c₂ : Cocone S.X₂) (hc₂ : IsColimit c₂)
  (c₃ : Cocone S.X₃) (hc₃ : IsColimit c₃)
  (f : c₁.pt ⟶ c₂.pt) (g : c₂.pt ⟶ c₃.pt)
  (hf : ∀ j, c₁.ι.app j ≫ f = S.f.app j ≫ c₂.ι.app j)
  (hg : ∀ j, c₂.ι.app j ≫ g = S.g.app j ≫ c₃.ι.app j)

/-- Given `S : ShortCompex (J ⥤ C)` and (colimit) cocones for `S.X₁`, `S.X₂`,
`S.X₃` equipped with suitable data, this is the induced
short complex `c₁.pt ⟶ c₂.pt ⟶ c₃.pt`. -/
@[simps]
def colim.mapShortComplex : ShortComplex C :=
  ShortComplex.mk f g (hc₁.hom_ext (fun j ↦ by
    dsimp
    rw [reassoc_of% (hf j), hg j, comp_zero, ← NatTrans.comp_app_assoc, S.zero,
      zero_app, zero_comp]))

variable {S c₁ c₂ c₃}

include hc₂ hc₃ hS in
/-- Assuming `HasExactColimitsOfShape J C`, this lemma rephases the exactness
of the functor `colim : (J ⥤ C) ⥤ C` by saying that if `S : ShortComplex (J ⥤ C)`
is exact, then the short complex obtained by taking the colimits is exact,
where we allow the replacement of the chosen colimit cocones of the
colimit API by arbitrary colimit cocones. -/
lemma colim.exact_mapShortComplex :
    (mapShortComplex S hc₁ c₂ c₃ f g hf hg).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).2 (hS.map colim)
  refine ShortComplex.isoMk
    (IsColimit.coconePointUniqueUpToIso hc₁ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₂ (colimit.isColimit _))
    (IsColimit.coconePointUniqueUpToIso hc₃ (colimit.isColimit _))
    (hc₁.hom_ext (fun j ↦ ?_)) (hc₂.hom_ext (fun j ↦ ?_))
  · dsimp
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
      colimit.cocone_ι, ι_colimMap, reassoc_of% (hf j),
      IsColimit.comp_coconePointUniqueUpToIso_hom, colimit.cocone_ι]
  · dsimp
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc,
      colimit.cocone_ι, ι_colimMap, reassoc_of% (hg j),
      IsColimit.comp_coconePointUniqueUpToIso_hom, colimit.cocone_ι]

end CategoryTheory.Limits
