/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Action of bifunctors on cokernels

Let `c₁` (resp. `c₂`) be a cokernel cofork for a morphism `f₁ : X₁ ⟶ Y₁`
in a category `C₁` (resp. `f₂ : X₂ ⟶ Y₂` in `C₂`). Given a bifunctor `F : C₁ ⥤ C₂ ⥤ C`,
we construct a cokernel cofork with point `(F.obj c₁.pt).obj c₂.pt` for
the obvious morphism `(F.obj X₁).obj Y₂ ⨿ (F.obj Y₁).obj X₂ ⟶ (F.obj Y₁).obj Y₂`,
and show that it is a colimit when both coforks are colimit, the cokernel of `f₁`
is preserved by `F.obj c₁.pt` and the cokernel of `f₂` is preserved by
`F.flip.obj X₁` and `F.flip.obj Y₁`.

-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C₁ C₂ C : Type*} [Category* C₁] [Category* C₂] [Category* C]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms C]

namespace CokernelCofork

variable {X₁ Y₁ : C₁} {f₁ : X₁ ⟶ Y₁} {c₁ : CokernelCofork f₁} (hc₁ : IsColimit c₁)
  {X₂ Y₂ : C₂} {f₂ : X₂ ⟶ Y₂} {c₂ : CokernelCofork f₂} (hc₂ : IsColimit c₂)
  (F : C₁ ⥤ C₂ ⥤ C)
  [(F.obj c₁.pt).PreservesZeroMorphisms]
  [F.PreservesZeroMorphisms]

set_option backward.isDefEq.respectTransparency false in
variable (c₁ c₂) in
/-- Let `c₁` (resp. `c₂`) be a cokernel cofork for a morphism `f₁ : X₁ ⟶ Y₁`
in a category `C₁` (resp. `f₂ : X₂ ⟶ Y₂` in `C₂`). Given a bifunctor `F : C₁ ⥤ C₂ ⥤ C`,
this is the cokernel cofork with point `(F.obj c₁.pt).obj c₂.pt` for
the obvious morphism `(F.obj X₁).obj Y₂ ⨿ (F.obj Y₁).obj X₂ ⟶ (F.obj Y₁).obj Y₂`. -/
noncomputable abbrev mapBifunctor [HasBinaryCoproduct ((F.obj X₁).obj Y₂) ((F.obj Y₁).obj X₂)] :
    CokernelCofork (coprod.desc ((F.map f₁).app Y₂) ((F.obj Y₁).map f₂)) :=
  CokernelCofork.ofπ (Z := (F.obj c₁.pt).obj c₂.pt)
    ((F.map c₁.π).app Y₂ ≫ (F.obj c₁.pt).map c₂.π) (by
      ext
      · simp [← NatTrans.comp_app_assoc, ← Functor.map_comp]
      · simp [← Functor.map_comp])

variable [PreservesColimit (parallelPair f₂ 0) (F.obj c₁.pt)]
  [PreservesColimit (parallelPair f₁ 0) (F.flip.obj Y₂)]

namespace isColimitMapBifunctor

include hc₁ hc₂

lemma hom_ext {T : C} {f g : (F.obj c₁.pt).obj c₂.pt ⟶ T}
    (h : (F.map c₁.π).app Y₂ ≫ (F.obj c₁.pt).map c₂.π ≫ f =
      (F.map c₁.π).app Y₂ ≫ (F.obj c₁.pt).map c₂.π ≫ g) : f = g :=
  Cofork.IsColimit.hom_ext (mapIsColimit _ hc₂ (F.obj c₁.pt))
    (Cofork.IsColimit.hom_ext (mapIsColimit _ hc₁ (F.flip.obj Y₂)) h)

variable [HasBinaryCoproduct ((F.obj X₁).obj Y₂) ((F.obj Y₁).obj X₂)]
  [PreservesColimit (parallelPair f₁ 0) (F.flip.obj X₂)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma exists_desc (s : CokernelCofork (coprod.desc ((F.map f₁).app Y₂) ((F.obj Y₁).map f₂))) :
    ∃ (l : (F.obj c₁.pt).obj c₂.pt ⟶ s.pt),
      (F.map c₁.π).app Y₂ ≫ (F.obj c₁.pt).map c₂.π ≫ l = s.π := by
  obtain ⟨l, hl⟩ := Cofork.IsColimit.desc' (mapIsColimit _ hc₁ (F.flip.obj Y₂)) s.π (by
    have := coprod.inl ≫= s.condition
    rw [coprod.inl_desc_assoc, comp_zero] at this
    rwa [zero_comp])
  obtain ⟨l', hl'⟩ := Cofork.IsColimit.desc' (mapIsColimit _ hc₂ (F.obj c₁.pt)) l (by
    have := coprod.inr ≫= s.condition
    rw [coprod.inr_desc_assoc, ← dsimp% hl, NatTrans.naturality_assoc, comp_zero] at this
    apply Cofork.IsColimit.hom_ext (mapIsColimit _ hc₁ (F.flip.obj X₂))
    rwa [zero_comp, comp_zero])
  exact ⟨l', by cat_disch⟩

end isColimitMapBifunctor

variable [HasBinaryCoproduct ((F.obj X₁).obj Y₂) ((F.obj Y₁).obj X₂)]
  [PreservesColimit (parallelPair f₁ 0) (F.flip.obj X₂)]

set_option backward.defeqAttrib.useBackward true in
open isColimitMapBifunctor in
/-- Let `c₁` (resp. `c₂`) be a colimit cokernel cofork for a morphism `f₁ : X₁ ⟶ Y₁`
in a category `C₁` (resp. `f₂ : X₂ ⟶ Y₂` in `C₂`). If `F : C₁ ⥤ C₂ ⥤ C` is a bifunctor,
then `(F.obj c₁.pt).obj c₂.pt` identifies to the cokernel of the morphism
`(F.obj X₁).obj Y₂ ⨿ (F.obj Y₁).obj X₂ ⟶ (F.obj Y₁).obj Y₂`
when the cokernel of `f₁` is preserved by `F.obj c₁.pt` and the cokernel of `f₂`
is preserved by `F.flip.obj X₁` and `F.flip.obj Y₁`. -/
noncomputable def isColimitMapBifunctor :
    IsColimit (mapBifunctor c₁ c₂ F) :=
  Cofork.IsColimit.mk _
    (fun s ↦ (exists_desc hc₁ hc₂ F s).choose)
    (fun s ↦ by simpa using (exists_desc hc₁ hc₂ F s).choose_spec)
    (fun s m hm ↦ hom_ext hc₁ hc₂ F (by
      rw [(exists_desc hc₁ hc₂ F s).choose_spec, ← dsimp% hm, Category.assoc]))

end CokernelCofork

end CategoryTheory.Limits
