/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Presentable.IsCardinalFiltered
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Subobjects in Grothendieck abelian categories

We study the complete lattice of subjects of `X : C`
when `C` is a Grothendieck abelian cateogry. In particular,
for a functor `F : J ⥤ MonoOver X` from a filtered category,
we relate the colimit of `F` (computed in `C`) and the
supremum of the subobjects corresponding to the objects
in the image of `F`.

-/

universe w v' v u' u

namespace CategoryTheory

open Limits

namespace IsGrothendieckAbelian

attribute [local instance] IsFiltered.isConnected

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {X : C} {J : Type w} [SmallCategory J] (F : J ⥤ MonoOver X)

section

variable [IsFiltered J] {c : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.forget _)}
  (hc : IsColimit c) (f : c.pt ⟶ X) (hf : ∀ (j : J), c.ι.app j ≫ f = (F.obj j).obj.hom)

include hc hf

/-- If `C` is a Grothendieck abelian category, `X : C`, if `F : J ⥤ MonoOver X` is a
functor from a filtered category `J`, `c` is a colimit cocone for the corresponding
functor `J ⥤ C`, and `f : c.pt ⟶ X` is induced by the inclusions,
then `f` is a monomorphism. -/
lemma mono_of_isColimit_monoOver : Mono f := by
  let α : F ⋙ MonoOver.forget _ ⋙ Over.forget _ ⟶ (Functor.const _).obj X :=
    { app j := (F.obj j).obj.hom
      naturality _ _ f := (F.map f).w }
  have := NatTrans.mono_of_mono_app α
  exact colim.map_mono' α hc (isColimitConstCocone J X) f (by simpa using hf)

/-- If `C` is a Grothendieck abelian category, `X : C`, if `F : J ⥤ MonoOver X` is a
functor from a filtered category `J`, the colimit of `F` (computed in `C`) gives
a subobject of `F` which is a supremum of the subobjects corresponding to
the objects in the image of the functor `F`. -/
lemma subobject_mk_of_isColimit_eq_iSup :
    haveI := mono_of_isColimit_monoOver F hc f hf
    Subobject.mk f = ⨆ j, Subobject.mk (F.obj j).obj.hom := by
  haveI := mono_of_isColimit_monoOver F hc f hf
  apply le_antisymm
  · rw [le_iSup_iff]
    intro s H
    induction' s using Subobject.ind with Z g _
    let c' : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.forget _) := Cocone.mk Z
      { app j := Subobject.ofMkLEMk _ _ (H j)
        naturality j j' f := by
          dsimp
          simpa only [← cancel_mono g, Category.assoc, Subobject.ofMkLEMk_comp,
            Category.comp_id] using MonoOver.w (F.map f) }
    exact Subobject.mk_le_mk_of_comm (hc.desc c')
      (hc.hom_ext (fun j ↦ by rw [hc.fac_assoc c' j, hf, Subobject.ofMkLEMk_comp]))
  · rw [iSup_le_iff]
    intro j
    exact Subobject.mk_le_mk_of_comm (c.ι.app j) (hf j)

end

/-- If `C` is a Grothendieck abelian category, `X : C`, if `F : J ⥤ MonoOver X` is a
functor from a `κ`-filtered category `J` with `κ` a regular cardinal such
that `HasCardinalLT (Subobject X) κ`, and if the colimit of `F` (computed in `C`)
maps epimorphically onto `X`, then there exists `j : J` such that `(F.obj j).obj.hom`
is an isomorphism. -/
lemma exists_isIso_of_functor_from_monoOver
    {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular] [IsCardinalFiltered J κ]
    (hXκ : HasCardinalLT (Subobject X) κ)
    (c : Cocone (F ⋙ MonoOver.forget _ ⋙ Over.forget _)) (hc : IsColimit c)
    (f : c.pt ⟶ X) (hf : ∀ (j : J), c.ι.app j ≫ f = (F.obj j).obj.hom) (h : Epi f) :
    ∃ (j : J), IsIso (F.obj j).obj.hom := by
  have := isFiltered_of_isCardinalDirected J κ
  have := mono_of_isColimit_monoOver F hc f hf
  rw [Subobject.epi_iff_mk_eq_top f,
    subobject_mk_of_isColimit_eq_iSup F hc f hf] at h
  let s (j : J) : Subobject X := Subobject.mk (F.obj j).obj.hom
  have h' : Function.Surjective (fun (j : J) ↦ (⟨s j, _, rfl⟩ : Set.range s)) := by
    rintro ⟨_, j, rfl⟩
    exact ⟨j, rfl⟩
  obtain ⟨σ, hσ⟩ := h'.hasRightInverse
  have hs : HasCardinalLT (Set.range s) κ :=
    hXκ.of_injective (f := Subtype.val) Subtype.val_injective
  refine ⟨IsCardinalFiltered.max σ hs, ?_⟩
  rw [Subobject.isIso_iff_mk_eq_top, ← top_le_iff, ← h, iSup_le_iff]
  intro j
  let t : Set.range s := ⟨_, j, rfl⟩
  trans Subobject.mk (F.obj (σ t)).obj.hom
  · exact (hσ t).symm.le
  · exact MonoOver.subobjectMk_le_mk_of_hom
      (F.map (IsCardinalFiltered.toMax σ hs t))

end IsGrothendieckAbelian

end CategoryTheory
