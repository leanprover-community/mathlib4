/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.RestrictedYoneda

/-!
# Characterization of dense functors

Let `F : C ⥤ D` be a full functor. We show that `F` is dense iff
the restricted Yoneda functor `D ⥤ Cᵒᵖ ⥤ Type _` is fully faithful.

## References

* https://ncatlab.org/nlab/show/dense+subcategory

-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open Opposite Limits Presheaf

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}

instance [F.IsDense] [LocallySmall.{w} D] : (restrictedShrinkYoneda.{w} F).Faithful where
  map_injective h :=
    (F.denseAt _).hom_ext' (fun X p ↦ by
      simpa [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}] using
        ConcreteCategory.congr_hom (NatTrans.congr_app h (op X))
          (shrinkYonedaObjObjEquiv.symm p))

instance [F.IsDense] [LocallySmall.{w} D] : (restrictedShrinkYoneda.{w} F).Full where
  map_surjective {Y Z} f := by
    let c : Cocone (CostructuredArrow.proj F Y ⋙ F) :=
      { pt := Z
        ι.app g := shrinkYonedaObjObjEquiv (f.app (op g.left)
            (shrinkYonedaObjObjEquiv.symm g.hom))
        ι.naturality g₁ g₂ φ :=
          shrinkYonedaObjObjEquiv.{w}.symm.injective (by
            simpa [shrinkYonedaObjObjEquiv_symm_comp.{w},
              shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}] using
              (f.naturality_apply φ.left.op (shrinkYonedaObjObjEquiv.symm g₂.hom)).symm) }
    refine ⟨(F.denseAt Y).desc c, ?_⟩
    ext ⟨X⟩ x
    obtain ⟨x, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective x
    apply shrinkYonedaObjObjEquiv.{w}.injective
    simpa [c, shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}] using
      (F.denseAt Y).fac c (.mk x)

instance [F.IsDense] : (restrictedYoneda F).Faithful :=
  Functor.Faithful.of_iso (restrictedYonedaIso F).symm

instance [F.IsDense] : (restrictedYoneda F).Full :=
  Functor.Full.of_iso (restrictedYonedaIso F).symm

instance [F.IsDense] : (restrictedULiftYoneda.{w} F).Faithful :=
  Functor.Faithful.of_iso (restrictedULiftYonedaIso F).symm

instance [F.IsDense] : (restrictedULiftYoneda.{w} F).Full :=
  Functor.Full.of_iso (restrictedULiftYonedaIso F).symm

lemma IsDense.of_fullyFaithful_restrictedShrinkYoneda [LocallySmall.{w} D] [F.Full]
    (h : (restrictedShrinkYoneda.{w} F).FullyFaithful) :
    F.IsDense where
  isDenseAt Y := by
    let φ (s : Cocone (CostructuredArrow.proj F Y ⋙ F)) :
        (restrictedShrinkYoneda.{w} F).obj Y ⟶ (restrictedShrinkYoneda F).obj s.pt :=
      { app X := ↾(fun x ↦ shrinkYonedaObjObjEquiv.symm
          (s.ι.app (.mk (shrinkYonedaObjObjEquiv x))))
        naturality X₁ X₂ f := by
          ext x
          let α : CostructuredArrow.mk (shrinkYonedaObjObjEquiv
            ((shrinkYoneda.{w}.obj Y).map (F.map f.unop).op x)) ⟶
              CostructuredArrow.mk (shrinkYonedaObjObjEquiv x) :=
            CostructuredArrow.homMk f.unop (by simp [shrinkYoneda_obj_map])
          simp [dsimp% [α] (s.w α).symm,
            shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm.{w}] }
    have hφ (s) (j) : (restrictedShrinkYoneda F).map j.hom ≫ φ s =
        (restrictedShrinkYoneda F).map (s.ι.app j) := by
      ext X x
      let α : CostructuredArrow.mk (shrinkYonedaObjObjEquiv
          ((shrinkYoneda.{w}.map j.hom).app (op (F.obj (unop X))) x)) ⟶ j :=
        CostructuredArrow.homMk (F.preimage (shrinkYonedaObjObjEquiv x)) (by
          obtain ⟨x, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective x
          simp [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}])
      apply shrinkYonedaObjObjEquiv.{w}.injective
      simp [φ, ← dsimp% [α] s.w α, shrinkYonedaObjObjEquiv_map_app.{w}]
    dsimp at hφ
    exact
      ⟨{desc s := (h.preimage (φ s))
        fac s j := h.map_injective (by simp [hφ])
        uniq s m hm := h.map_injective (by
          ext X x
          obtain ⟨x, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective x
          apply shrinkYonedaObjObjEquiv.{w}.injective
          simp [φ, ← hm, shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm.{w}]) }⟩

lemma IsDense.of_fullyFaithful_restrictedYoneda [F.Full]
    (h : (restrictedYoneda F).FullyFaithful) :
    F.IsDense :=
  IsDense.of_fullyFaithful_restrictedShrinkYoneda.{v₂} (h.ofIso (restrictedYonedaIso F))

lemma IsDense.of_fullyFaithful_restrictedULiftYoneda [F.Full]
    (h : (restrictedULiftYoneda.{w} F).FullyFaithful) :
    F.IsDense :=
  IsDense.of_fullyFaithful_restrictedShrinkYoneda.{max w v₂}
    (h.ofIso (restrictedULiftYonedaIso F))

lemma isDense_iff_fullyFaithful_restrictedShrinkYoneda [LocallySmall.{w} D] [F.Full] :
    F.IsDense ↔ Nonempty (restrictedShrinkYoneda.{w} F).FullyFaithful :=
  ⟨fun _ ↦ ⟨FullyFaithful.ofFullyFaithful _⟩,
    fun ⟨h⟩ ↦ IsDense.of_fullyFaithful_restrictedShrinkYoneda h⟩

lemma isDense_iff_fullyFaithful_restrictedYoneda [F.Full] :
    F.IsDense ↔ Nonempty (restrictedYoneda F).FullyFaithful :=
  ⟨fun _ ↦ ⟨FullyFaithful.ofFullyFaithful _⟩,
    fun ⟨h⟩ ↦ IsDense.of_fullyFaithful_restrictedYoneda h⟩

lemma isDense_iff_fullyFaithful_restrictedULiftYoneda [F.Full] :
    F.IsDense ↔ Nonempty (restrictedULiftYoneda.{w} F).FullyFaithful :=
  ⟨fun _ ↦ ⟨FullyFaithful.ofFullyFaithful _⟩,
    fun ⟨h⟩ ↦ IsDense.of_fullyFaithful_restrictedULiftYoneda h⟩

end CategoryTheory.Functor
