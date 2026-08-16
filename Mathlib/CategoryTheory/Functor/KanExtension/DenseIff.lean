/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Dense
public import Mathlib.CategoryTheory.Limits.Presheaf

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

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

instance [F.IsDense] : (restrictedULiftYoneda.{w} F).Faithful where
  map_injective h :=
    (F.denseAt _).hom_ext' (fun X p ↦ by
      simpa using! ULift.up_injective (ConcreteCategory.congr_hom (CC := fun X ↦ X)
        (NatTrans.congr_app h (op X)) (ULift.up p)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance [F.IsDense] : (restrictedULiftYoneda.{w} F).Full where
  map_surjective {Y Z} f := by
    let c : Cocone (CostructuredArrow.proj F Y ⋙ F) :=
      { pt := Z
        ι :=
          { app g := ((f.app (op g.left)) (ULift.up g.hom)).down
            naturality g₁ g₂ φ := by
              simpa [uliftFunctor, uliftYoneda,
                restrictedULiftYoneda, ← ULift.down_inj] using
                ((f.naturality_apply φ.left.op) (ULift.up g₂.hom)).symm } }
    refine ⟨(F.denseAt Y).desc c, ?_⟩
    ext ⟨X⟩ ⟨x⟩
    have := (F.denseAt Y).fac c (.mk x)
    dsimp [c] at this
    simpa using ULift.down_injective this

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {F} in
lemma IsDense.of_fullyFaithful_restrictedULiftYoneda [F.Full]
    (h : (restrictedULiftYoneda.{w} F).FullyFaithful) :
    F.IsDense where
  isDenseAt Y := by
    let φ (s : Cocone (CostructuredArrow.proj F Y ⋙ F)) :
        (restrictedULiftYoneda.{w} F).obj Y ⟶ (restrictedULiftYoneda F).obj s.pt :=
      { app := fun ⟨X⟩ ↦ ↾fun ⟨x⟩ ↦ ULift.up (s.ι.app (.mk x))
        naturality := by
          rintro ⟨X₁⟩ ⟨X₂⟩ ⟨f⟩
          ext ⟨x⟩
          let α : CostructuredArrow.mk (F.map f ≫ x) ⟶ CostructuredArrow.mk x :=
            CostructuredArrow.homMk f
          exact ULift.down_injective (s.w α).symm }
    have hφ (s) (j) : (restrictedULiftYoneda F).map j.hom ≫ φ s =
        (restrictedULiftYoneda F).map (s.ι.app j) := by
      ext ⟨X⟩ ⟨x⟩
      let α : .mk (x ≫ j.hom) ⟶ j := CostructuredArrow.homMk (F.preimage x)
      have := s.w α
      dsimp [uliftYoneda, φ, α] at this ⊢
      apply ULift.down_injective
      simpa using this.symm
    exact
      ⟨{desc s := (h.preimage (φ s))
        fac s j := h.map_injective (by simp [hφ])
        uniq s m hm := h.map_injective (by
          ext ⟨_⟩ ⟨_⟩
          simp [φ, ← hm]) }⟩

lemma isDense_iff_fullyFaithful_restrictedULiftYoneda [F.Full] :
    F.IsDense ↔ Nonempty (restrictedULiftYoneda.{w} F).FullyFaithful :=
  ⟨fun _ ↦ ⟨FullyFaithful.ofFullyFaithful _⟩,
    fun ⟨h⟩ ↦ IsDense.of_fullyFaithful_restrictedULiftYoneda h⟩

end CategoryTheory.Functor
