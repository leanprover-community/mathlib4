/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Functor.KanExtension.DenseAt
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Generator.StrongGenerator

/-!
# Dense functors

A functor `F : C ⥤ D` is dense (`F.IsDense`) if `𝟭 D` is a pointwise
left Kan extension of `F` along itself, i.e. any `Y : D` is the
colimit of all `F.obj X` for all morphisms `F.obj X ⟶ Y` (which
is the condition `F.DenseAt Y`).
When `F` is full, we show that this
is equivalent to saying that the restricted Yoneda functor
`D ⥤ Cᵒᵖ ⥤ Type _` is fully faithful (see the lemma
`Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda`).

We also show that the range of a dense functor is a strong
generator (see `Functor.isStrongGenerator_of_isDense`).

## References

* https://ncatlab.org/nlab/show/dense+subcategory

-/

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits Opposite Presheaf

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {C' : Type u₃} [Category.{v₃} C']

namespace Functor

/-- A functor `F : C ⥤ D` is dense if any `Y : D` is a canonical colimit
relatively to `F`. -/
class IsDense (F : C ⥤ D) : Prop where
  isDenseAt (F) (Y : D) : F.isDenseAt Y

/-- This is a choice of structure `F.DenseAt Y` when `F : C ⥤ D`
is dense, and `Y : D`. -/
noncomputable def denseAt (F : C ⥤ D) [F.IsDense] (Y : D) : F.DenseAt Y :=
  (IsDense.isDenseAt F Y).some

lemma isDense_iff_nonempty_isPointwiseLeftKanExtension (F : C ⥤ D) :
    F.IsDense ↔
      Nonempty ((LeftExtension.mk _ (rightUnitor F).inv).IsPointwiseLeftKanExtension) :=
  ⟨fun _ ↦ ⟨fun _ ↦ F.denseAt _⟩, fun ⟨h⟩ ↦ ⟨fun _ ↦ ⟨h _⟩⟩⟩

lemma IsDense.of_iso {F G : C ⥤ D} (e : F ≅ G) [F.IsDense] :
    G.IsDense where
  isDenseAt Y := by
    rw [← Functor.congr_isDenseAt e]
    exact ⟨F.denseAt Y⟩

lemma IsDense.iff_of_iso {F G : C ⥤ D} (e : F ≅ G) :
    F.IsDense ↔ G.IsDense :=
  ⟨fun _ ↦ of_iso e, fun _ ↦ of_iso e.symm⟩

variable (F : C ⥤ D)

instance (G : C' ⥤ C) [F.IsDense] [G.IsEquivalence] :
    (G ⋙ F).IsDense where
  isDenseAt Y := ⟨(F.denseAt Y).precompEquivalence G⟩

lemma IsDense.comp_left_iff_of_isEquivalence (G : C' ⥤ C) [G.IsEquivalence] :
    (G ⋙ F).IsDense ↔ F.IsDense := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  let e : G.inv ⋙ G ⋙ F ≅ F := (associator _ _ _).symm ≪≫
    isoWhiskerRight (G.asEquivalence.counitIso) _ ≪≫ F.leftUnitor
  exact of_iso e

instance [F.IsDense] : (restrictedULiftYoneda.{w} F).Faithful where
  map_injective h :=
    (F.denseAt _).hom_ext' (fun X p ↦ by
      simpa using ULift.up_injective (congr_fun (NatTrans.congr_app h (op X)) (ULift.up p)))

instance [F.IsDense] : (restrictedULiftYoneda.{w} F).Full where
  map_surjective {Y Z} f := by
    let c : Cocone (CostructuredArrow.proj F Y ⋙ F) :=
      { pt := Z
        ι :=
          { app g := ((f.app (op g.left)) (ULift.up g.hom)).down
            naturality g₁ g₂ φ := by
              simpa [uliftFunctor, uliftYoneda,
                restrictedULiftYoneda, ← ULift.down_inj] using
                (congr_fun (f.naturality φ.left.op) (ULift.up g₂.hom)).symm }}
    refine ⟨(F.denseAt Y).desc c, ?_⟩
    ext ⟨X⟩ ⟨x⟩
    have := (F.denseAt Y).fac c (.mk x)
    dsimp [c] at this
    simpa using ULift.down_injective this

variable {F} in
lemma IsDense.of_fullyFaithful_restrictedULiftYoneda [F.Full]
    (h : (restrictedULiftYoneda.{w} F).FullyFaithful) :
    F.IsDense where
  isDenseAt Y := by
    let φ (s : Cocone (CostructuredArrow.proj F Y ⋙ F)) :
        (restrictedULiftYoneda.{w} F).obj Y ⟶ (restrictedULiftYoneda F).obj s.pt :=
      { app := fun ⟨X⟩ ⟨x⟩ ↦ ULift.up (s.ι.app (.mk x))
        naturality := by
          rintro ⟨X₁⟩ ⟨X₂⟩ ⟨f⟩
          ext ⟨x⟩
          let α : CostructuredArrow.mk (F.map f ≫ x) ⟶ CostructuredArrow.mk x :=
            CostructuredArrow.homMk f
          simp [uliftYoneda, ← s.w α, α] }
    have hφ (s) (j) : (restrictedULiftYoneda F).map j.hom ≫ φ s =
        (restrictedULiftYoneda F).map (s.ι.app j) := by
      ext ⟨X⟩ ⟨x⟩
      let α : .mk (x ≫ j.hom) ⟶ j := CostructuredArrow.homMk (F.preimage x)
      have := s.w α
      dsimp [uliftYoneda, φ, α] at this ⊢
      rw [← this, map_preimage]
    exact
      ⟨{desc s := (h.preimage (φ s))
        fac s j := h.map_injective (by simp [hφ])
        uniq s m hm := h.map_injective (by
          ext ⟨X⟩ ⟨x⟩
          simp [uliftYoneda, φ, ← hm])}⟩

lemma isDense_iff_fullyFaithful_restrictedULiftYoneda [F.Full] :
    F.IsDense ↔ Nonempty (restrictedULiftYoneda.{w} F).FullyFaithful :=
  ⟨fun _ ↦ ⟨FullyFaithful.ofFullyFaithful _⟩,
    fun ⟨h⟩ ↦ IsDense.of_fullyFaithful_restrictedULiftYoneda h⟩

open ObjectProperty in
lemma isStrongGenerator_of_isDense [F.IsDense] :
    IsStrongGenerator (.ofObj F.obj) :=
  (IsStrongGenerator.mk_of_exists_colimitsOfShape.{max u₁ u₂ v₁ v₂,
      max u₁ v₁ v₂} (fun Y ↦ ⟨_, _, ⟨{
    ι := _
    diag := _
    isColimit := (IsColimit.whiskerEquivalence (F.denseAt Y)
      ((ShrinkHoms.equivalence _).symm.trans ((Shrink.equivalence _)).symm))
    prop_diag_obj := by simp }⟩⟩))

end Functor

end CategoryTheory
