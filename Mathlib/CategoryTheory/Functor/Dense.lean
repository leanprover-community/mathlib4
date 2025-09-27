/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Canonical
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Generator.StrongGenerator

/-!
# Dense functors

A functor `F : C ⥤ D` is dense (`F.IsDense`) if any `Y : D` is a
canonical colimit relatively to `F`. When `F` is full, we show that this
is equivalent to saying that the restricted Yoneda functor
`D ⥤ Cᵒᵖ ⥤ Type _` is fully faithful (see the lemma
`Functor.isDense_iff_fullyFaithful_restrictedULiftYoneda`).

We also show that the range of a dense functor is a strong
generator (see `Functor.isStrongGenerator_range_of_isDense`).

## References

* https://ncatlab.org/nlab/show/dense+subcategory

-/

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits Opposite Presheaf

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

namespace Functor

/-- A functor `F : C ⥤ D` is dense if any `Y : D` is a canonical colimit
relatively to `F`. -/
class IsDense (F : C ⥤ D) : Prop where
  isCanonicalColimit_eq_top (F) : F.isCanonicalColimit = ⊤

/-- This is a choice of structure `CanonicalColimit F Y` when `F : C ⥤ D`
is dense, and `Y : D`. -/
noncomputable def canonicalColimitOfIsDense (F : C ⥤ D) [F.IsDense] (Y : D) :
    CanonicalColimit F Y :=
  ((IsDense.isCanonicalColimit_eq_top F).symm.le _ (by simp)).canonicalColimit

variable (F : C ⥤ D)

instance [F.IsDense] : (restrictedULiftYoneda.{w} F).Faithful where
  map_injective h :=
    (canonicalColimitOfIsDense F _).hom_ext' (fun X p ↦
      ULift.up_injective (congr_fun (NatTrans.congr_app h (op X)) (ULift.up p)))

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
    refine ⟨(canonicalColimitOfIsDense F Y).desc c, ?_⟩
    ext ⟨X⟩ ⟨x⟩
    exact ULift.down_injective ((canonicalColimitOfIsDense F Y).fac c (.mk x))

variable {F} in
lemma IsDense.of_fullyFaithful_restrictedULiftYoneda [F.Full]
    (h : (restrictedULiftYoneda.{w} F).FullyFaithful) :
    F.IsDense where
  isCanonicalColimit_eq_top := by
    ext Y
    simp only [Pi.top_apply, «Prop».top_eq_true, iff_true]
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
          simp [uliftYoneda, φ, ← hm] ) }⟩

lemma isDense_iff_fullyFaithful_restrictedULiftYoneda [F.Full] :
    F.IsDense ↔ Nonempty (restrictedULiftYoneda.{w} F).FullyFaithful :=
  ⟨fun _ ↦ ⟨FullyFaithful.ofFullyFaithful _⟩,
    fun ⟨h⟩ ↦ IsDense.of_fullyFaithful_restrictedULiftYoneda h⟩

lemma isStrongGenerator_range_of_isDense [F.IsDense] :
    IsStrongGenerator (Set.range F.obj) :=
  IsStrongGenerator.mk_of_exists_colimitPresentation.{max u₁ u₂ v₁ v₂}
    (fun Y ↦ ⟨_, _, ColimitPresentation.mk _ _
      (IsColimit.whiskerEquivalence (canonicalColimitOfIsDense F Y)
        ((ShrinkHoms.equivalence _).symm.trans ((Shrink.equivalence _)).symm)),
          fun j ↦ ⟨⟨_, by simp⟩, ⟨Iso.refl _⟩⟩⟩)

end Functor

end CategoryTheory
