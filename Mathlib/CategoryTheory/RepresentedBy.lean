/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# `IsRepresentedBy` predicate

In this file we define the predicate `IsRepresentedBy`: A presheaf `F` is represented by `X`
with universal element `x : F.obj X` if the natural transformation `yoneda.obj X ⟶ F` induced
by `x` is an isomorphism.

For other declarations expressing a functor is representable, see also:

- `CategoryTheory.Functor.RepresentableBy`:
  Structure bundling an explicit natural isomorphism `yoneda.obj X ⟶ F`.
- `CategoryTheory.Functor.IsRepresentable`:
  Predicate asserting the existence of a representing object.

The relations to these other notions are given as
`CategoryTheory.Functor.IsRepresentable.iff_exists_isRepresentedBy` and
`CategoryTheory.Functor.IsRepresentedBy.iff_exists_representableBy`.

## TODOs

- Dualize to `IsCorepresentedBy`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Functor

open Opposite

variable {C : Type u} [Category.{v} C]

/--
A presheaf `F` is represented by `X` with universal element `x : F.obj X`
if the natural transformation `yoneda.obj X ⟶ F` induced by `x` is an isomorphism.
For better universe generality, we state this manually as for every `Y`, the
induced map `(Y ⟶ X) → F.obj Y` is bijective.
-/
@[mk_iff]
structure IsRepresentedBy (F : Cᵒᵖ ⥤ Type w) {X : C} (x : F.obj (op X)) : Prop where
  map_bijective {Y : C} : Function.Bijective (fun f : Y ⟶ X ↦ F.map f.op x)

variable {F : Cᵒᵖ ⥤ Type w} {X : C} {x : F.obj (op X)}

set_option backward.isDefEq.respectTransparency false in
lemma IsRepresentedBy.iff_isIso_uliftYonedaEquiv :
    F.IsRepresentedBy x ↔
      IsIso ((uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩) := by
  rw [isRepresentedBy_iff, NatTrans.isIso_iff_isIso_app, Opposite.op_surjective.forall]
  refine forall_congr' fun Y ↦ ?_
  rw [isIso_iff_bijective, ← Function.Bijective.of_comp_iff _ Equiv.ulift.{w}.symm.bijective,
    ← Function.Bijective.of_comp_iff' Equiv.ulift.{v}.bijective]
  rfl

/-- If `F` is represented by `X` with universal element `x : F.obj X`, modulo universe
lifting, it is isomorphic to `yoneda.obj X`. -/
@[simps! hom]
noncomputable def IsRepresentedBy.uliftYonedaIso (h : F.IsRepresentedBy x) :
    uliftYoneda.obj X ≅ F ⋙ uliftFunctor.{v} :=
  haveI : IsIso ((uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩) := by
    rwa [IsRepresentedBy.iff_isIso_uliftYonedaEquiv] at h
  asIso <| (uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩

/-- The canonical representation induced by the universal element `x : F.obj X`. -/
noncomputable def IsRepresentedBy.representableBy (h : F.IsRepresentedBy x) :
    F.RepresentableBy X :=
  Functor.representableByUliftFunctorEquiv.{v}
    ((RepresentableBy.equivUliftYonedaIso _ _).symm <| h.uliftYonedaIso)

@[simp]
lemma IsRepresentedBy.representableBy_homEquiv_apply (h : F.IsRepresentedBy x)
    {Y : C} (f : Y ⟶ X) :
    h.representableBy.homEquiv f = F.map f.op x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma RepresentableBy.isRepresentedBy (R : F.RepresentableBy X) :
    F.IsRepresentedBy (R.homEquiv (𝟙 X)) := by
  rw [IsRepresentedBy.iff_isIso_uliftYonedaEquiv]
  convert (RepresentableBy.equivUliftYonedaIso _ _ <|
    representableByUliftFunctorEquiv.{v}.symm R).isIso_hom
  ext
  simpa [uliftYonedaEquiv] using (homEquiv_eq _ _).symm

lemma IsRepresentedBy.iff_exists_representableBy :
    F.IsRepresentedBy x ↔ ∃ (R : F.RepresentableBy X), R.homEquiv (𝟙 X) = x :=
  ⟨fun h ↦ ⟨h.representableBy, by simp⟩, fun ⟨R, h⟩ ↦ h ▸ R.isRepresentedBy⟩

lemma IsRepresentedBy.of_natIso (h : F.IsRepresentedBy x) {F' : Cᵒᵖ ⥤ Type w}
    (e : F ≅ F') :
    F'.IsRepresentedBy (e.hom.app (op X) x) := by
  rw [iff_exists_representableBy]
  use h.representableBy.ofIso e
  simp [RepresentableBy.ofIso]

lemma IsRepresentedBy.iff_natIso {F' : Cᵒᵖ ⥤ Type w} (e : F ≅ F') :
    F'.IsRepresentedBy (e.hom.app (op X) x) ↔ F.IsRepresentedBy x :=
  ⟨fun h ↦ by simpa using h.of_natIso e.symm, fun h ↦ .of_natIso h _⟩

lemma IsRepresentedBy.of_isoObj (h : F.IsRepresentedBy x) {Y : C} (e : Y ≅ X) :
    F.IsRepresentedBy (F.map e.hom.op x) := by
  rw [iff_exists_representableBy]
  use h.representableBy.ofIsoObj e
  simp

lemma IsRepresentedBy.iff_of_isoObj {Y : C} (e : Y ≅ X) :
    F.IsRepresentedBy (F.map e.hom.op x) ↔ F.IsRepresentedBy x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.of_isoObj e⟩
  have : x = F.map e.inv.op (F.map e.hom.op x) := by
    simp [← comp_apply, ← map_comp, ← op_comp]
  exact this ▸ .of_isoObj h e.symm

lemma IsRepresentedBy.of_isRepresentable [F.IsRepresentable] : F.IsRepresentedBy F.reprx :=
  F.representableBy.isRepresentedBy

lemma IsRepresentable.iff_exists_isRepresentedBy :
    F.IsRepresentable ↔ ∃ (X : C) (x : F.obj (op X)), F.IsRepresentedBy x :=
  ⟨fun _ ↦ ⟨F.reprX, F.reprx, .of_isRepresentable⟩,
    fun ⟨_, _, h⟩ ↦ h.representableBy.isRepresentable⟩

end CategoryTheory.Functor
