/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.AlgebraicGeometry.Scheme

/-!
# The Residue Field of a Point in a Locally Ringed Space and Related Morphisms

In this file, we have defined the residue field of a point in a locally ringed space and some
useful homomorphisms. We aim to construct the following:
• given a locally ringed space `X` and a point `x : X.toTopCat`, the canonical morphism from the
  spectrum of the residue field of `x` to `X`.
-/

instance AlgebraicGeometry.SheafedSpace.section_over_bot_unique {X : SheafedSpace CommRingCat} :
    Unique (X.presheaf.obj { unop := ⊥ }) where
  default := 0
  uniq := fun a ↦ by
    let U : Empty → TopologicalSpace.Opens X.toPresheafedSpace := fun _ ↦ ⊥
    let h := TopCat.Sheaf.eq_of_locally_eq X.sheaf U
    simp only [IsEmpty.forall_iff, true_implies] at h
    rw [congrArg X.sheaf.val.obj (congrArg Opposite.op <| show iSup U = ⊥ by
      simp only [iSup_eq_bot, implies_true])] at h
    exact h a 0

namespace AlgebraicGeometry

namespace LocallyRingedSpace

/--
Given a locally ringed space `X` and a point `x : X.toTopCat`, the residue field of `x` is the
residue field of the stalk at `x`.
-/
noncomputable def ResidueField {X : LocallyRingedSpace} (x : X.toTopCat) : CommRingCat where
  α := LocalRing.ResidueField (stalk X x)
  str := LocalRing.ResidueFieldCommRing (X.stalk x)

lemma ResidueField.isField {X : LocallyRingedSpace} (x : X.toTopCat) :
    IsField (X.ResidueField x) :=
  Semifield.toIsField (LocalRing.ResidueField (X.stalk x))

noncomputable instance {X : LocallyRingedSpace} (x : X.toTopCat) : Field (X.ResidueField x) :=
  LocalRing.ResidueField.field (X.stalk x)

/--
`AlgebraicGeometry.LocallyRingedSpace.StalkToResidueFieldSpecGlobalSectionHom x` is defined as the
composition of `AlgebraicGeometry.StructureSheaf.toOpen (LocalRing.ResidueField (X.stalk x)) ⊤` and
`LocalRing.residue (X.stalk x)`.
-/
noncomputable def StalkToResidueFieldSpecGlobalSectionHom
    {X : LocallyRingedSpace} (x : X.toTopCat) :
    X.stalk x ⟶
    (Scheme.specObj (LocallyRingedSpace.ResidueField x)).presheaf.obj (Opposite.op ⊤) :=
  RingHom.comp (AlgebraicGeometry.StructureSheaf.toOpen (LocalRing.ResidueField (X.stalk x)) ⊤)
    (LocalRing.residue (X.stalk x))

instance Spec.structureSheaf.section_over_bot_unique {R : Type _} [CommRing R] :
    Unique ((Spec.structureSheaf R).val.obj {unop := ⊥}) := by
  rw [show (Spec.structureSheaf R).val.obj {unop := ⊥} =
    (Scheme.specObj ⟨R, _⟩).presheaf.obj {unop := ⊥} by exact rfl]
  exact SheafedSpace.section_over_bot_unique

/--
Given some `O : (TopologicalSpace.Opens ↑↑X.toPresheafedSpace)ᵒᵖ` which contains the point `x`,
there is a canonocal homomorphism from `X.presheaf.obj O` to the section over `O` in terms of the
pushforward of `(Scheme.specObj (LocallyRingedSpace.ResidueField x)).presheaf` along the constant
map `fun _ ↦ x`.
-/
noncomputable def ObjToPushforwardObjHomOfMem {X : LocallyRingedSpace} (x : X.toTopCat)
    (O : (TopologicalSpace.Opens ↑↑X.toPresheafedSpace)ᵒᵖ) (hxO : x ∈ O.unop) :
    X.presheaf.obj O ⟶ (⟨fun _ ↦ x, continuous_const⟩ _*
    (Scheme.specObj (LocallyRingedSpace.ResidueField x)).presheaf).obj O :=
  let x' : O.unop := ⟨x, hxO⟩
  let hom1 := @TopCat.Presheaf.germ CommRingCat _ _ X.toTopCat X.presheaf O.unop x'
  let hom2 := LocallyRingedSpace.StalkToResidueFieldSpecGlobalSectionHom x
  CategoryTheory.CategoryStruct.comp hom1 (CategoryTheory.CategoryStruct.comp hom2
    ((Scheme.specObj (LocallyRingedSpace.ResidueField x)).presheaf.map
    (TopologicalSpace.Opens.leTop _).op))

/--
Given some `O : (TopologicalSpace.Opens ↑↑X.toPresheafedSpace)ᵒᵖ` which does not contain `x`,
`fun _ ↦ 0` is the canonocal homomorphism from `X.presheaf.obj O` to the section over `O` in terms
of the pushforward of `(Scheme.specObj (LocallyRingedSpace.ResidueField x)).presheaf` along the
constant map `fun _ ↦ x`.
-/
noncomputable def ObjToPushforwardObjHomOfNotMem {X : LocallyRingedSpace} (x : X.toTopCat)
    (O : (TopologicalSpace.Opens ↑↑X.toPresheafedSpace)ᵒᵖ) (hxO : x ∉ O.unop) :
    X.presheaf.obj O ⟶ (⟨fun _ ↦ x, continuous_const⟩ _*
    (Scheme.specObj (LocallyRingedSpace.ResidueField x)).presheaf).obj O where
  toFun := fun _ ↦ 0
  map_one' := by
    let _ := @Spec.structureSheaf.section_over_bot_unique (LocallyRingedSpace.ResidueField x) _
    rw [TopCat.Presheaf.pushforwardObj_obj, CategoryTheory.Functor.op_obj]
    erw [(le_bot_iff.mp fun _ ↦ hxO :
      (@TopologicalSpace.Opens.map (Scheme.specObj (LocallyRingedSpace.ResidueField x)) X.toTopCat
      ⟨fun _ ↦ x, continuous_const⟩).obj O.unop = ⊥)]
    exact Eq.symm (Subsingleton.eq_zero 1)
  map_mul' := by simp_rw [mul_zero, implies_true]
  map_zero' := rfl
  map_add' := by simp_rw [add_zero, implies_true]

/--
Given an arbitrary `O : (TopologicalSpace.Opens ↑↑X.toPresheafedSpace)ᵒᵖ`, there is a canonocal
homomorphism from `X.presheaf.obj O` to the section over `O` in terms of the pushforward of
`(Scheme.specObj (LocallyRingedSpace.ResidueField x)).presheaf` along the constant map `fun _ ↦ x`.
-/
noncomputable def ObjToPushforwardObjHom {X : LocallyRingedSpace} (x : X.toTopCat)
    (O : (TopologicalSpace.Opens ↑↑X.toPresheafedSpace)ᵒᵖ) :
    X.presheaf.obj O ⟶ (⟨fun _ ↦ x, continuous_const⟩ _*
    (Scheme.specObj (LocallyRingedSpace.ResidueField x)).presheaf).obj O :=
  let _ := Classical.propDecidable (x ∈ O.unop)
  if hxO : x ∈ O.unop then ObjToPushforwardObjHomOfMem x O hxO
  else ObjToPushforwardObjHomOfNotMem x O hxO

/--
`AlgebraicGeometry.LocallyRingedSpace.ObjToPushforwardObjHom x` satisfies the natural property.
This theorem is a basis for constructing the canonical morphism from the spectrum of the residue
field of `x` to `X`.
-/
theorem ObjToPushforwardObjHom_naturality {X : LocallyRingedSpace} (x : X.toTopCat) :
    ∀ {O1 O2 : (TopologicalSpace.Opens ↑↑X.toPresheafedSpace)ᵒᵖ} (f : O1 ⟶ O2),
    CategoryTheory.CategoryStruct.comp (X.presheaf.map f) (ObjToPushforwardObjHom x O2) =
    CategoryTheory.CategoryStruct.comp (ObjToPushforwardObjHom x O1)
    ((⟨fun _ ↦ x, continuous_const⟩ _*
    (Scheme.specObj (LocallyRingedSpace.ResidueField x)).presheaf).map f) := by
  intro O1 O2 f
  ext s
  rw [ObjToPushforwardObjHom, ObjToPushforwardObjHom]
  by_cases hxO2 : x ∈ O2.unop
  · have hxO1 : x ∈ O1.unop := CategoryTheory.le_of_op_hom f hxO2
    simp only [hxO2, hxO1, CategoryTheory.comp_apply]
    erw [RingHom.comp_apply, TopCat.Presheaf.germ_res_apply X.presheaf f.unop ⟨x, hxO2⟩ s]
    rfl
  · simp only [hxO2]
    have : Unique (((Scheme.specObj (LocallyRingedSpace.ResidueField x)).presheaf.obj
        { unop := (TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).obj O2.unop })) := by
      erw [(le_bot_iff.mp fun _ ↦ hxO2 :
        (@TopologicalSpace.Opens.map (Scheme.specObj (LocallyRingedSpace.ResidueField x))
        X.toTopCat ⟨fun _ ↦ x, continuous_const⟩).obj O2.unop = ⊥)]
      exact @Spec.structureSheaf.section_over_bot_unique (LocallyRingedSpace.ResidueField x) _
    exact Eq.trans (this.eq_default _) (this.default_eq _)

end LocallyRingedSpace

end AlgebraicGeometry
