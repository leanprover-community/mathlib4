/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Canonical morphism

The main thing constructed in this file is:
Given a scheme `X` and a point `x : X.toTopCat`, the canonical scheme morphism from the
spectrum of the residue field of `x` to `X`.
-/

/--
If two rings are isomorphic and one of them is a field, then the other ring is also a field.
-/
theorem isField_of_iso {R : CommRingCat} {S : CommRingCat} (i : R ≅ S) (hS : IsField S) :
    IsField R where
  exists_pair_ne := by
    rcases hS.exists_pair_ne with ⟨x, y, hxy⟩
    exact ⟨i.symm.hom x, i.symm.hom y, fun h ↦ by
      have : i.hom (i.inv x) = i.hom (i.inv y) := congrArg i.hom h
      rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, CategoryTheory.Iso.inv_hom_id,
        CategoryTheory.id_apply] at this
      exact hxy this⟩
  mul_comm := fun x y ↦ by
    have (r : R) : r = i.inv (i.hom r) := by
      rw [← CategoryTheory.comp_apply, CategoryTheory.Iso.hom_inv_id, CategoryTheory.id_apply]
    rw [this x, this y, ← map_mul, mul_comm, map_mul]
  mul_inv_cancel := by
    intro a ha
    rcases hS.mul_inv_cancel (fun h ↦ by
      let this := congr_arg i.inv h
      rw [← CategoryTheory.comp_apply, CategoryTheory.Iso.hom_inv_id, CategoryTheory.id_apply,
        map_zero] at this
      exact ha this) with ⟨b, hb⟩
    exact ⟨i.inv b, by
      let hb' := congr_arg i.inv hb
      rw [map_mul, ← CategoryTheory.comp_apply, CategoryTheory.Iso.hom_inv_id,
        CategoryTheory.id_apply, map_one] at hb'
      exact hb'⟩

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

instance AlgebraicGeometry.Spec.structureSheaf.section_over_bot_unique {R : Type _} [CommRing R] :
    Unique ((Spec.structureSheaf R).val.obj {unop := ⊥}) := by
  rw [show (Spec.structureSheaf R).val.obj {unop := ⊥} =
    (Scheme.specObj ⟨R, _⟩).presheaf.obj {unop := ⊥} by exact rfl]
  exact SheafedSpace.section_over_bot_unique

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

/--
An isomorphism used for constructing a colimit.
-/
noncomputable def ConstMapObjResidueFieldIso
    {X : LocallyRingedSpace} (x : X.toTopCat) (O : (TopologicalSpace.OpenNhds x)ᵒᵖ) :
    (Spec.structureSheaf (LocallyRingedSpace.ResidueField x)).val.obj
    (Opposite.op ((TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).obj
    ((TopologicalSpace.OpenNhds.inclusion x).obj O.unop))) ≅
    (LocallyRingedSpace.ResidueField x) :=
  CategoryTheory.Iso.trans
    (CategoryTheory.eqToIso <| by
    rw [TopologicalSpace.Opens.map]; simp only; congr; simp only [Set.preimage_eq_univ_iff];
    intro x' h; change ∃ _, x = x' at h; rcases h with ⟨_, h1⟩; rw [← h1]; exact O.1.2 : _ ≅ _)
    (StructureSheaf.globalSectionsIso (LocallyRingedSpace.ResidueField x)).symm

/--
A cocone used for proving that a colimit is a field.
-/
noncomputable def OpenNhdsResidueFieldCocone {X : LocallyRingedSpace} (x : X.toTopCat) :
    CategoryTheory.Limits.Cocone
    ((TopologicalSpace.OpenNhds.inclusion x).op.comp
    ((TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).op.comp
    (Spec.structureSheaf (LocallyRingedSpace.ResidueField x)).val)) where
  pt := LocallyRingedSpace.ResidueField x
  ι := {
    app := fun O ↦ (ConstMapObjResidueFieldIso x O).hom
    naturality := fun O1 O2 f ↦ by
      simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.op_obj,
        CategoryTheory.Functor.const_obj_obj, CategoryTheory.Functor.comp_map,
        CategoryTheory.Functor.op_map, Quiver.Hom.unop_op, CategoryTheory.Functor.const_obj_map,
        CategoryTheory.Category.comp_id]
      have hO (O : (TopologicalSpace.OpenNhds x)ᵒᵖ) : (TopologicalSpace.Opens.map
          (@ContinuousMap.mk (PrimeSpectrum.Top (LocallyRingedSpace.ResidueField x)) X.toTopCat
          (PrimeSpectrum.Top (LocallyRingedSpace.ResidueField x)).str X.toTopCat.str (fun _ ↦ x)
          continuous_const)).obj ((TopologicalSpace.OpenNhds.inclusion x).obj O.unop) = ⊤ := by
        ext
        simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
          TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
        exact O.1.2
      rw [ConstMapObjResidueFieldIso, ConstMapObjResidueFieldIso]
      simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.eqToIso.hom,
        CategoryTheory.Iso.symm_hom, StructureSheaf.globalSectionsIso_inv,
        CategoryTheory.IsIso.eq_comp_inv, CategoryTheory.Category.assoc,
        CategoryTheory.IsIso.inv_hom_id, CategoryTheory.Category.comp_id]
      have heqToHom1 : ((TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).map
          ((TopologicalSpace.OpenNhds.inclusion x).map f.unop)).op = CategoryTheory.eqToHom
          (show _ = _ by rw [hO O1, hO O2]) := rfl
      have heqToHom2 : (Spec.structureSheaf (LocallyRingedSpace.ResidueField x)).val.map
          ((TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).map
          ((TopologicalSpace.OpenNhds.inclusion x).map f.unop)).op = CategoryTheory.eqToHom
          (show _ = _ by rw [hO O1, hO O2]) := by
        rw [heqToHom1, CategoryTheory.eqToHom_map]
      rw [heqToHom2, CategoryTheory.eqToHom_trans]
  }

theorem OpenNhdsResidueFieldCocone.isColimit_fac
    {X : LocallyRingedSpace} (x : X.toTopCat) (O : (TopologicalSpace.OpenNhds x)ᵒᵖ)
    (s : CategoryTheory.Limits.Cocone ((TopologicalSpace.OpenNhds.inclusion x).op.comp
      ((TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).op.comp
        (Spec.structureSheaf (LocallyRingedSpace.ResidueField x)).val))) :
    CategoryTheory.CategoryStruct.comp ((OpenNhdsResidueFieldCocone x).ι.app O)
      ((fun s ↦
        CategoryTheory.CategoryStruct.comp (ConstMapObjResidueFieldIso x { unop := ⊤ }).symm.hom
          (s.ι.app { unop := ⊤ })) s) = s.ι.app O := by
  simp_rw [OpenNhdsResidueFieldCocone, ConstMapObjResidueFieldIso]
  simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.op_obj,
    CategoryTheory.Functor.const_obj_obj, CategoryTheory.Iso.trans_hom,
    CategoryTheory.eqToIso.hom, CategoryTheory.Iso.symm_hom, StructureSheaf.globalSectionsIso_inv,
    CategoryTheory.eqToIso_refl, CategoryTheory.Iso.refl_trans, CategoryTheory.Iso.symm_symm_eq,
    StructureSheaf.globalSectionsIso_hom, CategoryTheory.Category.assoc,
    CategoryTheory.IsIso.inv_hom_id_assoc]
  rw [CategoryTheory.eqToHom_comp_iff, ← CategoryTheory.eqToHom_map _ <| show _ = _ by
    rw [Opposite.op_inj_iff]; ext; exact ⟨fun _ ↦ O.1.2, fun _ ↦ trivial⟩]
  exact Eq.symm (s.ι.naturality (Opposite.op (LE.le.hom fun _ _ ↦ trivial : O.unop ⟶ ⊤)))

/--
This is used for proving that the relative cocone is a field.
-/
noncomputable def OpenNhdsResidueFieldCocone.isColimit {X : LocallyRingedSpace} (x : X.toTopCat) :
    CategoryTheory.Limits.IsColimit (OpenNhdsResidueFieldCocone x) where
  desc := fun s ↦
    CategoryTheory.CategoryStruct.comp (ConstMapObjResidueFieldIso x (Opposite.op ⊤)).symm.hom
    (s.ι.app (Opposite.op ⊤))
  fac := fun s O ↦ OpenNhdsResidueFieldCocone.isColimit_fac x O s
  uniq := fun s hom h ↦ by
    simp only [CategoryTheory.Iso.symm_hom]
    rw [(CategoryTheory.Iso.eq_inv_comp (ConstMapObjResidueFieldIso x { unop := ⊤ })).mpr
      (h { unop := ⊤ })]

/--
An isomorphism used for constructing a colimit.
-/
noncomputable def PushForwardStalkResidueFieldIso {X : LocallyRingedSpace} (x : X.toTopCat) :
    (⟨fun _ ↦ x, continuous_const⟩ _*
    (Spec.structureSheaf (LocallyRingedSpace.ResidueField x)).val).stalk x ≅
    LocallyRingedSpace.ResidueField x :=
  (CategoryTheory.Limits.colimit.isColimit ((TopologicalSpace.OpenNhds.inclusion x).op.comp
  ((TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).op.comp
  (Spec.structureSheaf (LocallyRingedSpace.ResidueField x)).val))).coconePointUniqueUpToIso
  (OpenNhdsResidueFieldCocone.isColimit x)

/--
An isomorphsim used for constructing a colimit.
-/
noncomputable def SpecObjResidueFieldIso {X : LocallyRingedSpace} (x : X.toTopCat)
    (x1 : (Scheme.specObj (LocallyRingedSpace.ResidueField x)).toPresheafedSpace)
    (O : (TopologicalSpace.OpenNhds x1)ᵒᵖ) :
    (Spec.structureSheaf (LocallyRingedSpace.ResidueField x)).val.obj
    { unop := (TopologicalSpace.OpenNhds.inclusion x1).obj O.unop } ≅
    LocallyRingedSpace.ResidueField x :=
  CategoryTheory.Iso.trans
    (CategoryTheory.eqToIso <| by
      rw [show (TopologicalSpace.OpenNhds.inclusion x1).obj O.unop = ⊤ by
        ext x2; simp; rw [Eq.trans (PrimeSpectrum.instUnique.eq_default x2)
        (PrimeSpectrum.instUnique.default_eq x1)]; exact O.1.2])
    (StructureSheaf.globalSectionsIso (LocallyRingedSpace.ResidueField x)).symm

/--
A cocone used for proving that a colimit is a field.
-/
noncomputable def SpecObjResidueFieldCocone {X : LocallyRingedSpace} (x : X.toTopCat)
    (x1 : ↑↑(Scheme.specObj (LocallyRingedSpace.ResidueField x)).toPresheafedSpace) :
    CategoryTheory.Limits.Cocone
    ((TopologicalSpace.OpenNhds.inclusion x1).op.comp
    (Spec.structureSheaf (LocallyRingedSpace.ResidueField x)).val) where
  pt := LocallyRingedSpace.ResidueField x
  ι := {
    app := fun O ↦ (SpecObjResidueFieldIso x x1 O).hom
    naturality := fun O1 O2 f ↦ by
      simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.op_obj,
        CategoryTheory.Functor.const_obj_obj, CategoryTheory.Functor.comp_map,
        CategoryTheory.Functor.op_map, CategoryTheory.Functor.const_obj_map,
        CategoryTheory.Category.comp_id]
      rw [SpecObjResidueFieldIso, SpecObjResidueFieldIso]
      have : ((TopologicalSpace.OpenNhds.inclusion x1).map f.unop).op =
          CategoryTheory.eqToHom (by
          simp only [Scheme.specObj_toLocallyRingedSpace, Spec.locallyRingedSpaceObj_toSheafedSpace,
            Spec.sheafedSpaceObj_carrier, Opposite.op.injEq]
          ext x2
          rw [Eq.trans (PrimeSpectrum.instUnique.eq_default x2)
            (PrimeSpectrum.instUnique.default_eq x1)]
          exact ⟨fun _ ↦ O2.1.2, fun _ ↦ O1.1.2⟩) := by
        exact CategoryTheory.eq_of_comp_right_eq fun {X_1} ↦ congrFun rfl
      rw [this, CategoryTheory.eqToHom_map]
      simp only [CategoryTheory.Iso.trans_hom, CategoryTheory.eqToIso.hom,
        CategoryTheory.eqToHom_trans_assoc]
  }

set_option maxHeartbeats 500000

/--
This is used for proving that a colimit is a field.
-/
noncomputable def SpecObjResidueFieldCocone.isColimit {X : LocallyRingedSpace} (x : X.toTopCat)
    (x1 : ↑↑(Scheme.specObj (LocallyRingedSpace.ResidueField x)).toPresheafedSpace) :
    CategoryTheory.Limits.IsColimit (SpecObjResidueFieldCocone x x1) where
  desc := fun s ↦
    CategoryTheory.CategoryStruct.comp (SpecObjResidueFieldIso x x1 (Opposite.op ⊤)).symm.hom
    (s.ι.app (Opposite.op ⊤))
  fac := fun s O ↦ by
    simp_rw [SpecObjResidueFieldCocone]
    rw [SpecObjResidueFieldIso, SpecObjResidueFieldIso]
    simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.op_obj,
      CategoryTheory.Functor.const_obj_obj, Scheme.specObj_toLocallyRingedSpace,
      Spec.locallyRingedSpaceObj_toSheafedSpace, Spec.sheafedSpaceObj_carrier,
      CategoryTheory.Iso.trans_hom, CategoryTheory.eqToIso.hom, CategoryTheory.Iso.symm_hom,
      StructureSheaf.globalSectionsIso_inv, CategoryTheory.eqToIso_refl,
      CategoryTheory.Iso.refl_trans, CategoryTheory.Iso.symm_symm_eq,
      StructureSheaf.globalSectionsIso_hom, CategoryTheory.Category.assoc,
      CategoryTheory.IsIso.inv_hom_id_assoc]
    rw [CategoryTheory.eqToHom_comp_iff, ← CategoryTheory.eqToHom_map _ (by
      simp only [Opposite.op.injEq]
      ext x2
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, SetLike.mem_coe, true_iff]
      rw [Eq.trans (PrimeSpectrum.instUnique.eq_default x2)
        (PrimeSpectrum.instUnique.default_eq x1)]
      exact O.1.2)]
    exact Eq.symm (s.ι.naturality (Opposite.op (LE.le.hom fun _ _ ↦ trivial : O.unop ⟶ ⊤)))
  uniq := fun s hom h ↦ by
    simp_rw [← h (Opposite.op ⊤), SpecObjResidueFieldCocone]
    rw [← CategoryTheory.Category.assoc]
    simp only [CategoryTheory.Functor.const_obj_obj, Scheme.specObj_toLocallyRingedSpace,
      Spec.locallyRingedSpaceObj_toSheafedSpace, Spec.sheafedSpaceObj_carrier,
      CategoryTheory.Iso.symm_hom, CategoryTheory.Iso.inv_hom_id, CategoryTheory.Category.id_comp]

/--
The related stalk is isomorhpic to a field.
-/
noncomputable def SpecStalkResidueFieldIso {X : LocallyRingedSpace} (x : X.toTopCat)
    (x1 : ↑↑(Scheme.specObj (LocallyRingedSpace.ResidueField x)).toPresheafedSpace) :
    TopCat.Presheaf.stalk (Spec.structureSheaf (LocallyRingedSpace.ResidueField x)).val x1 ≅
    LocallyRingedSpace.ResidueField x :=
  (CategoryTheory.Limits.colimit.isColimit ((TopologicalSpace.OpenNhds.inclusion x1).op.comp
  (Spec.structureSheaf (LocallyRingedSpace.ResidueField x)).val)).coconePointUniqueUpToIso
  (SpecObjResidueFieldCocone.isColimit x x1)

theorem PresheafStalkFunctorMapHom_eq {X : LocallyRingedSpace} (x : X.toTopCat) :
    (TopCat.Presheaf.stalkFunctor CommRingCat x).map
    ⟨fun O ↦ ObjToPushforwardObjHom x O,
    fun O1 O2 f ↦ ObjToPushforwardObjHom_naturality x f⟩ =
    CategoryTheory.CategoryStruct.comp (CommRingCat.ofHom (LocalRing.residue (X.stalk x)))
    (CategoryTheory.CategoryStruct.comp (CategoryTheory.eqToHom (rfl : CommRingCat.of
    (LocalRing.ResidueField (X.stalk x)) = LocallyRingedSpace.ResidueField x))
    (PushForwardStalkResidueFieldIso x).inv) := by
  refine' Eq.symm (CategoryTheory.Limits.IsColimit.uniq
    (CategoryTheory.Limits.colimit.isColimit ((TopologicalSpace.OpenNhds.inclusion x).op.comp
      X.presheaf))
    (@CategoryTheory.Limits.Cocone.mk (TopologicalSpace.OpenNhds x)ᵒᵖ _ CommRingCat _
      ((TopologicalSpace.OpenNhds.inclusion x).op.comp X.presheaf)
      (CategoryTheory.Limits.colimit ((TopologicalSpace.OpenNhds.inclusion x).op.comp
        (⟨fun _ ↦ x, continuous_const⟩ _*
        (Spec.structureSheaf (LocallyRingedSpace.ResidueField x)).val)))
      (CategoryTheory.CategoryStruct.comp
        (@CategoryTheory.NatTrans.mk (TopologicalSpace.OpenNhds x)ᵒᵖ _ CommRingCat _
        ((TopologicalSpace.OpenNhds.inclusion x).op.comp X.presheaf)
        ((TopologicalSpace.OpenNhds.inclusion x).op.comp (⟨fun _ ↦ x, continuous_const⟩ _*
        (Spec.structureSheaf (LocallyRingedSpace.ResidueField x)).val))
        (fun O ↦ ObjToPushforwardObjHom x
        { unop := (TopologicalSpace.OpenNhds.inclusion x).obj O.unop })
        (CategoryTheory.whiskerLeft.proof_1 (TopologicalSpace.OpenNhds.inclusion x).op
        ⟨fun O ↦ ObjToPushforwardObjHom x O,
        fun O1 O2 f ↦ ObjToPushforwardObjHom_naturality x f⟩))
        (CategoryTheory.Limits.colimit.cocone ((TopologicalSpace.OpenNhds.inclusion x).op.comp
        (⟨fun _ ↦ x, continuous_const⟩ _*
        (Spec.structureSheaf (LocallyRingedSpace.ResidueField x)).val))).ι))
    (CategoryTheory.CategoryStruct.comp (CommRingCat.ofHom (LocalRing.residue (X.stalk x)))
      (PushForwardStalkResidueFieldIso x).inv) _)
  intro O
  simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.op_obj,
    Scheme.specObj_toLocallyRingedSpace, Spec.locallyRingedSpaceObj_toSheafedSpace,
    Spec.sheafedSpaceObj_carrier, Spec.sheafedSpaceObj_presheaf,
    CategoryTheory.Limits.colimit.cocone_x, CategoryTheory.Functor.const_obj_obj,
    CategoryTheory.Limits.colimit.cocone_ι, CategoryTheory.NatTrans.comp_app,
    TopCat.Presheaf.pushforwardObj_obj]
  rw [ObjToPushforwardObjHom, PushForwardStalkResidueFieldIso]
  have hxO (O : (TopologicalSpace.OpenNhds x)ᵒᵖ) :
    x ∈ (TopologicalSpace.OpenNhds.inclusion x).obj O.unop := O.1.2
  simp only [hxO, ↓reduceDite]
  rw [ObjToPushforwardObjHomOfMem, StalkToResidueFieldSpecGlobalSectionHom,
    ← CommRingCat.comp_eq_ring_hom_comp]
  simp only [CategoryTheory.Category.assoc]
  rw [OpenNhdsResidueFieldCocone.isColimit,
    CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso]
  simp only [CategoryTheory.Functor.mapIso_inv, CategoryTheory.Limits.IsColimit.uniqueUpToIso_inv,
    CategoryTheory.Limits.Cocones.forget_map,
    CategoryTheory.Limits.IsColimit.descCoconeMorphism_hom, CategoryTheory.Limits.colimit.cocone_x,
    CategoryTheory.Limits.colimit.cocone_ι]
  congr
  exact Eq.symm (@CategoryTheory.Limits.colimit.w
    (TopologicalSpace.OpenNhds x)ᵒᵖ _ CommRingCat _
    ((TopologicalSpace.OpenNhds.inclusion x).op.comp
    ((TopologicalSpace.Opens.map ⟨fun _ ↦ x, continuous_const⟩).op.comp
    (Spec.structureSheaf ↑(LocallyRingedSpace.ResidueField x)).val)) _
    (Opposite.op ⊤) O (CategoryTheory.opHomOfLE fun _ _ ↦ trivial : (Opposite.op ⊤) ⟶ O))

/--
Given a scheme `X` and a point `x : X.toTopCat`, the canonical scheme homomorphism from the
spectrum of the residue field of `x` to `X`.
-/
noncomputable def HomFromSpecObjResidueField {X : LocallyRingedSpace} (x : X.toTopCat) :
    (Scheme.specObj (LocallyRingedSpace.ResidueField x)).toLocallyRingedSpace ⟶ X where
  val := {
    base := ⟨fun _ ↦ x, continuous_const⟩
    c := ⟨fun O ↦ ObjToPushforwardObjHom x O,
      fun O1 O2 f ↦ ObjToPushforwardObjHom_naturality x f⟩
  }
  prop := fun x1 ↦ by
    let g := TopCat.Presheaf.stalkPushforward CommRingCat ⟨fun _ ↦ x, continuous_const⟩
      (Spec.structureSheaf (LocallyRingedSpace.ResidueField x)).val x1
    let f := (TopCat.Presheaf.stalkFunctor CommRingCat
      ((@DFunLike.coe (Spec.topObj (LocallyRingedSpace.ResidueField x) ⟶ X.toPresheafedSpace)
      (PrimeSpectrum (LocallyRingedSpace.ResidueField x))
      (fun _ ↦ (CategoryTheory.forget TopCat).obj X.toPresheafedSpace) _
      ⟨fun _ ↦ x, continuous_const⟩) x1)).map
      ⟨fun O ↦ ObjToPushforwardObjHom x O,
      fun O1 O2 f ↦ ObjToPushforwardObjHom_naturality x f⟩
    have hg : IsLocalRingHom g := IsLocalRingHom.mk fun a hga ↦ by
      let _ := (isField_of_iso (SpecStalkResidueFieldIso x x1)
        (LocallyRingedSpace.ResidueField.isField x)).nontrivial
      rw [isUnit_iff_exists] at hga ⊢
      have hga0 : g a ≠ 0 := fun h ↦ by
        rw [h] at hga
        simp only [zero_mul, zero_ne_one, mul_zero, and_self, exists_const] at hga
      have ha0 : a ≠ 0 := fun h ↦ by rw [h, map_zero] at hga0; exact hga0 rfl
      rcases ((isField_of_iso (PushForwardStalkResidueFieldIso x)
        (LocallyRingedSpace.ResidueField.isField x)).mul_inv_cancel ha0) with ⟨b, hb⟩
      exact ⟨b, hb, by rw [mul_comm]; exact hb⟩
    have hf : IsLocalRingHom f := by
      change IsLocalRingHom ((TopCat.Presheaf.stalkFunctor CommRingCat x).map _)
      erw [PresheafStalkFunctorMapHom_eq]
      let _ := isLocalRingHom_of_isIso (PushForwardStalkResidueFieldIso x).inv
      let _ : IsLocalRingHom (CommRingCat.ofHom (LocalRing.residue (X.stalk x))) :=
        @LocalRing.isLocalRingHom_residue (X.stalk x) _ _
      exact CommRingCat.isLocalRingHom_comp (CommRingCat.ofHom (LocalRing.residue (X.stalk x)))
        (PushForwardStalkResidueFieldIso x).inv
    exact @isLocalRingHom_comp _ _ _ _ _ _ g f hg hf

end LocallyRingedSpace

end AlgebraicGeometry
